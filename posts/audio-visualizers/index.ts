let FFTBinCount = 2049;
let FFTSize = (FFTBinCount - 1) * 2;
let HalfLifeMin = 0;
let HalfLifeMax = 1.5;

function lerp(a, b, t: number): number {
    return (1.0 - t)*a + t*b;
}

function clamp(a, b, t: number): number {
    return (t < a) ? a
         : (t > b) ? b
         : t;
}

function clampMin(a, t: number): number {
    return (t < a) ? a : t;
}

function remap(a, b, c, d, x: number): number {
    let t = (x - a) / (b - a);
    return lerp(c, d, t);
}

function logControl(c: number): number {
    return Math.pow(2, remap(0, 1, -16, 16, c)) ;
}

function compress(x: number, control: number): number {
    let c = logControl(control);
    // Note: for c that produces a linear warp, c is very large, so this only really works in f64
    let fudge = lerp(0.25, 1.0, control);
    return fudge * fudge * remap(Math.log(c), Math.log(c + 0.25), 0.0, 1.0, Math.log(c + x));
}

function cubicControlPosition(value: number, min: number, max: number): number {
    return Math.cbrt(remap(min, max, 0, 1, value));
}

function cubicControlValue(position: number, min: number, max: number): number {
    return remap(0, 1, min, max, position * position * position);
}

type Attrs = Record<string, string | number | boolean>;
type Child = Node | string;

function dom_element<K extends keyof HTMLElementTagNameMap>(tag: K, attrs: Attrs, ...children: Child[]) {
    let node = document.createElement(tag);
    for (let [name, value] of Object.entries(attrs)) {
        if (value !== false) node.setAttribute(name, value === true ? "" : String(value));
    }
    node.append(...children);
    return node;
}

function dom_div(attrs: Attrs, ...children: Child[]) { return dom_element("div", attrs, ...children); }
function dom_fieldset(attrs: Attrs, ...children: Child[]) { return dom_element("fieldset", attrs, ...children); }

function makePresetControl() {
    let input = dom_element("input", { type: "checkbox", checked: true });
    let name = dom_element("span", { class: "preset-name" });
    let element = dom_element("label", { class: "preset-control" },
        input,
        dom_element("span", {},
            dom_element("span", { class: "preset-heading" }, "Preset:"),
            name,
        ),
    );
    return { element, input, name };
}

type Settings = {
    f0: number;
    f1: number;
    f2: number;
    frequencyCompression: number;
    bassFrequency: number;
    midsFrequency: number;
    bassPower: number;
    compression: number;
    aBlend: number;
    aPower: number;
    halfLifeSeconds: number;
    decayQ: number;
    zeroDeltaHalfLifeSeconds: number;
    barCount: number;
    bassBarCount: number;
    scale: number;
};

let Defaults: Settings = {
    f0: 10,
    f1: 120,
    f2: 16000,
    frequencyCompression: 0,
    bassFrequency: 120,
    midsFrequency: 4000,
    bassPower: 0.15,
    compression: 0.33,
    aBlend: 1,
    aPower: 0.8,
    halfLifeSeconds: 40 / 1000,
    decayQ: 1,
    zeroDeltaHalfLifeSeconds: 100 / 1000,
    barCount: 96 + 24,
    bassBarCount: 12,
    scale: 5,
};

type Preset = { label: string; settings: Settings };

const Presets: Record<string, Preset> = {
    "noisy-bins":            { label: "No filtering",        settings: { ...Defaults, halfLifeSeconds: 0, zeroDeltaHalfLifeSeconds: 0 }},
    "sloshy-bins":           { label: "One pole filtering",  settings: { ...Defaults, zeroDeltaHalfLifeSeconds: 0, decayQ: 0 }},
    "default-bins":          { label: "Good",                settings: { ...Defaults }},
    "linear-bins":           { label: "Linear frequencies",  settings: { ...Defaults, frequencyCompression: 1, bassBarCount: 0 }},
    "geometric-bins":        { label: "No bass split",       settings: { ...Defaults, frequencyCompression: 0, f1: logHertzBassSplit(Defaults) }},
    "linear-magnitude-bins": { label: "Linear magnitudes",   settings: { ...Defaults, compression: 1 }},
    "no-aweighting-bins":    { label: "No A-weighting",      settings: { ...Defaults, aBlend: 0, aPower: 0 }},
    "no-juice-bins":         { label: "No juice",            settings: { ...Defaults, decayQ: 0, bassPower: 0, aPower: 1, zeroDeltaHalfLifeSeconds: 0, scale: Defaults.scale * Math.sqrt(2) }}
};

type ControlName = keyof Settings;

type Control = {
    input: HTMLInputElement;
    output: HTMLOutputElement;
};

type Controls = Partial<Record<ControlName, Control>>;

type Marker = {
    element: HTMLElement;
    preset: Preset;
};

function buildVisualizer(root: HTMLElement) {
    let controls: Controls = {};

    function control(name: ControlName, title: string, min: number, max: number, step: number | "any", defaultValue = Defaults[name]) {
        let input = dom_element("input", { type: "range", min, max, step, value: defaultValue });
        let output = dom_element("output", {});
        controls[name] = { input, output };
        return dom_element("label", { class: "control" },
            dom_element("span", {}, title),
            input,
            output,
        );
    }

    root.replaceChildren(
        dom_div({ class: "visualizer-bg" },
            dom_element("canvas", { role: "button" }),
            dom_div({ class: "visualizer-message" },
                dom_element("span", { class: "visualizer-message" }, "Click to play"),
            ),
        ),
        dom_div({ class: "frequency-axis" },
            dom_element("span", { "data-axis": "f0" }),
            dom_element("span", { "data-axis": "f1" }),
            dom_element("span", { "data-axis": "f2" }),
        ),
        dom_div({ class: "audio-controls" },
            dom_element("audio", { controls: true, loop: true }),
            dom_div({ class: "audio-source-row" },
                dom_element("span", { class: "audio-source" }, "Drag something you like on there"),
                dom_element("input", { class: "audio-file", type: "file", accept: "audio/*" }),
            ),
        ),
        dom_div({ class: "visualizer-controls" },
            dom_div({ class: "control-groups" },
                dom_fieldset({ class: "control-group" },
                    dom_element("legend", {}, "Display"),
                    control("f1", "Bass split", logHertzBassSplit(Defaults), 300, "any"),
                    control("frequencyCompression", "Frequency warp", 0, 1, 0.01),
                    control("compression", "Log compression", 0, 1, 0.01),
                    control("aPower", "A-weighting power", 0, 1, 0.01),
                ),
                dom_fieldset({ class: "control-group" },
                    dom_element("legend", {}, "Filter"),
                    control("halfLifeSeconds", "Decay half-life", 0, 1, 0.001, cubicControlPosition(Defaults.halfLifeSeconds, HalfLifeMin, HalfLifeMax)),
                    control("zeroDeltaHalfLifeSeconds", "Zero-delta half-life ", 0, 1, 0.001, cubicControlPosition(Defaults.zeroDeltaHalfLifeSeconds, HalfLifeMin, HalfLifeMax)),
                ),
                dom_fieldset({ class: "control-group" },
                    dom_element("legend", {}, "Juice"),
                    control("decayQ", "High-frequency decay", 0, 6, 0.1),
                    control("bassFrequency", "Bass end", 40, 400, 5),
                    control("midsFrequency", "Mids end", 300, 5000, 50),
                    control("bassPower", "Bass power", 0, 1, 0.01),
                ),
            ),
        ),
    );

    return controls;
}

function logHertzBassSplit(settings: Settings): number {
    return Math.pow(2, remap(0, settings.barCount,  Math.log2(settings.f0), Math.log2(settings.f2), settings.bassBarCount));
}

function formatWarp(position: number): string {
    if (position == 0) return "Logarithmic";
    if (position == 1) return "Linear";
    let exponent = Math.round(remap(0, 1, -16, 16, position));
    let superscript = String(exponent).replace(/[-0-9]/g, c => "⁻⁰¹²³⁴⁵⁶⁷⁸⁹"["-0123456789".indexOf(c)]);
    return `log(2${superscript} + x)`;
}

function formatHalfLife(ms: number): string {
    return ms ? `${Math.round(ms * 1000)} ms` : "Off";
}

function updateControl(control: Control, value: number, label: string) {
    let { input, output } = control;
    input.value = String(value);
    output.textContent = label;
    let position = remap(Number(input.min), Number(input.max), 0, 100, input.valueAsNumber);
    input.style.setProperty("--range-position", `${position}%`);
}

function updateControls(root: HTMLElement, controls: Controls, settings: Settings) {
    updateControl(controls.f1!, settings.f1, `${Math.round(settings.f1)} Hz`);
    updateControl(controls.frequencyCompression!, settings.frequencyCompression, formatWarp(settings.frequencyCompression));
    updateControl(controls.compression!, settings.compression, formatWarp(settings.compression));
    updateControl(controls.aPower!, settings.aPower, settings.aPower.toFixed(2));
    updateControl(controls.halfLifeSeconds!, cubicControlPosition(settings.halfLifeSeconds, HalfLifeMin, HalfLifeMax), formatHalfLife(settings.halfLifeSeconds));
    updateControl(controls.zeroDeltaHalfLifeSeconds!, cubicControlPosition(settings.zeroDeltaHalfLifeSeconds, HalfLifeMin, HalfLifeMax), formatHalfLife(settings.zeroDeltaHalfLifeSeconds));
    updateControl(controls.decayQ!, settings.decayQ, settings.decayQ.toFixed(1));
    updateControl(controls.bassFrequency!, settings.bassFrequency, `${Math.round(settings.bassFrequency)} Hz`);
    updateControl(controls.midsFrequency!, settings.midsFrequency, `${Math.round(settings.midsFrequency)} Hz`);
    updateControl(controls.bassPower!, settings.bassPower, settings.bassPower.toFixed(2));
    controls.f1!.input.disabled = (settings.bassBarCount == 0);

    root.querySelector("[data-axis=\"f0\"]")!.textContent = "_";
    root.querySelector("[data-axis=\"f1\"]")!.textContent = `${Math.round(settings.f1)} Hz`;
    root.style.setProperty("--split", `${remap(0, settings.barCount, 0, 100, settings.bassBarCount)}%`);
    root.querySelector("[data-axis=\"f2\"]")!.textContent = " ";
}

function frequencyForBar(bar: number, settings: Settings): number {
    let b0 = 0;
    let b1 = 0;
    let f0 = 0;
    let f1 = 0;
    if (bar < settings.bassBarCount) {
        b0 = 0;
        b1 = settings.bassBarCount;
        f0 = settings.f0;
        f1 = settings.f1;
    } else {
        b0 = settings.bassBarCount;
        b1 = settings.barCount;
        f0 = (settings.bassBarCount == 0) ? settings.f0 : settings.f1;
        f1 = settings.f2;
    }
    let c = settings.frequencyCompression ? logControl(settings.frequencyCompression) : 0;
    return Math.pow(2, remap(b0, b1, Math.log2(f0 + c), Math.log2(f1 + c), bar)) - c;
}

function resample(spectrum: Float32Array<ArrayBufferLike>, sampleRate: number, frequency: number, lowerFrequency: number, upperFrequency: number): number {
    let centreBin = (frequency / sampleRate) * FFTSize;
    let lowerBin = (lowerFrequency / sampleRate) * FFTSize;
    let upperBin = (upperFrequency / sampleRate) * FFTSize;
    let width = upperBin - lowerBin;

    function sample(bin: number): number {
        let lo = Math.floor(bin);
        let hi = clamp(0, spectrum.length - 1, lo + 1);
        return lerp(spectrum[lo], spectrum[hi], bin - lo);
    }

    let sum = 0;
    let weightSum = 0;
    let radius = clamp(1, 6, Math.ceil(width));
    for (let interval = -radius; interval <= radius; interval++) {
        let distance = interval / radius;
        let bin = (distance < 0) ? lerp(centreBin, lowerBin, -distance)
                                 : lerp(centreBin, upperBin,  distance);
        let weight = Math.exp(-distance * distance);
        sum += sample(bin) * weight;
        weightSum += weight;
    }
    return sum / weightSum;
}

function aweight(frequency: number, strength: number, blend: number): number {
    let f2 = frequency * frequency;
    let numerator = 12194 * 12194 * f2 * f2;
    let denominator = (f2 + 20.6 * 20.6) * Math.sqrt((f2 + 107.7 * 107.7) * (f2 + 737.9 * 737.9)) * (f2 + 12194 * 12194);
    let x = 1.2589 * numerator / denominator;
    return lerp(1.0, Math.pow(x, strength), blend);
}

function startVisualizer(root: HTMLElement, controls: Controls) {
    let canvas = root.querySelector("canvas")!;
    let audio = root.querySelector("audio")!;
    let fileInput = root.querySelector<HTMLInputElement>(".audio-file")!;
    let sourceName = root.querySelector(".audio-source")!;
    let message = root.querySelector(".visualizer-message")!;
    let paint = canvas.getContext("2d")!;

    let audioContext: AudioContext | undefined;
    let analyser: AnalyserNode | undefined;
    let analysisVolumeGain: GainNode | undefined;
    let playbackVolumeGain: GainNode | undefined;
    let spectrumDb: Float32Array | undefined;
    let spectrumLinear: Float32Array | undefined;
    let smoothedBars = new Float32Array(0);
    let objectUrl = "";
    audio.src = "/posts/audio-visualizers/20250817.mp3";

    let userSettings = { ...Defaults };
    let settings = userSettings;
    let stopTime = 0;

    function settleTimeMilliseconds() {
        return 10_000 * Math.max(settings.halfLifeSeconds, settings.zeroDeltaHalfLifeSeconds);
    }

    let presetMarkers: Marker[] = [];
    for (let element of document.querySelectorAll<HTMLElement>("div[data-preset]")) {
        if (Presets.hasOwnProperty(element.dataset.preset!)) {
            presetMarkers.push({ element, preset: Presets[element.dataset.preset!]})
        }
    }

    function applySettings() {
        let sectionPreset = activeMarker?.preset ?? Presets["default-bins"];
        settings = presetControl.input.checked ? sectionPreset.settings : userSettings;
        presetControl.name.textContent = sectionPreset.label;
        updateControls(root, controls, settings);
        if (audio.paused) {
            stopTime = performance.now() + settleTimeMilliseconds();
            requestAnimationFrame(draw);
        }
    }

    let activeMarker: Marker | undefined;
    let presetControl = makePresetControl();
    presetControl.input.addEventListener("change", applySettings);
    root.querySelector(".visualizer-controls")!.prepend(presetControl.element);

    let scrollPending = false;
    function scheduleScrollPreset() {
        if (scrollPending) return;
        scrollPending = true;
        requestAnimationFrame(_ => {
            scrollPending = false;
            let next: Marker | undefined;
            for (let marker of presetMarkers) {
                if (marker.element.getBoundingClientRect().top <= (0.35 * window.innerHeight)) {
                    next = marker;
                }
            }
            if (next != activeMarker) {
                activeMarker = next;
                presetControl.input.checked = true;
                applySettings();
            }
        });
    }

    function updateVolume() {
        if (!audioContext || !analysisVolumeGain || !playbackVolumeGain) return;
        let volume = audio.muted ? 0 : audio.volume;
        analysisVolumeGain.gain.setValueAtTime(1 / volume, audioContext.currentTime);
        playbackVolumeGain.gain.setValueAtTime(volume, audioContext.currentTime);
    }

    function connectAudio() {
        if (!audioContext) {
            audioContext = new AudioContext();
            analyser = audioContext.createAnalyser();
            analyser.fftSize = FFTSize;
            analyser.smoothingTimeConstant = 0;
            analyser.minDecibels = -100;
            analyser.maxDecibels = 0;
            analysisVolumeGain = audioContext.createGain();
            playbackVolumeGain = audioContext.createGain();
            spectrumDb = new Float32Array(analyser.frequencyBinCount);
            spectrumLinear = new Float32Array(analyser.frequencyBinCount);

            let source = audioContext.createMediaElementSource(audio);
            source.connect(analysisVolumeGain);
            analysisVolumeGain.connect(analyser);
            analyser.connect(playbackVolumeGain);
            playbackVolumeGain.connect(audioContext.destination);
            updateVolume();
        }
        if (audioContext.state == "suspended") audioContext.resume();
    }

    function loadFile(file: File) {
        if (file.type && !file.type.startsWith("audio/")) return;
        audio.pause();
        if (objectUrl) URL.revokeObjectURL(objectUrl);
        objectUrl = URL.createObjectURL(file);
        audio.src = objectUrl;
        audio.loop = false;
        sourceName.textContent = file.name;
        connectAudio();
        audio.play().catch(() => undefined);
    }

    function togglePlayback() {
        if (audio.paused) {
            connectAudio();
            audio.play().catch(() => {
                message.textContent = "Unable to play :(";
            });
        } else {
            audio.pause();
        }
    }

    let previousFrameTime = performance.now();
    function draw(frameTime: number) {
        let dt = (frameTime - previousFrameTime) / 1000;
        previousFrameTime = frameTime;
        let width = clampMin(1, Math.round(canvas.clientWidth));
        let height = clampMin(1, Math.round(canvas.clientHeight));
        if (canvas.width != width || canvas.height != height) {
            canvas.width = width;
            canvas.height = height;
        }

        paint.clearRect(0, 0, width, height);
        if (!audio.paused && analyser && spectrumDb && spectrumLinear) {
            analyser.getFloatFrequencyData(<any>spectrumDb);
            for (let bin = 0; bin < spectrumDb.length; bin++) {
                spectrumLinear[bin] = Math.pow(10, spectrumDb[bin] / 20);
            }
        }

        let barCount = settings.barCount;
        if (smoothedBars.length != barCount) {
            smoothedBars = new Float32Array(barCount);
        }
        let cellWidth = width / barCount;
        let gap = clamp(0, 2, cellWidth * 0.35);
        let barWidth = clampMin(0.5, cellWidth - gap);
        paint.fillStyle = "#888888";

        if (audioContext && spectrumLinear) {
            let T = audioContext.sampleRate / FFTSize;
            let bassEnd = clamp(0, spectrumLinear.length - 1, Math.floor(settings.bassFrequency / T));
            let midsEnd = clamp(0, spectrumLinear.length - 1, Math.floor(settings.midsFrequency / T));
            let bass = 1e-8;
            let mids = 1e-8;
            for (let bin = 0; bin <= bassEnd; bin++) bass += spectrumLinear[bin];
            for (let bin = bassEnd + 1; bin <= midsEnd; bin++) mids += spectrumLinear[bin];
            bass /= bassEnd;
            mids /= midsEnd - bassEnd;
            let nrg = Math.pow(bass + bass/mids, settings.bassPower);

            for (let bar = 0; bar < barCount; bar++) {
                let frequency = frequencyForBar(bar + 0.5, settings);
                let previousFrequency = frequencyForBar(bar - 0.5, settings);
                let nextFrequency = frequencyForBar(bar + 1.5, settings);
                let linear = resample(spectrumLinear, audioContext.sampleRate, frequency, previousFrequency, nextFrequency);
                let a = aweight(frequency, settings.aPower, settings.aBlend);
                let level = compress(a * nrg * linear, settings.compression);
                let lastLevel = smoothedBars[bar];

                let beta = 1.0 - ((settings.halfLifeSeconds / settings.zeroDeltaHalfLifeSeconds) / (1.0 + Math.exp(-Math.PI)));
                let delta = (level - lastLevel) / lastLevel;

                let deltaMultiplier = 1;
                if (settings.zeroDeltaHalfLifeSeconds > 0.0005)
                    deltaMultiplier = (1 + Math.exp(Math.PI * (delta - 1))) * (1 - beta*Math.exp(-delta * delta * Math.PI));

                let normalizedFrequency = clamp(0, 1, frequency / settings.f2);
                let rateMultiplier = (1 + settings.decayQ * normalizedFrequency) * deltaMultiplier;
                let halfLifeSeconds = settings.halfLifeSeconds / rateMultiplier;
                let alpha = halfLifeSeconds ? Math.pow(2, -dt / halfLifeSeconds) : 0;

                let displayLevel = lerp(level, lastLevel, alpha);

                if (bar == 0) displayLevel = nrg * 0.02 / Math.pow(0.001, settings.bassPower);
                if (bar == 1) displayLevel = Math.pow(bass, settings.bassPower) * 0.02 / Math.pow(0.001, settings.bassPower);
                if (bar == 2) displayLevel = Math.pow(mids, settings.bassPower) * 0.02 / Math.pow(0.001, settings.bassPower);
                if (bar == 3) paint.fillStyle = "#f5f3f0";

                let barHeight = displayLevel * height * settings.scale;
                paint.fillRect(bar * cellWidth + gap / 2, height - barHeight, barWidth, barHeight);
                smoothedBars[bar] = displayLevel;
            }
        }

        if (!audio.paused) stopTime = frameTime + settleTimeMilliseconds();
        if (!audio.paused || frameTime < stopTime) requestAnimationFrame(draw);
    }

    for (let name of Object.keys(controls) as ControlName[]) {
        controls[name]!.input.addEventListener("input", event => {
            let value = (<HTMLInputElement>event.target).valueAsNumber;
            if (name == "halfLifeSeconds" || name == "zeroDeltaHalfLifeSeconds") {
                value = cubicControlValue(value, HalfLifeMin, HalfLifeMax);
            }
            userSettings[name] = value;
            userSettings.midsFrequency = clampMin(userSettings.bassFrequency + 1, userSettings.midsFrequency);
            presetControl.input.checked = false;
            applySettings();
        });
    }

    applySettings();

    canvas.addEventListener("click", togglePlayback);
    canvas.addEventListener("keydown", event => {
        if (event.key == "Enter" || event.key == " ") {
            event.preventDefault();
            if (!event.repeat) togglePlayback();
        }
    });
    audio.addEventListener("play", () => {
        connectAudio();
        if (performance.now() >= stopTime) requestAnimationFrame(draw);
        root.classList.add("is-playing");
    });
    audio.addEventListener("pause", () => {
        root.classList.remove("is-playing");
        message.textContent = "Paused";
    });
    audio.addEventListener("volumechange", updateVolume);
    fileInput.addEventListener("change", () => {
        if (fileInput.files?.[0]) loadFile(fileInput.files[0]);
    });
    root.addEventListener("drop", event => {
        event.preventDefault();
        if (event.dataTransfer?.files[0]) loadFile(event.dataTransfer.files[0]);
    });
    root.addEventListener("dragenter", event => {
        event.preventDefault();
        root.classList.add("is-dragging");
    });
    root.addEventListener("dragover", event => event.preventDefault());
    root.addEventListener("dragleave", event => {
        let next = event.relatedTarget;
        if (!root.contains(<any>next)) root.classList.remove("is-dragging");
    });
    window.addEventListener("scroll", scheduleScrollPreset, { passive: true });
    window.addEventListener("resize", scheduleScrollPreset);
    window.addEventListener("pageshow", scheduleScrollPreset);
    window.addEventListener("load", scheduleScrollPreset);
}

function main() {
    let root = document.querySelector<HTMLElement>("#audio-visualizer")!;
    let controls = buildVisualizer(root);
    startVisualizer(root, controls);
}

if (document.readyState == "loading") {
    document.addEventListener("DOMContentLoaded", main);
} else {
    main();
}
