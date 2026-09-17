---
title: "How to audio visualizer good"
date: 2026-09-17T00:00:00+01:00
tags: [audio, dsp]
---

<div class="audio-visualizer" id="audio-visualizer"></div>

So, multiple times now I have found myself helping out people making audio visualizers. It's mostly easy but being able to bang out one that looks good takes a certain amount of tacit knowledge. The values you get from an FFT are linear in frequency and in magnitude, and noisy. To make a visualizer that looks good you need to sort out all three. My target audience for this post is people who have dealt with these but were never quite sure they understood what was going on.

Since this is about fundamentals, this post is only covers how to go from FFT frequency amplitiudes to the simplest spectrum analyzer you can make: monochrome bars, each bar gets a frequency, they move up and down. I'm not going to get into the FFT itself or justify any basic facts about it. Maybe later.

First order of business _for this page_ is to fix the garbage the WebAudio AudioAnalyser node gives you. This means calling it like this:

```js
analyser.fftSize = FFTSize;
analyser.smoothingTimeConstant = 0;
analyser.minDecibels = -100;
analyser.maxDecibels = 0;
```

and undecibeling it when it comes out the other end to get linear DFT magnitudes with no smoothing (do not use the WebAudio smoothing). Now we can start.

## Problem: noisy

<div data-preset="noisy-bins"></div>

Right, WebAudio gives you `smoothingTimeConstant` and I claim this is bad. This is simple, it's not frame rate independent. This is the display frame rate and has nothing do with the FFT size or audio sample rate. To make it independent, compute the smoothing constant with your time delta:

$$\alpha = 2^{-\Delta t/H}$$

where $H$ is the decay half-life. You can convince yourself this is plausibly right by knowing beforehand that the way this has to work is if you feed in a single $1$ then $0$s at intervals of $\Delta t=1$ with $H=1$, then it should fall by half immediately, and yes, $2^{-1} = 0.5$. You then also check that stepping twice as fast gives $0.5$ after two time steps, and yea, $2^{-1/2}2^{-1/2} = 0.5$, and a step of $3/4$ then $1/4$ works, too. You also know that this is pretty convincing because the quantity we care about is the ratio $\Delta t/H$ and not the actual numbers involved.

<div data-preset="sloshy-bins"></div>

But if you do only this, it's sloshy. If you stare at [tuneform](https://tuneform.com/audio-reactive-music-visualizers/) you'll see it there, too. There doesn't seem to be a middle ground between jittery and smooth that doesn't add inertia. 

The trick for this is to modulate $H$ depending on how the sound is changing, updating $H$ for every bar and every frame. Make it speed it up to follow attacks and slow it down to smooth out steady-state noise. Once you know you can do this it's pretty easy to hack something together. 

If you don't want to hack, try this. The rest of this post isn’t going to be quite so hardcore. Define

$$
\begin{array}{lll}
  \quad A_{i,k} \quad & \text{amplitude for bar k} \\
  \quad V_{i-1,k} \quad & \text{last filtered amplitude for bar k} \\
  \quad H       \quad & \text{base half-life} \\
  \quad H_\Delta\quad & \text{steady-state half-life}
\end{array}
$$

The idea is that $H_\Delta$ will kick in when the delta between $A_{i,k}$ and $V_{i-1,k}$ is small enough. Compute a per-bar $\alpha_k$ with

$$
\begin{aligned}
\beta &= 1 - \frac{1}{1 + e^{-\pi}} \frac{H}{H_\Delta} \\
d_k &= (A_{i,k} - V_{i-1, k}) / V_{i-1, k}\\
m_k &= (1 + e^{\pi (d_k - 1)}) (1 - \beta e^{-\pi d_k^2}) \\
H_k &= H / m_k\\
\alpha_k &= 2^{-\Delta t/H_k}
\end{aligned}
$$

<div data-preset="default-bins"></div>

When $A_{i,k} = V_{i-1,k} = 0$ this breaks, set $\alpha_k = 0$ in that case. Then apply the usual filter step $$V_{i,k} = \text{lerp}(A_{i,k}, V_{i-1,k}, \alpha_k)$$

And that's it. By the way, the discovery fiction version of this begins "Boy, I sure would like to multiply H by an $\exp(\Delta)$ term", which mostly works but is fiddly and annoying to tune; $m_k$ is then a nicer curve than an $\exp$ and $\beta$ is a way to tune it. This filter has 3 regimes:

$$
\begin{aligned}
A_{i,k}  \ll V_{i-1,k}     &\qquad& &\text{getting quieter, half-life } H \\
A_{i,k} \approx  V_{i-1,k} &\qquad& &\text{holding steady, half-life } H_\Delta \\
A_{i,k} \gg V_{i-1,k}      &\qquad& &\text{getting louder, half-life } 0
\end{aligned}
$$

{{< aside >}}

How it does that is going to take a little unpacking. All we're doing is updating the half-life for a bar, so we just need to understand how it's computing $H_k$.

First, $d_k$ is a normalized delta from the previous frame, normalized with respect to itself. This normalization makes a lot of the fiddly parameterization you typically have with this kind of thing go away. You can think of it like an approximation to [$f'(x)/f(x)$](https://en.wikipedia.org/wiki/Logarithmic_derivative). That thing is called the [logarithmic derivative](https://en.wikipedia.org/wiki/Logarithmic_derivative), which is a hint that this thing is responding to amplitude ratios rather than differences. This is nice because it keeps the filter scale invariant; that is, you get the same filtering before and after applying gain (I should check this). 

If you want to understand $m_k$, stick it in desmos. Ignore $\beta$ for a moment and assume its value is $1$. You'll find that 
$$1 + e^{\pi(d_k-1)}$$ 
is an $\exp(\Delta)$ term that makes us respond faster to new, loud sound, and 
$$1 - e^{-\pi d_k^2}$$
is a flipped gaussian, to lengthen the effective half-life when $d_k$ is small. This smooths more agressively when the bar heights are jittery rather than moving.

{{< wideimg "curve.png" >}}

Importantly, both of these terms go to $1$ as $d_k$ goes to $-\infty$, so when  $V_{i-1, k} \gg A_{i,k}$ we have $m_k = 1$ and recover $H/m_k = H$ as our decay time.

Finally, $\beta$. This gives us a way to tune the adaptivity. Without it, frame deltas near zero lock bars in place, because we've otherwise explicitly designed zero delta to give $m_k = 0$. Setting $\beta$ to a value in $[0,1]$ lifts the floor of the gaussian preventing this from happening. But how to choose a value for $\beta$? Well, we know $m_k$ is going to scale $H$, and $\beta$ is going to fix the minimum value $m_k$ can take on. So define $H_\Delta$ as the half-life when $d_k = 0$ and then $\beta$ is whatever gives $H/m_k=H_\Delta$ in that case.

{{< /aside >}}

This is an example of an adaptive filter in the same vein as the [1€ Filter](https://gery.casiez.net/1euro/). Before writing this post I had something a little more adhoc here that was annoying to parameterize. I landed on this after cleaning it up. If you look at 1€, they have this whole process by which you pick good parameters for it. I want to avoid that. You can introduce $\sigma$ terms to the exponentials if you want more control over the filter here; once you understand the shape of the curve you are manipulating it's pretty clear what is going on. The normalisation and asymmetry means this thing is only really appropriate for positive-only signals, in this respect it's unlike 1€ where you can slam it on position data.

## Problem: linear in frequency

<div data-preset="linear-bins"></div>

Linear FFT bins to logarithmic bars. This is explained everywhere but I feel like a couple fundamental pieces get dropped pretty often. The first is that underneath the logarithms that map bin frequencies to bar frequencies there's a simple `lerp`/`unlerp` logic and the second is how to actually think about mapping values _at_ those frequencies into bars. 
```c
float lerp(float a, float b, float t) {
    return (1.0f - t)*a + t*b;
}

float unlerp(float a, float b, float x) {
    return (x - a) / (b - a);
}

float remap(float a0, float a1, float b0, float b1, float x) {
    return lerp(b0, b1, unlerp(a0, a1, x));
}
```

Now remap maps the entire range $[a_0, a_1]$ to $[b_0, b_1]$ by applying a scale and shift. How do we use this? We want bars that equally subdivide octaves. We have $N$ bins and a desired frequency range. To equally subdivide octaves, which double in frequency per octave, we want our $B$ bar frequencies to take linear steps after applying $\log_2$. So construct that directly with remap:

```c
float bar_to_frequency(float b, int32_t B, float f0, float f1) {
    float f_log = remap(0.0f, float(B), log2f(f0), log2f(f1), b);
    return powf(2.0f, f_log);
}

float frequency_to_bin(float f, int32_t N, float sample_rate) {    
    float nyquist = sample_rate / 2.0f;
    return remap(0.0f, nyquist, 0.0f, float(N), f);
}
```

And we're done. It's maybe worth noting that the things we care about are the endpoints and the logarithmic warp, and the endpoints make the choice of base irrelevant; we could have used `expf` and `logf`. 

This looks a little different from how people usually do this. Yes. It'll appear if you expand it out and simplify.

Next, resampling bins into bars. First thing to understand here is that we do this by reaching back from the output, bars, to the input, bins, to grab what we need for each bar. That is, at no point do we ever pick up a bin, ask its frequency, and try to locate the corresponding bar for that frequency. At low frequencies, this will leave gaps: there'll be so little frequency resolution in the low bins that one bin to the next may skip multiple bars. Instead, we start from the output space we know must be dense and consistently sampled, the bars, and work backwards to figure out what bins we need. This general pattern is called a pullback; there are _multiple_ impressively unelightening wikipedia articles about it.

Once you have this mental model in place you see it's a matter of iterating over bars and sampling bins:

```c
for (int b = 0; b < B; b++) {
    float f = bar_to_frequency(float(b) + 0.5f, float(B), f0, f1);
    
    // simple
    bar[b] = bins[int(frequency_to_bin(f) + 0.5f)];
    // or, better for bass bins
    float bin = frequency_to_bin(f);
    float t = bin - floor(bin);
    bar[b] = lerp(bins[floorf(bin)], bins[ceilf(bin)], t);
    // or, less aliasiing
    float f_from = bar_to_frequency(float(b), float(N), f0, f1);
    float f_to = bar_to_frequency(float(b) + 1.0f, float(N), f0, f1);
    bar[b] = average(bins, frequency_to_bin(f_from), frequency_to_bin(f_to));
}
```
When I write this kind of code I tend to go on auto-pilot so the stuff on this page uses a gaussian window to weight the average and caps the number of bins that can contribute up at high frequencies. This... is not a big deal though.

<div data-preset="geometric-bins"></div>

But now we have too many bass bins. You can say this is wrong pyschoacoustically and go looking at mels or whatever, but it's also easy to just stitch together two ranges, like

```c 
if (b < cutoff) {
    return bar_to_frequency(b, cutoff, f0, f1);
} else {
    return bar_to_frequency(b - cutoff, N - cutoff, f1, f2);
}
```

<div data-preset="default-bins"></div>

So that's what I do here. I prefer this approach over psychoacoustics because it's nice to keep everything locally logarithmic: a breakpoint where the logarithmic rate doubles, say, so the same bin count now cover two octaves, looks better to me.

We're still missing some resolution we'd like to have in the bass and mids, but dealing with that is more than I want to get into for this post.

## Problem: linear in magnitude

<div data-preset="linear-magnitude-bins"></div>

There is some conspiracy perpetrated by the technically minded that you want decibels for this. Can't say that I agree. The dynamic range of linear is huge so peaking vocals can look a little preposterous but you can actually see the dynamics you are hearing. Under decibels, pretty much all music looks like a variation on 1/f noise. So my mindset here is we're trying to compress the dynamic range _without_ squashing it all down as aggressively as a straight log does. 

One way to do this is to just ease off on the log by choosing where on the log curve we assign the zero point, computing instead $\log(c + V_{i,k})$. Then $c \ge 0$ is just a parameter you can scrub until you find something you like. For $V_{i,k}$ in $[0,1]$, every value of $c$ above $1$ looks pretty much identical to linear after scaling, so all the interesting stuff is with very small $c$. 

This was pretty easy, right? Well, I have more to say. If you just scrub $c$ it's really, really annoying to get control over the dynamic range and keep all the bars sized right. It's impossible to meaningfully compare different values of $c$ if the scale of every bar changes dramatically. If you've never dealt with this you may not be in the target audience for this post! 

When $V_{i,k}$ is in $[0,1]$ we have that $\log(c + V_{i,k})$ is in $[\log(c), \log(c + 1)]$. So to get the range back into something sensible we _ought_ to be able to just map the range back linearly:
```c
float compress(float v, float c_param) {
    // Parameterizing c this way is nice for sliders over [0,1]
    float c = powf(2.0f, lerp(-16.0f, 16.0f, c_param));
    return remap(logf(c), logf(c + 1.0f), 0.0f, 1.0f, logf(c + v));
}
``` 
This doesn't work. Firstly, it doesn't work in the obvious sense that if $c_\text{tiny}$ gives a log scale and $c_\text{huge}$ gives a linear scale, then we are back where we started, just with numbers in $[0,1]$. But the non-obvious sense is that after this map linear magnitudes rarely use values near $1$, and logarthmic rarely uses values near $0$, so we want to boost the gain on linear magnitudes and duck it on logarithmic magnitudes, and it's not clear how to choose an appropriate gain given an arbitrary $c$.

<div data-preset="default-bins"></div>

Easy thing to do here is to stop caring about the _entire_ range and scale with respect to a value we know we're likely to see in practice, which means tweaking that $+ 1$ term. Here I take the range for to be $[0, 1/4]$ instead. This then boosts the log scale more than we might like so I just apply a fudge factor to bring it back down.

```c
float compress(float v, float c_param) {
    float c = powf(2.0f, lerp(-16.0f, 16.0f, c_param));
    float fudge_factor = square(lerp(0.25f, 1.0f, c_param));
    return remap(logf(c), logf(c + 0.25f), 0.0f, 1.0f, logf(c + v)) * fudge_factor;
}
``` 

On most music I point this at, you can see the overall scale shift when you scrub, but on the whole, the most prominent peaks are roughly the same height for all $c$, even if linear only rarely peaks that high.

You MAY be feeling an urge to expand this out and simplify. For most values of $c$ you will actually use this may not ever matter but there is a numerical precision point here I'm dumping in a footnote[^1].

<div data-preset="no-aweighting-bins"></div>

One last point here is A-weighting. A-weighting models how strongly the human ear responds to different frequenices. You should just apply A-weighting. Mostly A-weighting just brings the bass down to something reasonable. To implement A-weighting, you look it up on wikipedia and copy it. Do A-weighting immediately before `compress`. A-weighting works fine on linear magnitudes, too. If you want to dial A-weighting in a little, it's a multiplier, so raise it to a power $\le 1$, and that's the A-weighting power slider here.

## Juice

<div data-preset="no-juice-bins"></div>
{{< aside >}}
You should dial in A-weighting a little.
{{< /aside >}}

{{< aside >}}
Deep in my bones I know that high frequencies ought to react faster than lower frequencies. The way we're using the FFT doesn't give us that but we can fake it by scaling the decay rate by $$1 + f_\text{bar}/f_\text{max}$$
{{< /aside >}}

{{< aside >}}

With A-weighting we can do a nice trick. We can make the entire spectrum bounce along with energy in the bass, and since A-weighting pushes the bass down so harshly you can't tell that the bass is lifting the entire spectrum up mechanically. You want to be a little subtle with this, so I use $$(\text{bass} + \frac{\text{bass}}{\text{mids}})^{0.15}$$ as a multiplier to apply to every bar before compression, where $\text {bass}$ and $\text{mids}$ are the average FFT bin magnitudes over the frequency ranges defined by the sliders, and $^{0.15}$ dials down the effect. The mids term is mostly to prevent a lack of energy in the bass from ducking too heavily.

{{< /aside >}}

<div data-preset="default-bins"></div>

## Remap

I've deliberately used remap a lot in this post because I think it demystifies mapping from linear to logarithmic scales. When you see $f_0 \log(1 + x / a)$ type junk, $f_0$ and $a$ are usually mysterious constants with a simple remap logic lurking in the background. Knowing that you can frame these domain warps as a remap makes it a lot easier to just, write down remap, plug in the ranges you're interpolating over on either side, and apply the warp to the input or the output. You barely have to think about it.

At work recently I've been dealing a bit with colour spaces. Here's the ACEScct transfer curve written with remap:

```c
if (x <= x_break) {
    return remap(0.0f, x_break, y_black, y_break, x);
} else {
    return remap(logf(x_break), logf(1.0f), y_break, y_white, logf(x));
}
```

If you simplify this you get [the official form](https://docs.acescentral.com/encodings/acescct/#acescct). I like this way a lot better! It's really obvious how the curve is parameterized and I didn't know, before, that the choice of base was irrelevant. Now I do. Thanks, remap!

---
Typescript code for this post can be found [here](https://github.com/graemephi/graemephi.github.io/blob/master/posts/audio-visualizers/index.ts).

[^1]: The unlerp immediately computes $$\log(c + 1/4) - \log(c) = \log(\frac{c + 1/4}{c}) = \log(1 + \frac{1}{4c})$$ So large $c$, and here that's $2^{16}$, immediately pushes you to values that require `log1p` to avoid roundoff error. Without getting too much into it, floating point numbers get more precise the closer to $0$ you are, but, on the other hand, near $1$ you have 24 bits of fixed precision in float32. So if you do simplify, simplify all the way to `log1p`. For this post, where large values of $c$ are pretty pointless, this is not a big deal, but it's worth knowing that in float32 the log-to-linear interpolation is not really doing what you want if you use the form provided here. In float64, that the visualizer in this post uses, it's fine.