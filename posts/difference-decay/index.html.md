---
title: "Difference Decay"
date: 2021-12-29
tags: [programming, maths]
---

Here's a variation on the [damper](https://theorangeduck.com/page/spring-roll-call) I keep coming up with uses for. I find my code that uses it a bit subtle and annoying to figure out, hence this post. <!--more--> That theorangeduck post is about springs, which could be an interesting extension to this, but this post is setting our sights lower.

My first use for this was to clean up a noisy/unreliable clock by using a high resolution clock, taking the noisy clock's drift as authoritative. But I think of it more generally, as combining two signals `s` and `n` to produce a third with the short-term character of `s` but the long-term average of `n`:

```c++
float update(float *accumulator, float dt, float s, float n)
{
    float acc = *accumulator;
    float err = s - n;

    acc += err;
    acc *= expf(-dt);
    float x = n + acc;
    acc -= err;

    *accumulator = acc;
    return x;
}
```

`accumulator` is initialized to $0$ and we expect `dt` to be small and positive, so you can mentally substitute `expf(-dt)` with `1 - dt`.

The easiest way to explain it is to work backwards. The `+=`, `-=` pair removes a delay term (`err_prev` in the following), and is equivalent to:

```
err = s - n;
acc = (acc + (err - err_prev)) * expf(-dt);
err_prev = err;
x = n + acc;
```

To see what this is doing, suppose we don't apply the `expf(-dt)` decay factor. Then, over all `s` and `n`, we get something like `cumsum([0, diff(s - n)])`, which is a no-op. Written out,

$$ 
\begin{aligned}
\text{acc}_i &= \text{acc}_{i-1} + (\text{err}_i - \text{err}_{i-1}) \\
             &= \sum_{k=0}^i (\text{err}_k - \text{err}_{k-1}) \\
             &= \sum_{k=0}^i \text{err}_k - \sum_{k=1}^i \text{err}_{k-1} \\
             &= \text{err}_i \\
             &= s_i - n_i
\end{aligned}
$$

so our value for `x` would always equal the most recent `s`. Likewise, if we zeroed out `acc` completely, the damper would return `n` every time. 

Applying the decay to `acc` lets us decay _old updates_ to the difference between $s$ and $n$. If $s$ and $n$ grow at the different rates, this shrinks the gap between them and stops them drifting apart. But if $n$ updates less frequently or with jitter, this fills in the missing/incorrect detail with $s$.

If you care about tuning the decay factor or having something more momentum than exponential decay, check out the [theorangeduck post](https://theorangeduck.com/page/spring-roll-call). It's good!! One thing to note is this damper doesn't have any stability problems for large `dt` that I'm aware of, you just lose more history.

While retreading the maths for this post and trying to see if I could get it to look more intuitively damper-y, I noticed that if you scale the error difference term by the inverse of the decay to cancel out the first decay you get

$$
\begin{aligned}
\text{acc}_i & = [\text{acc}_{i-1}+(\text{err}_i - \text{err}_{i-1}) \exp(dt)] \exp(-dt) \\
    &= \text{acc}_{i-1} \exp(-dt) +(\text{err}_i - \text{err}_{i-1})
\end{aligned}
$$

which looks similar to the simple damper:
```
x = lerp(x, g, 1.0f - expf(-dt))
  = g + (x - g)*expf(-dt)
```

Instead of repeatedly folding `g` into `x`, we've isolated `x - g` as `acc`, and we repeatedly fold updates to `g` into `acc`, which we decay. This idea of isolating the difference is what I was thinking about when I came up with this; it's really another [phase inversion trick](/posts/dumb-tricks-with-phase-inversion). So maybe applying this scaling factor is more correct? 

Anyway, I came up with this to fix a decades old visual stuttering issue in the rhythm game Etterna, a fork of Stepmania. They position objects on the screen by repeatedly querying the system audio API for it's playback position. This turns out to work exactly as you'd hope on some hardware and APIs, and really not work at all on others. The game is visually stripped down enough that this looks like it has bad frame pacing issues, but the issue was entirely due to the reported audio position. There are variations here (figured out with [Tracy](https://github.com/wolfpld/tracy)):

- WaveOut, interestingly, appears to directly report whatever the hardware driver tells it. This means it works great for some devices and terrible on others. I first hit this issue when a driver update for my USB sound card changed the behaviour here, introducing jitter you could _see_. On the other hand, with my motherboard's audio you instead see nice steady drift away from `QueryPerformanceCounter`.

- DirectSound appears to correct for drift and jitter, and this turns out to be bad. When you sample playback positions it looks to be in sync with wall time, but audio hardware _does_ drift, and DirectSound eventually corrects for this by jumping. Which means a visible jump in the game. Furthermore, it only reports a new sample position every 10ms, and at the point you are querying you have no idea how long ago the update to the position occurred. You basically end up with a few milliseconds of jitter, unless you're running at very high frame rates.
  
- ALSA and PulseAudio appear to have no way to query this, so you only know the time you submitted the last buffer. This is probably fine, and possibly none of this would have been a problem if the game never queried the other APIs in the first place. You can get a continuous estimate by extrapolating from the submission time, which I suspect is what you get in the good WaveOut case. Due to the architecture of the game, this ended up with the same unknown update time issue as DirectSound.

- And possibly more, but I stopped looking.

So I wanted something that would eliminate jitter for all of these, without any parameter tuning, and not degrade the ideal 'good driver under WaveOut' case in any way. This worked well. 

One thing here worth mentioning, where `s` is high-quality time from `QueryPerformanceCounter` or equivalent and `n` is low-quality time from somewhere else, is that we only have samples $s(t_0)$ and $n(t_1)$. That is, we do not actually know the values of $t$, and we just assume $t_0 \approx t_1$. For this problem in particular, you might want to take a third sample $s(t_2)$ and check that $s(t_2) - s(t_0)$ is sufficiently small before using $n(t_1)$, as your [time slice](https://en.wikipedia.org/wiki/Time_slice) can run out between sampling $s$ and $n$. 

I wish I could say something about control theory here, since this kind of thing seems to be right in its wheelhouse. But I don't really know any.
