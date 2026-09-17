---
title: "Generating Unique Random Numbers"
date: 2024-09-27T20:08:28Z
tags: [maths, rng]
---

{{< aside >}}

This post has two things:
1) Two somewhat obscure non-linear invertible operations that work on only part of a register, and
2) A fast stateless random permutation generator that uses them, and passes some statistical tests for RNGs you may have seen before

The ideas are pretty simple so the hope is you can also get an intuition for how to think about the problem, which is the best thing you can get out of this post.

I got my intuition from these:
* [Bob Jenkins' talk](https://burtleburtle.net/bob/rand/talksmall.html) on writing hash functions,
* [Marc B Reynolds' post](https://marc-b-reynolds.github.io/math/2017/10/13/IntegerBijections.html) on integer bijections (everything in this post is an integer bijection), 
* Brent Burley's [Practical Hash-based Owen Scrambling](https://jcgt.org/published/0009/04/01/), highly recommend this one if you like path tracing,
* [Andrew Helmer's blog post](https://andrew-helmer.github.io/permute/) about Andrew Kensler's `permute` in this [correlated multi-jitter paper](https://graphics.pixar.com/library/MultiJitteredSampling/paper.pdf). Helmer's post is where I first saw this idea, I think.

{{< /aside >}}

Random numbers that don't repeat. Let me explain the basic idea first before I get into the weeds. We decide to generate unique random numbers in $[0, N)$, here 8, by shuffling this list of numbers:
$$(0,1,2,3,4,5,6,7)$$
Adding the same number mod $N$ to every element gives us back a new list with the same elements in a different order,
$$(0,1,2,3,4,5,6,7) + 3 \mod 8 = (3,4,5,6,7,0,1,2)$$
And so does multiplying by an odd number, mod $N$,
$$(3,4,5,6,7,0,1,2) * 5 \mod 8 = (7,4,1,6,3,0,5,2)$$
And this now looks pretty shuffled. So, take in the original numbers one at a time, apply these and other bijections the same way on each number, and out the other end we get a pseudorandom permutation without using any memory. We never need to construct the initial list. 

The operations we can use are any that can be undone (any shuffle can be re-sorted), so you hear people call them bijections and invertible functions interchangeably.

I got interested in this after looking at the low discrepancy sequence stuff, but I brushed off the connection in [my post]({{< ref some-low-discrepancy-noise-functions >}}) about it. With the tools there, its easy to generate numbers that don't repeat but hard to make them random. That is, you could feed truly random bits in and you'd randomly select from a small set of random-looking sequences, which is not what we want. At the time, I didn't know much about this problem, just that what I was doing didn't work. This [EA Seed post of Alan Wolfe and William Donnelly](https://www.ea.com/seed/news/constant-time-stateless-shuffling) that uses Feistel networks got me interested again. The thing that really got me is that quality/speed trade-off they mention: what does it take to max out the quality? How can you tell you've reached it? Rather than answer these questions I made my own that always maxes the quality out. 

To do that you need some organising principle. Mine is this: use all your bits.

What do I mean by this?

In the above example we have 8 numbers we can do an add with, from which we get 3 bits worth of permutations. The multiply is 2 bits, we lose a bit due to the odd constraint. We won't miss it for larger $N$. To choose these randomly we need 5 random bits, for 32 possible multiply-adds. That's 32 different permutations we can get after one multiply-add, and, yes, any sequence of multiply-adds can be replaced by just one multiply-add, so out of these two operations we can't get more than 32 permutations. No matter how many random bits we have with which to choose different madds, we'll always end up with a sequence that can be reduced to a choice made with just 5 bits. Any more than that bits than that are wasted. We haven't used them.

There are $8! = 42320$ permutations of length 8. 

## Feistel networks, entropy, and so on

What Feistel networks do is give you non-linear bijections, and you can turn the crank on them to get as many permutations as you want. How many turns of the crank you need can be found in this [2022 Mitchell et al. paper ](https://arxiv.org/abs/2106.06161) that adapts [philox](https://dl.acm.org/doi/10.1145/2063384.2063405) to generate permutations. Philox is (mostly) a Feistel network. To get good statistics, turns out it's quite a lot: they want 24. This is the kind of round count you see in cryptography. What gives?

In a Feistel network, you split each number into two halves, one half that keys a round function and another half that gets permuted with a xor. This means to know how one number is scrambled by the round function, you only need to know half the bits in each step, and *this* means you get effectively half the entropy out of each round you could be getting (see this footnote if you are suspicious[^bits]).  But this structure also makes it super easy to invert, which is very useful for encryption, right. For permutations of length 5, the function in the Mitchell paper will use 72 bits of entropy (and asks for some 700 bits that it just won't use). You need 7 bits to index all 120 permutations!!

[^bits]: This sidesteps the fact that over the permutation as a whole you get the full bit-width worth of bits of entropy. It's only the path through state space taken by neighbouring values that are bit-deficient. For 8 bits, you'd have a 4 bits worth of round functions that each map 4 bits to 4 bits. 16 round functions times 16 possible outputs each is 8 bits total to describe the full permutation. Each round function is totally independent of what the other round functions are doing, and it's only the number of bits required to encode the path a given value takes that is half that required to encode the entire permutation. Really weird.
\
\
This alone isn't enough to explain the high round counts you see in practice. Interestingly, if you ask instead about the average number of bits that will be flipped then the required round counts come out close to what you see empirically... but is that just a coincidence??

This half-the-bits thing is important and is a good example of the kind of thinking you want to being doing when making these things, so, here. This is to illustrate something about bijections and the Feistel part isn't super important so I'm not going to go in detail on that. Look:
{{< wideimg feistel.png >}}

This is a single round with the 8-bit input using a xor by some arbitrary function `f` as the round function. One Feistel round permutes only the blue box to produce the purple box; the orange box remains unchanged in the output and the low bits reappear, unchanged, as the new high bits. That's what I'm talking about in the previous paragraph. But if you stare at this a while you may realise there are only 16 ways that purple box can end up, and the only thing `f` and `seed` can do is make the choice more or less predictable. This is the important part: a better choice of `f` can't give you more permutations than that. If you only do this one thing, then each round you get at most 16x new permutations, and they're the same new permutations regardless of `f`. A bad choice of `f` might fall short of all 16x, but ruling those out, the thing a better choice of `f` is giving you is a more unpredictable order with respect to `seed`.

And that might sound good but for most $N$ there are so many permutations we don't care about the order. If the order you see permutations in matters, that's bias. There are just too many permutations for it to be otherwise. I'll get back to this point later.

{{< aside >}}

I say a Feistel network will require too many bits, but it turns out to be really hard to use the minimal number of bits. Since I've brought this up, check this out. How many bits will the Fisher-Yates shuffle use? It's the standard shuffle, and there used to be a little ecosystem of blog posts on how careless implementations could give bad statistics. My goal with this post is to match Fisher-Yates statistics-wise. ([Code from Wikipedia](https://en.wikipedia.org/wiki/Fisher-Yates_shuffle), why not):
```terminal
-- To shuffle an array a of n elements (indices 0..n-1):
for i from 0 to n−2 do
     j ← random integer such that i ≤ j < n
     exchange a[i] and a[j]
```
On the first iteration, we generate a number between $0$ and $N$, so $\log_2 N$ bits are needed to describe the number of possible outcomes of the first iteration. The second is between $1$ and $N,$ that's $\log_2(N - 1)$ bits, and it's smaller because we have one less possible values to choose from, right. Continue like this, then by the end we've used

$$
\begin{aligned}
\sum_{i=0}^{N - 2} \log_2(N - i) &= 
\sum_{i=2}^{N} \log_2 i \\
&= \log_2\prod_{i=2}^N i \\
&= \log_2 N!
\end{aligned}
$$

bits of entropy. Exactly enough bits for the $N!$ possible permutations: if you interpret the bits it draws as a number, then that number directly indexes into the big Lehmer-list in the sky of permutations of size $N$. So, assuming we could draw a fractional number of bits from an RNG, this shuffle is optimal in the number of bits it will use. Something that took me a while to realise is that the exact same reasoning applies to figuring out the minimum number of bits it would take to encode the next value in a permutation, given those you've already seen. :o

We won't get anywhere close to this lower bound, in both senses: for small $N$ I'll use too many bits, and for large $N$, well, nobody ever will get close to using enough.

If all this talk of bits and entropy is lost on you: read David MacKay's [Inference book](https://www.inference.org.uk/itprnn/).
{{< /aside >}}

Anyway, all that's why I went looking for other ways to map bits to bijections. My thinking is this: using cheaper non-linear bijections that operate on all the bits at once can produce more random lookin' permutations per unit time. The space of permutations that can be sampled *at all* can expand up to twice as quickly by having no half-width bottlenecks.

## Two invertible operations

#### 1

Everyone into this junk knows odd multiplies are invertible and even multiplies aren't. That's wrong: even multiplies are perfectly invertible. It's only after truncating the bits that don't fit in the register that invertibility is lost. They don't have invertibility $\text{mod } 2^b$, but here, $b$ is probably small, and there is still plenty of register left over. So, don't truncate: shift.
```terminal
a : value to permute
k : random bits, or constant, whatever

m = (1 << bitwidth(a)) - 1                 (mask for getting a back into range)

k_low_bits = (k & -k) - 1                  (turn trailing zeros into a mask)
k += ((k & m) == 0)                        (fix up if k is 0)

ak = a * k                                 (multiply)
a = ak + ((ak >> bits) & k_low_bits)       (rotate)
```

Spelled out: even multiplies can be split into two operations, an odd multiply and a left shift; the shift amount is the number of trailing zeros. To restore invertibility we could shift back to undo that shift, but this lands it back at an odd multiply so we're still down a bit. Instead, do a rotate, by shifting the bits otherwise masked out into the low bits that were just zeroed out by the multiply.

This is fine as is for small bit-widths, but if `bitwidth(a)` is greater than the half the register width then `k` can have so many trailing zeros that the multiply runs out of register. For `bitwidth(a)` up at like 30 then it can only handle at most 2 trailing zeros. We don't care about the missing bit that much in that case, so just detect when there are too many trailing zeros and turn it into a multiply by one:
```terminal
km = m & (~0u >> bits)                      (note, km == m when bits < regsiter width / 2)
k += ((k & km) == 0)                        (new fix up)
```

This is getting a bit complicated. The up shot is we get an almost full-bit multiply and a non-linearity out of it. 'Almost' because we still can't multiply by zero. To underscore the point a bit, the shift amount is constant with respect to $N$ but the effective rotation amount depends on `k`.

If you choose `k` randomly then the random rotates we get follow a geometric distribution: $1/2$ chance the first bit is zero, $1/4$ the first and second bit are both zero, ... So it's usually 0, 1 or 2. That works well here because it means it just works for all $N$--for small $N$, if we only have, say, 3 bits then we can only do rotates of 1 or 2 bits, so if we have a lot of larger rotates we aren't getting the non-linearities we want. Likewise for large $N$, where we need to avoid shifting away bits at the opposite end, we don't have to worry about that happening often either. But for other $N$ we'd really like to get bits moving in different ways. So there's room for improvement, maybe.

#### 2

The second invertible operation I'd like to point out is actually a repeat from [last time]({{< ref some-low-discrepancy-noise-functions >}}), where it appeared in the Laine-Karras scramble (and I got it from the [Brent Burley](https://jcgt.org/published/0009/04/01/) paper originally). But this time I got to it by thinking: the above is using the low zero bits of `k` as the shift amount. Can we swap our operands around and use the low zero bits of `a` as the shift amount? Then we'd get a varying rotate per `a`. But I couldn't figure out a way to use that idea that was actually invertible. However in a moment of zen I realized the following is invertible:
```terminal
a ^= (a * k) << 1
```
Which is exactly equivalent to the multiplication by even constants in the nested uniform scramble.

This is pretty interesting in that, if you look at it like a Feistel function, then rather than splitting up the permutation into equal sized classes indexed by half the bits, it splits it into classes indexed by the number of trailing zeros in `a`. Not only are the classes shuffled independently, so values in one class stay in that class, each class is a different size. Within each, the permute is driven by the multiply. (Sorry if all this is a bit abstract all of a sudden).

But in light of what I said before about Feistel networks I will use it like this, because the bits in `k` are valuable:
```terminal
a ^= ((a * k) << 1) ^ k
```

So that's two bijections. One is a little complicated code-wise but is really simple conceptually; an odd multiply followed by a rotate. It's easy to see why it's invertible. One is simple code-wise and is complicated conceptually; I don't know what to call it. It's a bit more subtle I think.

## permute

To use these, I need to define the problem. We want to **randomly sample permutations**, uniformly and independently. For small $N$, this means sometimes sampling 0, 1, 2, 3, 4... as a random permutation. So, that's a stateless function like this, where `seed` enumerates permutations in a pseudorandom order.
```c
uint32_t permute(uint32_t i, uint32_t N, uint32_t seed);

// Usage:
for (uint32_t i = 0; i < N; i++) {
	uint32_t index = permute(i, N, seed);
	
	// ... use index 
}
```

Secondary goal is that it should just work. No need to seed it well. Cycle walking for non powers of two[^cycle]. 

[^cycle]: Rejection sampling is faster, and even fast on the GPU as that Michell paper points out. I think it's better statistics-wise too; it just can't be dropped in and used anywhere. 

The idea is that generating pseudorandom bits is expensive, so do it once at the start, and shift out the generated bits from a register as a source of entropy. Then use each bit of entropy at least once. I found the two bijections above weren't enough on their own for good avalanche so I gray code between each use of entropy bits:


```c
static uint32_t hash32(uint32_t x) {
    x ^= x >> 16;
    x *= 0x21f0aaad;
    x ^= x >> 15;
    x *= 0xd35a2d97;
    x ^= x >> 15;
    return x;
}

static uint32_t log2_floor(uint32_t a) {
    return 31u - _lzcnt_u32(a);
}

static uint32_t log2_ceil(uint32_t a) {
    return log2_floor(a - 1u) + 1u;
}

uint32_t permute(uint32_t i, uint32_t n, uint32_t seed) {
    uint32_t bits = log2_ceil(n);
    uint32_t mask = (1u << bits) - 1u;
    uint32_t multiplier_mask = mask & (~0u >> bits); 
    uint32_t index_seed = (i >> bits) ^ n;
    
    uint32_t state0 = seed + index_seed; 
    uint32_t state1 = hash32(index_seed - seed);

    do {        
        uint32_t state = state0;
        uint32_t rounds = 2;

        while (rounds--) {
            uint32_t p = state;

            do {
                uint32_t q = p;
                p >>= bits;
                uint32_t r = p ^ state;
                p >>= bits;
                uint32_t s = p ^ state;
                p >>= bits;

                q &= ~1u;
                q += ((q & multiplier_mask) == 0u) << 1;
                uint32_t q_lb = (q & (0u - q)) - 1u;

                i ^= ((i * p) << 1) ^ p;
                i ^= (i & mask) >> 1;
                uint32_t iqr = (i * q) + r; 
                i = iqr + ((i ^ (iqr >> bits)) & q_lb);
                i ^= (i & mask) >> 3;
                i ^= ((i * s) << 1) ^ s;
                i ^= (i & mask) >> 7;
            } while (p);

            state = state1;
        }
        
        i &= mask;
    } while (i >= n);
    
    return i;
}
```

I kept it all within 32-bits to make it easier to analyze. It doesn't work for $N > 2^{31}$. If you want that, go to 64-bits. Replace the hash and add 
```c
i ^= (i & mask) >> 15;
```
somewhere. One benefit of having no constants is it's clear how to extend this thing to higher bit counts. 

### Fiddly detail

{{< aside >}}

The high bits in the index would otherwise go to waste so I use them as more seed bits, so each seed really defines a sequence of permutations per $N$, rather than just one permutation per $N$.

The `log2_ceil` is a little exotic in a non-systems language context but it is pretty much free here with `lzcnt`, you probably want to pass it in precomputed if it or an equivalent instruction is not available, the alternatives really dent the speed of this thing. [It's from Travis Downs](https://stackoverflow.com/a/51351885). 

The hash function is one of those [prospecting for hash functions](https://nullprogram.com/blog/2018/07/31/) hashes. The way I use it, you can see you could also pull it out precomputed once for the whole permutation, if you really wanted to.

As well as the add, I sneak in a xor of the original bits in middle of the multiply-rotate. Philox-y. And there's always at least 1 bit of rotation.

I don't like the `while (p)`, I'd rather use a fixed number of iterations derived from `n`. As it is, larger `n` shift bits out faster and stop earlier. But it will also stop early if the state becomes 0. It works better statistics-for-time this way, which I don't really understand.

{{< /aside >}}

### Justifications

For $N$ larger than 12, 32 bits is not enough seeds to index every permutation, so it's fine to fall short of hitting every permutation, so long as the sampling is[^bias] unbiased. 

[^bias]: indistinguishable from an unbiased sample until we exhaust the seed space. Do you care about this distinction? Did I need to add it? 

To be unbiased we need this: it doesn't matter how you seed this thing. Consecutive seeds must produce permutations that are uncorrelated. It doesn't take long before the space of $N!$ permutations it's supposed to be sampling from is so vast that all $2^{32}$ permutations are a vanishingly small subset. So, if nearby seeds are correlated, we already know we are sampling from a biased sample of all permutations. That's why I use the seed directly in the first round: we could hash it, and this will probably give us better `(state0, state1)` pairs to use (there are $2^{64}$ such pairs and we'll use $2^{32}$ of them), but there is no simple way to avoid having many mostly-zero states in one side of the pair; all we can control is what order we get them in.

For that reason, I don't think we can get away with using only 32 bits of state, even though we'll only ever map to 32 bits worth of permutations. If we hash, we can use an invertible hash to guarantee each seed maps to unique hash bits. But this means we just shuffled the low-entropy seeds around. Or we use a non-invertible hash, and we know for sure some seeds map to the same permutation--can't be having it. Even if we pack this thing to the gills with intimidating constants, a low entropy seed will mean we land on a permutation near (in some sense) to the default permutation selected by the constants.

Expanding the seed an extra 32 bits solves all this. 

To get an idea for why we really cannot have any correlations period, think about lexicographically sorting all the permutations and looking for correlations between nearby seeds. If $N = 500$ then for the first 10 values we have $${500 \choose 10} > 2^{67}$$ possible permutation-heads, so by the 11th value we expect the sorted permutations to be completely uncorrelated again.

The restriction to 32-bit integers is somewhat artificial but it also enabled reasoning like the above that I'm not sure I'd have got to without it. 

## Testing these things

A quick test that will fail most ideas you come up with is to generate permutations of size 8, each value is 3 bits so you only need 24 bits to represent an entire permutation. Generate a bunch, pack each into an int and compare the number of unique ints you get to unique numbers from a PRNG in $[0, 8!)$. Or math it out, but we're all friends here. This fails `permute` when using a single round.

To get an idea for the behaviour with larger $N$ you can make a [matrix diagram](https://bost.ocks.org/mike/shuffle/compare.html) that visualises how often a each input index gets mapped to each output index. This works but I found you could look good here while still being biased (this is true of avalanche as well). Instead, try this: look for correlations between adjacent indices. So, instead of counting `(i, permute(i))` pairs, count `(permute(i), permute(i + 1))` pairs. Somewhat interestingly, since these are always different, the pairs this gives you form a particular kind of permutation called a [derangement](https://en.wikipedia.org/wiki/Derangement). With that said, here's `permute` with only 1 round, $N=1024$ and $16N$ consecutive seeds near 0:
{{< wideimg urn_seq_1.png >}}
{{< aside >}}
Scaled down by $2\cdot16N\cdot\frac{1}{(N-1)}$ which puts the expected average at $0.5$. And fed through the `BrGB` colour map from matplotlib which is white in the middle. It's much more clear what's going on compared to grayscale.
{{< /aside >}}

The zeros along the diagonal are expected, as it's a derangement. But it's not quite there yet, note that near the diagonal it is slightly darker and undersampled.
Here's two rounds:
{{< wideimg  urn_seq_2.png >}}

👍. These are all the seeds around zero--all ones, all zeros, 31 ones, 31 zeros, that kind of junk.

The last test I like is for small $N$, counting repeat permutations. Similar to the first test but more involved to actually implement. This is an interesting test because when we randomly sample permutations of length $13$, there are more than $2^{32}$ permutations to sample but the number of samples before we expect to see a repeat is far less than $2^{32}$. Knuth in TAOCP somewhere has an approximate formula for this
$$Q(N!) \sim 1 + \sqrt{\frac{\pi N!}{2}} +\space\dots$$
which is also [lurking on the Wikipedia article on the birthday problem](https://en.wikipedia.org/wiki/Birthday_problem#Average_number_of_people_to_get_at_least_one_shared_birthday). From this you get that only after $N > 21$ or $22$ or so is it reasonable to map each seed to a unique permutation, as $$Q(21!) \approx 2^{33}$$ but $$Q(20!)\approx 2^{31}$$

Between 13 and 20, in order to look statistically right, we need to be producing repeats--even though there are more permutations than seeds!!

This test is the hardest I've found to pass: an older function I had was a real slow thing with some Feistel rounds that looked otherwise good, and this test failed it at $N = 19$. Unfailing it is how I got to the multiply-rotate. At the time I was looking at gaps, but [M.E. O'Neill points out you can also count repeats](https://www.pcg-random.org/posts/birthday-test.html) and tells you how many samples to take and how to compute p-values so let's just use that. I'm going to dump a table on you now. Each row looks at consecutive seeds starting at $0$:

| N   | samples    | dupes | expected | unique_dupes | p    |
| --- | ---------- | ----- | -------- | ------------ | ---- |
| 3   | 16         | 10    | 10.32    | 4            | 0.54 |
| 4   | 31         | 14    | 13.42    | 8            | 0.63 |
| 5   | 70         | 19    | 16.80    | 16           | 0.75 |
| 6   | 170        | 21    | 18.49    | 18           | 0.76 |
| 7   | 449        | 18    | 19.38    | 18           | 0.44 |
| 8   | 1270       | 16    | 19.78    | 16           | 0.24 |
| 9   | 3810       | 13    | 19.93    | 13           | 0.07 |
| 10  | 12048      | 14    | 19.98    | 14           | 0.11 |
| 11  | 39959      | 19    | 19.99    | 19           | 0.47 |
| 12  | 138420     | 19    | 20.00    | 19           | 0.47 |
| 13  | 499080     | 20    | 20.00    | 20           | 0.56 |
| 14  | 1867387    | 16    | 20.00    | 16           | 0.22 |
| 15  | 7232357    | 19    | 20.00    | 19           | 0.47 |
| 16  | 28929425   | 19    | 20.00    | 19           | 0.47 |
| 17  | 119279073  | 12    | 20.00    | 12           | 0.04 |
| 18  | 506058246  | 20    | 20.00    | 20           | 0.56 |
| 19  | 2205856754 | 26    | 20.00    | 26           | 0.92 |
| 20  | 4294967295 | 5     | 3.79     | 5            | 0.82 |
| 21  | 4294967295 | 1     | 0.18     | 1            | 0.99 |
| 22  | 4294967295 | 0     | 0.01     | 0            | 0.99 |

Yeh: looks random. The p-value breaks down a bit towards the end there because we are taking so few (!!) samples, but whatever. The `unique_dupes` column is just a sanity check that we aren't getting the same repeated permutation.

Counting repeats from all $2^{32}$ permutations turns out to be a bit non-trivial. [Code is here if you want](/posts/unique-random-numbers/count.cpp).

I've been less thorough with testing really large $N$. I dunno. Avalanche isn't really a great test here, necessary but not sufficient type beat.

## End

I've been sitting on this draft unpublished for a while now. I picked up some entropy intuition sometime around writing my low discrepancy noise post, I was trying to figure out why the permutations you can get out of xorshift and LCGs are so bad.

It's invertible, but I have no idea what the inverse function will look like.

I was aiming for the performance to be around the same as Andrew Kensler's permute, the correlated multi-jitter one. By the way, if you understood what I was talking about with the Feistel bits thing you can just eyeball it to get an idea of the permutations you'll get out of it. My permute is about 2x slower, or 1.4x if you let the optimizer precompute the seed hash for you. Given the statistical quality I'm after I think this is alright, I can just throw this thing at people and not worry about them seeding it wrong or whatever. I think you can do better speed-wise but I don't know how much better. 

And the small $N$ thing. Why the focus on that? Couldn't you just shuffle an array every time for those? Like, sure, maybe, but really my issue is: if you can't nail the small $N$ case where it's easy to verify the statistics are good, why would you think large $N$ is any better? Okay that's it. ThaNKS for reading

