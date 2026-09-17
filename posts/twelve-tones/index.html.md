---
title: "Twelve tones are inescapable"
date: 2025-03-31T12:00:00Z
tags: [music theory]
---

{{< aside >}}

Speculations. Nothing new just held up at a different angle than what you've 
seen before.

{{< /aside >}}

I want to write about something interesting you can do with a single pentatonic scale. I'm just going to begin with what I noticed that got me thinking about this.

<!--more--> 
 
Take $\text C$ major pentatonic,

$$ \text{C D E G A}$$
And transpose it onto $\text{G}$.
$$
\text{G A } \underline{\text B} \text{ D E}$$
A new note popped out. The structure of the scale didn't change but we needed a new note to represent it. If we didn't know about $\text B$, now we do. 

Now watch this. I've added the number of semitones between each note and color coded notes by the transposition they are introduced in. Start with $\text C$ major pentatonic:
$$ \color{#0073e6}\text{C D E G A} \\
\color{#000}\small\text{2 2 3 2 3}$$
Transpose onto $\text E$:
$$\color{#0073e6}\text{E }\color{#89ce00}\text{F♯ }\color{#89ce00}\text{G♯ }\color{#0073e6}\text{B }\color{#89ce00}\text{C♯} \\
\color{#000}\small\text{2 2 3 2 3} $$

Rotate to $\text G♯$: 
$$\color{#89ce00}\text{G♯ } \color{#0073e6}\text{B } \color{#89ce00}\text{C♯ } \color{#0073e6}\text{E } \color{#89ce00}\text{F♯ }\\ 
\color{#000}\small\text{3 2 3 2 2} $$
Transpose back to $\text C$: 
$$\color{#0073e6}\text{C } \color{#e6308a}\text{D♯ } \color{#e6308a}\text{F } \color{#89ce00}\text{G♯ } \color{#e6308a}\text{A♯} \\ 
\color{#000}\small\text{ 3 2 3 2 2} $$

And we've got all of the notes in 2 transpositions:
$$
\color{#0073e6}\text{A  }
\color{#e6308a}\text{A♯  }
\color{#89ce00}\text{B  }
\color{#0073e6}\text{C  }
\color{#89ce00}\text{C♯  }
\color{#0073e6}\text{D  }
\color{#e6308a}\text{D♯  }
\color{#0073e6}\text{E  }
\color{#e6308a}\text{F  }
\color{#89ce00}\text{F♯  }
\color{#0073e6}\text{G  }
\color{#89ce00}\text{G♯ } \\
\color{#000}\small\text{1 1 1 1 1 1 1 1 1 1 1 1} 
$$

So that's cool. Now what I would like to do is get an understanding of what is going on here that doesn't rely on existing twelve-tone theory. Being able to lump pitch-classes into one of twelve ordered symbols that wrap around is doing a lot of work. So the rest of this post is about how much structure you need before pentatonic scales start implying the chromatic scale. Then we get to speculatin'. If this doesn't sound interesting to you you can stop reading now.
## String theory

First I need to explain why the $\text G♯$ onto $\text C$ transposition is a totally normal thing to do. By rotating we get a mode, but why care about modes?

So suppose you have a pair of strings. If you have a string instrument handy, you can try playing around with this. For pitches I will use the first two scales above, so one tuned to $\text C$ and one tuned to $\text E$. We get the $\text C$ and $\text E$ scales by placing the 2-2-3-2 pattern onto them. 

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note blue" style="left: 0px;">C</div>
    <div class="note blue" style="left: 65.46px;">D</div>
    <div class="note blue" style="left: 123.78px;">E</div>
    <div class="note blue" style="left: 199.55px;">G</div>
    <div class="note blue" style="left: 243.24px;">A</div>
</div></div>
<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint green" style="left: 300px;"></div>
    <div class="marker green" style="left: 600px;"></div>
    <div class="note green" style="left: 0px;">E</div>
    <div class="note green" style="left: 65.46px;">F♯</div>
    <div class="note green" style="left: 123.78px;">G♯</div>
    <div class="note green" style="left: 199.55px;">B</div>
    <div class="note green" style="left: 243.24px;">C♯</div>
</div></div>

Now we want to play one of the scales one the opposite string. Looking for the $\text E$ scale on the $\text C$ string we find the same notes here (up to octave equivalence, I went back and forth on this but I don't think it matters): 

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green" style="left: 33.68px;">C♯</div>
    <div class="note green" style="left: 123.78px;">E</div>
    <div class="note green" style="left: 175.74px;">F♯</div>
    <div class="note green" style="left: 222.02px;">G♯</div>
    <div class="note green" style="left: 282.16px;">B</div>
</div></div>

Now we move the pattern we just found directly over to the $\text E$ string, and there we go, all the notes, no weird tricks, as promised. 

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint green" style="left: 0px;"></div>
    <div class="midpoint green" style="left: 300px;"></div>
    <div class="marker green" style="left: 600px;"></div>
    <div class="note red" style="left: 33.68px;">F</div>
    <div class="note red" style="left: 123.78px;">G♯</div>
    <div class="note red" style="left: 175.74px;">A♯</div>
    <div class="note red" style="left: 222.02px;">C</div>
    <div class="note red" style="left: 282.16px;">D♯</div>
</div></div>

This is pretty much immediate, right. You want to play the same scale on strings tuned to different pitches, and out it drops. 

Now, that got rid of symbolic manipulation and modes but I'm still relying on equal temperament. So I say it's immediate but justifying 12-TET takes a lot of theory. There's a gap here between experimenting with pentatonics on strings and reaching 12 tones that theory has already filled in.

That's easy enough to fix. We've got to redo the above with non 12-TET patterns. _Pattern_ because even scales are too much theory baggage for this part. To get away from any lingering chromaticism I'm going to dump down the fifth at $1/3$--I'll get to why even people who don't care about $3:2$ ratios or, hell, harmony, will find it notable later--and then fill in the empty space by placing nodes equally spaced between the gaps. This turns out to give a seven-limit tuning (exercise for the reader): 

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note blue" style="left: 0.00px;">0</div>
    <div class="note blue" style="left: 66.67px;">1/9</div>
    <div class="note blue" style="left: 133.33px;">2/9</div>
    <div class="note blue" style="left: 200.00px;">1/3</div>
    <div class="note blue" style="left: 250.00px;">5/12</div>
</div></div>
<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint green" style="left: 0px;"></div>
    <div class="midpoint green" style="left: 300px;"></div>
    <div class="marker green" style="left: 600px;"></div>
    <div class="note green" style="left: 0.00px;">0</div>
    <div class="note green" style="left: 66.67px;">1/9</div>
    <div class="note green" style="left: 133.33px;">2/9</div>
    <div class="note green" style="left: 200.00px;">1/3</div>
    <div class="note green" style="left: 250.00px;">5/12</div>
</div></div>

These two patterns are like our $\text C$ and $\text E$ before, except now the green string is tuned to the $2/9$ node of the blue. Find those green tones on the blue string, by ear, so I'm not going to pretend we have integer ratios for these:

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green" style="left: 55.56px;">0.09</div>
    <div class="note green" style="left: 133.33px;">0.22</div>
    <div class="note green" style="left: 185.19px;">0.31</div>
    <div class="note green" style="left: 237.04px;">0.40</div>
    <div class="note green" style="left: 288.89px;">0.48</div>
</div></div>
<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint green" style="left: 0px;"></div>
    <div class="midpoint green" style="left: 300px;"></div>
    <div class="marker green" style="left: 600px;"></div>
    <div class="note red" style="left: 55.56px;">0.09</div>
    <div class="note red" style="left: 133.33px;">0.22</div>
    <div class="note red" style="left: 185.19px;">0.31</div>
    <div class="note red" style="left: 237.04px;">0.40</div>
    <div class="note red" style="left: 288.89px;">0.48</div>
</div></div>

Placing the pattern on the green string without considering how it sounds made the red $\text G♯$ analogue. Now find it on the blue string, again by ear, so these produce the same pitches as on the green string,

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note red" style="left: 35.39px;">0.06</div>
    <div class="note red" style="left: 116.05px;">0.19</div>
    <div class="note red" style="left: 176.54px;">0.29</div>
    <div class="note red" style="left: 237.04px;">0.40</div>
    <div class="note red" style="left: 277.37px;">0.46</div>
</div></div>

Looking at the full gamut of notes we've generated gives...

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green up" style="left: 55.56px;">0.09</div>
    <div class="note green up" style="left: 133.33px;">0.22</div>
    <div class="note green up" style="left: 185.19px;">0.31</div>
    <div class="note green up" style="left: 237.04px;">0.40</div>
    <div class="note green up" style="left: 288.89px;">0.48</div>
    <div class="note red down" style="left: 35.39px;">0.06</div>
    <div class="note red down" style="left: 116.05px;">0.19</div>
    <div class="note red down" style="left: 176.54px;">0.29</div>
    <div class="note red down" style="left: 237.04px;">0.40</div>
    <div class="note red down" style="left: 277.37px;">0.46</div>
    <div class="note blue" style="left: 0.00px;">0</div>
    <div class="note blue" style="left: 66.67px;">1/9</div>
    <div class="note blue" style="left: 133.33px;">2/9</div>
    <div class="note blue" style="left: 200.00px;">1/3</div>
    <div class="note blue" style="left: 250.00px;">5/12</div>
</div></div>

Yeah. Compare to 12-TET:

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green" style="left: 33.68px;">0.06</div>
    <div class="note green up" style="left: 123.78px;">0.21</div>
    <div class="note green" style="left: 175.74px;">0.29</div>
    <div class="note green up" style="left: 222.02px;">0.37</div>
    <div class="note green" style="left: 282.16px;">0.47</div>
    <div class="note red down" style="left: 0.00px;">0.00</div>
    <div class="note red" style="left: 95.46px;">0.16</div>
    <div class="note red" style="left: 150.51px;">0.25</div>
    <div class="note red down" style="left: 222.02px;">0.37</div>
    <div class="note red" style="left: 263.26px;">0.44</div>
    <div class="note blue up" style="left: 0.00px;">0.00</div>
    <div class="note blue" style="left: 65.46px;">0.11</div>
    <div class="note blue down" style="left: 123.78px;">0.21</div>
    <div class="note blue" style="left: 199.55px;">0.33</div>
    <div class="note blue" style="left: 243.24px;">0.41</div>
</div></div>

 One thing to watch out for is we didn't start with the major pentatonic scale so we shouldn't expect the nodes to correspond to nodes we found using the 12-TET scale. That is, they are not in the wrong position, or shifted over from where they ought to be. They just are where they are. But notice that even though we've lost the clear 12 tone structure, we're still landing near 12-TET nodes. It's the fifth that's causing that. 

{{< aside >}}
It's not hard to see why this clustering happens in principle. Once you have a fifth then you also have a fourth by the interval between it and the octave. A whole tone is then the interval between them. Stacking whole tones on top of the fifth will eventually produce a semitone relative to the fundamental. 

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="note blue" style="left: 0px;">C</div>
    <div class="note green" style="left: 150.51px;">F</div>
    <div class="note green" style="left: 199.55px;">G</div>
    <div class="note red" style="left: 243.24px;">A</div>
    <div class="note red" style="left: 282.16px;">B</div>
    <div class="note red" style="left: 316.838px;">C♯</div>
    <div class="marker" style="left: 300px;"></div>
</div></div>

Once you've identified this thing as a semitone and try to unify it with other near-semitones--by ear or mathematically--you're entering chromatic territory. So all the pieces are there once you have the fifth and the octave. 

Mathematically, this is equivalent to Pythagorean tuning. I've just motivated it differently. For whatever reason nowadays the way it's presented is by stacking fifths and pointing out the comma you get after a comical number of fifths--try to do it on a real string and you will see what I mean--but slightly older textbooks like John Backus' *The Acoustical Foundations of Music* (1969, pretty interesting) have the actual way it was done which was to alternate fifths upwards and fourths downwards. A fourth down followed by a fifth up directly gives you the whole tone.

{{< /aside >}}

To finish this bit off I want to look at applying this procedure to $\text{C D E G A}$ again but in Pythagorean tuning and with just intonation. Here's 12-TET all on one string first, to compare with.

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green" style="left: 33.68px;">0.06</div>
    <div class="note green up" style="left: 123.78px;">0.21</div>
    <div class="note green" style="left: 175.74px;">0.29</div>
    <div class="note green up" style="left: 222.02px;">0.37</div>
    <div class="note green" style="left: 282.16px;">0.47</div>
    <div class="note red down" style="left: 0.00px;">0.00</div>
    <div class="note red" style="left: 95.46px;">0.16</div>
    <div class="note red" style="left: 150.51px;">0.25</div>
    <div class="note red down" style="left: 222.02px;">0.37</div>
    <div class="note red" style="left: 263.26px;">0.44</div>
    <div class="note blue up" style="left: 0.00px;">0.00</div>
    <div class="note blue" style="left: 65.46px;">0.11</div>
    <div class="note blue down" style="left: 123.78px;">0.21</div>
    <div class="note blue" style="left: 199.55px;">0.33</div>
    <div class="note blue" style="left: 243.24px;">0.41</div>
</div></div>

Pythagorean:

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green" style="left: 38.13px;">0.06</div>
    <div class="note green up" style="left: 125.93px;">0.21</div>
    <div class="note green" style="left: 178.60px;">0.30</div>
    <div class="note green up" style="left: 225.42px;">0.38</div>
    <div class="note green" style="left: 283.95px;">0.47</div>
    <div class="note red down" style="left: 8.08px;">0.01</div>
    <div class="note red" style="left: 100.56px;">0.17</div>
    <div class="note red" style="left: 156.06px;">0.26</div>
    <div class="note red down" style="left: 225.42px;">0.38</div>
    <div class="note red" style="left: 267.04px;">0.45</div>
    <div class="note blue up" style="left: 0.00px;">0</div>
    <div class="note blue" style="left: 66.67px;">1/9</div>
    <div class="note blue down" style="left: 125.93px;">0.21</div>
    <div class="note blue" style="left: 200.00px;">1/3</div>
    <div class="note blue" style="left: 244.44px;">11/27</div>
</div></div>

Just intonation:

<div class="string-container"><div class="string-overflow">
    <div class="string"></div>
    <div class="midpoint blue" style="left: 0px;"></div>
    <div class="midpoint blue" style="left: 300px;"></div>
    <div class="marker blue" style="left: 600px;"></div>
    <div class="note green up" style="left: 24.00px;">0.04</div>
    <div class="note green up" style="left: 120.00px;">1/5</div>
    <div class="note green up" style="left: 173.33px;">0.29</div>
    <div class="note green up" style="left: 216.00px;">0.36</div>
    <div class="note green up" style="left: 280.00px;">0.47</div>
    <div class="note red down" style="left: 88.00px;">0.15</div>
    <div class="note red down" style="left: 139.20px;">0.23</div>
    <div class="note red down" style="left: 216.00px;">0.36</div>
    <div class="note red down" style="left: 258.67px;">0.43</div>
    <div class="note blue" style="left: 0.00px;">0</div>
    <div class="note blue" style="left: 66.67px;">1/9</div>
    <div class="note blue" style="left: 120.00px;">1/5</div>
    <div class="note blue" style="left: 200.00px;">1/3</div>
    <div class="note blue" style="left: 240.00px;">2/5</div>
    <div class="note red down" style="left: 292.80px;">0.49</div>
</div></div>

Pythagorean tuning is doing a very good job at preserving structure we happen to already know is there. But if you didn't know, then what it is giving you is a way of moving patterns from one string to another that mostly just works. Without it, scale correspondences between strings jump all over the place, without clear structure and with annoying discrepancies everywhere, which you can see in just intonation and my arbitrary pentatonic scale.

To harp on just intonation a bit, I will quote acoustician [John Backus](https://en.wikipedia.org/wiki/John_Backus_(acoustician)), 
> Because of these difficulties, the just scale has never been of any practical use. Its theoretical attraction to individuals with numerological inclinations is extremely strong, however, so much so that it has even been called the “natural” scale, as though it had some fundamental basis in nature not possessed by other scales. It appears in practically every book dealing with the acoustics of music, where it has been given an emphasis it does not deserve.
>
> <cite>John Backus, The Acoustical Foundations of Music, 1969</cite>

It turns out people tried really hard to make just intonation work during the Renaissance. Back then, Vincenzo Galilei in *Dialogue on Ancient And Modern Music*[^ancient] did a similar thing to what I did above and systematically (and much more thoroughly than me) looked at how the intervals combine into near-misses. To what extent he is responsible for them abandoning just intonation, I don't know, but he wanted everyone to move on to meantone and equal temperaments ([sometimes both at once](https://www.youtube.com/watch?v=XNvUPtFwZ8Y)), and they did. Another thing: it was a matter of debate among themselves whether they sang in just intonation or not, and they didn't. This is pretty amusing to me as people still say the same thing. Galilei might have been the first person to actually check. If we've had 500 years of this, how many other things that I take for granted are just wrong? Do barbershop quartets really sing in just intonation? Wikipedia...
> However, "In practice, it seems that most leads rely on an approximation of an equal-tempered scale for the melody, to which the other voices adjust vertically in just intonation."[[5]](https://en.wikipedia.org/wiki/Barbershop_music#cite_note-Averill-5)

Oh my god dude it keeps happening

[^ancient]: _Vincenzo Galilei. Dialogue on Ancient and Modern Music. Translated by Claude V. Palisca. Music Theory Translation Series. New Haven: Yale University Press, 2003_.
\
\
The introduction to this book by the translator is worth reading if you're interested in what is the deal, historically, with all these scales. After showing _mathematically_ the mess commas get you into, Galilei then does scale construction by ear, by the way.


## This post part two: what's the deal with fifths anyway?

For a long time now I've been pretty sure the usual story you hear that justifies the chromatic scale by going just intonation consonances $\rightarrow$ Pythagorean approximation $\rightarrow$  meantone etc. $\rightarrow$  equal temperament is bogus. Not just historically unsupported but, as a story we tell ourselves, it seems off, to me. On the other hand, throwing up your hands and declaring it all arbitrary and culturally contingent is denying a lot of the underlying structure that pops up everywhere.

One reason I think pentatonic scales are important in motivating the 12 tone system is purely anthropological: they come along for the ride once you have anything resembling a scale and so are everywhere. But it's not the case that what you end up with are pentatonic scales _with a fifth_. Gamelan music is probably the best example where they dodged this and developed an entirely different approach to harmonic structure that uses a lot of inharmonic timbres. So transposing pentatonic scales alone isn't enough to motivate twelve tones, even if you find my trick above convincing.

Along similar lines, there's an interesting 2024 preprint by [McBride et al.](https://arxiv.org/abs/2408.12633), _Melody predominates over harmony in the evolution of musical scales across 96 countries_, that points out folk melodies survive by ease of use:  the whole tone to third interval range is in a goldilocks zone for singing. They focus on song but the same argument works for instruments too. It's just hard to be mechanically precise about pitch until you invent a [monochord](https://en.wikipedia.org/wiki/Monochord) or something like it. Their point on top of that is that, once you gather them all up and analyse them, the scales you get out of this in practice are not particularly harmonic (consonant) in general.

So what's not bogus. Well, if you're sufficiently serious about music for a long enough time you will eventually learn something about tone production. 

> *Salviati*: A string which has been struck begins to vibrate and continues the motion as long as one hears the sound; these vibrations cause the immediately surrounding air to vibrate and quiver; then these ripples in the air expand far into space and strike not only all the strings of the same instrument but even those of neighboring instruments. Since that string which is tuned to unison with the one plucked is capable of vibrating with the same frequency, it acquires, at the first impulse, a slight oscillation; after receiving two, three, twenty, or more impulses, delivered at proper intervals, it finally accumulates a vibratory motion equal to that of the plucked string, as is clearly shown by equality of amplitude in their vibrations. This undulation expands through the air and sets into vibration not only strings, but also any other body which happens to have the same period as that of the plucked string. Accordingly if we attach to the side of an instrument small pieces of bristle or other flexible bodies, we shall observe that, when a spinet is sounded, only those pieces respond that have the same period as the string which has been struck; the remaining pieces do not vibrate in response to this string, nor do the former pieces respond to any other tone.
>  
> <cite>Galileo Galilei, Two New Sciences, 1638, trans. Henry Crew and Alfonso De Salvio</cite>

Yeah I've been rooting around old texts from before 12-TET got really locked in to see what they find salient about music. The oldest I've got is the *Record of Music* which is dated to Warring States period China, so 200-400 BCE or so. They had proper Pythagorean twelve-tone tuning back then, too. I'm just going to quote from it, in full, starting from the very beginning, until we hit something relevant. 

> **The Roots of Music**
> 
> In all cases, the arising of music (yin) is born in the hearts of men. The movement of men's hearts is made so by \[external] things. They are touched off by things and move, thus they take shape in \[human] sound (sheng). Sounds respond to each other, and thus give birth to change.
> 
> <cite>Scott Cook, _Yue ji_ - Record of Music. Introduction, translation, notes, and commentary. Asian Music, vol. 26 no. 2, 1995</cite>

Yup. And like all sufficiently old texts it comes with commentary from ~100 CE that shows they understood this to be talking about sympathetic resonance, like Galileo up there. (By the way a gong here is pretty much the root note of a pentatonic scale.) 
>With musical instruments, when one plays a *gong*, then many *gong*'s respond. But this is not sufficient to be found enjoyable as music. For this reason, they are given to change and caused to be mixed together. The *Yi Jing* says: 'Alike sounds respond to each other, alike *qi* seek each other.'
>
> <cite>Zheng Xuan</cite>

Now, I need to point out that what follows in the translation I've got is 2 pages of modern-day translator's commentary on just these tiny fragments alone. And it did not occur to them, at all, that this was about resonance. They focus entirely on the metaphysics, movement of men's hearts or whatever. So my interpretation here is not necessarily self-evident, but, come on. The commentary is saying it directly: with musical instruments, when you play a $\text C$, $\text C$s respond!

This is what is so special about fifths: the $\text F$ below and the $\text G$ above _also_ respond. For higher harmonics the effect of this falls off very rapidly. And, it does sound good, but it doesn't resonate at its own pitch. You hear a harmonic, $\text C$ an octave up. Timbre-wise it's more like a reverb. So, if you have a string instrument, whenever your open strings form unisons, octaves, and fifths against whatever note you're playing, you get a richer sound that you can't get without them. But as Zheng Xuan says, you need more than unisons to make music. [Musicians really want this](https://en.wikipedia.org/wiki/Ten-string_classical_guitar_of_Yepes).

At this point, if all you have are 3 strings tuned a fifth apart, say $\text{C}_3$, $\text{ G}_3$ and $\text{ D}_4$, then finding $\text G_3$ and $\text D_3$ on the $\text C_3$ string is exactly the first two steps of a Pythagorean tuning. Sympathetic resonance leads you right to it, even if your musical sense is focused exclusively on melodic structure and chords don't interest you.

Finally, while I do think this is extremely relevant to the historical development of instruments, you also shouldn't ignore that Chinese text I quoted, which says, paraphrasing: when you hum the right way at things that resonate, they hum back. The significance of this to them will have been slightly different than its significance to us, right.

{{< aside >}}

By the way, the music stuff out of ancient China is incredible. We know they used the chromatic scale because we keep digging up [bronze bells](https://en.wikipedia.org/wiki/Bianzhong) that come in sets tuned to it. And you can hit them different places to produce one of two tones, a third apart, and we have no idea how they found the shape that does that, and cannot yet reproduce it ourselves without copying. At this point, the oldest bells are a thousand years older than any written record of them using Pythagorean tuning to tune the things in the first place. This has led one professor of Chinese art 'n' archaeology to say

> But the instruments that mattered in ancient China were bells, not
strings, and the theorists of a bell culture do not think in such terms. I am
proposing instead that, in a culture focused on bells, and at a time when
scales were a strictly aural phenomenon, the chromatic scale was discovered through transposition of the pentatonic scale. If in China the
chromatic scale was not a difficult idea, surely the reason is that the theorists who discovered it were not doing string-length calculations that
made transposition awkward. The chromatic scale as they conceived it
would have been an equal-semitone scale because there was no reason for
it to be anything else.
>
> <cite>Robert Bagley, The Prehistory of Chinese Music Theory, Proceedings of the British Academy, Volume 131, 2004</cite>

But as I say above, I think you can get away from arithmetic on strings, too. (Also can you even build a bell forge without knowing a lot about ratios of lengths? Serious question. Surely there will be a lot of hoisting involved. It sounds positively Archimedean to me.)

But in any case, the Pythagorean numerology only comes later, when you and the priests are trying to justify what you are doing. Which is totally fair, because if you can't show that your music unites the harmony of the stars with the harmony of the state, what are we even doing here,

{{< /aside >}}

## End 

This post ended up with its own folder in zotero. Man.

But, okay. Here's what I think. Forget all that stuff about the harmonic series and its consonances leading to the chromatic scale. Forget about the diatonic scales too, even. Say that stuff comes later, not before. 

Say instead sympathetic resonance between strings leads you to the _procedure_ of Pythagorean tuning, and it turns out you want to use it because it gives you nice way to organise all the pentatonic scales you play alongside the singers and guys with flutes. As a bonus, that procedural knowledge is something you can teach to just about anybody. You will still adjust your string tuning and intonation while playing a little bit to fit with what the other musicians are doing so you are not yet _playing_ the chromatic scale. But over time this provides a framework that eventually gets set in stone, due to the development of instruments that can only produce fixed pitches.

As a nice just-so story I think this one is a lot more plausible. And I think it gets closer to what is actually important in music. But that's just me
