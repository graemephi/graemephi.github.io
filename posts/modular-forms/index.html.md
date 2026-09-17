---
title: "WTF Are Modular Forms"
date: 2024-03-25T00:34:54Z
tags: [maths]
---
{{< aside >}}
This post is part of the [HMN Learning Jam](https://handmade.network/jam/learning-2024). One weekend to fill your head with stuff and one weekend to dump it back out. I've spent a few more days here and there (that convinced me I could learn the rest of what I needed to know in a weekend) but otherwise that's about how much time I've got in knowing about modular forms. This is a bit out of step from the rest of the submissions which are more programming focused but look: someone had to.

As always happens I probably learned the most while I was writing this post and not when I was reading stuff.

I'm gonna take a very non-standard approach that I've seen fragments of here and there in the Literature, so experts on this stuff know it all, but the path it takes is so irrelevant to what working with modular forms is _actually like_ that a mathematician would never be so cruel as to present it this way. 

However, I'm not a mathematician and am completely new to all this. From what I can tell, this path I'll take here is closer to what was going on when modular forms first appeared in mathematics 200 years ago. It's pretty far removed from modern day modular forms. But this means we get to see what modular forms _are_ in a certain naive sense that hopefully doesn't require a degree in mathematics to understand.

To get the most out of this, you want to know a a little linear algebra and be comfortable with complex numbers. You should also probably read the first half with a graphing calculator open. On the other hand, I've deliberately avoided some convenient mathematics notations/definitions that make maths inaccessible to many people, which makes life harder for me and probably people that know that stuff.

The two books I found most useful for this are:
* Development of Mathematics in the 19th Century, Felix Klein,1928
* Complex Analysis, Elias M. Stein and Rami Shakarchi, 2003

The first is by the Klein bottle guy. He was pretty much there when modular forms became modular forms and is where I got this general approach from. He's more brisk about it. Cool book, could not have understood any of this without it. 

Complex Analysis is a textbook for undergraduates. Goes slow in the right places. Really well written if you know how to read maths textbooks. 

Another book I'd like to recommend that you'll probably have trouble discovering on your own is
* Elliptic Curves, Henry McKean & Victor Moll, 1999

This is in my preferred style for maths textbooks, which I have heard called "breezy" before. Some people figure out they've got a tiny audience and write conversationally directly to them, it's great. No sweating on proofs, just big picture ideas from people fully in the [post-rigorous](https://terrytao.wordpress.com/career-advice/theres-more-to-mathematics-than-rigour-and-proofs/) phase of life, and they trust you have dryer references to fall back on if you need them. But it is squarely aimed at real deal mathematicians so beyond me for the most part. 

A cool resource is [Richard E Borcherds lecture series](https://www.youtube.com/watch?v=f8pjt9ivjjc&list=PL8yHsr3EFj51HisRtNyzHX-Xyg6I3Wl2F&pp=iAQB) on youtube if you want to see what it's really about to a mathematician. He's got a Fields medal in this stuff.

Another cool video is this [MathKiwi video](https://www.youtube.com/watch?v=z7A_bSl8kIw) which in some sense starts where I leave off and has many good visualisations.

To round this list out [here's a bunch of mathematicians saying what they find interesting about modular forms](https://mathoverflow.net/questions/24604/why-are-modular-forms-interesting). Check out how many different angles on them there are.
 
{{< /aside >}}

I can't motivate why you'd want to know about modular forms. If you want to know this stuff, you want to know, and if you don't, you don't. Instead, I want to start at a basic number theory question and make a bee line for modular forms. Modular forms come from a few related ideas hanging together, so we'll have to gather up those ideas first. 

Here's our number theory question: given an integer $n$, how many solutions does
$$n^2 = a^2 + b^2$$have? I start here because it makes the link to questions like these and Fermat's Last Theorem clear, but I am going to say well clear of any weird factorisations and algebra that usually immediately follow this question, don't worry.

What a lot of number theorists like to do when encountering something new is to compute large tables of numbers, and here since you never have to look at $a$ and $b$ above $n$ you don't have that many $(a,b)$ pairs to check. Well, for a few $n$, anyway. You can get pretty far along crunching numbers. Then you stare at the numbers and hope for insight. [This works surprisingly well](https://www.quantamagazine.org/elliptic-curve-murmurations-found-with-ai-take-flight-20240305/).

But instead the way to modular forms is to draw the sucker. This turns it into the following question: on how many places does the circle
$$n^2 = x^2 + y^2$$lie on integer coordinates? Now instead of crunching numbers, you just draw a circle on a grid. Solutions are where the circle lies on a point where the grid lines intersect. That set of points of intersection over the entire $xy$ plane is called a lattice.

The year is 1799 and we would like to solve this problem with a straightedge and compass. We dutifully draw the grid. We try it for one $n$, fill in the row in our table, try a second $n$, fill in the next row... Number theorists love their tables. Eventually, $n$ is too big for our compass. What do? We shrink the lattice. Instead of ever larger circles we ask about ever denser lattices. And instead of leaving this as just a convenience out in the world, we can make it real in the mathematics, and change the problem to looking for rational numbers that satisfy

$$\frac{x^2}{n^2} + \frac{y^2}{n^2} = 1.$$

Play with this a bit in a graphing calculator and you'll realise that once you've found a solution you can extend a line through it from the origin, and lattice points on that line are solutions for some other $n$. So something about the lattice is encoding information about the sums of two squares.

With lattice we encountered the first term that comes up all the time when people talk about modular forms, and maybe see how it's relevant to number theory, so we are making progress.

So, that's a circle. For this exposition I would like to encourage you to act like a mathematician and be willing to entertain idle questions. What about where an ellipse goes through a lattice point? We apply a similar trick as before, and get an axis-aligned ellipse by stretching $x$ and $y$, with $$n^2 = ax^2 + by^2.$$Instead of drawing the ellipse, we stretch the lattice in $x$ and $y$, and we are back to a circle. So we think of an ellipse as a transformed circle, and apply the inverse transform to the lattice instead, and this let's us answer more questions with our compass. Very good.

{{< fitimg "stretch.png" >}}

{{< aside >}}
I quickly made these in [tldraw](https://www.tldraw.com/) cause you really gotta be thinking in pictures to follow this and it's just good manners to show the pictures. However I haven't actually checked these are valid transforms. Sometimes even in a graphing calculator you'll see what looks like an intersection and plug in the numbers and find it's a near miss. So. No rigour here. Also I think the axis $a$ and $b$ here should be sqrtd. Too late now.
{{< /aside >}}

What about an ellipse that isn't aligned to the axis? Rotating the circle does nothing and rotating the lattice is the same as rotating the circle the other way. Instead, we have to shear the ellipse. What Gauss observed is that if we have $$n^2 = ax^2 + bxy + cy^2$$ then we can interpret this as tilting our lattice so it now tiles the plane with parallelograms, rather than squares. The way to get the lattice sheared just right is to set the sides of each parallelogram to $\sqrt a$ and $\sqrt c$ and the slope of the line to $\frac{b}{\sqrt{4ac}}$. (I got this from Klein and verified it in a graphing calculator. Beats me. Visually it makes sense but I'm out of time to spell it out).

And once again: we can read out integer solutions to this equation by drawing a circle of radius $n$ around the origin, and counting the lattice points it goes through.

{{< fitimg "ellipse.png" >}}

The right hand side of that equation is a _binary quadratic form_ and number theorists talk about it as a function in its own right, $$ q(x,y) = ax^2 + bxy + cy^2.$$And now we've landed on a form, so modular forms are appearing over the horizon. What's a form? What makes thing form? It's something polynomial-like that obeys
$$P(tx) = t^kP(x)$$
for some $k$, and, in 2 variables, and you can figure more variables out yourself, $$P(tx, ty) = t^kP(x, y).$$You see that? Linear scaling in the input becomes power scaling in the output. You can see this immediately for $P(x)=x^2$, where $P(tx) = (tx)^2 = t^2x^2 = t^2P(x)$. So $x^2$ is a form. When we have two variables as in $q(x,y)$, then the exponents in each term need to sum to the same number, which gives you the $k$. In $q(x,y)$ it's $2$. That makes it quadratic. And it's binary because we stop at $y$ and don't have a $z$. 

You can imagine why this property might be interesting to people. Distance travelled at constant acceleration or whatever.

Anyway, whatever modular forms are, we now know they are a kind of function, and we expect to see that relationship between its inputs and outputs pop up.

To get to modularity we now want to look more at the lattice and other things we can do to it. The key observation is this: if we have a transformation that sends every lattice point to another lattice point on the original lattice, then with it we can generate more solutions to questions like those above, analogous to extending out the line through the origin we saw with the circle. Since we're interested in integer solutions we'll want transformations we can express with integers. The easiest to find are rotating the lattice by right angles, which give transformations like
$$\begin{bmatrix}0 & -1 \\1 & 0\end{bmatrix}\begin{bmatrix}x \\ y\end{bmatrix}=\begin{bmatrix}-y \\ x\end{bmatrix}.$$
Another one is to shift everything over one lattice point; the translation $$\begin{bmatrix}1 & 1 \\ 0 & 1\end{bmatrix}.$$If you apply that one to $q$ you'll get $q'(x,y) = a(x+y)^2+b(x+y)y+cy^2$ and if you plot that sucker $= n^2$ you'll find it gives a new ellipse that intersects $q$ where $q$ goes through a lattice point, i.e. is an integer solution to $q'(x,y) = n^2$. And if you expand out the terms you'll find yourself back on a binary quadratic form.

You can apply these over and over with each other to get more elaborate transformations that stretch out the parallelograms. The thing they all have in common is they have determinant 1. We recall from 3blue1brown that the determinant is how a matrix will scale the area of the parallelogram, so what these matrices are doing is _preserving_ the area of each cell in the lattice. So we have two ways of seeing why these matrices and their compositions will let lattice points line up 1-to-1 before and after: firstly because we've built them out of simple individual steps that always do this (and it turns out any such integer $\det 1$ matrix can be built this way), and secondly because we know the area never changes, so the density of the lattice is always the same.  

Mathematicians call these--2x2 integer matrices with determinant 1--unimodular. I have no idea why. Since you can multiply them together with abandon and always get back a unimodular matrix, $\det AB = \det A \cdot \det B$, that makes these things collectively a group, the modular group.

We've got modular. We've got forms. We can see what they each have to do with lattices and what lattices have to do with number theory. But still, they're somewhat disconnected.

To tie these things together we need complex numbers. We've been thinking about lattices on the plane this whole time, and now we think of each lattice point as $z = x + iy$. And as usual with complex numbers we can now think of the action of multiplying by $z$ as rotating and scaling the complex plane, so $z$ sends the lattice point $(1,0$) to $(x, y$).

To line things up the same way mathematicians do, here's another way to define a lattice. Take two complex numbers, $\omega_1$ and $\omega_2$ (this is the notation everyone uses), and so long as they do not lie on the same line, we can generate a lattice with $m\omega_1 + n\omega_2$, for integer $m, n$, stepping out in steps of $\omega_1$ as $m$ increases and in steps of $\omega_2$ as $n$ increases. 

If you think about it a bit you can see a purely real $\omega_1$ and a purely imaginary $\omega_2$ will give you a square lattice. Non-orthogonal $\omega$ will give parallelograms. 

{{< fitimg "lattice.png" >}}

Now, in this context we're interested in lattices with integer parts in $\omega$, and there are a lot of symmetries in the plane we want to get rid of, so applying a trick similar to shrinking the lattice to turn questions about integers into questions about rational numbers, we divide out the scale and imaginary part of $\omega_1$, and substitute $\omega_1, \omega_2$ for $1, \tau = 1, \omega_2 / \omega_1$. This is more like the lattices we've been talking about already to shear ellipses, where stepping out in $m$ will step along the $x$ axis. However, unlike before, we always step out in steps of $1$, rather than $\sqrt a$. Compare that to the rational number variant of the sums of squares question we started on.

Mathematicians loathe and fear the bottom half of the complex plane and so swap $\omega_1$ and $\omega_2$ freely to ensure $\tau$ lies on the positive half-plane.

So, now we want to think about a normalized lattice that has points in $x$ axis in steps of $1$ and into the upper half of the complex plane in steps of $\tau$. We get $\tau$ from our choice of $\omega_1$ and $\omega_2$.

This next step I can't justify all that well and found I didn't understand properly when I came to write it. We have a point on the lattice, $z$. We would like to multiply it by a unimodular matrix and get back another point on the lattice. But we can't multiply a 2x2 matrix by a single $z$. We need a second term. It turns out we need homogeneous coordinates--you know, like from video games--and tack a one next to it. Then we get

$$\begin{bmatrix}a & b \\ c & d\end{bmatrix}\begin{bmatrix}z \\ 1\end{bmatrix}=
z\begin{bmatrix}a \\ c\end{bmatrix} + \begin{bmatrix}b \\ d\end{bmatrix}=\begin{bmatrix}az + b \\ az +d \end{bmatrix}$$
which gives us two new $\omega_1$ and $\omega_2$, and we scale that sucker back down to normalise back to $\tau$, and so we the action of these matrices is understood the same as projection matrices. Written directly, that's $$\frac{az + b}{cz + d}.$$ This seems truthy to me, in the sense of collapsing together structure as in our line-through-the-origin case, but I can't explain it fully on it if you press me on it. Remember that here $a, b, c, d$ are all integers.

_Now_ we come to modular forms proper. Before, forms were (implicitly) purely real, but now we see we're knee deep in complex numbers. We had $$P(tx) = t^kP(x).$$These are forms with respect to linear scaling. What we want are forms with respect to the modular group. This means we're going to have some function on the complex plane, and it's inputs are going to be related to its outputs by some power scaling law, after those inputs have been acted on by the modular group.

Let's step back a bit. In this exposition, what we're really interested in is the lattice. We want modular forms to tell us about the lattice; interest in modular forms in their own right comes later.  The tack I've seen taken is to say what we're really interested in are _modular functions_, rather than _forms_, $$f(\frac{az + b}{cz + d})= f(z),\ \ \det([a\ b; c\ d])= 1$$ which act more or less exactly like our lattice in that it doesn't change after being acted on by unimodular matrices, but now for all $z$ in the complex plane. Upper half-plane. Whatever. The hope is that such functions can encode number-theoretic information we care about, the same way $q(x,y)=n^2$ reveals an ellipse.

They then relax this requirement, saying such functions are too hard to find or maybe uninteresting, and require instead $$f(\frac{az+b}{cz+d})=(cz+d)^k f(z).$$
That's our modular form. So... why this? Where'd $az+b$ go? And how to interpret $k$? The way I interpret this is projective geometry-wise, so if you know homogenous coordinates you'll be used to being able to pile up a bunch of transforms then divide out $w$ at the end to land back on a plane. That $(cz + d)$ is saying under a unimodular transformation, $z$ needs to be sent _somewhere_ on the lattice? (I think!) of points scaling by $cz+d$ is able to identify, projectively, as the same point. But, this is pretty handwavey and I think I can only get this idea across to people who already know projection matrices and homogeneous coordinates and all that, and I don't really have an good intuition for how its working here as opposed to in Euclidian 3D.

Naturally, mathematicians are even more restrictive about what kind of function $f$ can be, which I won't bother with.

Here's the punchline. We don't have any such $f$ yet and this post is not really going to go into them. My goal has been to get at why if you find such an $f$, number theory tends to drop out of it, without definition overload. I'll go over two kinds quickly. 

The first is the historical first, the lemniscate elliptic functions. They arose when Euler was investigating the physics of... [elastic ribbons](https://www.jstor.org/stable/41133708). They were particularly interested in this [figure 8 curve](https://www.desmos.com/calculator/d4nfqoor32), called a [lemniscate](https://en.wikipedia.org/wiki/Lemniscate) (Latin for ribbon, naturally), which Gauss figured out a $\sin$ and $\cos$ analogue to, and these turn out to be 'doubly periodic' when extended to complex numbers in the same way as these lattices. 

The second is a much more direct construction that I think was come up with to nail this case, the [Weierstrass elliptic functions](https://en.wikipedia.org/wiki/Weierstrass_elliptic_function). Conceptually, you just drop a divide by zero on every lattice point. This makes the lattice 'puncture' the complex plane which I find weirdly satisfying. You'd like to be able to just do 

$$
f(z) = \sum_{m,n} \frac{1}{(z - (m + n\tau))^2}
$$
and make it so that as $z$ nears a lattice point the $z-(m + n\tau)$ term for that point goes to zero, but this turns out not to converge. Fixing it is a nice trick and then showing it's a modular form is also simple if you are comfortable whippin' sums. For an explanation of this I really recommend the Stein and Sharkachi book, it's good and will occasionally repeat information that needs repeating, a rare skill among mathematicians. 

Putting these to work in real theorems and such is also another matter entirely. So this post hasn't captured the character and feel of how modular forms are used at all. If you do have any skill in that, and you try to define modular forms, you start in weird places, and start talking about q-series (not the $q$ above), and rational points on elliptic curves, and Fourier expansions of partition functions, and
