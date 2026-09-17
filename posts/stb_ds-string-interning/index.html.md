---
title: "stb_ds: string interning"
date: 2020-08-27
tags: [programming]
---

[stb_ds](https://github.com/nothings/stb) is a generic container library for C. It was probably from seeing the same technique in [bitwise](https://github.com/pervognsen/bitwise), but I've had it at the back of my mind for a while now that one of the good use cases for stb_ds was easy string interning. But it's not mentioned anywhere, not even in the [gentle introduction](http://nothings.org/stb_ds)! Well, the pieces are there, but how to put them together is a little subtle.

<!--more-->

By the way, string interning is when you keep at most one copy of a given string in memory, and use immutable references to such copies as your string value type. In return, you get $O(1)$ string equality and you use less memory.

You can do string interning with a single stb_ds hash table, and that's it. I'm pretty sure stb_ds is designed to ensure that this is possible--you can't do it with most hash tables. Several features fitting together just right makes it work.

First, table entries are stored contiguously in memory, and their order is stable, even when the hash table is resized. This is in constrast to other hash table implementations that store their data in sparse arrays. This isn't just an implementation detail but a documented part of the API. For more on why you might want a hash table that does this, check out [this blog post from PyPy](https://morepypy.blogspot.com/2015/01/faster-more-memory-efficient-and-more.html).

Second, stb_ds can hash strings for use as key types. Once you have string interning, you only need primitive type keys for your hash tables. But if you don't have proper string keys before you have interning, you need to figure out what you're doing. We don't have to worry about it.

Third, string hash tables can be configured to store their keys in a memory arena managed by the hash table. This means we won't have to manage the intern pool memory at all. The arena gives us stable pointers and minimises the number of calls to the underlying allocator.

And lastly, although stb_ds's hash table maps keys to values, it's possible to use it without specifying values at all. (And you don't waste any space doing this.)

All of these are useful in their own right! But check this out:

```C
typedef struct { char *key; } Intern;
static Intern *interns = NULL;

ptrdiff_t intern(char *str)
{
    if (str == NULL) {
        return -1;
    }
    if (interns == NULL) {
        sh_new_arena(interns);
    }
    ptrdiff_t result = shgeti(interns, str);
    if (result == -1) {
        shputs(interns, (Intern) { .key = str });
        result = shlen(interns) - 1;
    }
    return result;
}

char *from_intern(ptrdiff_t handle)
{
    char *result = NULL;
    if (handle >= 0 && handle < shlen(interns)) {
        result = interns[handle].key;
    }
    return result;
}
```

Table entries go into the hash table as just a key, without a corresponding value. To get a value to use as a handle, we use their index in the table's key storage. When we want to turn a handle back into `char *`, we index off the `interns` pointer.

Since pointers to the interned strings are stable, you might want to hand out those pointers directly, instead of handles. On the other hand, pointer-sized handles are somewhat big on 64-bit systems, so there you might want to use a smaller handle type. On 64-bit, the above code is a bit worst-of-both-worlds, but I wanted to show the idea as cleanly as possible.[^1]

[^1]: If they're smaller than pointer-sized, handles can overflow. I figure if I post code it should be working code that can be copy-pasted somewhere without blowing up some indeterminate time in the future. Although, I'm not keen on the behaviour it has with null strings and invalid handles. I feel like both of those indicate that bad things are happening, and returning null pointers is just adding fuel to the fire. 

If you're using a version of stb_ds older than v0.65 the above code won't work, as using `shputs` will store the pointer in `key` directly instead of a pointer to the copy it will allocate from the arena. Prior to v0.65, you had to manage the intern pool's memory directly. That's okay, because stb_ds exposes its internal memory arena functionality as part of the API. The idea is the same, just slightly less convenient.

Also, I first call `shgeti` there, but you really ought to be able to get away with just calling `shputs` and calling it a day. If you use pointers instead of handles this works, because `shputs` returns the inserted key. But I'm not convinced you can rely on that for future versions.

And... I think that's it.
