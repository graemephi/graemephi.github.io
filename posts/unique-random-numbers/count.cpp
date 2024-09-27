


// cl -O2 /std:c++17 /W4 -Zi -EHsc count.cpp /Fe:count.exe && count.exe
// gcc and clang will be slow without -ltbb


#define NOMINMAX
#include <cstdint>
#include <cstdlib>
#include <cmath>
#include <assert.h>

#include <vector>
#include <algorithm>
#include <execution>
#include <atomic>

#include <immintrin.h>

double Pi = 0x1.921fb54442d18p1;

static uint32_t log2_floor(uint32_t a)
{
    return 31 - _lzcnt_u32(a);
}

static uint32_t log2_ceil(uint32_t a)
{
    return log2_floor(a - 1) + 1;
}

static uint64_t log2_floor64(uint64_t a)
{
    return 63 - _lzcnt_u64(a);
}

static uint64_t log2_ceil64(uint64_t a)
{
    return log2_floor64(a - 1) + 1;
}


struct Stats
{
    double n;
    double min;
    double max;
    double m;
    double s;
};

static void stats_add(Stats *stats, double x)
{
    if (stats->n == 0)
    {
        *stats = { 1, x, x, x, 0 };
    }
    else
    {
        stats->min = std::min(stats->min, x);
        stats->max = std::max(stats->max, x);
        double n = stats->n + 1;
        double m = stats->m;
        double s = stats->s;
        stats->n = n;
        stats->m = m + (x - m) / n;
        stats->s = s + (x - m) * (x - stats->m);
    }
}

static Stats stats_combined(Stats a, Stats b)
{
    Stats result = {};
    if (a.n && b.n) {
        result.n = a.n + b.n;
        result.min = std::min(a.min, b.min);
        result.max = std::max(a.max, b.max);

        double delta = b.m - a.m;
        result.m = ((a.n * a.m) + (b.n * b.m)) / result.n;
        result.s = a.s + b.s + (delta * delta * a.n * b.n) / result.n;
    } else if (a.n) {
        result = a;
    } else if (b.n) {
        result = b;
    }
    return result;
}

static double stats_mean(Stats *stats)
{
    return stats->m;
}

static double stats_std(Stats *stats)
{
    return std::sqrt(stats->s / (stats->n - 1.0));
}

static void stats_test()
{
    /*
    import numpy as np

    a = np.array([1,2,3,4,5])
    print(a.mean())
    print(a.std(ddof=1))
    */
    Stats s = {};
    stats_add(&s, 1.0);
    stats_add(&s, 2.0);
    stats_add(&s, 3.0);
    stats_add(&s, 4.0);
    stats_add(&s, 5.0);
    assert(stats_mean(&s) == 3.0);
    assert(stats_std(&s) == 1.5811388300841898);
}

static uint32_t hash32(uint32_t x)
{
    x ^= x >> 16;
    x *= 0x21f0aaad;
    x ^= x >> 15;
    x *= 0xd35a2d97;
    x ^= x >> 15;
    return x;
}

static uint64_t hash64(uint64_t x)
{
    x ^= x >> 32;
    x *= 0xd6e8feb86659fd93U;
    x ^= x >> 32;
    x *= 0xd6e8feb86659fd93U;
    x ^= x >> 32;
    return x;
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

static uint32_t pcg_hash(uint32_t input)
{
    uint32_t state = input * 747796405u + 2891336453u;
    uint32_t word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
    return (word >> 22u) ^ word;
}

static uint32_t Encrypt(uint32_t index, uint32_t length, uint32_t roundCount, uint32_t seed)
{
	uint32_t halfIndexBits = log2_ceil(length) / 2;
	uint32_t halfIndexBitsMask = (1u << halfIndexBits) - 1u;
	uint32_t left = (index >> halfIndexBits);
	uint32_t right = index & halfIndexBitsMask;

	for (uint32_t i = 0; i < roundCount; ++i)
	{
		uint32_t newLeft = right;
		uint32_t newRight = left ^ (pcg_hash(i ^ right ^ seed) & halfIndexBitsMask);
		left = newLeft;
		right = newRight;
	}

	return (left << halfIndexBits) | right;
}

static uint32_t permute_encrypt(uint32_t index, uint32_t length, uint32_t seed)
{
    uint32_t result = index;
    do {
        result = Encrypt(result, length, 64, seed);
    } while (result >= length);
    return result;
}

static unsigned permute_ak(unsigned i, unsigned l, unsigned p) {
    unsigned w = l - 1;
    w |= w >> 1;
    w |= w >> 2;
    w |= w >> 4;
    w |= w >> 8;
    w |= w >> 16;
    do {
        i ^= p;             i *= 0xe170893d;
        i ^= p >> 16;
        i ^= (i & w) >> 4;
        i ^= p >> 8;        i *= 0x0929eb3f;
        i ^= p >> 23;
        i ^= (i & w) >> 1;  i *= 1 | p >> 27;
                            i *= 0x6935fa69;
        i ^= (i & w) >> 11; i *= 0x74dcb303;
        i ^= (i & w) >> 2;  i *= 0x9e501cc3;
        i ^= (i & w) >> 2;  i *= 0xc860a3df;
        i &= w;
        i ^= i >> 5;
     } while (i >= l);
    return (i + p) % l;
}

#define permute permute

static uint64_t hash_permutation(uint32_t seed, uint32_t size)
{
    uint64_t hash = 0xcbf29ce484222325;
    uint32_t stop = size > 23 ? 23 : size;
    for (uint32_t i = 1; i < stop; i++) {
        uint64_t b = permute(i, size, seed);
        hash ^= b;
        hash *= 0x00000100000001B3;
    }
    
    // xx hash, XXH3_avalanche
    hash = hash ^ (hash >> 37);
    hash *= 0x165667919E3779F9ULL;
    hash = hash ^ (hash >> 32);
    
    // Stick permute(0) in the high bits so we know where it goes in the bloom filter 
    uint32_t b = log2_ceil(size);
    uint32_t shift = (b > 3) ? b : 3;
    return (hash >> shift) + ((uint64_t)permute(0, size, seed) << (64 - shift));
}

static uint64_t permutations_equal(uint32_t seed_a, uint32_t seed_b, uint32_t size)
{
    for (uint32_t i = 0; i < size; i++) {
        if (permute(i, size, seed_a) != permute(i, size, seed_b)) {
            return false;
        }
    }

    return true;
}

static void print_permutation(uint32_t seed, uint32_t size)
{
    printf("%08x: ", (uint32_t)seed);
    for (uint32_t i = 0; i < size; i++) {
        printf("%d ", (uint32_t)permute(i, size, seed));
    }
    printf("| %016zx\n", hash_permutation(seed, size));
}

static double square(double x)
{
    return x * x;
}

struct PermHash
{
    uint32_t seed;
    uint32_t low;
    uint32_t high;
};

struct Map
{
    std::vector<uint32_t> seeds;
    uint64_t mask = 0;
    
    struct
    {
        Stats gets;
        Stats puts;
    } stats;

    void remake(size_t N) 
    { 
        N = N < 256 ? 256 : N;
        N = 1ull << log2_ceil64(N);

        seeds.clear();
        seeds.resize(N);
        
        stats.gets = {};
        stats.puts = {};
        mask = N - 1;
    }

    uint64_t walk(uint64_t hash, uint32_t step)
    {
        int32_t half_step = step >> 1;
        int32_t sign = -(int32_t)(step & 1);
        uint64_t walked = hash + (uint64_t)(half_step ^ sign);
        return walked & mask;
    }

    void put(uint64_t hash, uint32_t seed)
    {
        assert(hash);
        assert(~hash);

        uint32_t step = 0;
        uint64_t walked = walk(hash, 0);
        while (seeds[walked]) {
            step++;
            assert(step < seeds.size());
            walked = walk(hash, step);
        }

        seeds[walked] = seed;
        stats_add(&stats.puts, step);
    }

    struct GetResult
    {
        uint32_t valid;
        uint32_t seed;
        uint32_t next;
    };

    GetResult get(uint64_t hash, uint32_t step)
    {
        GetResult result = {};

        uint64_t walked = walk(hash, step);
        uint32_t seed = seeds[walked];
        if (seed) {
            result.valid = true;
            result.seed = seed;
            result.next = step + 1;
        }

        stats_add(&stats.gets, step);
        return result;
    }
};

// Stuff for testing Map

struct TestPermutation
{
    uint32_t seed;
    uint32_t len;
    bool operator==(const TestPermutation other) const
    {
        if (len != other.len) {
            return false;
        }

        if (seed != other.seed) {
            for (uint32_t i = 0; i < len; i++) {
                if (permute(i, len, seed) != permute(i, len, other.seed)) {
                    return false;
                }
            }
        }

        return true;
    }
};

template<>
struct std::hash<TestPermutation>
{
    size_t operator()(const TestPermutation& permutation) const noexcept
    {
        return (size_t)hash_permutation(permutation.seed, permutation.len);
    }
};

struct TestResult
{
    size_t n_repeats;
    size_t n_unique;
    std::vector<uint32_t> seeds;
};

#include <unordered_map>
TestResult test_permutations(uint32_t permutation_size, size_t sample_size)
{
    std::unordered_map<TestPermutation, uint32_t> permutations;
    for (uint32_t i = 0; i < sample_size; i++) {
        permutations[{ i, permutation_size }] += 1;
    }

    size_t n_repeats = 0;
    std::vector<uint32_t> seeds;
    for (auto [permutation, count] : permutations) {
        n_repeats += count - 1;
        if (count > 1) {
            seeds.push_back(permutation.seed);
        }
    }
    
    std::sort(seeds.begin(), seeds.end());
    return { n_repeats, seeds.size(), seeds };
}

//

void repeats()
{
    printf("%-2s%20s%20s%20s%20s%20s%20s%20s%20s\n", "N", "samples", "dupes", "expected", "unique_dupes", "p", "bloom hits log2", "put walks", "get walks");
    
    std::vector<uint64_t> bloom;
    std::vector<Map> maps(23);    
    for (uint32_t permutation_size = 3; permutation_size < 23; permutation_size++) {
        double n_permutations = std::tgamma((double)permutation_size + 1.0);
        
        double factor = sqrt(2.0*20); 
        double sample_size = std::ceil(factor * std::sqrt(n_permutations));
        if (sample_size > UINT32_MAX) {
            sample_size = UINT32_MAX;
        }
        
        // Not accurate: more than k bits are set and the hashes are biased so really its multiple bloom filters
        double false_positive_rate = 0x1p-8;

        double expected = sample_size - n_permutations * -expm1(sample_size*log1p(-1/n_permutations));
        uint32_t N = (uint32_t)sample_size; 
        size_t k = (size_t)std::ceil(-log(false_positive_rate) / log(2.0));
        size_t m_bits = (size_t)(-(double)N * log(false_positive_rate) / square(log(2)));
        size_t m_log2 = log2_ceil64(m_bits / 64);

        if (m_log2 < 6) {
            m_log2 = 6;
        }

        size_t m = 1ull << m_log2;
        size_t m_mask = m - 1;

        bloom.clear();
        bloom.resize(m); 

        for (size_t i = 0; i < permutation_size; i++) {
            double shrinkage = sqrt(1.0 / permutation_size);
            maps[i].remake((size_t)(4.0 * false_positive_rate * sample_size * shrinkage));
        }

        struct Dupes
        {
            size_t n_possible_dupes;
            Stats chains;
            std::vector<uint32_t> seeds;
        };

        std::vector<Dupes> dupes(permutation_size);
        std::for_each(std::execution::par_unseq, dupes.begin(), dupes.end(), [&](Dupes& s) {
            uint32_t p = (uint32_t)(&s - &dupes[0]);

            size_t n_possible_dupes = 0;
            for (uint32_t i = 0; i < N; i++) {
                if (permute(0, permutation_size, i) == p) {
                    uint64_t h = hash_permutation(i, permutation_size);
                    uint64_t h_hi = h >> 32;
                    
                    bool possible_dupe = true;
                    uint64_t hx = h;
                    uint64_t idx = (h >> (64 - m_log2));
                    for (size_t hash_index = 0; hash_index < k/2 + (k&1); hash_index++) {
                        hx ^= (h_hi * hash_index);
                        uint64_t pattern = (1ull << (hx & 63))
                                         | (1ull << ((hx >> 6) & 63))
                                         | (1ull << ((hx >> 12) & 63));
                        hx ^= hx >> 5;
                        
                        idx = (idx & ~7) + ((idx + hash_index) & 7);
                        idx &= m_mask;

                        possible_dupe = possible_dupe && ((bloom[idx] & pattern) == pattern);
                        bloom[idx] |= pattern;
                    }
                    
                    if (possible_dupe) {
                        n_possible_dupes++;
                        maps[p].put(h, i);
                    }
                }
            }

            dupes[p].n_possible_dupes = n_possible_dupes;
        });

        std::for_each(std::execution::par_unseq, dupes.begin(), dupes.end(), [&](Dupes& d) {
            size_t p = (size_t)(&d - &dupes[0]);

            for (uint32_t i = 0; i < N; i++) {
                if (permute(0, permutation_size, i) == p) {
                    uint64_t h = hash_permutation(i, permutation_size);

                    double chain_length = 0;
                    Map::GetResult got = maps[p].get(h, 0);
                    while (got.valid) {
                        if ((i != got.seed) && permutations_equal(i, got.seed, permutation_size)) {
                            d.seeds.push_back(i);
                            d.seeds.push_back(got.seed);
                        }
                        got = maps[p].get(h, got.next);
                        chain_length += 1.0;
                    }
                    if (chain_length) {
                        stats_add(&d.chains, chain_length);
                    }
                    if (d.seeds.size() > 100) {
                        break;
                    }
                }
            }
        });

        size_t n_possible_dupes = 0;
        std::vector<uint32_t> seeds;
        Stats chains = {};
        Stats gets = {};
        Stats puts = {};
        for (size_t p = 0; p < permutation_size; p++)  {
            Dupes *d = &dupes[p];
            for (auto s : d->seeds) {
                bool is_new = true;
                for (size_t i = 0; i < seeds.size(); i++) {
                    if (seeds[i] == s) {
                        is_new = false;
                        break;
                    }
                }
                if (is_new) {
                    seeds.push_back(s);
                }    
            }

            chains = stats_combined(chains, d->chains);
            n_possible_dupes += d->n_possible_dupes;
            gets = stats_combined(gets, maps[p].stats.gets);
            puts = stats_combined(puts, maps[p].stats.puts);
        }

        size_t n_repeats = 0;
        std::vector<uint32_t> unique_seeds;
        for (size_t i = 0; i < seeds.size(); i++) {
            // print_permutation(seeds[i], permutation_size);
            bool hit = false;
            for (size_t j = i + 1; j < seeds.size(); j++) {
                if (seeds[i] == seeds[j]) {
                    break;
                }
                if (permutations_equal(seeds[i], seeds[j], permutation_size)) {
                    seeds[j] = seeds[i];
                    n_repeats++;
                    if (!hit) {
                        unique_seeds.push_back(seeds[i]);
                        hit = true;
                    }
                }
            }
        }

        size_t n_unique = unique_seeds.size();

        // From ME O'Neill https://www.pcg-random.org/posts/birthday-test.html
        double p = 0.0;
        for (size_t r = 0; r <= n_repeats; ++r) {
            double pdf_value = exp(log(expected)*r - expected - lgamma(1.0+r));
            p += pdf_value;
            if (p > 0.5)
                p = p - 1;
        }

        printf("%-2d%20.0f%20zd%20.2f%20zd%20.2f%20.2f%20.2f%20.2f\n", permutation_size, sample_size, n_repeats, expected, n_unique, p < 0 ? 1.0 + p : p, std::log2(n_possible_dupes), stats_mean(&puts), stats_mean(&chains));

        if (permutation_size < 14)
        {
            TestResult test = test_permutations(permutation_size, N);
            assert(test.n_repeats == n_repeats);
            assert(test.n_unique == n_unique);
            std::sort(unique_seeds.begin(), unique_seeds.end());
            for (size_t i = 0; i < unique_seeds.size(); i++) {
                assert(unique_seeds[i] == test.seeds[i]);
            }
        }
    }
}

int main()
{
    stats_test();
    repeats();    
}

/*
N              samples               dupes            expected        unique_dupes                   p     bloom hits log2           put walks           get walks
3                   16                  10               10.32                   4                0.54                3.32                0.90                2.71
4                   31                  14               13.42                   8                0.63                3.81                0.71                2.18
5                   70                  19               16.80                  16                0.75                4.25                0.16                1.31
6                  170                  21               18.49                  18                0.76                4.39                0.14                1.21
7                  449                  18               19.38                  18                0.44                4.17                0.00                1.00
8                 1270                  16               19.78                  16                0.24                4.17                0.00                1.00
9                 3810                  13               19.93                  13                0.07                4.46                0.00                1.00
10               12048                  14               19.98                  14                0.11                4.58                0.00                1.00
11               39959                  19               19.99                  19                0.47                7.70                0.05                1.19
12              138420                  19               20.00                  19                0.47                7.67                0.00                1.02
13              499080                  20               20.00                  20                0.56                7.95                0.00                1.01
14             1867387                  16               20.00                  16                0.22                8.37                0.00                1.00
15             7232357                  19               20.00                  19                0.47                9.36                0.00                1.00
16            28929425                  19               20.00                  19                0.47               10.70                0.00                1.00
17           119279073                  12               20.00                  12                0.04               18.73                0.03                1.08
18           506058246                  20               20.00                  20                0.56               20.83                0.03                1.08
19          2205856754                  26               20.00                  26                0.92               23.21                0.03                1.10
20          4294967295                   5                3.79                   5                0.82               23.54                0.02                1.06
21          4294967295                   1                0.18                   1                0.99               23.13                0.01                1.04
22          4294967295                   0                0.01                   0                0.99               22.73                0.01                1.03
*/
