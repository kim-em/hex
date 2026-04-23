#include <lean/lean.h>
#include <stdint.h>

#if defined(__x86_64__) && defined(__PCLMUL__)
#include <wmmintrin.h>
#endif

#if defined(__aarch64__) && defined(__ARM_FEATURE_CRYPTO)
#include <arm_neon.h>
#endif

static void hex_portable_clmul(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    uint64_t acc_hi = 0;
    uint64_t acc_lo = 0;
    for (unsigned i = 0; i < 64; ++i) {
        if (((b >> i) & 1u) == 0) {
            continue;
        }
        acc_lo ^= a << i;
        if (i != 0) {
            acc_hi ^= a >> (64 - i);
        }
    }
    *hi = acc_hi;
    *lo = acc_lo;
}

LEAN_EXPORT lean_obj_res lean_hex_clmul_u64(uint64_t a, uint64_t b) {
    uint64_t hi;
    uint64_t lo;

#if defined(__x86_64__) && defined(__PCLMUL__)
    __m128i lhs = _mm_set_epi64x(0, (long long)a);
    __m128i rhs = _mm_set_epi64x(0, (long long)b);
    __m128i prod = _mm_clmulepi64_si128(lhs, rhs, 0x00);
    uint64_t words[2];
    _mm_storeu_si128((__m128i*)words, prod);
    lo = words[0];
    hi = words[1];
#elif defined(__aarch64__) && defined(__ARM_FEATURE_CRYPTO)
    poly128_t prod = vmull_p64((poly64_t)a, (poly64_t)b);
    uint64x2_t words = vreinterpretq_u64_p128(prod);
    lo = vgetq_lane_u64(words, 0);
    hi = vgetq_lane_u64(words, 1);
#else
    hex_portable_clmul(a, b, &hi, &lo);
#endif

    lean_object* result = lean_alloc_ctor(0, 0, 2 * sizeof(uint64_t));
    lean_ctor_set_uint64(result, 0, hi);
    lean_ctor_set_uint64(result, sizeof(uint64_t), lo);
    return result;
}
