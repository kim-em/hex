#include <lean/lean.h>
#include <stdint.h>

#if defined(__PCLMUL__) && (defined(__x86_64__) || defined(_M_X64))
#include <immintrin.h>
#endif

#if defined(__ARM_FEATURE_CRYPTO) && (defined(__aarch64__) || defined(_M_ARM64))
#include <arm_neon.h>
#endif

static inline void hex_clmul_portable(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    uint64_t out_hi = 0;
    uint64_t out_lo = 0;
    for (unsigned bit = 0; bit < 64; ++bit) {
        if (((b >> bit) & 1ULL) == 0) {
            continue;
        }
        if (bit == 0) {
            out_lo ^= a;
        } else {
            out_lo ^= a << bit;
            out_hi ^= a >> (64 - bit);
        }
    }
    *hi = out_hi;
    *lo = out_lo;
}

#if defined(__PCLMUL__) && (defined(__x86_64__) || defined(_M_X64))
static inline void hex_clmul_intrinsic(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    __m128i lhs = _mm_set_epi64x(0, (long long)a);
    __m128i rhs = _mm_set_epi64x(0, (long long)b);
    __m128i prod = _mm_clmulepi64_si128(lhs, rhs, 0x00);
    *lo = (uint64_t)_mm_cvtsi128_si64(prod);
    *hi = (uint64_t)_mm_extract_epi64(prod, 1);
}
#elif defined(__ARM_FEATURE_CRYPTO) && (defined(__aarch64__) || defined(_M_ARM64))
static inline void hex_clmul_intrinsic(uint64_t a, uint64_t b, uint64_t* hi, uint64_t* lo) {
    poly64_t lhs = (poly64_t)a;
    poly64_t rhs = (poly64_t)b;
    poly128_t prod = vmull_p64(lhs, rhs);
    *lo = (uint64_t)prod;
    *hi = (uint64_t)(prod >> 64);
}
#endif

LEAN_EXPORT lean_obj_res lean_hex_clmul_u64(uint64_t a, uint64_t b) {
    uint64_t hi;
    uint64_t lo;
#if defined(__PCLMUL__) && (defined(__x86_64__) || defined(_M_X64))
    hex_clmul_intrinsic(a, b, &hi, &lo);
#elif defined(__ARM_FEATURE_CRYPTO) && (defined(__aarch64__) || defined(_M_ARM64))
    hex_clmul_intrinsic(a, b, &hi, &lo);
#else
    hex_clmul_portable(a, b, &hi, &lo);
#endif
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(hi));
    lean_ctor_set(pair, 1, lean_box_uint64(lo));
    return pair;
}
