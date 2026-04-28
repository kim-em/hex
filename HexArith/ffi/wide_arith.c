#include <lean/lean.h>
#include <stdint.h>

LEAN_EXPORT uint64_t lean_hex_uint64_mul_hi(uint64_t a, uint64_t b) {
    return (uint64_t)(((__uint128_t)a * (__uint128_t)b) >> 64);
}

LEAN_EXPORT lean_obj_res lean_hex_uint64_add_carry(uint64_t a, uint64_t b, uint8_t cin) {
    uint64_t sum;
    uint64_t total;
    uint8_t carry1 = __builtin_add_overflow(a, b, &sum);
    uint8_t carry2 = __builtin_add_overflow(sum, (uint64_t)cin, &total);
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(total));
    lean_ctor_set(pair, 1, lean_box(carry1 | carry2));
    return pair;
}

LEAN_EXPORT lean_obj_res lean_hex_uint64_sub_borrow(uint64_t a, uint64_t b, uint8_t bin) {
    uint64_t diff;
    uint64_t total;
    uint8_t borrow1 = __builtin_sub_overflow(a, b, &diff);
    uint8_t borrow2 = __builtin_sub_overflow(diff, (uint64_t)bin, &total);
    lean_object* pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(total));
    lean_ctor_set(pair, 1, lean_box(borrow1 | borrow2));
    return pair;
}
