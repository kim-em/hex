#include <lean/lean.h>
#include <stdint.h>

LEAN_EXPORT uint64_t lean_hex_zmod64_mul(b_lean_obj_arg p, uint64_t a, uint64_t b) {
    lean_object* max_word_nat = lean_uint64_to_nat(UINT64_MAX);
    __uint128_t product = (__uint128_t)a * (__uint128_t)b;
    uint64_t result;

    if (lean_nat_lt(max_word_nat, p)) {
        /* The only bounded modulus above UINT64_MAX is 2^64 itself. */
        result = (uint64_t)product;
    } else {
        uint64_t modulus = lean_uint64_of_nat(p);
        result = (uint64_t)(product % modulus);
    }

    lean_dec(max_word_nat);
    return result;
}
