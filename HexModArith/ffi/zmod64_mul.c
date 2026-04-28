#include <lean/lean.h>
#include <stdint.h>

LEAN_EXPORT uint64_t lean_hex_zmod64_mul(uint64_t a, uint64_t b, size_t p) {
    return (uint64_t)(((__uint128_t)a * (__uint128_t)b) % ((__uint128_t)p));
}
