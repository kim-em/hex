#include <lean/lean.h>

LEAN_EXPORT lean_object* lp_Hex_Hex_pureIntExtGcd___boxed(lean_object*, lean_object*);

LEAN_EXPORT lean_obj_res lean_hex_mpz_gcdext(b_lean_obj_arg a, b_lean_obj_arg b) {
    /*
    FFI entry point for the `mpz_gcdext` attachment.
    Keep runtime behavior aligned with the logical Lean model by
    delegating to the pure reference implementation.
    */
    return lp_Hex_Hex_pureIntExtGcd___boxed(a, b);
}
