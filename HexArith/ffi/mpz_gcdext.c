#include <lean/lean.h>
#include <lean/lean_gmp.h>

LEAN_EXPORT lean_object * lean_alloc_mpz(mpz_t);
LEAN_EXPORT void lean_extract_mpz_value(lean_object * o, mpz_t v);

static void lean_int_to_mpz(b_lean_obj_arg value, mpz_t out) {
    if (lean_is_scalar(value)) {
        mpz_set_si(out, lean_scalar_to_int64(value));
    } else {
        lean_extract_mpz_value((lean_object *)value, out);
    }
}

static lean_obj_res lean_mpz_to_nat_obj(mpz_t value) {
    if (mpz_fits_ulong_p(value)) {
        return lean_uint64_to_nat((uint64_t)mpz_get_ui(value));
    }
    return lean_alloc_mpz(value);
}

static lean_obj_res lean_mpz_to_int_obj(mpz_t value) {
    if (mpz_fits_slong_p(value)) {
        return lean_int64_to_int((int64_t)mpz_get_si(value));
    }
    return lean_alloc_mpz(value);
}

LEAN_EXPORT lean_obj_res lean_hex_mpz_gcdext(b_lean_obj_arg a, b_lean_obj_arg b) {
    mpz_t a_z;
    mpz_t b_z;
    mpz_t g_z;
    mpz_t s_z;
    mpz_t t_z;
    lean_object *g;
    lean_object *s;
    lean_object *t;
    lean_object *coeffs;
    lean_object *result;

    mpz_init(a_z);
    mpz_init(b_z);
    mpz_init(g_z);
    mpz_init(s_z);
    mpz_init(t_z);

    lean_int_to_mpz(a, a_z);
    lean_int_to_mpz(b, b_z);
    mpz_gcdext(g_z, s_z, t_z, a_z, b_z);

    g = lean_mpz_to_nat_obj(g_z);
    s = lean_mpz_to_int_obj(s_z);
    t = lean_mpz_to_int_obj(t_z);

    coeffs = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(coeffs, 0, s);
    lean_ctor_set(coeffs, 1, t);

    result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, g);
    lean_ctor_set(result, 1, coeffs);

    mpz_clear(t_z);
    mpz_clear(s_z);
    mpz_clear(g_z);
    mpz_clear(b_z);
    mpz_clear(a_z);
    return result;
}
