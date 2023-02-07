AttachSpec("coleman.spec");

import "reductions.m": integral_denom, coeffs_denom, reduce_mod_vN, reduce_mod_pN_K_list,
    reduce_mod_pN_K, reduce_mod_pN_Kx, reduce_mod_pN_K_mat, reduce_mod_pN_Ki, reduce_mod_pN_Ki_mat,
    reduce_mod_pN_Kttinv, inv_Ki;

QQ := RationalField();
R<x> := PolynomialRing(QQ);
K<a> := NumberField(x^2 + x + 1);
L<b> := ext< K | ChangeRing(x^3 - x - 1, K) >;
p := 7;
v_QQ := p * Integers(RationalsAsNumberField());
v_K := Factorization(p * Integers(K))[1][1];
N := 10;

// integral_denom tests
assert integral_denom(2) eq 1;
assert integral_denom(1 / 2) eq 2;
assert integral_denom(K!(1/2)) eq 2;
assert integral_denom(a) eq 1;
assert integral_denom(1/a) eq 1;
assert integral_denom(2*a + 1) eq 1;
assert integral_denom(1/(2*a + 1)) eq 3;

// coeffs_denom tests
assert coeffs_denom(1/2 + 1/3 * x + 1/5 * x^3) eq 30;
assert coeffs_denom(Matrix(QQ, 2, 2, [1/2, -1/3, 5/4, 1/6])) eq 12;
assert coeffs_denom([1/(2*a + 1), -a/7]) eq 21;

// reduce_mod_vN tests
red, O := reduce_mod_vN(v_QQ, N);
assert O eq Integers(7^10);
assert red(-1) eq 7^10 - 1;
assert red(7^10) eq 0;
assert red(6*7^9) eq 6*7^9;
red, O := reduce_mod_vN(v_K, N);
assert red(-1) eq 7^10 - 1;
assert red(a) eq 135967276;
assert red(1/a) eq 146507972;

// reduce_mod_pN_K_list tests
assert reduce_mod_pN_K(-1/7, v_QQ, N) eq -1/7;
// TODO: more tests
