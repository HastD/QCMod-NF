AttachSpec("coleman.spec");
import "auxpolys.m": auxpolys, genus, is_integral, log, smooth;
import "coho.m": ord_0_mat, ord_inf_mat, mat_W0, mat_Winf, con_mat, ddx_mat, jordan_inf, jordan_0, ram, basis_coho;
import "froblift.m": frobenius, froblift, getrings;
import "reductions.m": convert_to_Kxzzinvd, reduce_with_fs, red_lists, coho_red_fin, change_basis_b0binf, coho_red_inf, change_basis_binfb0;
import "singleintegrals.m": max_prec, frobmatrix;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
OK := Integers(K);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);

p := 13;
v := Factorization(p*OK)[1][1];
N := 15;

time data := ColemanData(Q, v, N);
