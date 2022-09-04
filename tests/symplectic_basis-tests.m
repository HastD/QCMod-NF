AttachSpec("QCMod.spec");
load "data/quartic-test-data.m";

for data in test_data_list do
  h1basis := data`h1basis;
  Q := data`Q;
  K := BaseRing(BaseRing(Q));
  g := data`g;
  r := data`r;
  W0 := data`W0;
  prec := data`cpm_prec;
  standard_sympl_mat := ZeroMatrix(K, 2*g, 2*g);
  for i in [1..g] do
    standard_sympl_mat[i, g+i] := 1;
    standard_sympl_mat[g+i, i] := -1;
  end for;
  cpm1 := CupProductMatrix(h1basis, Q, g, r, W0 : prec := prec, split := true);
  cpm2 := CupProductMatrix(h1basis, Q, g, r, W0 : prec := prec, split := false);
  sympl := SymplecticBasisH1(cpm1);
  new_complementary_basis := [&+[sympl[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
  sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
  // check equations
  assert cpm1 eq cpm2;
  assert CupProductMatrix(sympl_basis, Q, g, r, W0 : prec := prec) eq standard_sympl_mat;
  // check against recorded values
  assert cpm1 eq data`cpm;
  assert sympl eq data`sympl_coeffs;
  printf "Expected outputs computed for Q = %o.\n", Q;
end for;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);
p := 13;
v := Factorization(p*Integers(K))[1][1];
N := 15;
h1basis, g, r, W0 := H1Basis(Q, v);
prec := 2*g;
standard_sympl_mat := ZeroMatrix(K, 2*g, 2*g);
for i in [1..g] do
  standard_sympl_mat[i, g+i] := 1;
  standard_sympl_mat[g+i, i] := -1;
end for;

time cpm1 := CupProductMatrix(h1basis, Q, g, r, W0 : prec := prec, split := true);
sympl1 := SymplecticBasisH1(cpm1);
new_complementary_basis1 := [&+[sympl1[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
sympl_basis1 := [h1basis[i] : i in [1..g]] cat new_complementary_basis1;

time cpm2 := CupProductMatrix(h1basis, Q, g, r, W0 : prec := prec, split := false);
sympl2 := SymplecticBasisH1(cpm2);
new_complementary_basis2 := [&+[sympl2[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
sympl_basis2 := [h1basis[i] : i in [1..g]] cat new_complementary_basis2;

assert CupProductMatrix(sympl_basis1, Q, g, r, W0 : prec := prec, split := true) eq standard_sympl_mat;
assert CupProductMatrix(sympl_basis2, Q, g, r, W0 : prec := prec, split := false) eq standard_sympl_mat;
assert cpm1 eq cpm2;

printf "symplectic_basis.m tests done.\n";
