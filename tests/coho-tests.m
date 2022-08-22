AttachSpec("coleman.spec");
import "coho.m" : mat_W0, mat_Winf;
load "data/short-coleman-test-data.m";
load "data/quartic-test-data.m";

for i := 1 to #short_coleman_data_list do
  data := short_coleman_data_list[i];
  Q := data`Q;
  W0 := mat_W0(Q);
  Winf := mat_Winf(Q);
  basis := H1Basis(Q, data`p);
  // check equations
  // TODO
  // check against recorded values
  assert W0 eq data`W0;
  assert Winf eq data`Winf;
  assert basis eq test_data_list[i]`h1basis;
  printf "Expected outputs computed for Q = %o.\n", Q;
end for;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);
mat_W0(Q);
mat_Winf(Q);

printf "coho.m tests passed.\n";
