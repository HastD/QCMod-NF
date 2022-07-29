AttachSpec("coleman.spec");
import "coho.m" : mat_W0, mat_Winf;
load "data/short-coleman-test-data.m";

for data in short_coleman_data_list do
  Q := data`Q;
  W0 := mat_W0(Q);
  Winf := mat_Winf(Q);
  // check equations
  // TODO
  // check against recorded values
  assert W0 eq data`W0;
  assert Winf eq data`Winf;
  printf "mat_W0(Q) and mat_Winf(Q) give expected output for Q = %o.\n", Q;
end for;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);

printf "coho.m tests passed.\n";
