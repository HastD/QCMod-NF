AttachSpec("coleman.spec");
import "auxpolys.m" : auxpolys;
load "tests/quartic-test-data.m";

for test in test_data_list do
  Q := test`Q;
  r, Delta, s := auxpolys(Q);
  // check equations
  assert Delta eq Discriminant(Q);
  assert r eq Delta/GCD(Delta, Derivative(Delta));
  assert IsZero((s*Derivative(Q) - Delta) mod Q);
  // check against recorded values
  assert r eq test`r;
  assert Delta eq test`Delta;
  assert s eq test`s;
  printf "auxpolys(Q) gives expected output for Q = %o.\n", Q;
end for;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);
r, Delta, s := auxpolys(Q);
assert Delta eq Discriminant(Q);
assert r eq Delta/GCD(Delta, Derivative(Delta));
assert IsZero((s*Derivative(Q) - Delta) mod Q);
printf "auxpolys(Q) passes sanity checks for Q = %o.\n", Q;

printf "auxpolys.m tests passed.\n";
