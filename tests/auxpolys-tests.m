AttachSpec("coleman.spec");
import "auxpolys.m" : auxpolys, genus, smooth;
load "data/short-coleman-test-data.m";

function auxpoly_assertions(Q, r, Delta, s)
  return (Delta eq Discriminant(Q)) and (r eq Delta/GCD(Delta, Derivative(Delta))) and IsZero((s*Derivative(Q) - Delta) mod Q);
end function;

for data in short_coleman_data_list do
  Q := data`Q;
  r, Delta, s := auxpolys(Q);
  g := genus(Q, data`p);
  assert auxpoly_assertions(Q, r, Delta, s);
  // check against recorded values
  assert r eq data`r;
  assert Delta eq data`Delta;
  assert s eq data`s;
  assert g eq data`g;
  assert smooth(r, p);
  printf "auxpolys functions give expected output for Q = %o, p = %o.\n", Q, data`p;
end for;

assert smooth(x^5 + x + 1, 11);
assert smooth((x^2 + 1)*(x^3 + x + 3), 23);
assert not smooth(x^5 + x + 1, 7);
assert not smooth((x + 1)^2, 13);
assert not smooth((x + 1)^3 + 7*x, 7);

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);
r, Delta, s := auxpolys(Q);
assert auxpoly_assertions(Q, r, Delta, s);
printf "auxpolys(Q) passes assertions for Q = %o.\n", Q;
assert &and[genus(Q, p) eq 3 : p in [2, 5, 7, 11, 13]];

printf "auxpolys.m tests passed.\n";
