AttachSpec("coleman.spec");
import "applications.m": Fp_points, Qp_points;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
OK := Integers(K);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);

p := 13;
v := Factorization(p*OK)[1][1];
N := 15;

data := ColemanData(Q, v, N);
Fppts := Fp_points(data);

Fp, res := ResidueClassField(v);
A2<x, y> := AffineSpace(Fp, 2);
f := &+[&+[res(Coefficient(ci, j))*x^j*y^i : j in [0 .. Degree(ci)]] where ci := Coefficient(Q, i) : i in [0 .. Degree(Q)]];
Xp := Scheme(A2, f);

if #Fppts eq #Points(ProjectiveClosure(Xp)) then
  printf "Confirmed that Fp_points yields correct number of points (%o).\n", #Fppts;
else
  error "Wrong number of Fp_points!\n";
end if;

Qppts := Qp_points(data);
