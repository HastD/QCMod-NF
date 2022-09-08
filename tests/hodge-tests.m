AttachSpec("QCMod.spec");
load "data/quartic-test-data.m";
load "data/short-coleman-test-data.m";

for i := 1 to #test_data_list do
  test := test_data_list[i];
  Q := test`Q; g := test`g; r := test`r; W0 := test`W0; bpt := test`bpt;
  basis := short_coleman_data_list[i]`basis;
  printf "Testing Hodge data for Q = %o...\n", Q;
  for i in [1 .. #test`corresp] do
    Z := test`corresp[i];
    hodge_prec := test`hodge_prec[i];
    eta, betafil, gammafil, hodge_loss := HodgeData(Q, g, W0, basis, Z, bpt : r:=r, prec:=hodge_prec);
    assert eta eq test`eta[i];
    assert betafil eq test`betafil[i];
    assert gammafil eq test`gammafil[i];
    assert hodge_loss eq test`hodge_loss[i];
    printf "Test passed for correspondence %o.\n", i;
  end for;
end for;

R<t> := PolynomialRing(Rationals());
K<u> := NumberField(t^2 + t + 1);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := y^4 + (u - 1)*y^3*x + (2*u + 2)*y*x^3 + (3*u + 2)*y^3 - 3*u*y*x^2 - u*x^3 - 3*y^2 + 3*u*y*x + 3*u*x^2 - 2*u*y + (-u + 1)*x + (u + 1);
p := 13;
v := Factorization(p*Integers(K))[1][1];
N := 15;
// TODO: add tests over number fields

printf "Hodge data tests completed.\n";
