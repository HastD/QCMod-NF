AttachSpec("QCMod.spec");
import "singleintegrals.m": is_bad, xy_coordinates, teichmueller_pt;
import "misc.m": function_field, eval_mat_R;
import "applications.m": Qp_points;

load "data/NF-example-coleman-data.m";
load "data/NF-example-test-data.m";
Q := data`Q;
r := data`r;
v := data`v;
correspondences := test_NF`corresp;

printf "Testing Frobenius structures for Q = %o...\n", Q;
for l := 1 to #correspondences do
  Z := correspondences[l];
  eta := Vector(test_NF`eta[l]);
  Nhodge := test_NF`Nhodge;
  b0pt := test_NF`b0pt;
  G, NG := FrobeniusStructure(data, Z, eta, b0pt : N:=Nhodge);
  G_list := [* *];
  Qppoints := Qp_points(data : Nfactor := 1.5);
  for i := 1 to #Qppoints do
    if is_bad(Qppoints[i], data) then
      G_list[i] := 0;
    else
      P  := teichmueller_pt(Qppoints[i], data); // P is the Teichmueller point in this disk
      pt := [IntegerRing()!c : c in xy_coordinates(P, data)]; // xy-coordinates of P
      G_list[i] := eval_mat_R(G, pt, r, v); // P is finite good, so no precision loss. 
    end if;
  end for;
  assert NG eq test_NF`NG[l];
  assert G_list eq test_NF`G_list[l];
  printf "Test passed for correspondence %o.\n", l;
end for;

printf "Running tests for example curves over rationals...\n";
printf "(Have to recreate Coleman data, so these tests are slower.)\n";
load "data/quartic-test-data.m";
for i := 1 to #test_data_list do
  test := test_data_list[i];
  Q := test`Q;
  r := test`r;
  printf "Testing Frobenius structures for Q = %o...\n", Q;
  data := ColemanData(Q, test`p, test`N : useU:=true, basis0:=test`basis0, basis1:=test`basis1, basis2:=test`basis2);
  for l in [1 .. #test`corresp] do
    Z := test`corresp[l];
    eta := test`eta[l];
    b0pt := test`b0pt[l];
    Nhodge := test`Nhodge[l];
    G, NG := FrobeniusStructure(data, Z, eta, b0pt : N:=Nhodge);
    G_list := [* *];
    Qppoints := test`Qppoints;
    teichpoints := test`teichpoints;
    for j := 1 to #Qppoints do
      if is_bad(Qppoints[j], data) then
        G_list[j] := 0;
      else
        P  := teichpoints[j]; // P is the Teichmueller point in this disk
        pt := [IntegerRing()!c : c in xy_coordinates(P, data)]; // xy-coordinates of P
        G_list[j] := eval_mat_R(G, pt, r, data`v); // P is finite good, so no precision loss. 
      end if;
    end for;
    assert NG eq test`NG[l];
    assert G_list eq test`G_list[l];
    printf "Test passed for correspondence %o.\n", l;
  end for;
end for;

printf "Frobenius structure tests completed.\n";
