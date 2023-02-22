AttachSpec("QCMod.spec");
import "misc.m": function_field;

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

load "data/NF-example-coleman-data.m";
load "data/NF-example-test-data.m";
Q := data`Q; g := data`g; r := data`r; W0 := data`W0; basis := data`basis;
bpt := test_NF`bpt; // Base point as place on the function field
printf "Testing Hodge data for Q = %o...\n", Q;
correspondences := test_NF`corresp;
hodge_prec := test_NF`hodge_prec;
for l := 1 to #correspondences do
  Z := correspondences[l];
  eta, betafil, gammafil, hodge_loss := HodgeData(Q, g, W0, basis, Z, bpt : r:=r, prec:=hodge_prec);
  assert eta eq test_NF`eta[l];
  assert betafil eq test_NF`betafil[l];
  assert gammafil eq test_NF`gammafil[l];
  assert hodge_loss eq test_NF`hodge_loss[l];
  printf "Test passed for correspondence %o.\n", l;
end for;

printf "Hodge data tests completed.\n";
