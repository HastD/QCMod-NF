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
Q := data`Q; g := data`g; r := data`r; W0 := data`W0; basis := data`basis;
bQ_xy := [-1/2*u, -1/2];
FF<y> := function_field(Q);
x := BaseRing(FF).1;
bpt := CommonZeros([x-bQ_xy[1], y-bQ_xy[2]])[1]; // Base point as place on the function field
// TODO: record the values of corresp and hodge_prec so we can actually run these tests
corresp := [];
hodge_prec := [];
printf "Testing Hodge data for Q = %o...\n", Q;
for i := 1 to #test`corresp do
  Z := corresp[i];
  hodge_prec := hodge_prec[i];
  eta, betafil, gammafil, hodge_loss := HodgeData(Q, g, W0, basis, Z, bpt : r:=r, prec:=hodge_prec);
  printf "Built Hodge data for correspondence %o.\n", i;
end for;
// TODO: add tests over number fields

printf "Hodge data tests completed.\n";
