AttachSpec("QCMod.spec");
load "data/quartic-test-data.m";

for test in test_data_list do
  printf "Building Coleman data for Q = %o...\n", test`Q;
  data := ColemanData(test`Q, test`p, test`N : useU:=true, basis0:=test`basis0, basis1:=test`basis1, basis2:=test`basis2);
  printf "Coleman data built. Testing Hodge data...\n";
  for i in [1 .. #test`corresp] do
    eta, betafil, gammafil, hodge_loss := HodgeData(data, test`corresp[i], test`bpt : prec := test`hodge_prec[i]);
    assert eta eq test`eta[i];
    assert betafil eq test`betafil[i];
    assert gammafil eq test`gammafil[i];
    assert hodge_loss eq test`hodge_loss[i];
    printf "Test passed for correspondence %o.\n", i;
  end for;
end for;
printf "All Hodge data tests passed.\n";
