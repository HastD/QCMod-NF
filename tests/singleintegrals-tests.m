AttachSpec("QCMod.spec");
import "singleintegrals.m": max_prec, frobmatrix, is_bad, local_data, find_bad_point_in_disk, eval_poly_Qp;

printf "Running tests for example curves over rationals...\n";
load "data/quartic-test-data.m";
load "data/short-coleman-test-data.m";

for i := 1 to #test_data_list do
  data := short_coleman_data_list[i];
  test := test_data_list[i];
  test`Winf:=data`Winf;
  test`v := data`p * Integers();

   for j:=1 to #test_data_list[i]`bad_Qppoints do

    P:=test`bad_Qppoints[j];
    badpoint:=find_bad_point_in_disk(P,test);
    
    assert badpoint`x eq test_data_list[i]`vbad_Qppoints[j]`x ; 
    assert badpoint`b eq test_data_list[i]`vbad_Qppoints[j]`b ;
    assert badpoint`inf eq test_data_list[i]`vbad_Qppoints[j]`inf ;
    end for;
end for;

//Add examples for number fields with other curves. 