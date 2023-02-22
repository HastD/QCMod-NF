AttachSpec("QCMod.spec");
import "singleintegrals.m": is_bad, xy_coordinates, teichmueller_pt, tadicprec;
import "misc.m": function_field, eval_mat_R, minprec, minval;
import "applications.m": Qp_points;
import "heights.m": frob_equiv_iso, expand_algebraic_function;

load "data/NF-example-coleman-data.m";
load "data/NF-example-test-data.m";
Q := data`Q;
g := data`g;
r := data`r;
bQ := test_NF`bQ;
b0 := teichmueller_pt(bQ, data);
correspondences := test_NF`corresp;

Qppoints := Qp_points(data : Nfactor := 1.5);
numberofpoints := #Qppoints;
teichpoints := [**]; 
for i := 1 to numberofpoints do
  teichpoints[i] := is_bad(Qppoints[i],data) select 0  else teichmueller_pt(Qppoints[i],data); // No precision loss
end for;

prec := test_NF`tadicprec;

printf "Testing parallel transport for Q = %o...\n", Q;
for l := 1 to #correspondences do
  Z := correspondences[l];
  eta := Vector(test_NF`eta[l]);
  gammafil := test_NF`gammafil[l];
  Nhodge := test_NF`Nhodge[l];
  Ncurrent := Min(Nhodge, test_NF`NG[l]);
  G_list := test_NF`G_list[l];

  PhiAZb_to_b0, Nptb0 := ParallelTransport(bQ,b0,Z,eta,data:prec:=prec,N:=Nhodge);
  for i := 1 to 2*g do
    PhiAZb_to_b0[2*g+2,i+1] := -PhiAZb_to_b0[2*g+2,i+1];
  end for;

  assert PhiAZb_to_b0 eq test_NF`PhiAZb_to_b0[l];

  PhiAZb := [**]; // Frobenius on the phi-modules A_Z(b,P) (0 if P bad)

  Ncurrent := Min(Ncurrent, Nptb0);
  Nfrob_equiv_iso := Ncurrent;
  minvalPhiAZbs := [0 : i in [1..numberofpoints]];
  for i := 1 to numberofpoints do

    if G_list[i] eq 0 then
      PhiAZb[i] := 0;
    else 
      pti, Npti := ParallelTransport(teichpoints[i],Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge);
      isoi, Nisoi := frob_equiv_iso(G_list[i],data,Ncurrent);
      MNi := Npti lt Nisoi select Parent(pti) else Parent(isoi);
      PhiAZb[i] := MNi!(pti*PhiAZb_to_b0*isoi);
      Nfrob_equiv_iso := Min(Nfrob_equiv_iso, minprec(PhiAZb[i]));
      minvalPhiAZbs[i] := minval(PhiAZb[i]);
    end if;
    assert PhiAZb[i] eq test_NF`PhiAZb[l][i];
  end for;
  Ncurrent := Nfrob_equiv_iso;

  PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
  for i := 1 to numberofpoints do
    PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
      ParallelTransportToZ(Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge)*PhiAZb[i];
    assert PhiAZb_to_z[i] eq (eval test_NF`PhiAZb_to_z[l][i]);
  end for;

  gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 
  for i := 1 to numberofpoints do
    if G_list[i] ne 0 then
      gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, Nhodge, prec);
    end if;
    assert gammafil_listb_to_z[i] eq Parent(gammafil_listb_to_z[i])!test_NF`gammafil_listb_to_z[l][i];
  end for;
  printf "Test passed for correspondence %o.\n", l;
end for;

printf "Running tests for example curves over rationals...\n";
load "data/quartic-test-data.m";
load "data/short-coleman-test-data.m";
for k := 1 to #test_data_list do
  data := short_coleman_data_list[k];
  test := test_data_list[k];
  Q := data`Q;
  g := data`g;
  r := data`r;
  data`v := data`p * Integers();
  bQ := test`bQ;
  b0 := teichmueller_pt(bQ, data);
  correspondences := test`corresp;

  Qppoints := test`Qppoints;
  numberofpoints := #Qppoints;
  teichpoints := test`teichpoints;
  prec := test`tadicprec;

  printf "Testing parallel transport for Q = %o...\n", Q;
  for l := 1 to #correspondences do
    Z := correspondences[l];
    eta := Vector(test`eta[l]);
    gammafil := test`gammafil[l];
    Nhodge := test`Nhodge[l];
    Ncurrent := Min(Nhodge, test`NG[l]);
    G_list := test`G_list[l];

    PhiAZb_to_b0, Nptb0 := ParallelTransport(bQ,b0,Z,eta,data:prec:=prec,N:=Nhodge);
    for i := 1 to 2*g do
      PhiAZb_to_b0[2*g+2,i+1] := -PhiAZb_to_b0[2*g+2,i+1];
    end for;

    assert PhiAZb_to_b0 eq test`PhiAZb_to_b0[l];

    PhiAZb := [**]; // Frobenius on the phi-modules A_Z(b,P) (0 if P bad)

    Ncurrent := Min(Ncurrent, Nptb0);
    Nfrob_equiv_iso := Ncurrent;
    minvalPhiAZbs := [0 : i in [1..numberofpoints]];
    for i := 1 to numberofpoints do

      if G_list[i] eq 0 then
        PhiAZb[i] := 0;
      else 
        pti, Npti := ParallelTransport(teichpoints[i],Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge);
        isoi, Nisoi := frob_equiv_iso(G_list[i],data,Ncurrent);
        MNi := Npti lt Nisoi select Parent(pti) else Parent(isoi);
        PhiAZb[i] := MNi!(pti*PhiAZb_to_b0*isoi);
        Nfrob_equiv_iso := Min(Nfrob_equiv_iso, minprec(PhiAZb[i]));
        minvalPhiAZbs[i] := minval(PhiAZb[i]);
      end if;
      assert PhiAZb[i] eq test`PhiAZb[l][i];
    end for;
    Ncurrent := Nfrob_equiv_iso;

    PhiAZb_to_z := [**]; // Frobenius on the phi-modules A_Z(b,z) for z in residue disk of P (0 if P bad)
    for i := 1 to numberofpoints do
      PhiAZb_to_z[i] := G_list[i] eq 0 select 0 else
        ParallelTransportToZ(Qppoints[i],Z,eta,data:prec:=prec,N:=Nhodge)*PhiAZb[i];
      assert PhiAZb_to_z[i] eq (eval test`PhiAZb_to_z[l][i]);
    end for;

    gammafil_listb_to_z := [* 0 : k in [1..numberofpoints] *]; // evaluations of gammafil at local coordinates for all points 
    for i := 1 to numberofpoints do
      if G_list[i] ne 0 then
        gammafil_listb_to_z[i] := expand_algebraic_function(Qppoints[i], gammafil, data, Nhodge, prec);
      end if;
      assert gammafil_listb_to_z[i] eq Parent(gammafil_listb_to_z[i])!test`gammafil_listb_to_z[l][i];
    end for;
    printf "Test passed for correspondence %o.\n", l;
  end for;
end for;

printf "Parallel transport tests completed.\n";
