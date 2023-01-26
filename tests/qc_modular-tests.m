AttachSpec("QCMod.spec");
import "auxpolys.m": auxpolys, log;
import "singleintegrals.m": evalf0, is_bad, local_coord, set_point, tadicprec, teichmueller_pt, xy_coordinates;
import "misc.m": are_congruent, equivariant_splitting, eval_mat_R, eval_Q, FindQpointQp, fun_field, alg_approx_Qp, minprec, minval, minvalp;
import "applications.m": Q_points, Qp_points, roots_with_prec, separate;
import "heights.m": E1_tensor_E2, expand_algebraic_function, frob_equiv_iso, height, parallel_transport, parallel_transport_to_z;

QQ := RationalField();
K<u> := CyclotomicField(3);
P2<X, Y, Z> := ProjectiveSpace(K, 2);
Q_homog := Y^4 + (u - 1)*Y^3*X + (2*u + 2)*Y*X^3 + (3*u + 2)*Y^3*Z - 3*u*Y*X^2*Z - u*X^3*Z
  - 3*Y^2*Z^2 + 3*u*Y*X*Z^2 + 3*u*X^2*Z^2 - 2*u*Y*Z^3 + (-u + 1)*X*Z^3 + (u + 1)*Z^4;
C := Curve(P2, Q_homog);
OK := Integers(K);
Kx<x> := PolynomialRing(K);
Kxy<y> := PolynomialRing(Kx);
Q := Evaluate(Q_homog, [x, y, 1]);

// other example: X_{S_4}(13):
//Q := 4*x^3*y - x^3- 3*x^2*y^2 + 16*x^2*y+ 3*x^2+ 3*x*y^3 - 11*x*y^2+ 9*x*y+x+ 5*y^3+ y^2+ 2*y;

Cpts := [
  [0,1,0], // j = 1728, D = -4
  [u+1,1,0], // j = 287496, D = -16 
  [-u-1,0,1], // j = 1728, D = -4
  [-u-1,1,1], // j = -884736000, D = -43
  [-u-1,u+1,1], // j = 1728, D = -4
  [-u,0,1], // j = -3375, D = -7
  [0,u+1,1], // j = -884736, D = -19
  [u,2*u+2,1], // j = 16581375, D = -28
  [1,u,1], // j = 1728, D = -4
  [(1/2)*(u+2),(1/2)*(u-3),1], // j = (-3238903991430*u - 4786881515880)^3/19^27, non-CM
  [(1/3)*(u+2),(1/3)*(-u-2),1], // j = -147197952000, D = -67
  [-1/2,(-1/2)*u,1], // j = 1728, D = -4
  [-1,(1/7)*(5*u+4),1] // j=-262737412640768000, D = -163
];

known_aff_pts := [[pt[2]/pt[3], pt[1]/pt[3]] : pt in Cpts | not IsZero(pt[3])];

p := 13;
v := Factorization(p*OK)[1][1];
N := 15;

"Constructing symplectic basis of H1...";
h1basis, g, r, W0 := H1Basis(Q, v);
prec := 2*g;
cpm := CupProductMatrix(h1basis, Q, g, r, W0 : prec := prec, split := true);
sympl := SymplecticBasisH1(cpm);
new_complementary_basis := [&+[sympl[i,j]*h1basis[j] : j in [1..2*g]] : i in [1..g]];
sympl_basis := [h1basis[i] : i in [1..g]] cat new_complementary_basis;
basis0 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [1..g]]; // basis of regular differentials
basis1 := [[sympl_basis[i,j] : j in [1..Degree(Q)]] : i in [g+1..2*g]];  // basis of complementary subspace
"Symplectic basis constructed.";

"Constructing Coleman data...";
time data := ColemanData(Q, v, N : useU:=true,  basis0:=basis0, basis1:=basis1);
"Coleman data constructed.";

"Finding points...";
Qpoints := Q_points(data, 100 : known_points:=known_aff_pts);
Qppoints := Qp_points(data : Nfactor := 1.5);

bad_Qppoints := [P : P in Qppoints | is_bad(P, data) and not P`inf];
bad_Qpoints := [P : P in Qpoints | is_bad(P, data) and not P`inf];
bad_Qpindices := [i : i in [1..#Qppoints] | is_bad(Qppoints[i], data) and not Qppoints[i]`inf];

good_Qpoints := [P : P in Qpoints | not is_bad(P, data) and not P`inf];
good_Q_Qp_indices := [FindQpointQp(P,Qppoints) : P in good_Qpoints];
numberofpoints := #Qppoints;

good_coordinates := [xy_coordinates(P,data) : P in good_Qpoints];
good_affine_rat_pts_xy := [[alg_approx_Qp(P[1], v), alg_approx_Qp(P[2], v)] : P in good_coordinates]; 
bad_coordinates := [xy_coordinates(P,data) : P in bad_Qpoints];
bad_affine_rat_pts_xy := [[alg_approx_Qp(P[1], v), alg_approx_Qp(P[2], v)] : P in bad_coordinates]; 

printf "Good affine rational points:\n%o\n\n", good_affine_rat_pts_xy;
printf "Bad affine rational points:\n%o\n\n", bad_affine_rat_pts_xy;

global_base_point_index := 1;
bQ := good_Qpoints[global_base_point_index]; // base point as Qpoint
bQ_xy := good_affine_rat_pts_xy[global_base_point_index];  // xy-coordinates of base point
local_base_point_index := FindQpointQp(bQ,Qppoints);

FF<y>   := fun_field(data);
x := BaseRing(FF).1;
bpt   := CommonZeros([x-bQ_xy[1], y-bQ_xy[2]])[1]; // Base point as place on the function field
printf "Using the base point %o.\n\n", bQ_xy;
good_affine_rat_pts_xy_no_bpt := Remove(good_affine_rat_pts_xy, global_base_point_index); 

ks := Exclude(good_Q_Qp_indices, local_base_point_index);  // indices in Qppoints of good affine 
                                                           // rational points with base point removed

teichpoints := [**]; 
for i := 1 to numberofpoints do
  teichpoints[i] := is_bad(Qppoints[i],data) select 0  else teichmueller_pt(Qppoints[i],data); // No precision loss
end for;

correspondences := [
  Matrix(RationalField(), 6, 6,
  [ 0, -1, 3, 0, -2, 1,
    0, -1, 1, 2, 0, 2,
    0, -1, 1, -1, -2, 0,
    0, 0, -1, 0, 0, 0,
    0, 0, -1, -1, -1, -1,
    1, 1, 0, 3, 1, 1 ]),
  Matrix(RationalField(), 6, 6,
    [ -1, 0, 1, 0, -1, 0,
      2, 1, -3, 1, 0, -2,
      0, 1, 0, 0, 2, 0,
      0, 1, 0, -1, 2, 0,
      -1, 0, 2, 0, 1, 1,
      0, -2, 0, 1, -3, 0 ])
];

Z := correspondences[1];    
printf "Computing Hodge filtration for correspondence %o.\n", 1;
hodge_prec := 5; 
eta,betafil,gammafil,hodge_loss := HodgeData(Q,g,W0,data`basis,Z,bpt : r:=r, prec:=hodge_prec);
printf "eta = %o\nbetafil = %o\ngammafil = %o\n", eta, betafil, gammafil;

Z := correspondences[2];    
printf "Computing Hodge filtration for correspondence %o.\n", 2;
hodge_prec := 5; 
eta,betafil,gammafil,hodge_loss := HodgeData(Q,g,W0,data`basis,Z,bpt : r:=r, prec:=hodge_prec);
printf "eta = %o\nbetafil = %o\ngammafil = %o\n", eta, betafil, gammafil;
