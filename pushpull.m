declare verbose LocalHeights, 3;

intrinsic ChangeCoordinatesHyp(f::RngUPolElt) -> RngUPolElt, RngUPolElt
  {input: a monic polynomial of even degree f defining a hyperelliptic curve y^2=f(x)
  outut: two polynomials h, g such that the curve y^2+hy=g is isomorphic to the above}
  assert IsEven(Degree(f));
  require IsSquare(LeadingCoefficient(f)) : "Non-square leading coefficients not yet supported";
  R<x>:=Parent(f);
  _<yy> := PolynomialRing(Parent(f));
  mon := x^(Degree(f) div 2);
  yPrime := yy+mon;
  g := f - R!Evaluate(yPrime^2,0);
  while Degree(g) ge Degree(mon) do
    yPrime +:= LeadingCoefficient(g)*x^(Degree(g)-Degree(mon))/2;
    g := f - R!Evaluate(yPrime^2,0);
  end while;
  h := R!Coefficient(yPrime^2,1);
  return h,g;
end intrinsic;

intrinsic FindEndoMatrix(X::CrvHyp) -> AlgMatElt
    {Tries to return a nontrival endomorphism}
    Per := PeriodMatrix(CurveExtra(X));
    G := GeometricEndomorphismRepresentation(Per, RationalsExtra());
    require #G gt 1 : "Not GL2 type";
    return G[2][1];
end intrinsic;

intrinsic AnyRationalPoint(X::CrvHyp) -> PtHyp
    {Any rational point}
    C, pi := SimplifiedModel(X);
    pts := RationalPoints(C : Bound := 1000);
    finitepts := [(pi^(-1))(pt) : pt in pts | (pi^(-1))(pt)[3] ne 0];
    return Random(finitepts);
end intrinsic;

intrinsic ConstructCorrespondence(Xp::CrvHyp, P0::PtHyp, T::AlgMatElt) -> SeqEnum, Crv
    {Construct the correspondence associated to T}
    vprintf LocalHeights, 1: "Constructing Correspondence.\n";
    _, D := DivisorFromMatrixAmbientSplit(Xp, P0, Xp, P0, T : LowerBound := 1);
    U := Xp`U;
    eqs := DefiningEquations(D);
    R<y2,y1,x2,x1> := Parent(eqs[1]);
    vprintf LocalHeights, 1: "Computing irreducible components.\n";
    comps := IrreducibleComponents(D);
    Zi := [c : c in comps | Dimension(c) gt 0 ];
    swap_Zi := [Scheme(AmbientSpace(Z), [Evaluate(z, [y1, y2, x1, x2]) : z in Equations(Z)]) : Z in Zi];
    Ci := [Curve(Z) : Z in Zi];
    return Ci, U;
end intrinsic;

// intrinsic TraceByGroebnerBasis(pi::MapSch, g::FldFunFracSchElt, C::Crv) -> .
//   {Take the trace of g by pi}

//   require IsProjective((Domain(pi))) and IsProjective((Codomain(pi))): "The map must have projective domain and codomain";
//   degpi := Degree(pi);
//   gnum := Numerator(g);
//   gden := Denominator(g);

//   deqns := DefiningEquations(C);

//   Rz<z, x1, y1, x2, y2> := PolynomialRing(Rationals(), 5);
//   gnum := Evaluate(gnum, [y2, y1, x2, x1]);
//   gden := Evaluate(gden, [y2, y1, x2, x1]);
//   deqns := [ Evaluate(d, [y2, y1, x2, x1]) : d in deqns];

//   I := ideal<Rz | deqns cat [gden*z -gnum]>;  // this is the correspondence and the two curves
//   elimI := EliminationIdeal(I, {x1, y1, z});

//   R1<xx1,yy1> := PolynomialRing(Rationals(),2);
//   R1z<zz> := PolynomialRing(R1);

//   polys := [ Evaluate(zpoly, [zz, xx1, yy1, 0, 0]) : zpoly in Basis(elimI)];
//   sortedbyz := Sort(polys,func<x,y | Degree(x)-Degree(y)>);
//   sortedbyz := [ s : s in sortedbyz |Degree(s) gt 0];
//   zpoly := sortedbyz[1]; //this is the smallest z-degree poly (assert that z-degree divides the degpi)

//   assert degpi mod Degree(zpoly) eq 0;

//   z2coef := Coefficient(zpoly,Degree(zpoly) - 1);
//   lczpoly := Coefficient(zpoly, Degree(zpoly));
//   scalefactor := degpi / Degree(zpoly);
//   tr := scalefactor* (-z2coef/lczpoly);
//   KU<u,v> := FunctionField(Codomain(pi));
//   tr := Evaluate(tr,[u,v]);
//   vprint LocalHeights, 2 : "The trace is", tr;

//   return tr;
// end intrinsic;

intrinsic Trace(pi::MapSch, g::FldFunFracSchElt, C::Crv) -> .
 {}

  require IsProjective((Domain(pi))) and IsProjective((Codomain(pi))): "The map must have projective domain and codomain";
  degpi := Degree(pi);
  norms := [Pushforward(pi,g-a) : a in [0..degpi]];
  //Norm(s-a) = constant term of P(x+a)
  Rx<x>:=PolynomialRing(Rationals());
  M := [[Coefficient((x+i)^j, 0): j in [0 .. degpi]] : i in [0 ..degpi]];
  Minv := Matrix(M)^(-1);
  ans := [&+[row[j]*norms[j] : j in [1..Ncols(Minv)]] : row in Rows(Minv)];
  lc := ans[degpi+1];
  tr :=  -ans[degpi]/lc;
  vprint LocalHeights, 2 : "The trace is", tr;
  return tr;

end intrinsic;


intrinsic EndoAction(Xp::CrvHyp, Ci::SeqEnum, U::Crv, omega::DiffCrvElt) -> DiffCrvElt
    {Act by the corresopndence Ci on omega}
    fp, hp := HyperellipticPolynomials(Xp);
    R<y2,y1,x2,x1> := Parent(Equations(Ci[1])[1]);
    KU := FunctionField(U);
    u := KU.1;
    v := KU.2;
    omega0 := Differential(u)/(2*v + Evaluate(hp,u));  
    Zomegas := [];
    for C in Ci do
        pi1proj := map<ProjectiveClosure(C)-> ProjectiveClosure(U) | [x1,y1,1]>;
        pi2proj := map<ProjectiveClosure(C)-> ProjectiveClosure(U) | [x2,y2,1]>;

        //Z^*(omega) = pi1_*(pi2^*(omega)) = pi1_*(endo) . omega_0
        endo := Pullback(pi2proj, omega)/Pullback(pi1proj, omega0);
        //Zomega := Pushforward(pi1,endo)*omega0;
        tr := Trace(pi1proj, endo, C);
        //tr2 := TraceByGroebnerBasis(pi1proj,endo,C);
        Zomega := tr*omega0;
        Append(~Zomegas, Zomega);
    end for;
    return &+Zomegas; //The sum is the right way to deal with irred. components, right?
end intrinsic;

intrinsic ConstructDifferentials(X ::CrvHyp, Xp ::CrvHyp, rho::MapIsoSch, KUp::FldFunFracSch) -> SeqEnum, SeqEnum
    {Given isomorphic hypereliptic curves X, Xp (under rho:X to Xp), with X of the form y^2 + 0y= fX
     it returns a basis for the second kind differentials on the curve Xp of the form v^2 + hp v = fp by first finding them on X}
    g := Genus(X);
    R := BaseRing(X);
    fp, hp := HyperellipticPolynomials(Xp);
    u := KUp.1;
    v := KUp.2;

    P<t> := PuiseuxSeriesRing(R); //R = Rationals(), x = 1/t parameter
    fX,hX := HyperellipticPolynomials(X);
    assert IsZero(hX);
    sqrtf := Sqrt(Evaluate(fX,1/t));  //y^2 = f(1/t), sqrt(f(1/t)) = y
    //y = v +1/2h

    differentials := [-(1/t^2) * (1/t)^(i-1)/(2*sqrtf) : i in [1..2*g+1]];
    //differentials is basisDR evaluated in u = 1/t

    coeffs := [Coefficient(differentials[i],-1) : i in [1..2*g+1]];
    a := coeffs[g+1];
    vprintf LocalHeights, 1: "The residues of x^idx/(2y) at infinity are %o.\n", coeffs;
    vprintf LocalHeights, 2: "The residue of x^gdx/(2y) is  %o.\n", a;

    // This is the basis of differentials in Xp coming from the canonical basis in X
    holoDiff:=[u^(i-1)*Differential(u)/(2*v + Evaluate(hp,u)) : i in [1..g]];
    nonholoDiff:= [coeffs[i]*u^g*Differential(u)/(2*v + Evaluate(hp,u)) - a*(u^(i-1)*Differential(u)/(2*v + Evaluate(hp,u))) : i in [g+2..2*g+1]];

    basisDR := holoDiff cat nonholoDiff;

    vprintf LocalHeights, 3: "The basis for the non-holomorphic differential forms that we chose is %o.\n", nonholoDiff;

    matrixChange := [[i eq j select 1 else 0 :j in [1..2*g+1]]: i in [1..g]] cat [[0 : j in [1..g]] cat [coeffs[i]] cat [g+j eq i select -a else 0 : j in [2..g+1]] : i in [g+2..2*g+1]];
    return basisDR, coeffs, Matrix(matrixChange);
end intrinsic;

function GetCoefficientDerivative(poly,degree,i)
  if i eq 0 then
    return 0;
  end if;
  return i*Coefficient(poly,degree-(i-1));
end function;

function GetCoefficient(poly,degree,i)
  if degree-i lt 0 then
    return 0;
  end if;
  return Coefficient(poly,degree-i);
end function;

function GetCoefficientSmallPoly(Q,degree,i)
  // We organize the coefficients as C0 + C1x^1+...
  if degree lt i then
    return 0;
  else
    return Coefficient(Q,degree-i);
  end if;
end function;

function BoundDegree(f,D,num)
  return Max(0,Degree(num)-(Degree(f)+Degree(D))+1);
end function;

intrinsic GetMatrix(f::RngUPolElt,D::RngUPolElt,Q::RngUPolElt,num::RngUPolElt,bound::RngIntElt) -> ModMatFldElt
  {}
  // Assume the big polynomial has degree deg (this is deg(num+1) elts)
  // Assume the small polynomial has degree degf (this is degf+1 elts)
  deg := Degree(num);
  degf := Degree(f);
  R := Parent(f);
  PprimeTimes := R!(2*D*f);
  Ptimes := R!(2*Derivative(D)*f-2*(D*Derivative(Q)*f/Q)+D*Derivative(f));
  matrix := [];
  for degree in [0..deg-1] do
    vecDeg := [];
    Append(~vecDeg,GetCoefficient(Ptimes,degree,0));
    for i in [1..degree] do
      Append(~vecDeg,GetCoefficientDerivative(PprimeTimes,degree,i)+GetCoefficient(Ptimes,degree,i));
    end for;
    Append(~vecDeg,GetCoefficientDerivative(PprimeTimes,degree,degree+1));
    // We need to add one more column for P
    vecDeg := vecDeg cat [0:i in [degree+2..deg]];
    Append(~matrix, [vecDeg[i] : i in [1..bound+1]] cat [GetCoefficientSmallPoly(Q,degree,i): i in [0..degf-2]]);
  end for;
  vv := [GetCoefficientDerivative(PprimeTimes,deg,i)+GetCoefficient(Ptimes,deg,i): i in [0..bound]];
  Append(~matrix, vv cat [GetCoefficientSmallPoly(Q,deg,i): i in [0..degf-2]]);
  return Matrix(matrix);
end intrinsic;

intrinsic ReduceInCohomology(omega::DiffCrvElt, X::CrvHyp) -> DiffCrvElt, SeqEnum
  {Given a differential form omega on X, return the reduction in de Rham cohomology as a differential form,
  and as a sequence of coeffcients on the basis elements of de Rham cohomology x^i dx / (2y)}
  f, h := HyperellipticPolynomials(X);
  require h eq 0 : "Must be working on a y^2 = f model";
  Rx<x> := Parent(f);
  U := Curve(omega);
  KUp<u,v>:= FunctionField(U);
  rat := omega/Differential(u); // g(u,v) du, where this is a rational function
  KX<a,b>:= FunctionField(X);
  ratX := KX!rat;
  coefs, mons := CoefficientsAndMonomials(ratX); //A + By
  if #mons eq 2 then
    ratMin := coefs[2]*mons[2] - coefs[1]*mons[1]; // A - By (hyperellpitic involution)
  elif #mons eq 1 and mons[1] ne 1 then
    ratMin := -coefs[1]*mons[1];
  elif #mons eq 0 then
    ratMin := 0;
  else
    ratMin := coefs[1]*mons[1];
  end if;
  gOdd := (1/2)*(ratX - ratMin); // 1/2( A + By (A -By)) = By

//ratX - gOdd = d(stuff)
//y*ratX - gOdd*y = d(stuff)y
//gEven = gOdd* y*2, so
//y*ratX - gEven/2 = d(stuff)y
//ratX - gEven/(2y) = d(stuff)
//then ratX = gEven/(2y) + dstuff

  _, mons := CoefficientsAndMonomials(gOdd);
  gEven := mons[1]*gOdd*2; //this is now a function just in x, By^2

  if Index(Sprint(gEven), "/") eq 0 then
    num := eval ReplaceString(Sprint(gEven),"a","x");
    num := Rx!num;
    den := Rx!1;
  else
    num, den := Explode(Split(Sprint(gEven),"/"));
    num1 := eval num;
    den1 := eval den;
    assert num1/den1 eq gEven;
    textg2 := ReplaceString(Sprint(gEven),"a","x");
    num, den := Explode(Split(textg2,"/"));
    num := eval num;
    den := eval den;
    den := Rx!den;
    num := Rx!num;
  end if;

  if den eq Rx!1 and Degree(num) le Degree(f)-2 then
    coeffsnum := Coefficients(num);
    return omega, coeffsnum cat [0 : i in [ 1..(Degree(f)- 1) - #coeffsnum]];
  end if;

  degNum := Degree(num);
  D := Rx!(den/GCD(f*Derivative(den),den));
  bound := BoundDegree(f,D,num);
  vprintf LocalHeights, 1: "Starting with bound %o.\n", bound;
  matrix := Transpose(GetMatrix(f,D,den,num,bound));
  vec := Vector([Coefficient(num,i) : i in [0..degNum]]);
  solved := false;
  while not solved do
    try
      sol,kernel := Solution(matrix,vec);
      vprintf LocalHeights, 1 : "The dimension of the space of solutions for the reduction is %o.\n", Dimension(kernel);
      solved := true;
    catch e
      bound +:=1;
      matrix := Transpose(GetMatrix(f,D,den,num,bound));
      vprintf LocalHeights, 1: "Increasing bound to %o.\n", bound;
    end try;
  end while;
  P := &+[sol[i]*x^(i-1) : i in [1..bound+1]];
  hh := P*D/den;
  poly := &+[sol[i+bound+1]*x^(i-1) : i in [1..Degree(f)-1]];
  require num/den -( 2*f*Derivative(hh) + hh*Derivative(f) + poly) eq 0 : "Something went wrong computing the reduction.\n";
  P := &+[sol[i]*x^(i-1) : i in [1..bound+1]];
  return &+[sol[i+bound+1]*a^(i-1)/(2*b) : i in [1..Degree(f)-1]]*Differential(b), [sol[i+bound+1] : i in [1..Degree(f)-1]];
end intrinsic;


intrinsic MatrixH1DR(X::CrvHyp, T::AlgMatElt, P0::PtHyp) -> SeqEnum, ModMatFldElt
    {Given X hyperelliptic curve, P0 a point on X in the affine patch away from infinity, and T an endomorphism given as
    the action of T on the tangent space, return the matrix for T acting on H1 de Rham}
    f, h := HyperellipticPolynomials(X);
    g := Genus(X);
    Rx<x> := Parent(f);
    if h ne 0 then error "h must be 0"; end if;
    hp, fp := ChangeCoordinatesHyp(f);
    Xp := HyperellipticCurve(fp,hp);
    vprintf LocalHeights, 1: "Using auxiliary model %o", Xp;
    KXp := FunctionField(Xp);
    _, rho := IsIsomorphic(X,Xp);
    if Pullback(rho,KXp.1) ne Parent(Pullback(rho,KXp.1)).1 then error "The change of coordinates must be u=x"; end if; //TODO FIX ME in some other cases like scaling x by a constant
    P0p := rho(P0);

    Ci, Up := ConstructCorrespondence(Xp, P0p, T);
    KUp := FunctionField(Up);
    u := KUp.1;
    basisDR, coeffsDR, changeOfBasis := ConstructDifferentials(X, Xp, rho, KUp);
    zo := [EndoAction(Xp, Ci, Up, basisDR[i]): i in [1..#basisDR]]; // This requires a y^2+h*y=f(x) model with h not 0
    KX<a,b> := FunctionField(X);
    zoX := [Pullback(rho, KXp!(zo[i]/Differential(u)))*Differential(a) : i in [1 .. #zo]];

    action := [];
    for dd in zoX do
      zomegabar, sol := ReduceInCohomology(dd, X);
      Append(~action,sol);
    end for;
    action := Transpose(Matrix(action));
    return RightInverseMatrix(Transpose(changeOfBasis))*action;
end intrinsic;
