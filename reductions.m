freeze;

import "auxpolys.m": log;
import "coho.m": ord_0_mat, ord_inf_mat;

function integral_denom(c)
  // Integer d such that d*c is integral
  _, d := IsIntegral(c);
  return d;
end function;

function coeffs_denom(A)
  // Common denominator of coefficients of polynomial or matrix A
  return LCM([integral_denom(c) : c in Eltseq(A)]);
end function;

function reduce_mod_vN(v, N)
  OK := Order(v);
  K := NumberField(OK);
  if (Degree(K) gt 1) and not IsSplit(v) then
    error "p must split completely in K.";
  end if;
  p := Norm(v);
  OKloc := Localization(OK, v);
  Ov, loc := Completion(OK, v : Precision := N);
  O := IntegerRing(p^N);
  red := map< OKloc -> O | x :-> Integers()!(BaseRing(Ov)!(loc(d*x)/loc(d))) where d := integral_denom(K!x) >;
  return red, O;
end function;

function reduce_mod_pN_K_list(A, v, N)

  // Reduce a list of elements A over K mod p^N, where v|p splits in K

  if IsZero(A) then
    return A;
  end if;
  K := NumberField(Order(v));
  p := Norm(v);
  assert IsPrime(p);
  denom := coeffs_denom(A);
  A := [denom*c : c in A];

  ord, unit := Valuation(denom, p);
  m := p^(N+ord);
  ppow := p^ord;

  red := reduce_mod_vN(v, N+ord);
  unitinv := red(unit)^(-1);
  A_red := [unitinv*red(c) : c in A];
  ChangeUniverse(~A_red, IntegerRing());
  ChangeUniverse(~A_red, K);
  A_red := [c/ppow : c in A_red];
  return A_red;
end function;

function reduce_mod_pN_K(f,v,N)
  // Reduce a number field element f mod p^N, where v|p splits in K
  return reduce_mod_pN_K_list([f], v, N)[1];
end function;

function reduce_mod_pN_Kx(f, v, N)
  // Reduce a polynomial f over K mod p^N, where v|p splits in K
  return Parent(f)!reduce_mod_pN_K_list(Coefficients(f), v, N);
end function;

function reduce_mod_pN_K_mat(A, v, N)
  // Reduce a matrix over a number field K mod p^N, where v|p splits in K
  return Matrix(BaseRing(A), NumberOfRows(A), NumberOfColumns(A), reduce_mod_pN_K_list(Eltseq(A), v, N));
end function;

function reduce_mod_pN_Ki(f, v, N)
  // Reduce coefficients of element of Ki/K mod p^N, where v|p splits in K
  return Parent(f)!reduce_mod_pN_K_list(Eltseq(f), v, N);
end function;

function reduce_mod_pN_Ki_mat(A, v, N)
  // Reduce a matrix over a number field Ki/K mod p^N, where v|p splits in K
  Ki := BaseRing(A);
  C := &cat[Eltseq(x) : x in Eltseq(A)];
  C_red := reduce_mod_pN_K_list(C, v, N);
  A_red := Partition(C_red, Degree(Ki));
  return Matrix(Ki, NumberOfRows(A), NumberOfColumns(A), A_red);
end function;


function reduce_mod_pN_Kttinv(f, v, N)
  // Reduce an element of K[t,t^{-1}] mod p^N, where v|p splits in K
  if f eq 0 then
    return f;
  else
    Kttinv := Parent(f);
    return (Kttinv.1)^(Valuation(f)) * Kttinv!reduce_mod_pN_K_list(Coefficients(f), v, N);
  end if;
end function;


function inv_Ki(f, v, N)

  // Invert an element of Ki mod p^N

  Ki := Parent(f);
  ri := DefiningPolynomial(Ki);

  C := Eltseq(f);  
  val := Minimum([Valuation(c, v) : c in C]);

  N +:= val;
  p := Norm(v);
  f /:= p^(val);

  Fp, res := ResidueClassField(v);
  Fpx<x> := PolynomialRing(Fp);

  rimodp := Fpx![res(c) : c in Coefficients(ri)];

  Fpxmodri<xbar> := quo<Fpx|rimodp>;
  fmodp := Fpxmodri![res(c) : c in Eltseq(f)];

  invmodp := 1/fmodp;
  inv := Ki!ChangeUniverse(Coefficients(invmodp), IntegerRing());

  prec := [];
  while N gt 1 do
    Append(~prec, N);
    N := Ceiling(N/2);
  end while;
  Reverse(~prec);
  
  for i:=1 to #prec do
    inv := reduce_mod_pN_Ki(inv*(2-inv*f), v, prec[i]);
  end for; 
  
  return inv/(p^val);
end function;


function push_to_Ki_mat(A, Ki)
  // Push a matrix to Ki
  coeffs := [Ki!Eltseq(a) : a in Eltseq(A)];
  return Matrix(Ki, NumberOfRows(A), NumberOfColumns(A), coeffs);
end function;


function red_lists(Q,v,N,r,W0,Winf,G0,Ginf,e0,einf,J0,Jinf,T0,Tinf,T0inv,Tinfinv) 

  // Precompute the finite and infinite reduction matrices, that will be used in
  // the cohomological reductions (coho_red_fin and coho_red_inf)

  p := Norm(v);
  assert IsPrime(p);
  d:=Degree(Q);
  W:=Winf*W0^(-1);

  K := BaseRing(r);
  Kx := Parent(r);
  fac := Factorisation(r);
  lc_r := LeadingCoefficient(r);
  rK := Numerator(r/lc_r);

  // Finite reduction matrices

  N0:=Floor(log(p,p*e0*(N-1)));
  Nw:=N+N0; // working precision, check
  
  riseq:=[];
  redlistfinfac:=[**];
  for i:=1 to #fac do
    redlistfinKi:=[];

    ri := Kx!(fac[i][1]);
    ri := reduce_mod_pN_Kx(ri, v, Nw);
    Append(~riseq, ri);
    if Degree(ri) gt 1 then
      Ki<s> := ext<K|ri>; // redefining Ki, same mod p^Nw  
    else
      Ki := K;
      s := -Evaluate(ri, 0); 
    end if;
    
    D := push_to_Ki_mat(J0[i], Ki);
    P := reduce_mod_pN_Ki_mat(push_to_Ki_mat(T0[i], Ki), v, Nw);
    Pinv := reduce_mod_pN_Ki_mat(push_to_Ki_mat(T0inv[i], Ki), v, Nw);

    denom := reduce_mod_pN_Ki(Evaluate(Derivative(rK), s), v, Nw);
    denominv := inv_Ki(denom, v, Nw); 

    for l:=1 to p*(N-1) do
      D -:= IdentityMatrix(Ki, d);  
      mat := Pinv*D^(-1)*P;
      mat := reduce_mod_pN_Ki_mat(mat, v, Nw);
      mat *:= denominv;
      mat := reduce_mod_pN_Ki_mat(mat, v, Nw);
      Append(~redlistfinKi, mat);
    end for;
    Append(~redlistfinfac, redlistfinKi);
  end for;

  rK0:=reduce_mod_pN_Kx(rK, v, Nw);

  L:=[];
  for i:=1 to #J0 do
    fiseq:=[];
    for k:=1 to #J0 do
      if k eq i then
        fiseq[k]:=Kx!1;
      else
        fiseq[k]:=Kx!0;
      end if;   
    end for;
    Append(~L, reduce_mod_pN_Kx(ChineseRemainderTheorem(fiseq, riseq), v, Nw));
  end for;

  redlistfin:=[];
  for l:=1 to p*(N-1) do
    mat:=ZeroMatrix(Kx,d,d);
    for i:=1 to d do
      for j:=1 to d do
        entry:=Kx!0;
        for k:=1 to #J0 do
          entry +:= ((Kx!Eltseq(redlistfinfac[k][l][i,j]))*L[k] mod rK0);
        end for;
        mat[i,j] := reduce_mod_pN_Kx(entry, v, Nw);
      end for;
    end for;
    Append(~redlistfin, mat);
  end for;

  // Infinite reduction matrices

  Ninf:=Floor(log(p,-(ord_inf_mat(W^(-1))+1)*einf));
  Nw:=N+(N0+Ninf); // working precision check

  D := reduce_mod_pN_K_mat(Jinf, v, Nw);
  P := reduce_mod_pN_K_mat(Tinf, v, Nw);
  Pinv := reduce_mod_pN_K_mat(Tinfinv, v, Nw);
  redlistinf := [];
  //"ord_0_mat(W)", ord_0_mat(W); "ord_inf_mat(W)",ord_inf_mat(W); "ord_inf_mat(W^(-1))",ord_inf_mat(W^(-1)); "(-p*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)))", (-p*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)));
  for m:=1 to  (-p*(ord_0_mat(W)+ord_inf_mat(W)+1)-ord_inf_mat(W^(-1)))+100 do // 20/04/20 added 100 for fun
    D -:= IdentityMatrix(K, d);
    mat := Pinv*D^(-1)*P;
    mat := reduce_mod_pN_K_mat(mat, v, Nw);
    Append(~redlistinf, mat);
  end for;

  return redlistfin,redlistinf;

end function;


function convert_to_Kxzzinvd(w,Q)

  // Converts an element of S^d to one of (K[x][z,z^{-1}])^d 

  d:=Degree(Q);
  K := BaseRing(BaseRing(Q));
  Kx<x> := PolynomialRing(K);
  Kxz<z> := LaurentSeriesRing(Kx);
  C:=[];
  for i:=1 to d do
    D,val:=Coefficients(w[i]);
    E:=[];
    for j:=1 to #D do
      E[j]:=(Kx!PolynomialRing(IntegerRing())!D[j]);  
    end for;
    C[i]:=z^(-1)*(Kxz.1)^(val+1)*(Kxz!E); 
  end for;
  
  return C;
end function;


function val_Kxz_d(v)
  // Compute the valuation of an element of (Q[x][z,z^{-1}])^d.  
  return Minimum([Valuation(c) : c in Eltseq(v)]);
end function;


function coho_red_fin(w,Q,v,N,r,G0,red_list_fin)

  // Reduce the 1-form w dx/z w.r.t. the basis [b^0_0,..,b^0_{d-1}] in cohomology 
  // until it has logarithmic poles at all points lying over the zeros of r.

  Kx := Parent(r);
  Kxz<z> := LaurentSeriesRing(Kx);

  d := Degree(Q);
  V := RSpace(Kx, d);
  Kxzd := RSpace(Kxz, d);

  M:=r*G0;

  r:=Kx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r);
  
  f0 := Kxzd!0;

  r := reduce_mod_pN_Kx(r, v, N); 
  for i:=1 to NumberOfRows(M) do 
    for j:=1 to NumberOfColumns(M) do 
      M[i,j] := Parent(M[i,j])!reduce_mod_pN_Kx(Numerator(M[i,j]), v, N); 
    end for;
  end for;

  if IsZero(w) then
    return w,f0;
  end if;

  l0 := -val_Kxz_d(w);
  if l0 le 0 then
    return w,f0;
  end if;

  wcoefs:=[];
  for i:=1 to d do
    vec:=[Kx|];
    for j:=-l0 to 0 do
      vec[j+l0+1]:=Coefficient(w[i],j);  
    end for;
    Append(~wcoefs, vec);
  end for;

  l:=l0;
  while l gt 0 do
    wvec:=V!0;
    for i:=1 to d do
      wvec[i]:=wcoefs[i][-l+l0+1];
    end for;
    red_mat:=red_list_fin[l];
    vvec:=wvec*red_mat;
    for i:=1 to d do
      vvec[i]:=vvec[i] mod r;
    end for;
    for i:=1 to d do
      f0[i] +:= (Kxz!reduce_mod_pN_Kx(vvec[i],v,N))*z^(-l);
    end for;
    mat := Matrix(Kx, d, d, [Kx!Numerator(c) : c in Eltseq(M)]);
    mat := mat/lc_r;
    for i:=1 to d do
      mat[i,i] -:= l*(Kx!Coefficients(Derivative(r)));
    end for;
    uvec:=wvec-vvec*mat; 
    for i:=1 to d do
      uvec[i] := reduce_mod_pN_Kx((uvec[i] div r)-Derivative(vvec[i]), v, N);
    end for;
    for i:=1 to d do
      wcoefs[i][-l+l0+1] -:= wvec[i];
      wcoefs[i][-l+l0+2] +:= uvec[i];
    end for;
    l:=l-1;
  end while;
  
  for i:=1 to d do 
    C:=[];   
    C[1]:=wcoefs[i][l0+1];   
    if w[i] ne 0 then
      for j:=1 to Degree(w[i]) do
        C[j+1]:=Coefficient(w[i],j);  
      end for;
    end if; 
    w[i] := Kxz!C;
  end for;

  return w,f0;
end function;


function eval_pN(f, g, v, N)

  // Evaluate f at g mod p^N.

  if f eq 0 then
    return CoefficientRing(Parent(f))!0;
  end if;

  k:=Ceiling((Degree(f)+1)/4);
  h:=[];
  for i:=0 to k-1 do
    h[i+1]:=CoefficientRing(Parent(f))!Coefficient(f,4*i+3);
    for j:=1 to 3 do
      h[i+1]:=h[i+1]*g+Coefficient(f,4*i+3-j);
    end for;
  end for;
  h[k+1]:=0;

  gpow:=reduce_mod_pN_Kx(g^4,v,N);

  while k gt 1 do
    h_old:=h;
    h:=[];
    k:=Ceiling(k/2);
    for i:=0 to k-1 do
      h[i+1]:=reduce_mod_pN_Kx(h_old[2*i+1]+h_old[2*i+2]*gpow,v,N);  
    end for;
    h[k+1]:=0;
    if k gt 1 then
      gpow:=reduce_mod_pN_Kx(gpow^2,v,N);  
    end if;
  end while;
 
  return h[1];
end function;


function change_basis_b0binf(w,v,N,r,W0,Winf)

  // Change basis from [b^0_0,..b^0_(d-1)] to [b^{inf}_0,..,b^{inf}_{d-1}].

  d:=NumberOfRows(Winf);

  K := BaseRing(r);
  Kx := Parent(r);
  r := Numerator(r/LeadingCoefficient(r));

  Kttinv<t> := LaurentSeriesRing(K);
  Kttinvd := RSpace(Kttinv, d);
  
  W:=Winf*W0^(-1);
  Winv:=W^(-1);
  wnew:=Kttinvd!0;
  for i:=1 to d do
    temp := eval_pN(w[i], r, v, N);
    if temp eq 0 then
      wnew[i] := Kttinv!0;
    else
      wnew[i] := t^(-Degree(temp))*(Kttinv!Reverse(Coefficients(temp)));
    end if;
  end for;
  w:=wnew*Evaluate(Winv,t^(-1));

  return w;
end function;


function coho_red_inf(w,Q,v,N,r,W0,Winf,Ginf,red_list_inf)

  // Reduce the 1-form w dx/z w.r.t. the basis [b^{inf}_0,..,b^{inf}_{d-1}] in cohomology,
  // lowering the pole order at the points lying over the point at infinity.

  d:=Degree(Q);
  degr:=Degree(r);

  K := BaseRing(BaseRing(Q));
  Kx<x> := PolynomialRing(K);
  Kttinv<t> := LaurentSeriesRing(K);
  Kttinvd := RSpace(Kttinv, d);
  Kd := RSpace(K, d);
  Kxxinv<x> := LaurentSeriesRing(K);
  Kxxinvd := RSpace(Kxxinv,d);
  
  finf:=Kxxinvd!0;

  if IsZero(w) then
    return w,finf;
  end if;

  Minf:=r*Ginf;
  
  W:=Winf*W0^(-1);  
  ord0W:=ord_0_mat(W);

  r:=Kx!r;
  lc_r:=LeadingCoefficient(r);
  r:=Numerator(r/lc_r);
  Minf:=Minf/lc_r;

  Minftinv:=Evaluate(Minf,t^(-1));
  rtinv:=Evaluate(r,1/t);

  rtinv := reduce_mod_pN_Kttinv(rtinv, v, N); 
  for i:=1 to NumberOfRows(Minftinv) do 
    for j:=1 to NumberOfColumns(Minftinv) do 
      Minftinv[i,j] := reduce_mod_pN_Kttinv(Minftinv[i,j], v, N); 
    end for; 
  end for; 

  vallist:=[];
  deglist:=[0];
  for i:=1 to d do
    if w[i] ne 0 then
      Append(~vallist,Valuation(w[i]));
      Append(~deglist,Degree(w[i]));
    end if;
  end for;

  valw:=Minimum(vallist);
  degw:=Maximum(deglist);

  wcoefs:=[];
  for i:=1 to d do
    vec:=[K|];
    for j:=valw to degw do
      vec[j-valw+1]:=Coefficient(w[i],j);  
    end for;
    Append(~wcoefs,vec);
  end for;

  m0:=-valw-degr+1;
//  "valw", valw; "degr", degr; "m0", m0; "ord0W", ord0W; "m0+ord0W+1",   m0+ord0W+1; "#red_list_inf ", #red_list_inf ;
  
  m:=m0;

  while m gt -(ord0W+1) do
    wvec:=Kd!0;
    for i:=1 to d do
      wvec[i]:=-wcoefs[i][-m+m0+1];
    end for;
    red_mat:=red_list_inf[m];
    vvec:=wvec*red_mat;
    for i:=1 to d do
      finf[i] +:= reduce_mod_pN_K(vvec[i], v, N)*x^m;
    end for;
    dif:=((Kttinvd!vvec)*t^(-m)*Minftinv)+rtinv*m*t^(1-m)*(Kttinvd!vvec);
    for i:=1 to d do
      difmodpN := reduce_mod_pN_Kttinv(dif[i], v, N);
      C,val:=Coefficients(difmodpN);
      for j:=1 to #C do                           
        wcoefs[i][j+val-1+m0+degr]:=wcoefs[i][j+val-1+m0+degr]-C[j];  
      end for;
      wcoefs[i][-m+m0+1]:=0;
    end for;
    m:=m-1;
  end while;

  for i:=1 to d do
    w[i] := reduce_mod_pN_Kttinv(t^(-m0-degr+1)*(Kttinv!wcoefs[i]), v, N);
  end for;  

  return w,finf,m0;
end function;


function change_basis_binfb0(w,W0,Winf)

  // Change basis from [b^{inf}_0,..,b^{inf}_{d-1}] to [b^0_0,..b^0_(d-1)].

  t:=Parent(w[1]).1;
  K := BaseRing(BaseRing(w));
  Kx := PolynomialRing(K);
  W:=Winf*W0^(-1);
  w:=w*Evaluate(W,t^(-1));
  w:=Evaluate(w,t^(-1));
  for i:=1 to NumberOfColumns(w) do
    temp:=w[1,i];
    if temp ne 0 then
      for j:=Valuation(temp) to -1 do
        temp:=temp-Coefficient(temp,j)*t^j;
      end for;
    end if;
    w[1,i]:=temp;
  end for;
  w:=Evaluate(w,Kx.1);
  return w;
end function;


function reduce_with_fs(dif,Q,v,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map)

    // Reduces the differential dif (given w.r.t. the basis b^0 dx/z) in H^1(U).
    // 
    // returns:
    // --------
    // coefs    : the coefficients of the cohomology class (w.r.t. the given basis of H^1(U))
    // f0,finf,f: the three functions one has to substract the d of, to get from dif to its 
    //            reduction (w.r.t. b^0,b^inf,b^0)

    d:=Degree(Q); 
    degr:=Degree(r);

    dif0:=dif;

    dif,f0:=coho_red_fin(dif,Q,v,Nmax,r,G0,red_list_fin); 
    dif:=change_basis_b0binf(dif,v,Nmax,r,W0,Winf);
    dif,finf,minf:=coho_red_inf(dif,Q,v,Nmax,r,W0,Winf,Ginf,red_list_inf); 
    // minf is the bound on precision loss during reduction above 
    dif:=change_basis_binfb0(dif,W0,Winf);

    W:=Winf*W0^(-1);
    ord0W:=ord_0_mat(W);
    ordinfW:=ord_inf_mat(W);

    T:=[];
    for k:=1 to d do
      for j:=0 to degr-ord0W-ordinfW-2 do
        Append(~T,Coefficient(dif[1,k],j));
      end for;
    end for;

    vec := Vector(T)*quo_map;

    coefs:=[];
    for j:=1 to #basis do
      coefs[j]:=reduce_mod_pN_K(vec[j],v,N);
    end for;

    fend:=Parent(integrals[1])!0;
    for j:=1 to #integrals do
      fend +:= reduce_mod_pN_K(vec[NumberOfColumns(quo_map)-#integrals+j], v, Nmax)*integrals[j];
    end for;

    // Optional test:

    // test_reduce_with_fs(Vector(dif0),Q,v,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map,coefs,f0,finf,f); 

    return coefs,f0,finf,fend,minf; 

end function;
