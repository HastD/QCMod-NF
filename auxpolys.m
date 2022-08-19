freeze;

auxpolys:=function(Q);

  // Compute the polynomials r,Delta,s.

  Delta:=Discriminant(Q); 
  r:=Numerator(Delta/GCD(Delta,Derivative(Delta)));

  K := BaseRing(BaseRing(Q));
  Kx<x>:=RationalFunctionField(K);
  Kxy<y>:=PolynomialRing(Kx);
  d:=Degree(Q);
  // Syl is (the transpose of) the Sylvester matrix for f, df/dy
  Syl:=ZeroMatrix(Kx,2*d-1,2*d-1);
  coefs1:=Reverse(Coefficients(Q));
  coefs2:=Reverse(Coefficients(Derivative(Q)));
  for i:=1 to d-1 do
    for j:=1 to d+1 do
      Syl[i,i+j-1]:=coefs1[j];
    end for;
  end for;
  for i:=d to 2*d-1 do
    for j:=1 to d do
      Syl[i,i-d+j]:=coefs2[j];
    end for;
  end for;

  v:=[Kx|];
  for i:=1 to 2*d-2 do
    v[i]:=0;
  end for;
  v[2*d-1]:=Delta; 
  M:=RModule(Kx,2*d-1);
  sol:=Solution(Syl,M!v);
  
  com_fac:=Delta;
  for i:=1 to d do
    com_fac:=GCD(com_fac,Numerator(sol[2*d-i]));
  end for;
  Delta:=Numerator(Delta/com_fac);
  for i:=1 to d do
    sol[2*d-i]:=sol[2*d-i]/com_fac;
  end for; 

  s:=Parent(Q)!0;
  for i:=1 to d do
    s:=s+(BaseRing(Parent(Q))!Numerator(sol[2*d-i]))*(Parent(Q).1)^(i-1);
  end for;

  // (s*Derivative(Q)-Delta)/Q; // test
  
  return BaseRing(Parent(Q))!r,BaseRing(Parent(Q))!Delta,Parent(Q)!s;
end function;

function genus(Q,p)
  // Computes the genus of the smooth projective curve defined by Q
  K := BaseRing(BaseRing(Q));
  if IsCoercible(K, p) then
    p := p*Integers(K);
  end if;
  if not IsPrime(p) then
    genera := [genus(Q, pri[1]) : pri in Factorization(p)];
    assert &and[g eq genera[1] : g in genera];
    return genera[1];
  end if;
  Fp,res:=ResidueClassField(p);
  A2:=AffineSpace(Fp,2);
  Fpxy:=CoordinateRing(A2);
  Qmodp:=Fpxy!0;
  C:=Coefficients(Q);
  for i:=1 to #C do
    D:=Coefficients(C[i]);
    for j:=1 to #D do
        Qmodp+:=res(D[j])*Fpxy.1^(j-1)*Fpxy.2^(i-1);
    end for;
  end for;
  if not IsIrreducible(Qmodp) then
    error "bad prime";
  end if;
  g:=Genus(Curve(A2,Qmodp));
  return g;  
end function;

function smooth(f,p)
  // Is f mod p separable?
  K := BaseRing(f);
  if IsCoercible(K, p) then
    p := p*Integers(K);
  end if;
  if not IsPrime(p) then
    return &and[smooth(f, pri[1]) : pri in Factorization(p)];
  end if;
  Fp,res:=ResidueClassField(p);
  Fpx:=PolynomialRing(Fp);
  fmodp := &+[res(Coefficient(f, i))*Fpx.1^i : i in [0 .. Degree(f)]];
  return (Degree(fmodp) eq Degree(f) and IsSeparable(fmodp));
end function;

log:=function(p,x)
  if x gt 0 then
    return Log(p,x);
  else
    return 0; 
  end if;
end function;

function is_integral(A,p)
  // Is the matrix A p-adically integral?
  K := BaseRing(BaseRing(A));
  if IsCoercible(K, p) then
    p := p*Integers(K);
  end if;
  if not IsPrime(p) then
    return &and[is_integral(A, pri[1]) : pri in Factorization(p)];
  end if;
  A:=A*Denominator(A);
  for i:=1 to NumberOfRows(A) do
    for j:=1 to NumberOfColumns(A) do
      if A[i,j] ne 0 then
        coeffs := Coefficients(Numerator(A[i,j]));
        if K eq Rationals() then
          ChangeUniverse(~coeffs, RationalsAsNumberField());
        end if;
        m:=Minimum([Valuation(x,p) : x in Coefficients(Numerator(A[i,j]))]);
        if m lt 0 then
          return false;
        end if;
      end if;
    end for;
  end for;
  return true; 
end function;


