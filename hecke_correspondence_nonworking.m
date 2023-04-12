{\rtf1\ansi\ansicpg1252\cocoartf2639
\cocoatextscaling0\cocoaplatform0{\fonttbl\f0\fnil\fcharset0 Menlo-Regular;}
{\colortbl;\red255\green255\blue255;\red202\green202\blue202;\red23\green23\blue23;\red89\green138\blue67;
\red194\green126\blue101;\red212\green214\blue154;\red140\green211\blue254;\red167\green197\blue152;\red183\green111\blue179;
\red238\green46\blue56;\red70\green137\blue204;\red205\green173\blue106;}
{\*\expandedcolortbl;;\cssrgb\c83137\c83137\c83137;\cssrgb\c11765\c11765\c11765;\cssrgb\c41569\c60000\c33333;
\cssrgb\c80784\c56863\c47059;\cssrgb\c86275\c86275\c66667;\cssrgb\c61176\c86275\c99608;\cssrgb\c70980\c80784\c65882;\cssrgb\c77255\c52549\c75294;
\cssrgb\c95686\c27843\c27843;\cssrgb\c33725\c61176\c83922;\cssrgb\c84314\c72941\c49020;}
\margl1440\margr1440\vieww28600\viewh17520\viewkind0
\deftab720
\pard\pardeftab720\partightenfactor0

\f0\fs24 \cf2 \cb3 \expnd0\expndtw0\kerning0
\outl0\strokewidth0 \strokec2 freeze;\cb1 \
\
\pard\pardeftab720\partightenfactor0
\cf4 \cb3 \strokec4 //////////////////////////////////////////////////\cf2 \cb1 \strokec2 \
\cf4 \cb3 \strokec4 // Function for computing Hecke correspondence  //\cf2 \cb1 \strokec2 \
\cf4 \cb3 \strokec4 //////////////////////////////////////////////////\cf2 \cb1 \strokec2 \
\
\pard\pardeftab720\partightenfactor0
\cf2 \cb3 import \cf5 \strokec5 "misc.m"\cf2 \strokec2 : algdepQp,lindepQp;\cb1 \
\
\cb3 intrinsic \cf6 \strokec6 HeckeCorrespondenceQC\cf2 \strokec2 (data::Rec, q::RngIntElt, N::RngIntElt :\cb1 \
\cb3                                 basis0:=[], basis1:=[], use_polys:=[])\cb1 \
\cb3   -> \cf7 \strokec7 SeqEnum\cf2 \strokec2 [AlgMatElt], AlgMatElt, RngIntElt\cb1 \
\cb3   \{For i=\cf8 \strokec8 1\cf2 \strokec2 ,...,g-\cf8 \strokec8 1\cf2 \strokec2 , construct a nice correspondence Zi from the ith power of\cb1 \
\cb3   the Hecke operator Aq using Eichler-Shimura. \cb1 \
\cb3   N is the precision \cf9 \strokec9 for\cf2 \strokec2  the q-adic computation. \cb1 \
\cb3   \cb1 \
\cb3   Both Aq^i and Zi are encoded as matrices representing their action on H^\cf10 \strokec10 1_dR\cf2 \strokec2 (X)\cb1 \
\cb3   \cb1 \
\cb3   If basis0 and basis1 are given, we assume that they form a symplectic basis\cb1 \
\cb3   of H^\cf10 \strokec10 1_dR\cf2 \strokec2 (X). \cf7 \strokec7 If\cf2 \strokec2  they are not given, such a basis is computed along the way.\cb1 \
\cb3   \cf9 \strokec9 if\cf2 \strokec2  a list of rational polynomials [f1,...,fd] is given \cf11 \strokec11 in\cf2 \strokec2  use_polys, then the Zi returned will be \cf8 \strokec8 2\cf2 \strokec2 *g*\cf6 \strokec6 fi\cf2 \strokec2 (Tq)-\cf6 \strokec6 Trace\cf2 \strokec2 (\cf6 \strokec6 fi\cf2 \strokec2 (Tq)).\}\cb1 \
\
\cb3   Q:=data`Q; g:=data`g; d:=\cf6 \strokec6 Degree\cf2 \strokec2 (Q); p:=data`p; \cb1 \
\cb3   K:=\cf6 \strokec6 BaseRing\cf2 \strokec2 (\cf6 \strokec6 BaseRing\cf2 \strokec2 (Q));\cb1 \
\cb3   C:=\cf6 \strokec6 ZeroMatrix\cf2 \strokec2 (K,\cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 ,\cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 );\cb1 \
\cb3   \cf9 \strokec9 for\cf2 \strokec2  i:=\cf8 \strokec8 1\cf2 \strokec2  to g \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3     \cf7 \strokec7 C\cf2 \strokec2 [i,g+i]:=\cf8 \strokec8 1\cf2 \strokec2 ;\cb1 \
\cb3     \cf7 \strokec7 C\cf2 \strokec2 [g+i,i]:=-\cf8 \strokec8 1\cf2 \strokec2 ; \cb1 \
\cb3   end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\
\cb3   \cf9 \strokec9 if\cf2 \strokec2  basis0 ne [] then\cb1 \
\cb3     v0:=\cf6 \strokec6 Minimum\cf2 \strokec2 (&\cf7 \strokec7 cat\cf2 \strokec2 [[\cf6 \strokec6 Valuation\cf2 \strokec2 (coef,q):coef \cf11 \strokec11 in\cf2 \strokec2  &\cf7 \strokec7 cat\cf2 \strokec2 [\cf6 \strokec6 Coefficients\cf2 \strokec2 (\cf7 \strokec7 basis0\cf2 \strokec2 [i][j]):j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..d\cf2 \strokec2 ]]]: i \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..g\cf2 \strokec2 ]]); \cf4 \strokec4 // valuation basis0\cf2 \cb1 \strokec2 \
\cb3   \cf9 \strokec9 else\cf2 \cb1 \strokec2 \
\cb3     v0:=\cf8 \strokec8 0\cf2 \strokec2 ;\cb1 \
\cb3   end \cf9 \strokec9 if\cf2 \strokec2 ;\cb1 \
\
\cb3   \cf9 \strokec9 if\cf2 \strokec2  basis1 ne [] then\cb1 \
\cb3     v1:=\cf6 \strokec6 Minimum\cf2 \strokec2 (&\cf7 \strokec7 cat\cf2 \strokec2 [[\cf6 \strokec6 Valuation\cf2 \strokec2 (coef,q):coef \cf11 \strokec11 in\cf2 \strokec2  &\cf7 \strokec7 cat\cf2 \strokec2 [\cf6 \strokec6 Coefficients\cf2 \strokec2 (\cf7 \strokec7 basis1\cf2 \strokec2 [i][j]):j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..d\cf2 \strokec2 ]]]: i \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..g\cf2 \strokec2 ]]); \cf4 \strokec4 // valuation basis1\cf2 \cb1 \strokec2 \
\cb3   \cf9 \strokec9 else\cf2 \cb1 \strokec2 \
\cb3     v1:=\cf8 \strokec8 0\cf2 \strokec2 ;\cb1 \
\cb3   end \cf9 \strokec9 if\cf2 \strokec2 ;\cb1 \
\
\cb3   v:=\cf6 \strokec6 Minimum\cf2 \strokec2 ([v0,v1]);\cb1 \
\
\cb3   \cf4 \strokec4 // multiply by constant to remove denominator in basis0 and basis1\cf2 \cb1 \strokec2 \
\cb3   \cf9 \strokec9 if\cf2 \strokec2  v lt \cf8 \strokec8 0\cf2 \strokec2  then\cb1 \
\cb3     \cf9 \strokec9 for\cf2 \strokec2  i:=\cf8 \strokec8 1\cf2 \strokec2  to g \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3       \cf9 \strokec9 for\cf2 \strokec2  j:=\cf8 \strokec8 1\cf2 \strokec2  to d \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3         \cf7 \strokec7 basis0\cf2 \strokec2 [i][j]:=q^(-v)*\cf7 \strokec7 basis0\cf2 \strokec2 [i][j];\cb1 \
\cb3         \cf7 \strokec7 basis1\cf2 \strokec2 [i][j]:=q^(-v)*\cf7 \strokec7 basis1\cf2 \strokec2 [i][j];\cb1 \
\cb3       end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3     end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3   end \cf9 \strokec9 if\cf2 \strokec2 ;\cb1 \
\
\cb3   \cf9 \strokec9 if\cf2 \strokec2  q ne p then \cb1 \
\cb3     vprintf QCMod: \cf5 \strokec5 "\cf12 \strokec12 \\n\cf5 \strokec5 Compute Coleman data wrt q=\cf7 \strokec7 %o\cf12 \strokec12 \\n\cf5 \strokec5 "\cf2 \strokec2 , q;\cb1 \
\cb3     data:=\cf6 \strokec6 ColemanData\cf2 \strokec2 (Q,q,N:basis0:=basis0,basis1:=basis1);\cb1 \
\cb3   end \cf9 \strokec9 if\cf2 \strokec2 ;\cb1 \
\
\cb3   F := data`F;\cb1 \
\cb3   \cf9 \strokec9 if\cf2 \strokec2  q eq p then F := \cf6 \strokec6 Submatrix\cf2 \strokec2 (data`F,\cf8 \strokec8 1\cf2 \strokec2 ,\cf8 \strokec8 1\cf2 \strokec2 ,\cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 ,\cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 ); end \cf9 \strokec9 if\cf2 \strokec2 ;\cf4 \strokec4 // Necessary when q=p\cf2 \cb1 \strokec2 \
\cb3   Finv := \cf6 \strokec6 Transpose\cf2 \strokec2 (F)^(-\cf8 \strokec8 1\cf2 \strokec2 );\cb1 \
\cb3   Aq := \cf6 \strokec6 Transpose\cf2 \strokec2 (F)+q*Finv;   \cf4 \strokec4 // Eichler-Shimura -> Hecke operator\cf2 \cb1 \strokec2 \
\cb3   prec_loss_bd := \cf6 \strokec6 Valuation\cf2 \strokec2 (\cf6 \strokec6 Determinant\cf2 \strokec2 (Finv), p);\cb1 \
\cb3   prec_loss_bd +:= q eq p select \cf8 \strokec8 1\cf2 \strokec2  \cf9 \strokec9 else\cf2 \strokec2  \cf8 \strokec8 0\cf2 \strokec2 ;\cb1 \
\
\cb3   Zs:=[]; As:=[];\cb1 \
\cb3   AK := \cf6 \strokec6 ZeroMatrix\cf2 \strokec2 (K, \cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 , \cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 ); ZK := AK;\cb1 \
\
\cb3   \cf9 \strokec9 if\cf2 \strokec2  #use_polys eq \cf8 \strokec8 0\cf2 \strokec2  then\cb1 \
\
\cb3     \cf9 \strokec9 for\cf2 \strokec2  i \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..g\cf2 \strokec2 -\cf8 \strokec8 1\cf2 \strokec2 ] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3       A := Aq^i; \cf4 \strokec4 // ith power of hecke operator\cf2 \cb1 \strokec2 \
\cb3       Zmx := (\cf8 \strokec8 2\cf2 \strokec2 *g*A-\cf6 \strokec6 Trace\cf2 \strokec2 (A)*\cf6 \strokec6 IdentityMatrix\cf2 \strokec2 (K,\cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 ))*C^(-\cf8 \strokec8 1\cf2 \strokec2 );  \cb1 \
\cb3       \cf4 \strokec4 // Zmx is a q-adic approximation of a nice correspondence Z\cf2 \cb1 \strokec2 \
\cb3       \cf4 \strokec4 // Now clear denominators to find A and Z exactly\cf2 \cb1 \strokec2 \
\cb3       D1 := \cf6 \strokec6 LCM\cf2 \strokec2 ([\cf6 \strokec6 LCM\cf2 \strokec2 ([\cf6 \strokec6 Denominator\cf2 \strokec2 (\cf7 \strokec7 Zmx\cf2 \strokec2 [j,k]):k \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g]]):j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g]]);\cb1 \
\cb3       D2 := \cf6 \strokec6 LCM\cf2 \strokec2 ([\cf6 \strokec6 LCM\cf2 \strokec2 ([\cf6 \strokec6 Denominator\cf2 \strokec2 (\cf7 \strokec7 A\cf2 \strokec2 [j,k]):k \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g]]):j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g]]);\cb1 \
\cb3       D := \cf6 \strokec6 LCM\cf2 \strokec2 (D1,D2);\cb1 \
\cb3       A *:= D;\cb1 \
\cb3       Zmx *:= D;\cb1 \
\cb3       \cf9 \strokec9 for\cf2 \strokec2  j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3         \cf9 \strokec9 for\cf2 \strokec2  k \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3           \cf7 \strokec7 AQ\cf2 \strokec2 [j,k] := \cf6 \strokec6 lindepQp\cf2 \strokec2 (\cf6 \strokec6 pAdicField\cf2 \strokec2 (q, N-\cf8 \strokec8 1\cf2 \strokec2 )!\cf7 \strokec7 A\cf2 \strokec2 [j,k]);    \cf4 \strokec4 // recognition of integer in Zp via LLL\cf2 \cb1 \strokec2 \
\cb3           \cf7 \strokec7 ZQ\cf2 \strokec2 [j,k] := \cf6 \strokec6 lindepQp\cf2 \strokec2 (\cf6 \strokec6 pAdicField\cf2 \strokec2 (q, N-\cf8 \strokec8 1\cf2 \strokec2 )!\cf7 \strokec7 Zmx\cf2 \strokec2 [j,k]);  \cf4 \strokec4 // dito\cf2 \cb1 \strokec2 \
\cb3         end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3       end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3       \cf9 \strokec9 if\cf2 \strokec2  \cf6 \strokec6 Trace\cf2 \strokec2 (ZQ*\cf7 \strokec7 C\cf2 \strokec2 ) ne \cf8 \strokec8 0\cf2 \strokec2  then \cf4 \strokec4 // approximation issue. Perturbe ZQ slightly.\cf2 \cb1 \strokec2 \
\cb3         \cf9 \strokec9 if\cf2 \strokec2  q ne p then \cb1 \
\cb3           error \cf5 \strokec5 "q-adic approximation of nice correspondence not exact."\cf2 \strokec2 ;  \cb1 \
\cb3         end \cf9 \strokec9 if\cf2 \strokec2 ;\cb1 \
\cb3           \cb1 \
\cb3         W:=\cf6 \strokec6 ZeroMatrix\cf2 \strokec2 (K,\cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 , \cf8 \strokec8 2\cf2 \strokec2 *\cf7 \strokec7 g\cf2 \strokec2 );\cb1 \
\cb3         \cf7 \strokec7 W\cf2 \strokec2 [\cf8 \strokec8 1\cf2 \strokec2 ,g+\cf8 \strokec8 1\cf2 \strokec2 ]:=\cf6 \strokec6 Trace\cf2 \strokec2 (ZK*\cf7 \strokec7 C\cf2 \strokec2 );\cb1 \
\cb3         \cf7 \strokec7 W\cf2 \strokec2 [g+\cf8 \strokec8 1\cf2 \strokec2 ,\cf8 \strokec8 1\cf2 \strokec2 ]:=-\cf6 \strokec6 Trace\cf2 \strokec2 (ZK*\cf7 \strokec7 C\cf2 \strokec2 );\cb1 \
\cb3         ZK:=\cf8 \strokec8 2\cf2 \strokec2 *ZK+W;\cb1 \
\cb3       end \cf9 \strokec9 if\cf2 \strokec2 ;\cb1 \
\cb3       \cf6 \strokec6 Append\cf2 \strokec2 (~Zs,ZK);\cb1 \
\cb3       \cf6 \strokec6 Append\cf2 \strokec2 (~As,AK);\cb1 \
\cb3     end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3   \cf9 \strokec9 else\cf2 \cb1 \strokec2 \
\cb3     \cf9 \strokec9 for\cf2 \strokec2  i \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..g\cf2 \strokec2 -\cf8 \strokec8 1\cf2 \strokec2 ] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3       AK := \cf6 \strokec6 ChangeRing\cf2 \strokec2 (\cf6 \strokec6 ChangeRing\cf2 \strokec2 (Aq,\cf6 \strokec6 pAdicRing\cf2 \strokec2 (p,N))^i,K); \cf4 \strokec4 // ith power of hecke operator\cf2 \cb1 \strokec2 \
\cb3       \cf6 \strokec6 Append\cf2 \strokec2 (~As,AK);\cb1 \
\cb3     end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\
\cb3     A0:=\cf6 \strokec6 ChangeRing\cf2 \strokec2 (\cf6 \strokec6 Evaluate\cf2 \strokec2 (\cf7 \strokec7 use_polys\cf2 \strokec2 [\cf8 \strokec8 1\cf2 \strokec2 ],\cf6 \strokec6 ChangeRing\cf2 \strokec2 (\cf7 \strokec7 As\cf2 \strokec2 [\cf8 \strokec8 1\cf2 \strokec2 ],\cf6 \strokec6 pAdicRing\cf2 \strokec2 (p,N))),K);\cb1 \
\cb3     \cf9 \strokec9 for\cf2 \strokec2  i \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 2..\cf2 \strokec2 #use_polys] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3       A :=\cf6 \strokec6 ChangeRing\cf2 \strokec2 (\cf6 \strokec6 Evaluate\cf2 \strokec2 (\cf7 \strokec7 use_polys\cf2 \strokec2 [i],\cf6 \strokec6 ChangeRing\cf2 \strokec2 (\cf7 \strokec7 As\cf2 \strokec2 [\cf8 \strokec8 1\cf2 \strokec2 ],\cf6 \strokec6 pAdicRing\cf2 \strokec2 (p,N))),K); \cb1 \
\cb3       ZK := (\cf6 \strokec6 Trace\cf2 \strokec2 (A0)*A-\cf6 \strokec6 Trace\cf2 \strokec2 (A)*A0)*C^(-\cf8 \strokec8 1\cf2 \strokec2 );  \cb1 \
\cb3       \cf6 \strokec6 Append\cf2 \strokec2 (~Zs,ZK);\cb1 \
\cb3     end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\
\cb3     A:=Aq;\cb1 \
\cb3     D := \cf6 \strokec6 LCM\cf2 \strokec2 ([\cf6 \strokec6 LCM\cf2 \strokec2 ([\cf6 \strokec6 Denominator\cf2 \strokec2 (\cf7 \strokec7 Aq\cf2 \strokec2 [j,k]):k \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g]]):j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g]]);\cb1 \
\cb3     A *:= D;\cb1 \
\cb3     \cf9 \strokec9 for\cf2 \strokec2  j \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3       \cf9 \strokec9 for\cf2 \strokec2  k \cf11 \strokec11 in\cf2 \strokec2  [\cf10 \strokec10 1..2\cf2 \strokec2 *g] \cf9 \strokec9 do\cf2 \cb1 \strokec2 \
\cb3         \cf7 \strokec7 A\cf2 \strokec2 [j,k] := \cf6 \strokec6 lindepQp\cf2 \strokec2 (\cf6 \strokec6 pAdicField\cf2 \strokec2 (q, N-\cf8 \strokec8 1\cf2 \strokec2 )!\cf7 \strokec7 A\cf2 \strokec2 [j,k]);    \cf4 \strokec4 // recognition of integer in Zp via LLL\cf2 \cb1 \strokec2 \
\cb3       end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3     end \cf9 \strokec9 for\cf2 \strokec2 ;\cb1 \
\cb3     As:=[A];\cb1 \
\
\cb3   end \cf9 \strokec9 if\cf2 \strokec2 ; \cf4 \strokec4 // #use_polys eq 0 \cf2 \cb1 \strokec2 \
\
\cb3   \cf9 \strokec9 return\cf2 \strokec2  Zs, \cf7 \strokec7 As\cf2 \strokec2 [\cf8 \strokec8 1\cf2 \strokec2 ], prec_loss_bd;\cb1 \
\cb3 end intrinsic;\cb1 \
\
\
\
\
}