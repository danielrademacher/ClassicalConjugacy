#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: CoefficientRing, Degree, Determinant, FactoredOrder,
#  Factorization, GL, GLCentralizerOrder, Gcd, Generators, JordanForm,
#  Multiplicity, Nrows

#  Defines: GLCentralizerOrder, SLCentralizerOrder

DeclareGlobalFunction("GLCentralizerOrder@");

DeclareGlobalFunction("SLCentralizerOrder@");

#   G = GL(n,q) or SL(n,q)
#   compute the factored order of the centralizer of x in G
#   if the JordanForm of x is known, the function can be
#   called with the parameter JF
InstallGlobalFunction(GLCentralizerOrder@,
function(G,x)
local F,JF,S,SLOrder,_,c,d,forgetvar1,forgetvar2,g,i,j,n,q,r;
  JF:=ValueOption("JF");
  if JF=fail then
    JF:=[];
  fi;
  F:=CoefficientRing(G);
  q:=Size(F);
  n:=Length(x);
  if JF=[] then
    # =v= MULTIASSIGN =v=
    c:=JordanForm(x);
    forgetvar1:=c.val1;
    forgetvar2:=c.val2;
    c:=c.val3;
    # =^= MULTIASSIGN =^=
  else
    c:=JF;
  fi;
  #   check if special case holds
  SLOrder:=ForAll(Generators(G),x->DeterminantMat(x)=1);
  S:=List( # {@-list:
    [1..Size(c)],i->c[i]);
  r:=FactoredOrder(GL(Multiplicity(c,S[1]),q^(Degree(c[1][1]))));
  i:=2;
  while i <= Size(S) do
    r:=r*FactoredOrder(GL(Multiplicity(c,S[i]),q^(Degree(S[i][1]))));
    i:=i+1;
  od;
  if SLOrder then
    d:=Gcd(List([1..Size(S)],i->S[i][2]));
    d:=Gcd(d,q-1);
    r:=r/Factorization(q-1);
    r:=r*Factorization(d);
  fi;
  g:=0;
  i:=1;
  while i <= Size(S) do
    j:=i+1;
    g:=g+Degree(S[i][1])*(S[i][2]-1)*Multiplicity(c,S[i])^2;
    while j <= Size(S) and S[i][1]=S[j][1] do
      #  we know that c[i][2] <= c[j][2] for i<j
      g:=g+2*Degree(S[j][1])*S[i][2]*Multiplicity(c,S[i])*Multiplicity(c,S[j]);
      j:=j+1;
    od;
    i:=i+1;
  od;
  g:=Factorization(q^g);
  return r*g;
end);

InstallGlobalFunction(SLCentralizerOrder@,
function(G,x)
local JF;
  JF:=ValueOption("JF");
  if JF=fail then
    JF:=[];
  fi;
  return GLCentralizerOrder@(G,x:JF:=JF);
end);


