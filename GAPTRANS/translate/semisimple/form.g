#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AHom, Append, BaseRing, BlockMatrix, Characteristic,
#  Coefficients, CompanionMatrix, ConjugateTranspose, Degree, Determinant,
#  Diagonal, Discriminants, FrobeniusImage, GF, GL, GModule, Generators,
#  IdentityMatrix, Insert, InvariantQuadraticForms, IsConsistent, IsElementOf,
#  IsEven, IsIrreducible, IsOdd, IsOrthogonalGroup, IsSquare,
#  IsSymplecticGroup, IsTrivial, IsUnitaryGroup, Matrix, MatrixAlgebra,
#  Multiplicity, MyClassicalType, MyIsOrthogonalGroup, MyIsSymplecticGroup,
#  MyIsUnitaryGroup, Nrows, PrimitiveElement, Prune, QuadraticForm,
#  QuadraticSpace, Random, ReciprocalPolynomial, Remove, Reverse, SFC,
#  SemilinearDual, SetToSequence, SpinN, SpinorNorm, StandardHermitianForm,
#  StandardQuadraticForm, SymmetricMatrix, SymplecticForm, Transpose,
#  UnitaryForm, UpperTriangularMatrix, VectorSpace, WittIndex, Zero,
#  ZeroMatrix, mu

#  Defines: CheckSplitOmega, ConjugatePolynomial, DetermineForm, Discriminants,
#  FormForCompanionMatrix, IndicateType, IsElementOf, MyClassicalType,
#  MyIsOrthogonalGroup, MyIsSymplecticGroup, MyIsUnitaryGroup, SFC, SpinN

DeclareGlobalFunction("CheckSplitOmega@");

DeclareGlobalFunction("ConjugatePolynomial@");

DeclareGlobalFunction("DetermineForm@");

DeclareGlobalFunction("FormForCompanionMatrix@");

DeclareGlobalFunction("IndicateType@");

DeclareGlobalFunction("IsElementOf@");

DeclareGlobalFunction("SpinN@");

MyIsSymplecticGroup@:=function(G)
local type;
  if IsBound(G.ClassicalType) then
    type:=G.ClassicalType;
    return type in ["Sp"];
  else
    return IsSymplecticGroup(G);
  fi;
end;

MyIsUnitaryGroup@:=function(G)
local type;
  if IsBound(G.ClassicalType) then
    type:=G.ClassicalType;
    return type in ["SU","GU"];
  else
    return IsUnitaryGroup(G);
  fi;
end;

MyIsOrthogonalGroup@:=function(G)
local Limit,flag,nmr,type;
  if IsBound(G.ClassicalType) then
    type:=G.ClassicalType;
    return type in ["GO","GO+","GO-","SO","SO-","SO+","Omega+","Omega-","Omega"]
     ;
  else
    nmr:=0;
    Limit:=5;
    flag:=false;
    repeat
      flag:=IsOrthogonalGroup(G);
      nmr:=nmr+1;
      
    until flag or nmr > Limit;
    return flag;
  fi;
end;

MyClassicalType@:=function(G)
local flag,type;
  # =v= MULTIASSIGN =v=
  type:=GroupType(G); #TODO: GroupType@(G)
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if type in ["GO+","SO+","Omega+"] then
    return "orthogonalplus";
  fi;
  if type in ["GO-","SO-","Omega-"] then
    return "orthogonalminus";
  fi;
  if type in ["GO","SO","Omega"] then
    return "orthogonalcircle";
  fi;
end;

#   SFC := system for coefficients
#   given a polynomial f, returns a matrix A and a vector v
#   such that the vector w=vA^-1 is the vector of the coefficients
#   of the matrix of the quadratic form preserved by
#   CompanionMatrix (f) as in FormForCompanionMatrix below
SFC@:=function(f)
local A,F,V,a,i,j,m,n,v;
  F:=BaseRing(f);
  n:=Degree(f);
  if f<>ReciprocalPolynomial(f) then
    Error("f is not self-dual");
  fi;
  m:=QuoInt(Degree(f),2);
  a:=Coefficients(f);
  A:=IdentityMatrix(F,m);
  A[1][1]:=2;
  for i in [1..m-1] do
    for j in [1..m-i] do
      A[j][j+i]:=a[i+1];
    od;
  od;
  V:=VectorSpace(F,m);
  v:=Zero(V);
  for i in [1..m] do
    v[i]:=-a[i+1];
  od;
  v[1]:=v[1]*2;
  v[2]:=v[2]-1;
  if IsEvenInt(Size(F)) then
    for j in [0..m-1] do
      A[j+1][1]:=Sum(List([1..m-j],i->a[i]*a[m+i+j]));
    od;
    v[1]:=Sum(List([1..m+1],i->a[i]*a[m+i-1]));
  fi;
  return rec(val1:=A,
    val2:=v);
end;

#   given a form X (diagonal join of standard forms), return
#   the set of discriminants of the forms of odd dimension
#   it is useful in the case "Omega", q odd
Discriminants@:=function(varX)
local F,Vect,i,k,n,t;
  n:=Length(varX);
  F:=BaseRing(varX);
  Vect:=[];
  for i in [1..n] do
    if varX[i][i]<>0 then
      t:=0;
      k:=1;
      while i+k <= n and i-k >= 1 and varX[i-k][i+k]<>0 do
        t:=t+1;
        k:=k+1;
      od;
      Add(Vect,(-1)^t*varX[i][i]/2);
    fi;
  od;
  return Vect;
end;

#   given the element c of the Cartesian product (see end of code "fixed-ss.m"),
#   returns true if its class in SO splits into two classes in Omega
InstallGlobalFunction(CheckSplitOmega@,
function(c,F,L)
local Answer,Discr,ExistsDg,ExistsPm,SplitDg,SplitPm,T,i,setv,v;
  SplitPm:=true;
  SplitDg:=true;
  ExistsDg:=false;
  ExistsPm:=false;
  Discr:=[];
  Answer:=false;
  for i in [1..Size(c)] do
    if L[i][3]=0 then
      ExistsPm:=true;
      T:=List( # {-list:
        [1,1+2..L[i][2]],j->Multiplicity(c[i][5],j));
      if not (T in [Set([0]),Set([1]),Set([0,1])]) then
        SplitPm:=false;
      elif T=Set([0,1]) or T=Set([1]) then
        v:=Discriminants@(c[i][4]);
        setv:=List( # {-list:
          v,x->IsSquare(x*FORCEOne(F)));
        if Size(setv)=2 then
          SplitPm:=false;
        else
          Add(Discr,SetToSequence(setv)[1]);
        fi;
      fi;
    else
      ExistsDg:=true;
      if IsOddInt(c[i][5]) then
        SplitDg:=false;
      fi;
    fi;
  od;
  if Size(Discr)=2 and Discr[1]<>Discr[2] then
    SplitPm:=false;
  fi;
  if SplitPm and SplitDg then
    Answer:=true;
  fi;
  return Answer;
end);

#   return TildeDualPolynomial if unitary eq true, DualPolynomial otherwise
InstallGlobalFunction(ConjugatePolynomial@,
function(unitary) #TODO: This function has to be checked completly. Where is Dualpolynomial coming from?
local DualPolynomial;
DualPolynomial := 0;
if unitary then
    return DualPolynomial; # TODO: TildeDualPolynomial
  else
    return DualPolynomial;
  fi;
end);

#   SpinorNorm is defined in different ways in odd and even char
InstallGlobalFunction(SpinN@,
function(x,Q,p)
local V;
  if IsOddInt(p) then
    V:=QuadraticSpace(Q);
    return SpinorNorm(V,x);
  else
    return SpinorNorm(x,Q);
  fi;
end);

#   returns the orthogonal type of the form B
InstallGlobalFunction(IndicateType@,
function(B)
local F,V,n;
  n:=Length(B);
  F:=BaseRing(B);
  if IsOddInt(n) then
    return "orthogonal";
  fi;
  if IsOddInt(Size(F)) then
    if IsSquare((-1*FORCEOne(F))^(QuoInt(n,2))*DeterminantMat(B)) then
      return "orthogonalplus";
    else
      return "orthogonalminus";
    fi;
  else
    V:=QuadraticSpace(B);
    if WittIndex(V)=QuoInt(n,2) then
      return "orthogonalplus";
    else
      return "orthogonalminus";
    fi;
  fi;
end);

#   given polynomial f and its companion matrix C, return B such that CBC*=B,
#   where B is hermitian, alternating, symmetric or quadratic
InstallGlobalFunction(FormForCompanionMatrix@,
function(f,type)
local 
   A,C,D,varE,F,F0,Gr,M,MA,_,c,d,deg,flag,forgetvar1,h,i,j,l,m,mu,n,q,v,w,x,y;
  C:=CompanionMat(f);
  F:=BaseRing(C);
  n:=Length(C);
  if n=1 then
    return IdentityMatrix(F,1);
  fi;
  if type in ["GU","SU"] then
    Gr:=SubStructure(GL(n,F),C);
    # =v= MULTIASSIGN =v=
    q:=IsSquare(Size(F));
    flag:=q.val1;
    q:=q.val2;
    # =^= MULTIASSIGN =^=
    F0:=GF(q);
    MA:=MatrixAlgebra(F,n);
    w:=PrimitiveElement(F);
    M:=GModule(Gr);
    mu:=GroupHomomorphismByFunction(F,F,
      x->x^q);
    D:=SemilinearDual(M,mu);
    varE:=AHom(M,D);
    d:=0;
    while d=0 do
      x:=Random(varE);
      y:=x+ConjugateTranspose(x,mu);
      d:=DeterminantMat(y);
      if d=0 then
        y:=(w-mu(w))*(x-ConjugateTranspose(x,mu));
        d:=DeterminantMat(y);
      fi;
    od;
  elif type="Sp" then
    c:=[];
    deg:=Length(C);
    h:=QuoInt(deg,2);
    for l in [1..h-1] do
      c[l]:=C[deg][l+1];
      if l > 1 then
        c[l]:=c[l]+Sum(List([1..l-1],j->C[deg][j+1]*c[l-j]));
      fi;
    od;
    Insert(TILDEc,1,1);
    d:=[];
    for i in [1..h] do
      d:=Concatenation(d,c);
      Prune(TILDEc);
    od;
    A:=UpperTriangularMatrix(F,d);
    y:=BlockMatrix(2,2,[0,A,-TransposedMat(A),0]);
  elif IsOddInt(Size(F)) then
    c:=[];
    i:=Length(C);
    h:=QuoInt(i,2);
    c:=[1,C[i][2]];
    if h=1 then
      c:=[1,C[i][2]/2];
    fi;
    if h > 1 then
      c[3]:=C[i][2]*c[2]+C[i][3]-1;
    fi;
    if h > 2 then
      for l in [3..h] do
        c[l+1]:=Sum(List([1..l],j->C[i][j+1]*c[l-j+1]));
      od;
    fi;
    Reversed(TILDEc);
    c:=Concatenation(c,List([1..h-1],v->0));
    d:=[];
    for v in [1..i] do
      d:=Concatenation(c,d);
      Remove(TILDEc,1);
    od;
    y:=SymmetricMatrix(F,d);
  else
    if n=2 then
      y:=MatrixByEntries(F,2,2,[1,C[2][2],0,1]);
    else
      # =v= MULTIASSIGN =v=
      v:=SFC@(f);
      A:=v.val1;
      v:=v.val2;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      w:=SolutionMat(A,v);
      forgetvar1:=w.val1;
      w:=w.val2;
      # =^= MULTIASSIGN =^=
      m:=QuoInt(n,2);
      y:=ZeroMatrix(F,n,n);
      for i in [1..m] do
        for j in [1..m+1-i] do
          y[j][j+m+i-1]:=w[i];
        od;
      od;
      for i in [1..m+1] do
        y[i][i+m-1]:=1;
      od;
    fi;
  fi;
  return y;
end);

#   check if x in G, a group of supplied type preserving
#   sesquilinear form B and quadratic form Q;
#   also decide if the element is in SO or Omega
InstallGlobalFunction(IsElementOf@,
function(G,x,type,B,Q)
local F,IsOmega,e,n,p,special;
  F:=BaseRing(G);
  p:=Characteristic(F);
  n:=Length(x);
  special:=false;
  IsOmega:=false;
  if type="unitary" then
    e:=QuoInt(Degree(F),2);
    if x*B*TransposedMat(FrobeniusImage(x,e))<>B then
      Error("x must be in G");
    fi;
  elif type<>"symplectic" and p=2 then
    if x*B*TransposedMat(x)<>B or Diagonal(x*Q*TransposedMat(x)+Q)<>List([1..n]
       ,i->0) then
      Error("x must be in G");
    fi;
  elif x*B*TransposedMat(x)<>B then
    Error("x must be in G");
  fi;
  #   in orthogonal case, check if G is of special type or Omega type
  if Size(F)<>2 and (type="unitary" or (type<>"symplectic" and type<>"unitary" 
     and p<>2)) then
    special:=ForAll(Generators(G),g->DeterminantMat(g)=1);
  fi;
  if type<>"unitary" and type<>"symplectic" and (special or p=2) then
    IsOmega:=ForAll(Generators(G),g->SpinN@(g,Q,p)=0);
  fi;
  #   check if x is in the special group G
  if special and DeterminantMat(x)<>1 then
    Error("x must be in G");
  fi;
  #  check if x is in the Omega group G
  if IsOmega and SpinN@(x*FORCEOne(GL(n,F)),Q,p)<>0 then
    Error("x must be in G");
  fi;
  return rec(val1:=special,
    val2:=IsOmega);
end);

#   determine form and check that x is in G
InstallGlobalFunction(DetermineForm@,
function(G,x)
local B,F,IsAbelian,IsOmega,Q,_,e,flag,forgetvar1,n,p,q,sgn,special,type;
  lvarIsAbelian:=false;
  F:=BaseRing(G);
  q:=Size(F);
  p:=Characteristic(F);
  n:=Length(x);
  sgn:=1;
  e:=0;
  #   compute form of G
  if MyIsSymplecticGroup@(G) then
    sgn:=(-1)*FORCEOne(F);
    # =v= MULTIASSIGN =v=
    B:=SymplecticForm(G);
    forgetvar1:=B.val1;
    B:=B.val2;
    # =^= MULTIASSIGN =^=
    type:="symplectic";
  elif Degree(G)=1 then
    #   unitary group of dimension 1
    type:="unitary";
    lvarIsAbelian:=true;
    B:=StandardHermitianForm(1,F);
  elif q=4 and Degree(G)=2 and Size(G)=3 then
    #   OmegaPlus (2, 4) treated apart (erroneously recognized by UnitaryForm)
    type:="orthogonalplus";
    Q:=InvariantQuadraticForms(G)[1];
    lvarIsAbelian:=true;
    B:=Q+TransposedMat(Q);
  elif q=9 and Degree(G)=2 and Size(G)=4 then
    #   OmegaPlus (2, 9) treated apart (erroneously recognized by UnitaryForm)
    type:="orthogonalplus";
    Q:=InvariantQuadraticForms(G)[1];
    lvarIsAbelian:=true;
    B:=Q+TransposedMat(Q);
  elif MyIsUnitaryGroup@(G)=true then
    type:="unitary";
    # =v= MULTIASSIGN =v=
    B:=UnitaryForm(G);
    forgetvar1:=B.val1;
    B:=B.val2;
    # =^= MULTIASSIGN =^=
  elif MyIsOrthogonalGroup@(G) then
    type:=MyClassicalType@(G);
    if not IsTrivial(G) and Degree(G)=2 and IsIrreducible(G)=false then
      # =v= MULTIASSIGN =v=
      Q:=FormsReducibleCase@(G,type);
      flag:=Q.val1;
      Q:=Q.val2;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      Q:=QuadraticForm(G);
      flag:=Q.val1;
      Q:=Q.val2;
      # =^= MULTIASSIGN =^=
    fi;
    Assert(1,flag);
    B:=Q+TransposedMat(Q);
  elif Degree(G)=2 and Size(G)=1 then
    #   OmegaPlus (2, 2), OmegaPlus (2, 3)
    type:="orthogonalplus";
    Q:=StandardQuadraticForm(2,F);
    B:=Q+TransposedMat(Q);
    lvarIsAbelian:=true;
  else
    Error("G must be a classical group");
  fi;
  if IsBound(Q) then
    # =v= MULTIASSIGN =v=
    IsOmega:=IsElementOf@(G,x,type,B,Q);
    special:=IsOmega.val1;
    IsOmega:=IsOmega.val2;
    # =^= MULTIASSIGN =^=
    if (special or IsOmega) and Degree(G)=2 then
      lvarIsAbelian:=true;
    fi;
    return rec(val1:=B,
      val2:=type,
      val3:=sgn,
      val4:=special,
      val5:=IsOmega,
      val6:=Q,
      val7:=lvarIsAbelian);
  else
    # =v= MULTIASSIGN =v=
    IsOmega:=IsElementOf@(G,x,type,B,[]);
    special:=IsOmega.val1;
    IsOmega:=IsOmega.val2;
    # =^= MULTIASSIGN =^=
    return rec(val1:=B,
      val2:=type,
      val3:=sgn,
      val4:=special,
      val5:=IsOmega,
      val6:=_,
      val7:=lvarIsAbelian);
  fi;
end);


