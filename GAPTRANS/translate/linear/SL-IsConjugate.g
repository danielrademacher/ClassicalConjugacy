#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: CoefficientRing, CompanionMatrix, Degree,
#  Determinant, DiagonalJoin, Eltseq, GL, Gcd, Generic, IntegerRing, Integers,
#  IsDivisibleBy, JordanForm, Log, Matrix, Norm, Nrows, PrimitiveElement,
#  Solution, ZeroMatrix

#  Defines: GLIsConjugate, SLIsConjugate

DeclareGlobalFunction("GLIsConjugate@");

DeclareGlobalFunction("SLIsConjugate@");

#   if x and y are conjugate in GL, then returns true and z in SL
#   such that z^-1*x*z=y, otherwise returns false
InstallGlobalFunction(GLIsConjugate@,
function(G,x,y)
local B,C,Jx,Jy,c,forgetvar3;
  # =v= MULTIASSIGN =v=
  c:=JordanForm(x);
  Jx:=c.val1;
  B:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  forgetvar3:=JordanForm(y);
  Jy:=forgetvar3.val1;
  C:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  if Jx=Jy then
    return rec(val1:=true,
      val2:=(B^-1*C)*FORCEOne(Generic(G)));
  else
    return rec(val1:=false,
      val2:=_);
  fi;
end);

#   if x and y are conjugate in SL, then returns true and z in SL
#   such that z^-1*x*z=y, otherwise returns false
InstallGlobalFunction(SLIsConjugate@,
function(S,x,y)
local 
   A,B,C,varE,F,Form,R,W,varX,Y,_,a,answer,ax,ay,bX,c,d,deg,f,forgetvar1,
   forgetvar3,g,i,j,m,n,s,t,v,w;
  # =v= MULTIASSIGN =v=
  c:=JordanForm(x);
  ax:=c.val1;
  B:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  forgetvar3:=JordanForm(y);
  ay:=forgetvar3.val1;
  C:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  m:=Size(c);
  answer:=false;
  if ax<>ay then
    return rec(val1:=false,
      val2:=_);
  fi;
  F:=CoefficientRing(S);
  n:=Length(x);
  if Size(F)=2 then
    return rec(val1:=true,
      val2:=(B^-1*C)*FORCEOne(GL(n,F)));
  fi;
  d:=Gcd(Gcd(List([1..m],i->c[i][2])),Size(F)-1);
  R:=IntegerRing(Size(F)-1);
  w:=PrimitiveElement(F);
  s:=B^-1*C;
  f:=Log(w,DeterminantMat(s));
  # rewritten select statement
  if d<>Size(F)-1 then
    answer:=IsDivisibleBy(f*FORCEOne(R),d*FORCEOne(R));
  else
    answer:=(f*FORCEOne(R)=0);
  fi;
  if answer then
    #   construct matrix Y commuting with the JordanForm
    #   and such that det Y = det (s)^-1 = w^-f
    Form:=ZeroMatrix(F,0,0);
    for i in [1..m] do
      deg:=Degree(c[i][1]);
      varX:=DirectSumMat(List([1..c[i][2]],j->CompanionMat(c[i][1])));
      for j in [1..deg*(c[i][2]-1)] do
        varX[j][deg+j]:=1;
      od;
      Form:=DirectSumMat(Form,varX);
    od;
    #   Form = modified Jordan Form of X
    # =v= MULTIASSIGN =v=
    forgetvar3:=JordanForm(Form);
    forgetvar1:=forgetvar3.val1;
    bX:=forgetvar3.val2;
    forgetvar3:=forgetvar3.val3;
    # =^= MULTIASSIGN =^=
    A:=MatrixByEntries(R,m,1,List([1..m],i->c[i][2]));
    W:=MatrixByEntries(R,1,1,[-f]);
    v:=SolutionMat(A,W);
    Y:=ZeroMatrix(F,0,0);
    for i in [1..m] do
      varE:=ExtStructure(F,c[i][1]:Optimize:=false);
      # Implicit generator Assg from previous line.
      a:=varE.1;
      t:=PrimitiveElement(varE);
      g:=Log(Norm(t,F),w);
      varX:=CompanionMat(c[i][1]);
      varX:=Sum(List([1..Degree(c[i][1])],j->varX^(j-1)*Eltseq(t,F)[j]));
      varX:=varX^(Int((g*v[1][i])));
      Y:=DirectSumMat(Y,DirectSumMat(List([1..c[i][2]],j->varX)));
    od;
    s:=B^-1*bX*Y*bX^-1*C;
    s:=s*FORCEOne(GL(n,F));
    return rec(val1:=true,
      val2:=s);
  else
    return rec(val1:=answer,
      val2:=_);
  fi;
end);


