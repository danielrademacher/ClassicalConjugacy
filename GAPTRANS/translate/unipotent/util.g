#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Basis, CoefficientRing, Degree,
#  Determinant, DiagonalJoin, Dimension, Eltseq, FrobeniusImage, GF, Generic,
#  Identity, IsIrreducible, KMatrixSpace, Matrix, MatrixAlgebra, Ncols, Ngens,
#  NormaliseQuadForm, Nrows, NullSpace, NumberOfColumns, NumberOfRows, Parent,
#  PolynomialRing, PrimitiveElement, Sort, SpinorNorm, Transpose, VectorSpace,
#  XGCD, ZeroMatrix

#  Defines: CayleyTransform, CentralisedSpace, ChooseAlpha, FixesForm,
#  FixesQuadraticForm, FixesUnitaryForm, JordanBlock, KernelOfHom,
#  MyCommutatorSpace, MyDiagonalJoin, MyInnerProduct, MyInsert, MyPerpSpace,
#  MySort, MySpinorNorm, NonSquare, NormaliseQuadForm, PerpSpace, Q_value

DeclareGlobalFunction("MySpinorNorm@");

#   building blocks
InstallGlobalFunction(MySpinorNorm@,
function(g,form)
#  /out: assert IsSymmetric (form);
local value;
  # rewritten select statement
  if DeterminantMat(g)=1 and SpinorNorm(g,form+TransposedMat(form))=0 then
    value:=0;
  else
    value:=1;
  fi;
  return value;
end);

NonSquare@:=function(K)
return PrimitiveElement(K);
  #   assert exists(k){ x : x in K | IsSquare (x) eq false};
  #   return k;
end;

ChooseAlpha@:=function(q)
local P,x;
  P:=PolynomialRing(GF(q));
  # Implicit generator Assg from previous line.
  x:=P.1;
  Assert(1,alpha:=ForAny(GF(q),alpha->IsIrreducible(x^2+x+alpha)));
  return alpha;
end;

MySort@:=function(m)
local C,L,varX,Y,i,p;
  varX:=List([1..Size(m)],i->m[i][1]*m[i][2]);
  Y:=[[1..varX[1]]];
  Y:=Concatenation(Y,List([2..Size(varX)],j->List([1..varX[j]]
   ,x->Sum(List([1..j-1],i->varX[i])+x))));
  C:=function(x,y)
  return y[1]-x[1];
  end;

  Sort(TILDEm,C,TILDEp);
  p:=Eltseq(p);
  L:=[];
  for i in [1..Size(p)] do
    L[i]:=Y[p[i]];
  od;
  L:=Concatenation((L));
  return rec(val1:=m,
    val2:=L);
end;

CayleyTransform@:=function(u)
local F,MA,d,u;
  d:=Length(u);
  F:=BaseRing(u);
  MA:=MatrixAlgebra(F,d);
  u:=u*FORCEOne(MA);
  return (u^0-u)*(u^0+u)^-1;
end;

MyCommutatorSpace@:=function(V,U,gens)
return SubStructure(V,Concatenation(List(Basis(U),
    v->List(gens,
      g->v-v*g)));
end;

CentralisedSpace@:=function(g)
local A,F,G,N,a;
  G:=Parent(g);
  F:=CoefficientRing(G);
  A:=MatrixAlgebra(F,Degree(G));
  a:=g*FORCEOne(A);
  N:=NullSpace(a-Identity(A));
  #   vprint Except: "Nullspace has dimension ", Dimension (N);
  return N;
end;

#   write down perp space of U meet Space wrt Form; Form is
#  defined only on Space and not on the full vector space 
PerpSpace@:=function(Form,U,Space)
local F,L,W,d,r;
  W:=Intersection(U,Space);
  F:=BaseRing(U);
  d:=Degree(U);
  r:=DimensionOfMatrixGroup(W);
  L:=List(Basis(W),w->Eltseq(w));
  W:=Concatenation(List([1..d],j->List([1..r],i->L[i][j])))
   *FORCEOne(KMatrixSpace(F,d,r));
  return Intersection(NullSpace(Form*W),Space);
end;

#   perp space for S
MyPerpSpace@:=function(S,form)
local K,L,N,V,W,d,r;
  d:=Length(form);
  K:=BaseRing(Parent(form));
  V:=VectorSpace(K,d,form);
  L:=List(Basis(S),w->Eltseq(w));
  r:=DimensionOfMatrixGroup(S);
  #   if r eq 0 then return sub<V| >; end if;
  W:=Concatenation(List([1..d],j->List([1..r],i->L[i][j])))
   *FORCEOne(KMatrixSpace(K,d,r));
  N:=NullSpace(form*W);
  N:=SubStructure(V,List([1..DimensionOfMatrixGroup(N)],i->N.i));
  return N;
end;

MyInnerProduct@:=function(form,u,v,q)
local F,MA,a,d;
  F:=BaseRing(form);
  d:=Length(form);
  MA:=KMatrixSpace(F,d,1);
  a:=u*form*Eltseq(v)*FORCEOne(MA);
  return a[1];
end;

MyDiagonalJoin@:=function(L)
local A,i;
  if Size(L)=0 then
    return L;
  fi;
  Assert(1,Size(L)<>0);
  A:=L[1];
  for i in [2..Size(L)] do
    A:=DirectSumMat(A,L[i]);
  od;
  return A;
end;

FixesForm@:=function(r,form)
local F,G,d;
  d:=Length(form);
  F:=BaseRing(Parent(form));
  G:=MatrixAlgebra(F,d);
  return r*FORCEOne(G)*form*FORCEOne(G)*TransposedMat(r)*FORCEOne(G)=form;
end;

FixesUnitaryForm@:=function(x,form)
local F,MA,e,x;
  F:=BaseRing(form);
  e:=QuoInt(Degree(F),2);
  MA:=MatrixAlgebra(F,Length(x));
  x:=x*FORCEOne(MA);
  return x*form*TransposedMat(FrobeniusImage(x,e))=form;
end;

#   Convert quadratic form to an upper triangular matrix
NormaliseQuadForm@:=function(form)
local i,j,n,newForm;
  n:=Length(form);
  Assert(1,NumberOfColumns(form)=n);
  newForm:=ZeroMatrix(CoefficientRing(form),n,n);
  for i in [1..n] do
    for j in [i..n] do
      if not i=j then
        newForm[i][j]:=form[i][j]+form[j][i];
      else
        newForm[i][j]:=form[i][j];
      fi;
    od;
  od;
  return newForm;
end;

#   does g preserve quadratic form?
FixesQuadraticForm@:=function(g,form)
local n_form,new_form;
  n_form:=NormaliseQuadForm@(form);
  new_form:=NormaliseQuadForm@(g*form*TransposedMat(g));
  return n_form=new_form;
end;

JordanBlock@:=function(d,q)
local A,M,i;
  M:=MatrixAlgebra(GF(q),d);
  A:=Identity(M);
  for i in [1..d-1] do
    A[i][i+1]:=1;
  od;
  return A;
end;

MyInsert@:=function(M,N,a,b)
local i,j;
  for i in [1..Length(N)] do
    for j in [1..Ncols(N)] do
      M[a[i]][b[j]]:=N[i][j];
    od;
  od;
  return M;
end;

Q_value@:=function(form,v)
local V;
  V:=MatrixByEntries(v)*form*TransposedMat(MatrixByEntries(v));
  return V[1][1];
end;

#   compute kernel of hom from G to cyclic group C
#   images of generators of G in C are listed in image
KernelOfHom@:=function(G,C,image)
local H,K,a,g,n;
  if Size(C)=1 then
    return G;
  fi;
  # =v= MULTIASSIGN =v=
  a:=XGCD(Concatenation(image,[Size(C)]));
  n:=a.val1;
  a:=a.val2;
  # =^= MULTIASSIGN =^=
  g:=Product(List([1..Ngens(G)],i->G.i^a[i]));
  #   generators of kernel as normal subgroup
  H:=List([1..Ngens(G)],i->G.i*g^(QuoInt(-image[i],n)));
  #   add in conjugates to generate kernel as subgroup
  K:=Concatenation([g^(QuoInt(Size(C),n))],Concatenation(List([0..Size(C)-1],
    u->List([1..Size(H)],
      i->H[i]^(g^u))));
  return SubStructure(Generic(G),K);
end;


