#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BlockMatrix, CoefficientRing,
#  CompanionMatrix, Degree, Determinant, DiagonalJoin, GL, Gcd, Generators,
#  Generic, IdentityMatrix, Include, InsertBlock, IntegerRing, Integers,
#  IsConsistent, JordanForm, Log, Matrix, Max, Min, Multiplicity, Ngens, Norm,
#  Nrows, PresOrder, PrimitiveElement, SL, ScalarMatrix

#  Defines: PresOrder, SLCentralizer

DeclareGlobalFunction("SLCentralizer@");

#   returns the smallest k such that (m+k(q-1),q^r-1)=(m,q-1)
PresOrder@:=function(q,r,m)
local g,k;
  g:=Gcd(q-1,m);
  k:=0;
  while Gcd(m+k*(q-1),q^r-1)<>g do
    k:=k+1;
  od;
  return m+k*(q-1);
end;

#   x is an element of S = SL(d, q); determine its centraliser
InstallGlobalFunction(SLCentralizer@,
function(S,x)
local 
   A,B,C,varE,F,Gen,Gr,H,K,R,T,_,a,array,b,c,forgetvar1,forgetvar2,forgetvar3,
   gl,h,i,j,k,li,lj,m,mat,mu,n,order,pos,r,t,u,w,zero;
  gl:=Generic(S);
  if ForAny(Generators(S),s->DeterminantMat(s)<>1) then
    Error("Group is not SL");
  fi;
  if DeterminantMat(x)<>1 then
    Error("Element does not have determinant 1");
  fi;
  F:=CoefficientRing(S);
  n:=Length(x);
  # =v= MULTIASSIGN =v=
  c:=JordanForm(x);
  a:=c.val1;
  b:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  T:=List( # {@-list:
    [1..Size(c)],i->c[i]);
  #  begin semisimple part
  Gen:=# {@-list:
  [];
  for j in [1..Size(T)] do
    varE:=ExtStructure(F,T[j][1]:Optimize:=false);
    m:=Multiplicity(c,T[j]);
    Gr:=SL(m,varE);
    pos:=Sum(List([1..j],k->Multiplicity(c,T[k])*Degree(T[k][1])*T[k][2])
     -m*Degree(T[j][1])*T[j][2]);
    #  creation elements of single blocks of SL
    for k in [1..Ngens(Gr)] do
      r:=BlockMatrix(m,m,Concatenation(List([1..m],
        l1->List([1..m],
          l2->StdEm@(ScalarMat(varE,T[j][2],(Gr.k)[l1][l2]),F)))));
      UniteSet(Gen,InsertBlock(IdentityMatrix(F,n),r,pos+1,pos+1) # actually TildeGen!!! TODO
       *FORCEOne(gl));
    od;
    w:=PrimitiveElement(varE);
    #   creation elements in single blocks of determinant non 1 over the larger
    #  field
    r:=IdentityMatrix(varE,m*T[j][2]);
    for k in [1..T[j][2]] do
      r[k][k]:=w^(((Size(F)-1)/Gcd(T[j][2],Size(F)-1))*FORCEOne(IntegerRing()))
       ;
    od;
    r:=StdEm@(r,F);
    UniteSet(Gen,InsertBlock(IdentityMatrix(F,n),r,pos+1,pos+1) # actually TildeGen!!! TODO
     *FORCEOne(gl));
  od;
  #  first set of generators
  if Size(F)<>2 then
    R:=(Integers mod (Size(F)-1));
    #  second set of generators: for which determinant of single block is
    #  nonzero
    A:=MatrixByEntries(R,Size(T),1,List([1..Size(T)],i->T[i][2]));
    zero:=MatrixByEntries(R,1,1,[0]);
    # =v= MULTIASSIGN =v=
    K:=SolutionMat(A,zero);
    forgetvar1:=K.val1;
    forgetvar2:=K.val2;
    K:=K.val3;
    # =^= MULTIASSIGN =^=
    w:=PrimitiveElement(F);
    for k in [1..Ngens(K)] do
      array:=[];
      for j in [1..Size(T)] do
        varE:=ExtStructure(F,T[j][1]:Optimize:=false);
        m:=Multiplicity(c,T[j]);
        t:=PrimitiveElement(varE);
        t:=t^PresOrder@(Size(F),Degree(T[j][1]),Log(Norm(t,F),w));
        #   end construction of primitive element t of E of norm w
        mat:=IdentityMatrix(varE,m*T[j][2]);
        u:=t^(PresOrder@(Size(F),Degree(T[j][1]),(K.k)[j])
         *FORCEOne(IntegerRing()));
        for h in [1..T[j][2]] do
          mat[h][h]:=u;
        od;
        mat:=mat*FORCEOne(GL(m*T[j][2],varE));
        Add(array,StdEm@(mat,F));
      od;
      UniteSet(Gen,DirectSumMat(array)*FORCEOne(gl)); # actually TildeGen!!! TODO
    od;
  fi;
  #  end semisimple part
  for j in [1..Size(T)] do
    #  begin internal blocks
    m:=T[j][2];
    if m > 1 then
      varE:=ExtStructure(F,T[j][1]:Optimize:=false);
      mu:=Multiplicity(c,T[j]);
      u:=StdEm@(MatrixByEntries(varE,1,1,[PrimitiveElement(varE)]),F);
      pos:=1;
      if j > 1 then
        pos:=pos+Sum(List([1..j-1],i->Degree(T[i][1])*T[i][2]
         *Multiplicity(c,T[i])));
      fi;
      for k in [1..m-1] do
        for h in [1..Degree(varE)] do
          r:=IdentityMatrix(F,n);
          for i in [1..m-k] do
            InsertBlock(r,u^(h-1),pos+(i-1)*Degree(varE,F),pos+(i+k-1) # actually Tilder!!! TODO
             *Degree(varE,F));
          od;
          UniteSet(Gen,r*FORCEOne(gl)); # actually TildeGen!!! TODO
        od;
      od;
    fi;
  od;
  #  end internal blocks
  r:=IdentityMatrix(F,n);
  #  begin external blocks
  w:=PrimitiveElement(F);
  pos:=1;
  for i in [1..Size(c)-1] do
    if c[i][1]=c[i+1][1] and c[i][2]<>c[i+1][2] then
      li:=Degree(c[i][1])*c[i][2];
      lj:=Degree(c[i+1][1])*c[i+1][2];
      for k in [0..Degree(F)-1] do
        UniteSet(Gen,InsertBlock(r,w^k*IdentityMatrix(F,Min(li,lj)) # actually TildeGen!!! TODO
         ,pos,pos+li+Max(0,lj-li))*FORCEOne(gl));
        UniteSet(Gen,InsertBlock(r,w^k*IdentityMatrix(F,Min(li,lj)) # actually TildeGen!!! TODO
         ,pos+li,pos+Max(li-lj,0))*FORCEOne(gl));
      od;
    fi;
    pos:=pos+Degree(c[i][1])*c[i][2];
  od;
  #  end external blocks
  #  begin construction of generalized Jordan form matrix
  r:=DirectSumMat(List( # <-list:
    [1..Size(c)],i->DirectSumMat(List([1..c[i][2]],j->CompanionMat(c[i][1])))))
   ;
  pos:=1;
  for i in [1..Size(c)] do
    if c[i][2] >= 2 then
      for j in [1..c[i][2]-1] do
        InsertBlock(r,IdentityMatrix(F,Degree(c[i][1])),pos+(j-1) # actually Tilder!!! TODO
         *Degree(c[i][1]),pos+j*Degree(c[i][1]));
      od;
    fi;
    pos:=pos+Degree(c[i][1])*c[i][2];
  od;
  #  end construction generalized Jordan form matrix
  # =v= MULTIASSIGN =v=
  forgetvar3:=JordanForm(x);
  forgetvar1:=forgetvar3.val1;
  B:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  forgetvar3:=JordanForm(r*FORCEOne(Generic(S)));
  forgetvar1:=forgetvar3.val1;
  C:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  H:=SubStructure(Generic(S),Gen);
  H:=H^((C^-1*B)*FORCEOne(GL(n,F)));
  order:=GLCentralizerOrder@(S,x:JF:=c);
  H.FactoredOrder:=order;
  H.Order:=Int(order);
  return rec(val1:=H,
    val2:=H.Order);
end);


