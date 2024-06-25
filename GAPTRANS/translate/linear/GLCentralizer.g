#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BlockMatrix, CoefficientRing, CompanionMatrix,
#  Degree, DiagonalJoin, GL, Generic, IdentityMatrix, Include, InsertBlock,
#  Integers, JordanForm, Matrix, Max, Min, Multiplicity, Ngens, Nrows,
#  PrimitiveElement, ScalarMatrix, StdEm, WriteMatrixOverSmallerField

#  Defines: GLCentralizer, StdEm

DeclareGlobalFunction("GLCentralizer@");

#  matrix in E = F_q^r --> matrix in F_q
StdEm@:=function(A,F)
return WriteMatrixOverSmallerField(A,F);
end;

#   x is an element of G = GL(d, q); determine its centraliser
InstallGlobalFunction(GLCentralizer@,
function(G,x)
#  /out:need StdEm
local 
   B,C,varE,F,Gen,Gr,H,lvarSet,_,a,b,c,forgetvar1,forgetvar3,gl,h,i,j,k,li,lj,m,mu,
   n,order,pos,r,u;
  gl:=Generic(G);
  F:=CoefficientRing(G);
  n:=Length(x);
  # =v= MULTIASSIGN =v=
  c:=JordanForm(x);
  a:=c.val1;
  b:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  lvarSet:=List( # {@-list:
    [1..Size(c)],i->c[i]);
  #  begin semisimple part
  Gen:=# {@-list:
  [];
  for j in [1..Size(lvarSet)] do
    varE:=ExtStructure(F,lvarSet[j][1]:Optimize:=false);
    m:=Multiplicity(c,lvarSet[j]);
    Gr:=GL(m,varE);
    pos:=Sum(List([1..j],k->Multiplicity(c,lvarSet[k])*Degree(lvarSet[k][1])
     *lvarSet[k][2])-m*Degree(lvarSet[j][1])*lvarSet[j][2]);
    for k in [1..Ngens(Gr)] do
      r:=BlockMatrix(m,m,Concatenation(List([1..m],
        l1->List([1..m],
          l2->StdEm(ScalarMat(varE,lvarSet[j][2],(Gr.k)[l1][l2]),F))))); # there was an @!!! TODO
      UniteSet(Gen,InsertBlock(IdentityMatrix(F,n),r,pos+1,pos+1 )# actually TildeGen!!! TODO
       *FORCEOne(gl));
    od;
  od;
  #  end semisimple part
  for j in [1..Size(lvarSet)] do
    #  begin internal blocks
    m:=lvarSet[j][2];
    if m > 1 then
      varE:=ExtStructure(F,lvarSet[j][1]:Optimize:=false);
      mu:=Multiplicity(c,lvarSet[j]);
      u:=StdEm@(MatrixByEntries(varE,1,1,[PrimitiveElement(varE)]),F);
      pos:=1;
      if j > 1 then
        pos:=pos+Sum(List([1..j-1],i->Degree(lvarSet[i][1])*lvarSet[i][2]
         *Multiplicity(c,lvarSet[i])));
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
  pos:=1;
  for i in [1..Size(c)-1] do
    if c[i][1]=c[i+1][1] and c[i][2]<>c[i+1][2] then
      li:=Degree(c[i][1])*c[i][2];
      lj:=Degree(c[i+1][1])*c[i+1][2];
      UniteSet(Gen,InsertBlock(r,IdentityMatrix(F,Min(li,lj)) # actually TildeGen!!! TODO
       ,pos,pos+li+Max(0,lj-li))*FORCEOne(gl));
      UniteSet(Gen,InsertBlock(r,IdentityMatrix(F,Min(li,lj)) # actually TildeGen!!! TODO
       ,pos+li,pos+Max(li-lj,0))*FORCEOne(gl));
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
  forgetvar3:=JordanForm(r*FORCEOne(gl));
  forgetvar1:=forgetvar3.val1;
  C:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  H:=SubStructure(gl,Gen);
  H:=H^((C^-1*B)*FORCEOne(gl));
  order:=GLCentralizerOrder@(gl,x:JF:=c);
  H.FactoredOrder:=order;
  H.Order:=Int(order);
  return rec(val1:=H,
    val2:=H.Order);
end);


