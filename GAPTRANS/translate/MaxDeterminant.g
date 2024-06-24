#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Characteristic, Determinant, GL, GO,
#  GOMinus, GOPlus, GU, Gcd, Generators, Generic, Identity, IdentityMatrix,
#  Integers, InternalUnipotentCentralizer, IsConsistent, IsSquare, IsUnipotent,
#  Log, Matrix, Ngens, Nrows, PrimitiveElement, SetToSequence,
#  StandardQuadraticForm, StandardSymmetricForm, TransformForm, Transpose, Type

#  Defines: ElementOfMaxDeterminant, ElementOfSpinorNorm1

DeclareGlobalFunction("ElementOfMaxDeterminant@");

DeclareGlobalFunction("ElementOfSpinorNorm1@");

#   This code is needed for GenCentralizer.m.
#   We assume that input x is unipotent with a unique el.div.
#   if type = "unitary", "orthogonalplus", "orthogonalminus"
#   given an element x in the unitary group G with form B where
#   m := TransformForm (B, type);
#   return an element of the centralizer of x in G with determinant of maximal
#  order;
#   returns also the centralizer of x in G, which saves later computations
#   if type := "linear"
#   given a Jordan block x in G=GL(n, F), B = vector of sizes of the blocks
#   where m = IdentityMatrix (F, n)
#   return an element of the centralizer of x in G with determinant of maximal
#  order;
#   returns also GCD, which saves later computations
InstallGlobalFunction(ElementOfMaxDeterminant@,
function(x,B,m,type)
local A,C,F,GCD,MyH,R,SetDet,SetGen,SetLog,W,_,d,forgetvar1,i,j,n,pos,q,v,w,y;
  Assert(1,IsUnipotent(x));
  F:=BaseRing(x);
  n:=Length(x);
  if type="linear" then
    q:=Size(F);
    R:=(Integers mod (q-1));
    w:=PrimitiveElement(F);
    d:=Size(B);
    A:=MatrixByEntries(R,d,1,B);
    GCD:=Gcd(Concatenation(B,[q-1]));
    W:=MatrixByEntries(R,1,1,[GCD]);
    # =v= MULTIASSIGN =v=
    v:=SolutionMat(A,W);
    forgetvar1:=v.val1;
    v:=v.val2;
    # =^= MULTIASSIGN =^=
    y:=IdentityMatrix(F,n);
    pos:=1;
    for i in [1..d] do
      for j in [1..B[i]] do
        y[pos][pos]:=w^(Int(v[1][i]));
        pos:=pos+1;
      od;
    od;
    C:=GL(n,F);
    #   this is useless
  elif type="unitary" then
    # =v= MULTIASSIGN =v=
    q:=IsSquare(Size(F));
    forgetvar1:=q.val1;
    q:=q.val2;
    # =^= MULTIASSIGN =^=
    R:=(Integers mod (q+1));
    MyH:=GU(n,F);
    MyH.ClassicalType:="GU";
    C:=InternalUnipotentCentralizer@(MyH,(m^-1*x*m)*FORCEOne(Generic(MyH)));
    w:=PrimitiveElement(F);
    SetGen:=SetToSequence(Generators(C));
    d:=Size(SetGen);
    SetDet:=List(SetGen,y->DeterminantMat(y));
    SetLog:=List(SetDet,y->QuoInt(Log(w,y),(q-1)));
    A:=MatrixByEntries(R,d,1,List(SetLog,y->y*FORCEOne(R)));
    GCD:=Gcd(Concatenation(SetLog,[q+1]));
    W:=MatrixByEntries(R,1,1,[GCD]);
    # =v= MULTIASSIGN =v=
    v:=SolutionMat(A,W);
    forgetvar1:=v.val1;
    v:=v.val2;
    # =^= MULTIASSIGN =^=
    y:=Product(List([1..d],i->SetGen[i]^(Int(v[1][i]))));
  elif type="orthogonalplus" or type="orthogonalminus" then
    q:=Size(F);
    GCD:=2;
    if type="orthogonalplus" then
      MyH:=GOPlus(n,q);
      MyH.ClassicalType:="GO+";
      C:=InternalUnipotentCentralizer@(MyH,(m^-1*x*m)*FORCEOne(GL(n,q)));
    else
      MyH:=GOMinus(n,q);
      MyH.ClassicalType:="GO-";
      C:=InternalUnipotentCentralizer@(MyH,(m^-1*x*m)*FORCEOne(GL(n,q)));
    fi;
    i:=First([1..Ngens(C)],i->DeterminantMat(C.i)=-1);
    if i<>fail then
      y:=C.i;
      GCD:=1;
    else
      y:=C.1;
    fi;
  fi;
  return rec(val1:=m*y*m^-1,
    val2:=GCD,
    val3:=C);
end);

#   If there exists an element y in the centralizer of x in GO
#   with spinor norm 1, then the code returns y, true.
#   If there are no elements of spinor norm 1, then the code returns y, false
#   where y is an element in the centralizer of x in GO with determinant -1
#   (if such exists) or 1.
#   If special=true, then we search for the element only in SO.
#   B is the form preserved by GO / SO.
#   If C is not [], then it is the centralizer of x in GO.
#   If m is not [], then it is result of TransformForm (x, type)
#   so we avoid recomputing it
InstallGlobalFunction(ElementOfSpinorNorm1@,
function(x,B)
local C,Cent,F,Form,G,varX,det,done,i,m,n,p,s,special,type,y,z;
  special:=ValueOption("special");
  if special=fail then
    special:=false;
  fi;
  C:=ValueOption("C");
  if C=fail then
    C:=[];
  fi;
  m:=ValueOption("m");
  if m=fail then
    m:=[];
  fi;
  Assert(1,IsUnipotent(x));
  F:=BaseRing(x);
  p:=Characteristic(F);
  n:=Length(x);
  type:=IndicateType@(B);
  if Type(m)=SeqEnum then
    m:=TransformForm(B,type:Restore:=false);
  fi;
  varX:=m^-1*x*m;
  if type="orthogonalplus" then
    G:=GOPlus(n,F);
    G.ClassicalType:="GO+";
    # rewritten select statement
    if p=2 then
      Form:=StandardQuadraticForm(n,F);
    else
      Form:=StandardSymmetricForm(n,F);
    fi;
  elif type="orthogonalminus" then
    G:=GOMinus(n,F);
    G.ClassicalType:="GO-";
    # rewritten select statement
    if p=2 then
      Form:=StandardQuadraticForm(n,F:Minus:=true,Variant:="Default");
    else
      Form:=StandardSymmetricForm(n,F:Minus:=true,Variant:="Default");
    fi;
  elif type="orthogonal" or type="orthogonalcircle" then
    if n<>1 then
      G:=GO(n,F);
      G.ClassicalType:="GO";
    fi;
    # rewritten select statement
    if p=2 then
      Form:=StandardQuadraticForm(n,F);
    else
      Form:=StandardSymmetricForm(n,F:Variant:="Default");
    fi;
    #   need this otherwise the spinor norm may be affected
    if B<>m*Form*TransposedMat(m) then
      Form:=Form*PrimitiveElement(F);
    fi;
  fi;
  if Type(C)=SeqEnum then
    if n=1 then
      Cent:=SubStructure(GL(1,F),-IdentityMatrix(F,1));
    else
      Cent:=InternalUnipotentCentralizer@(G,varX*FORCEOne(Generic(G)));
    fi;
  else
    Cent:=C;
  fi;
  done:=index:=ForAny([1..Ngens(Cent)],i->SpinN@(Cent.i,Form,p)=1);
  if done then
    y:=Cent.index;
  fi;
  if not done then
    y:=Identity(GL(n,F));
    if special or p=2 then
      return rec(val1:=y,
        val2:=false);
    fi;
    done:=i:=ForAny([1..Ngens(Cent)],i->DeterminantMat(Cent.i)=-1);
    if done then
      y:=Cent.i;
    fi;
    return rec(val1:=m*y*m^-1,
      val2:=false);
  fi;
  if DeterminantMat(y)=-1 then
    done:=false;
    for i in [1..index-1] do
      if DeterminantMat(Cent.i)=-1 then
        y:=y*Cent.i;
        done:=true;
        break i;
      fi;
    od;
    if not done then
      for i in [index+1..Ngens(Cent)] do
        z:=Cent.i;
        det:=DeterminantMat(z);
        s:=SpinN@(z,Form,p);
        if det=-1 and s=0 then
          y:=y*z;
          done:=true;
          break i;
        elif det=1 and s=1 then
          y:=z;
          done:=true;
          break i;
        fi;
      od;
    fi;
  fi;
  if special and done=false then
    return rec(val1:=Identity(GL(n,F)),
      val2:=false);
  else
    return rec(val1:=m*y*m^-1,
      val2:=true);
  fi;
end);


