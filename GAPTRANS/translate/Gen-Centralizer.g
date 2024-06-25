#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BaseRing, BlockMatrix, Centraliser,
#  Characteristic, ClassicalGroupType, CompanionMatrix, ConjPol,
#  ConstantCoefficient, Degree, Determinant, DiagonalJoin, DicksonInvariant,
#  Eltseq, Exclude, FactoredOrder, Factorization, FixJordanForm,
#  FrobeniusImage, GL, GO, GOMinus, GOPlus, GU, Gcd, GenCentralizer,
#  Generators, Generic, IdentityMatrix, Insert, InsertBlock, Integers,
#  InternalUnipotentCentralizer, IsCentral, IsConjugate, IsConsistent, IsEven,
#  IsIrreducible, IsOdd, IsSemisimple, IsUnipotent, JordanForm, Log, Matrix,
#  MatrixAlgebra, Ngens, Nrows, Parent, PolynomialRing, QuadraticForm,
#  QuadraticSpace, SL, SO, SOMinus, SOPlus, SU, ScalarMatrix,
#  SequenceToFactorization, Sp, StandardHermitianForm, Star, Submatrix,
#  TransformForm, Transpose, Type, ZeroMatrix

#  Defines: ClassicalCentralizer, FixJordanForm, GenCentralizer,
#  IsClassicalCentralizerApplicable, ValidTypes

DeclareGlobalFunction("FixJordanForm@");

#   modify the standard Magma description of the elementary divisors
#   Now c is a sequence [<f_i, [m_i1, ... , m_ij] > : i], where the m_i1, ... ,
#  m_ij
#   are the dimensions of the Jordan blocks relative to the elementary divisor
#  f_i
#   Moreover, the polynomials t+1 and t-1 are put at the beginning of the
#  sequence.
InstallGlobalFunction(FixJordanForm@,
function(r,t)
local c,d,i,y;
  i:=0;
  c:=[];
  for y in r do
    if y[1]<>t-1 and y[1]<>t+1 then
      if i > 0 and y[1]=c[i][1] then
        Add(c[i][2],y[2]);
      else
        i:=i+1;
        Add(c,[y[1],[y[2]]]);
      fi;
    fi;
  od;
  for y in r do
    if y[1]=t-1 or y[1]=t+1 then
      if i > 0 and y[1]=c[1][1] then
        Insert(c[1][2],1,y[2]);  # Changed from Insert(TILDEc[1][2],1,y[2]);
      else
        i:=i+1;
        Insert(c,1,[y[1],[y[2]]]);  # Changed from Insert(TILDEc,1,[y[1],[y[2]]]);
      fi;
    fi;
  od;
  #   this is to put t+1 and t-1 at the beginning of the list
  #   if the first elementary divisor is t-1 of multiplicity 1, then
  #   it is not possible to correct both Determinant and SpinorNorm
  if Size(c) > 1 and c[1][1]=t-1 and Sum(c[1][2]=1 and c[2][1]=t+1) then
    d:=c[1];
    c[1]:=c[2];
    c[2]:=d;
  fi;
  return c;
end);

#   G must be a classical group (GO, GU, Sp, SO, Su, Omega) and x in G
#   returns Centralizer (G, x) with assigned Order and FactoredOrder
#   Does not work for orthogonal groups in even characteristic and odd 
 dimension
GenCentralizer@:=function(G,x)
local 
   A,A1,AddDeterminant,ArrayDet,ArrayInv,As,B,B1,Card,Cent,ConjPol,CorrectSp,
   DetC,varE,F,FirstHasDim1,GCD,H,H1,IsOmega,K,M,MyH,Q,R,S,SetGen,SetGen1,Split,
   Star,T,ThereIsOdd,U1,W,varX,X1,Y,Y1,_,a,alpha,b,b1,bX,c,d,deg,e,f,forgetvar1,
   forgetvar2,i,ind,is_abelian,j,j1,j2,k,k1,l,lm,m,mInv,n,p,pos,pos1,q,r,sgn,
   special,suss,t,type,type1,w,y,zm;
  F:=BaseRing(G);
  # Implicit generator Assg from previous line.
  w:=F.1;
  n:=Length(x);
  p:=Characteristic(F);
  q:=Size(F);
  t:=PolynomialRing(F).1;
  M:=MatrixAlgebra(F,n);
  Card:=Factorization(1);
  FirstHasDim1:=false;
  # =v= MULTIASSIGN =v=
  is_abelian:=DetermineForm@(G,x);
  B:=is_abelian.val1;
  type:=is_abelian.val2;
  sgn:=is_abelian.val3;
  special:=is_abelian.val4;
  IsOmega:=is_abelian.val5;
  Q:=is_abelian.val6;
  is_abelian:=is_abelian.val7;
  # =^= MULTIASSIGN =^=
  #   trivial case
  if is_abelian then
    return G;
  fi;
  # rewritten select statement
  if type="unitary" then
    e:=QuoInt(Degree(F),2);
  else
    e:=0;
  fi;
  #  conjugate transpose matrix
  Star:=function(M)
  local exp;
    exp:=e;
    return TransposedMat(FrobeniusImage(M,exp));
  end;

  #  conjugate polynomial
  ConjPol:=ConjugatePolynomial@(type="unitary");
  # =v= MULTIASSIGN =v=
  r:=JordanForm(x);
  a:=r.val1;
  b:=r.val2;
  r:=r.val3;
  # =^= MULTIASSIGN =^=
  c:=FixJordanForm@(r,t);
  SetGen:=[];
  #   generators for the centralizer
  varX:=ZeroMatrix(F,0,0);
  #   X: form in which is easier to compute the centralizer
  i:=1;
  pos:=1;
  while i <= Size(c) do
    f:=c[i][1];
    d:=Degree(f);
    Y:=ZeroMatrix(F,0,0);
    for m in c[i][2] do
      #   m = dimension of the Jordan block
      y:=DirectSumMat(List([1..m],j->CompanionMat(f)));
      for j in [1..m*d-d] do
        y[j][j+d]:=1;
      od;
      Y:=DirectSumMat(Y,y);
    od;
    varX:=DirectSumMat(varX,Y);
    if f<>ConjPol(f) then
      varX:=DirectSumMat(varX,Star(Y)^-1);
      RemoveSet(c,[ConjPol(f),c[i][2]]); # actually TILDEc!!! TODO
    fi;
    i:=i+1;
  od;
  # =v= MULTIASSIGN =v=
  bX:=JordanForm(varX);
  forgetvar1:=bX.val1;
  bX:=bX.val2;
  # =^= MULTIASSIGN =^=
  b1:=bX^-1*b;
  #   rewrite A in the upper triangular form
  if p=2 and type<>"unitary" and type<>"symplectic" then
    A:=b1*Q*Star(b1);
    #   A = quadratic form preserved by X
    for i in [1..n] do
      for j in [i+1..n] do
        A[i][j]:=A[i][j]+A[j][i];
        A[j][i]:=0;
      od;
    od;
  else
    A:=b1*B*Star(b1);
    #   A = sesquilinear form preserved by X
  fi;
  if special and type<>"unitary" then
    ThereIsOdd:=false;
    if c[1][1] in [t+1,t-1] then
      if true in List(c[1][2],d->IsOddInt(d)) then
        ThereIsOdd:=true;
      elif Size(c) > 1 and c[2][1] in [t-1,t+1] then
        if true in List(c[2][2],d->IsOddInt(d)) then
          ThereIsOdd:=true;
          FirstHasDim1:=true;
        fi;
      fi;
    fi;
    if ThereIsOdd=false then
      special:=false;
      #   in this case the centralizers in GO and SO coincide
    fi;
  fi;
  #   CorrectSp is an element in the centralizer of the first el.div.
  #   (or the second el.div. in the case x^2-1 has rank n-1)
  #   with determinant 1 and SpinorNorm 1
  if (special or IsOmega) and type<>"unitary" then
    # =v= MULTIASSIGN =v=
    FirstHasDim1:=CorrectSpecial(c,F,n,q,p,e,type,A,b1);
    CorrectSp:=FirstHasDim1.val1;
    FirstHasDim1:=FirstHasDim1.val2;
    # =^= MULTIASSIGN =^=
    DetC:=DeterminantMat(CorrectSp);
  fi;
  #   the i-th element of AddDeterminant is Y_i, where Y_i is an element
  #   in the centralizer in GU of X_i of maximal order of the determinant
  if special and type="unitary" then
    AddDeterminant:=[];
  fi;
  #   create generators
  #   case Special Orthogonal:
  #   if <x_1, ..., x_k> are generators for centralizer of x in the general
  #  group,
  #   generators of the centralizer of the first el.div. are replaced by
  #  generators
  #   for centralizer in the special group;
  #   the other generators are multiplied by some power of CorrectSp,
  #   depending on determinant
  #   case Special Unitary: the first part produces generators of the
  #   centralizer of every single block in its corresponding special group;
  #   elements with overall determinant 1, but not for every single block,
  #   are added in second part
  #   case Omega: the set of generators is the same as the special case;
  #   it will be modified in the third part
  Y:=IdentityMatrix(F,n);
  pos:=1;
  ind:=1;
  if FirstHasDim1 then
    ind:=2;
  fi;
  for i in [1..Size(c)] do
    f:=c[i][1];
    d:=Sum(c[i][2]);
    deg:=Degree(f);
    if f=ConjPol(f) and deg=1 then
      B1:=Submatrix(A,pos,pos,d,d);
      X1:=Submatrix(varX,pos,pos,d,d);
      #   U1 = unipotent part. They have the same centralizer
      U1:=X1*ScalarMat(d,(-ConstantCoefficient(f))^-1);
      if type="unitary" then
        m:=TransformForm(B1,"unitary":Restore:=false);
        mInv:=m^-1;
        if special then
          MyH:=SU(d,F);
          MyH.ClassicalType:="SU";
          Cent:=InternalUnipotentCentralizer@(MyH,(mInv*U1*m)*FORCEOne(GL(d,F)))
           ;
          Add(AddDeterminant,ElementOfMaxDeterminant@(U1,B1,m,"unitary"));
          for j in [1..Ngens(Cent)] do
            Y1:=InsertBlock(Y,m*Cent.j*mInv,pos,pos);
            Y1:=b1^-1*Y1*b1;
            Add(SetGen,Y1);
          od;
        else
          MyH:=GU(d,F);
          MyH.ClassicalType:="GU";
          Cent:=InternalUnipotentCentralizer@(MyH,(mInv*U1*m)*FORCEOne(GL(d,F)))
           ;
          for j in [1..Ngens(Cent)] do
            Y1:=InsertBlock(Y,m*Cent.j*mInv,pos,pos);
            Y1:=b1^-1*Y1*b1;
            Add(SetGen,Y1);
          od;
        fi;
        Card:=Card*FactoredOrder(Cent);
      elif type="symplectic" then
        m:=TransformForm(B1,"symplectic":Restore:=false);
        MyH:=SP(d,F);
        MyH.ClassicalType:="Sp";
        Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)*FORCEOne(GL(d,F)));
        for j in [1..Ngens(Cent)] do
          Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
          Add(SetGen,b1^-1*Y1*b1);
        od;
        Card:=Card*FactoredOrder(Cent);
      elif type="orthogonalcircle" or type="orthogonalplus" or 
         type="orthogonalminus" or type="orthogonal" then
        if d=1 then
          type1:="orthogonal";
          if not special or i<>ind then
            Y1:=InsertBlock(Y,-IdentityMatrix(F,1),pos,pos);
            Y1:=b1^-1*Y1*b1;
            if special then
              Y1:=Y1*CorrectSp;
            fi;
            Card:=Card*SequenceToFactorization([[2,1]]);
            Add(SetGen,Y1);
          fi;
        else
          type1:=IndicateType@(B1);
          m:=TransformForm(B1,type1:Restore:=false);
          if type1="orthogonalplus" then
            if special or (IsOmega and IsOddInt(p)) then
              if i=ind then
                MyH:=SOPlus(d,F);
                MyH.ClassicalType:="SO+";
                Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
                 *FORCEOne(GL(d,F)));
                for j in [1..Ngens(Cent)] do
                  Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                  Y1:=b1^-1*Y1*b1;
                  Add(SetGen,Y1);
                od;
              else
                MyH:=GOPlus(d,F);
                MyH.ClassicalType:="GO+";
                Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
                 *FORCEOne(GL(d,F)));
                for j in [1..Ngens(Cent)] do
                  Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                  Y1:=b1^-1*Y1*b1;
                  if DeterminantMat(Y1)=-1 then
                    Y1:=Y1*CorrectSp;
                  fi;
                  Add(SetGen,Y1);
                od;
              fi;
            else
              MyH:=GOPlus(d,F);
              MyH.ClassicalType:="GO+";
              Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
               *FORCEOne(GL(d,F)));
              for j in [1..Ngens(Cent)] do
                Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                Y1:=b1^-1*Y1*b1;
                Add(SetGen,Y1);
              od;
            fi;
          elif type1="orthogonalminus" then
            if special or (IsOmega and IsOddInt(p)) then
              if i=ind then
                MyH:=SOMinus(d,F);
                MyH.ClassicalType:="SO-";
                Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
                 *FORCEOne(GL(d,F)));
                for j in [1..Ngens(Cent)] do
                  Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                  Y1:=b1^-1*Y1*b1;
                  Add(SetGen,Y1);
                od;
              else
                MyH:=GOMinus(d,F);
                MyH.ClassicalType:="GO-";
                Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
                 *FORCEOne(GL(d,F)));
                for j in [1..Ngens(Cent)] do
                  Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                  Y1:=b1^-1*Y1*b1;
                  if DeterminantMat(Y1)=-1 then
                    Y1:=Y1*CorrectSp;
                  fi;
                  Add(SetGen,Y1);
                od;
              fi;
            else
              MyH:=GOMinus(d,F);
              MyH.ClassicalType:="GO-";
              Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
               *FORCEOne(GL(d,F)));
              for j in [1..Ngens(Cent)] do
                Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                Y1:=b1^-1*Y1*b1;
                Add(SetGen,Y1);
              od;
            fi;
          else
            if special or (IsOmega and IsOddInt(p)) then
              if i=ind then
                MyH:=SO(d,F);
                MyH.ClassicalType:="SO";
                Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
                 *FORCEOne(GL(d,F)));
                for j in [1..Ngens(Cent)] do
                  Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                  Y1:=b1^-1*Y1*b1;
                  Add(SetGen,Y1);
                od;
              else
                MyH:=GO(d,F);
                MyH.ClassicalType:="GO";
                Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
                 *FORCEOne(GL(d,F)));
                for j in [1..Ngens(Cent)] do
                  Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                  Y1:=b1^-1*Y1*b1;
                  if DeterminantMat(Y1)=-1 then
                    Y1:=Y1*CorrectSp;
                  fi;
                  Add(SetGen,Y1);
                od;
              fi;
            else
              MyH:=GO(d,F);
              MyH.ClassicalType:="GO";
              Cent:=InternalUnipotentCentralizer@(MyH,(m^-1*U1*m)
               *FORCEOne(GL(d,F)));
              for j in [1..Ngens(Cent)] do
                Y1:=InsertBlock(Y,m*Cent.j*m^-1,pos,pos);
                Y1:=b1^-1*Y1*b1;
                Add(SetGen,Y1);
              od;
            fi;
          fi;
          Card:=Card*FactoredOrder(Cent);
        fi;
      fi;
      pos:=pos+d;
    elif f<>ConjPol(f) then
      varE:=ExtStructure(F,f:Optimize:=false);
      # Implicit generator Assg from previous line.
      l:=varE.1;
      A1:=Submatrix(A,pos,pos+d*deg,d*deg,d*deg);
      y:=IdentityMatrix(varE,d);
      pos1:=1;
      for j1 in c[i][2] do
        for j2 in [1..j1-1] do
          y[pos1][pos1+1]:=1;
          pos1:=pos1+1;
        od;
        pos1:=pos1+1;
      od;
      if special and type="unitary" then
        MyH:=SL(d,varE);
        MyH.ClassicalType:="SL";
        Cent:=InternalUnipotentCentralizer@(MyH,y*FORCEOne(GL(d,varE)));
        # =v= MULTIASSIGN =v=
        GCD:=ElementOfMaxDeterminant@(y,c[i][2],IdentityMatrix(varE,d),"linear")
         ;
        y:=GCD.val1;
        GCD:=GCD.val2;
        # =^= MULTIASSIGN =^=
        suss:=BlockMatrix(d,d,Concatenation(List([1..d],
          j1->List([1..d],
            j2->Sum(List([1..deg],k->CompanionMat(f)^(k-1)*Eltseq(y[j1][j2],F)
         [k])))));
        suss:=DirectSumMat(suss,Star(A1^-1*suss^-1*A1));
        Add(AddDeterminant,suss);
        #   add an element having determinant 1 in SU(d*deg, F), but not in
        #  SU(d, E)
        #   Gcd (deg*GCD, p^e+1) = Gcd (GCD * (p^(2*e*deg)-1) / (p^2e-1), p^e+1)
         
        alpha:=QuoInt((p^e+1),Gcd(GCD,p^e+1));
        y:=InsertBlock(Y,suss^alpha,pos,pos);
        Add(SetGen,b1^-1*y*b1);
        Card:=Card*Factorization(p^(2*e*deg)-1);
        Card:=Card/Factorization(GCD*alpha);
      else
        MyH:=GL(d,varE);
        MyH.ClassicalType:="GL";
        Cent:=InternalUnipotentCentralizer@(MyH,y*FORCEOne(GL(d,varE)));
      fi;
      for j in [1..Ngens(Cent)] do
        a:=Cent.j;
        suss:=BlockMatrix(d,d,Concatenation(List([1..d],
          j1->List([1..d],
            j2->Sum(List([1..deg],k->CompanionMat(f)^(k-1)*Eltseq(a[j1][j2],F)
         [k])))));
        suss:=DirectSumMat(suss,Star(A1^-1*suss^-1*A1));
        y:=InsertBlock(Y,suss,pos,pos);
        y:=b1^-1*y*b1;
        if special then
          if type<>"unitary" then
            if DeterminantMat(y)=-1 then
              y:=y*CorrectSp;
            fi;
          fi;
        fi;
        Add(SetGen,y);
      od;
      pos:=pos+2*d*deg;
      Card:=Card*FactoredOrder(Cent);
    else
      varE:=ExtStructure(F,f:Optimize:=false);
      # Implicit generator Assg from previous line.
      l:=varE.1;
      H:=GL(deg,F);
      # =v= MULTIASSIGN =v=
      T:=IsConjugate(H,CompanionMat(f)*FORCEOne(H)^-1,Star(CompanionMat(f))
       *FORCEOne(H));
      forgetvar1:=T.val1;
      T:=T.val2;
      # =^= MULTIASSIGN =^=
      if DeterminantMat(T+sgn*Star(T))=0 then
        T:=CompanionMat(f)*T+sgn*Star(CompanionMat(f)*T);
      else
        T:=T+sgn*Star(T);
      fi;
      T:=T^-1;
      A1:=Submatrix(A,pos,pos,d*deg,d*deg);
      if p=2 and type<>"unitary" and type<>"symplectic" then
        A1:=A1+TransposedMat(A1);
      fi;
      B1:=A1*DirectSumMat(List([1..d],j->T));
      H1:=ZeroMatrix(varE,d,d);
      #   H1 = matrix B1 over the smaller field
      #  changed:for j1, j2 in [1..d] do
      for j1 in [1..d] do
        for j2 in [1..d] do
          H1[j1][j2]:=Sum(List([1..deg],k->l^(k-1)*B1[deg*(j1-1)+1][deg*(j2-1)
           +k]));
        od;
      od;
      m:=TransformForm(H1,"unitary":Restore:=false);
      y:=IdentityMatrix(varE,d);
      pos1:=1;
      lm:=l^-1;
      for j1 in c[i][2] do
        for j2 in [1..j1-1] do
          y[pos1][pos1+1]:=lm;
          pos1:=pos1+1;
        od;
        pos1:=pos1+1;
      od;
      y:=m^-1*y*m;
      if special and type="unitary" then
        MyH:=SU(d,varE);
        MyH.ClassicalType:="SU";
        Cent:=InternalUnipotentCentralizer@(MyH,y*FORCEOne(GL(d,varE)));
        # =v= MULTIASSIGN =v=
        GCD:=ElementOfMaxDeterminant@(y,StandardHermitianForm(d,varE)
         ,IdentityMatrix(varE,d),"unitary");
        S:=GCD.val1;
        GCD:=GCD.val2;
        # =^= MULTIASSIGN =^=
        S:=m*S*m^-1;
        suss:=BlockMatrix(d,d,Concatenation(List([1..d],
          j1->List([1..d],
            j2->Sum(List([1..deg],k->CompanionMat(f)^(k-1)*Eltseq(S[j1][j2],F)
         [k])))));
        Add(AddDeterminant,suss);
        #   add an element having determinant 1 in SU(d*deg, F), but not in
        #  SU(d, E)
        alpha:=QuoInt((p^e+1),Gcd(GCD,p^e+1));
        S:=InsertBlock(Y,suss^alpha,pos,pos);
        Add(SetGen,b1^-1*S*b1);
        Card:=Card*Factorization(p^(e*deg)+1);
        Card:=Card/Factorization(alpha*GCD);
      else
        MyH:=GU(d,varE);
        MyH.ClassicalType:="GU";
        Cent:=InternalUnipotentCentralizer@(MyH,y*FORCEOne(GL(d,varE)));
      fi;
      for j in [1..Ngens(Cent)] do
        S:=m*Cent.j*m^-1;
        suss:=BlockMatrix(d,d,Concatenation(List([1..d],
          j1->List([1..d],
            j2->Sum(List([1..deg],k->CompanionMat(f)^(k-1)*Eltseq(S[j1][j2],F)
         [k])))));
        Y1:=InsertBlock(Y,suss,pos,pos);
        Y1:=b1^-1*Y1*b1;
        if special then
          if type<>"unitary" then
            if DeterminantMat(Y1)=-1 then
              Y1:=Y1*CorrectSp;
            fi;
          fi;
        fi;
        Add(SetGen,Y1);
      od;
      pos:=pos+d*deg;
      Card:=Card*FactoredOrder(Cent);
    fi;
  od;
  #   add elements with determinant of the single blocks
  #   different from 1, but overall determinant 1
  if special and type="unitary" then
    R:=(Integers mod (q-1));
    ArrayDet:=List(AddDeterminant,y->DeterminantMat(y));
    ArrayInv:=List(ArrayDet,y->Log(w,y));
    As:=MatrixByEntries(R,Size(c),1,List(ArrayInv,y->y*FORCEOne(R)));
    W:=MatrixByEntries(R,1,1,[0*FORCEOne(R)]);
    # =v= MULTIASSIGN =v=
    K:=SolutionMat(As,W);
    forgetvar1:=K.val1;
    forgetvar2:=K.val2;
    K:=K.val3;
    # =^= MULTIASSIGN =^=
    for k in Generators(K) do
      k1:=List(Eltseq(k),ki->Int(ki));
      Y:=DirectSumMat(List( # <-list:
        [1..Size(c)],i->AddDeterminant[i]^(k1[i])));
      Add(SetGen,b1^-1*Y*b1);
    od;
  fi;
  #   correct generating set in Omega case:
  #   if x is a generator for SO, then the set of generators for Omega 
   contains:
  #   x and z^-1xz (if x in Omega) or xz and z^-1x (if x not in Omega),
  #   with z = element in the centralizer of SO with spinor norm 1
  if IsOmega then
    Split:=z:=ForAny(SetGen,y->SpinN@(y*FORCEOne(GL(n,F)),Q,p)=1);
    if Split then
      SetGen1:=SetGen;
      SetGen:=[];
      zm:=z^-1;
      for y in SetGen1 do
        if SpinN@(y*FORCEOne(GL(n,F)),Q,p)=0 then
          Add(SetGen,y);
          Add(SetGen,zm*y*z);
        else
          Add(SetGen,zm*y);
          Add(SetGen,y*z);
        fi;
      od;
    fi;
  fi;
  #   correcting cardinality in Special and Omega case
  if special then
    if type="unitary" then
      GCD:=List(c,y->Gcd(Concatenation(y[2],[p^e+1])));
      Card:=Card*Factorization(p^e+1)^(Size(c)-1);
      Card:=Card/Product(List(GCD,y->Factorization(y)));
      Card:=Card*Factorization(Gcd(GCD));
    fi;
  fi;
  if IsOmega then
    if Split then
      Card:=Card/SequenceToFactorization([[2,1]]);
    fi;
  fi;
  H:=SubStructure(GL(n,F),SetGen);
  H.FactoredOrder:=Card;
  H.Order:=Int(Card);
  return H;
end;

ValidTypes@:=Set(["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+",
 "SO-","SO","GO+","GO-","GO"]);
IsClassicalCentralizerApplicable@:=function(G,g)
#  -> ,BoolElt  Does the ClassicalCentralizer intrinsic function apply to this
#  group
local F,V,apply,d,even,flag,form,form_type,type;
  d:=Degree(G);
  F:=BaseRing(G);
  if Type(F)<>FldFin or (d=2 and Size(F) <= 4) then
    return false;
  fi;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not flag or not (type in ValidTypes@) or not 
     MyIsIn@(G,g:Add:=Set(["SL","GL"])) then
    return false;
  fi;
  even:=Characteristic(F)=2;
  if type="GL" or (type="GO" and IsOddInt(d) and even) then
    return false;
  fi;
  if even and type in 
     ["Omega+","Omega-","Omega","SO+","SO-","SO","GO+","GO-","GO"] then
    if not IsIrreducible(G) then
      return false;
    fi;
    # =v= MULTIASSIGN =v=
    form_type:=QuadraticForm(G);
    flag:=form_type.val1;
    form:=form_type.val2;
    form_type:=form_type.val3;
    # =^= MULTIASSIGN =^=
    V:=QuadraticSpace(form);
    apply:=DicksonInvariant(V,g)=0;
    if not apply then
      return false;
    fi;
  fi;
  return true;
end;

ClassicalCentralizer@:=function(G,g)
#  -> ,GrpMat  Centralizer of g in classical group G
local CB,F,Gr,varZ,d,flag,type;
  if not (Generic(Parent(g))=Generic(G)) then
    Error("Input element is not in group");
  fi;
  #   require g in G: "Element not in group";
  if not MyIsIn@(G,g:Add:=Set(["GL","SL"])) then
    Error("Input element is not in group");
  fi;
  if IsCentral(G,g) then
    return G;
  fi;
  d:=Degree(G);
  F:=BaseRing(G);
  if d=2 and Size(F) <= 4 then
    return Centraliser(G,g);
  fi;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not flag and type in ValidTypes@ then
    Error(["Type of group must be one of ",ValidTypes@]);
  fi;
  if IsOddInt(d) and IsEvenInt(Size(F)) and type="GO" then
    Error("Function does not apply to this case");
  fi;
  if type in ["SL","GL"] then
    #   EOB -- changed to Centralizer because it's faster
    #   Yes .. but if G is NOT set up as GL(d, q) then Magma does not use
    #  Murray algorithm
    #   so back to our implementation of GLCentraliser
    return # rewritten select statement
    function(xxx)if xxx then return SLCentralizer@(G,g);else return 
     GLCentralizer@(G,g);fi;end(type="SL");
    #   return type eq "SL" select SLCentralizer (G, g) else Centralizer (G, g)
     ;
  fi;
  CB:=TransformMatrix@(G);
  Gr:=G^CB;
  Gr.ClassicalType:=G.ClassicalType;
  if IsSemisimple(g) then
    varZ:=SSCentralizer(Gr,g^CB);
  elif IsUnipotent(g) then
    varZ:=InternalUnipotentCentralizer@(Gr,g^CB);
  else
    varZ:=GenCentralizer@(Gr,g^CB);
  fi;
  return varZ^(CB^-1);
end;


