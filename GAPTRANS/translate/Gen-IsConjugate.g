#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BaseRing, BlockMatrix, Characteristic,
#  ClassicalGroupType, CompanionMatrix, ConjPol, ConstantCoefficient, Degree,
#  Determinant, DiagonalJoin, DicksonInvariant, Eltseq, Exclude,
#  FrobeniusImage, GL, GO, GOMinus, GOPlus, GU, Gcd, GenIsConjugate, Generic,
#  HaveSameLabel, HaveSameType, Identity, IdentityMatrix, InsertBlock,
#  Integers, InternalUnipotentCentralizer, InternalUnipotentIsConjugate,
#  IsAbelian, IsConjugate, IsConsistent, IsEven, IsIrreducible, IsOdd,
#  IsSemisimple, IsSquare, IsUnipotent, IsometryGroupClassLabel, JordanForm,
#  Log, Matrix, MatrixAlgebra, MatrixInCentralizerEQ, MatrixInCentralizerNE,
#  Multiplicity, Ngens, Norm, Nrows, Order, Parent, PolynomialRing,
#  QuadraticForm, QuadraticSpace, ScalarMatrix, Sp, StandardHermitianForm,
#  Star, Submatrix, TransformForm, Transpose, Type, ZeroMatrix

#  Defines: ClassicalIsConjugate, GenIsConjugate, HaveSameLabel, HaveSameType,
#  IsClassicalIsConjugateApplicable, MatrixInCentralizerEQ,
#  MatrixInCentralizerNE, ValidTypes

DeclareGlobalFunction("GenIsConjugate@");

#   are g and h both semisimple or unipotent?
HaveSameType@:=function(g,h)
if IsUnipotent(g) then
    return IsUnipotent(h);
  elif IsSemisimple(g) then
    return IsSemisimple(h);
  fi;
  return true;
end;

#   do g and h have same label in the isometry group?
#   called only for mixed elements
HaveSameLabel@:=function(G,g,h)
local flag,type;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if type in ["GO","SO","Omega"] then
    type:="GO";
  fi;
  if type in ["GO+","SO+","Omega+"] then
    type:="GO+";
  fi;
  if type in ["GO-","SO-","Omega-"] then
    type:="GO-";
  fi;
  if type in ["GU","SU"] then
    type:="GU";
  fi;
  return IsometryGroupClassLabel@(type,g)=IsometryGroupClassLabel@(type,h);
end;

#   returns an element in the centralizer of a block with max determinant order
#   case f not equal to f*
MatrixInCentralizerNE@:=function(F,f,pos,A1,d,deg,c3,type)
local B1,varE,Star,e,j1,j2,l,lm,pos1,suss,y,z;
  # rewritten select statement
  if type="unitary" then
    e:=QuoInt(Degree(F),2);
  else
    e:=0;
  fi;
  Star:=function(M)
  local exp;
    exp:=e;
    return TransposedMat(FrobeniusImage(M,exp));
  end;

  varE:=ExtStructure(F,f);
  # Implicit generator Assg from previous line.
  l:=varE.1;
  B1:=Submatrix(A1,pos,pos+d*deg,d*deg,d*deg);
  z:=IdentityMatrix(varE,d);
  lm:=l^-1;
  pos1:=1;
  for j1 in c3[2] do
    for j2 in [1..j1-1] do
      z[pos1][pos1+1]:=lm;
      pos1:=pos1+1;
    od;
    pos1:=pos1+1;
  od;
  #   z is the unipotent part (the centralizer is the same)
  y:=ElementOfMaxDeterminant@(z,c3[2],IdentityMatrix(varE,d),"linear");
  suss:=BlockMatrix(d,d,Concatenation(List([1..d],
    j1->List([1..d],
      j2->Sum(List([1..deg],k->CompanionMat(f)^(k-1)*Eltseq(y[j1][j2],F)[k])))))
   ;
  suss:=DirectSumMat(suss,Star(B1^-1*suss^-1*B1));
  return rec(val1:=suss,
    val2:=DeterminantMat(y));
end;

#   returns an element in the centralizer of a block with max determinant order
#   case f=f*
MatrixInCentralizerEQ@:=function(F,f,pos,sgn,A1,d,deg,c3,type)
local B1,B2,varE,H,H1,S,Star,T,_,e,forgetvar1,j1,j2,l,lm,m,pos1,suss,y;
  # rewritten select statement
  if type="unitary" then
    e:=QuoInt(Degree(F),2);
  else
    e:=0;
  fi;
  Star:=function(M)
  local exp;
    exp:=e;
    return TransposedMat(FrobeniusImage(M,exp));
  end;

  varE:=ExtStructure(F,f);
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
  B2:=Submatrix(A1,pos,pos,d*deg,d*deg);
  B1:=B2*DirectSumMat(List([1..d],j->T));
  H1:=ZeroMatrix(varE,d,d);
  #   H1 = matrix B1 over the smaller field
  #  changed: for j1, j2 in [1..d] do
  for j1 in [1..d] do
    for j2 in [1..d] do
      H1[j1][j2]:=Sum(List([1..deg],k->l^(k-1)*B1[deg*(j1-1)+1][deg*(j2-1)+k]))
       ;
    od;
  od;
  m:=TransformForm(H1,"unitary":Restore:=false);
  y:=IdentityMatrix(varE,d);
  lm:=l^-1;
  pos1:=1;
  for j1 in c3[2] do
    for j2 in [1..j1-1] do
      y[pos1][pos1+1]:=lm;
      pos1:=pos1+1;
    od;
    pos1:=pos1+1;
  od;
  #   y is the unipotent part (the centralizer is the same)
  y:=m^-1*y*m;
  S:=ElementOfMaxDeterminant@(y,StandardHermitianForm(d,varE)
   ,IdentityMatrix(varE,d),"unitary");
  S:=m*S*m^-1;
  suss:=BlockMatrix(d,d,Concatenation(List([1..d],
    j1->List([1..d],
      j2->Sum(List([1..deg],k->CompanionMat(f)^(k-1)*Eltseq(S[j1][j2],F)[k])))))
   ;
  return rec(val1:=suss,
    val2:=DeterminantMat(S));
end;

#   return flag, _ or flag, z
#   flag = true if x2, x1 are conjugate in G, and z in G such that z^-1*x2*z =
#  x1;
#   works for G = Sp, GU, SU, GO, SO, Omega (in every basis)
#   we exclude orthogonal groups in odd dimension and even characteristic
InstallGlobalFunction(GenIsConjugate@,
function(G,x2,x1)
local 
   A,A1,A2,ArrayElements,B,B1,B2,C,Cent,Checks,ConjPol,DetS,Dety,DoesNotSplit,F,
   GCD,H,IsOmega,IsOmega2,K,M,MyH,PreserveElements,Q,R,SetLog,Star,T,ThereIs,W,
   varX,X1,Y,Y1,Y2,varZ,_,a,a1,a2,b1,b2,bX,c,c1,c2,c3,d,d1,d2,deg,det,detZ,e,f,
   forgetvar1,forgetvar2,forgetvar3,i,is_abelian,j,j1,j2,k,m,m1,m2,minv,n,ni,
   num,p,pos,pos1,r1,r2,s,s1,s2,sgn,special,special2,split,suss,t,type,type1,v,
   vero,w,y,z;
  Checks:=ValueOption("Checks");
  if Checks=fail then
    Checks:=true;
  fi;
  if Checks then
    if not HaveSameType@(x2,x1) then
      return rec(val1:=false,
        val2:=_);
    fi;
    if not HaveSameLabel@(G,x2,x1) then
      return rec(val1:=false,
        val2:=_);
    fi;
  fi;
  F:=BaseRing(G);
  # Implicit generator Assg from previous line.
  w:=F.1;
  n:=Length(x1);
  e:=Degree(F);
  p:=Characteristic(F);
  sgn:=1;
  M:=MatrixAlgebra(F,n);
  t:=PolynomialRing(F).1;
  # =v= MULTIASSIGN =v=
  is_abelian:=DetermineForm@(G,x1);
  B:=is_abelian.val1;
  type:=is_abelian.val2;
  sgn:=is_abelian.val3;
  special:=is_abelian.val4;
  IsOmega:=is_abelian.val5;
  Q:=is_abelian.val6;
  is_abelian:=is_abelian.val7;
  # =^= MULTIASSIGN =^=
  if is_abelian then
    #      if x2 notin G then
    if not MyIsIn@(G,x2) then
      Error("Element is not in input group");
    else
      #   trivial case
      if x1=x2 then
        return rec(val1:=true,
          val2:=Identity(G));
      else
        return rec(val1:=false,
          val2:=_);
      fi;
    fi;
  elif IsBound(Q) then
    # =v= MULTIASSIGN =v=
    IsOmega2:=IsElementOf@(G,x2,type,B,Q);
    special2:=IsOmega2.val1;
    IsOmega2:=IsOmega2.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    IsOmega2:=IsElementOf@(G,x2,type,B,[]);
    special2:=IsOmega2.val1;
    IsOmega2:=IsOmega2.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if (special2<>special) or (IsOmega2<>IsOmega) then
    Error("Both elements do not lie in same input group");
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
  r1:=JordanForm(x1);
  a1:=r1.val1;
  b1:=r1.val2;
  r1:=r1.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  r2:=JordanForm(x2);
  a2:=r2.val1;
  b2:=r2.val2;
  r2:=r2.val3;
  # =^= MULTIASSIGN =^=
  if a1<>a2 then
    return rec(val1:=false,
      val2:=_);
  fi;
  c:=FixJordanForm@(r1,t);
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
      RemoveSet(c,[ConjPol(f),c[i][2]]); # actually Tildec!!! TODO
    fi;
    i:=i+1;
  od;
  c1:=c;
  c2:=c;
  # =v= MULTIASSIGN =v=
  forgetvar3:=JordanForm(varX);
  forgetvar1:=forgetvar3.val1;
  bX:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  d1:=bX^-1*b1;
  d2:=bX^-1*b2;
  if type<>"unitary" and type<>"symplectic" and p=2 then
    A1:=d1*Q*Star(d1);
    A2:=d2*Q*Star(d2);
  else
    A1:=d1*B*Star(d1);
    A2:=d2*B*Star(d2);
  fi;
  #   method: compute an easy form X, d1 x1 d1^-1 = X = d2 x2 d2^-1.
  #   Thus X is isometry for A1, A2 defined above. Compute Y such that Y A2 Y*
  #  = A1.
  #   Then the conjugating element is d2^-1 Y^-1 d1.
  if type in 
     ["orthogonalplus","orthogonalminus","orthogonal","orthogonalcircle"] and 
     p<>2 then
    if DeterminantMat(x1*FORCEOne(M)-1)=0 and DeterminantMat(x1*FORCEOne(M)+1)
       =0 then
      k:=Sum(c1[1][2]);
      #   the first element in c1 is t-1 or t+1
      B1:=Submatrix(A1,1,1,k,k);
      B2:=Submatrix(A2,1,1,k,k);
      if not IsSquare(DeterminantMat(B1)*DeterminantMat(B2)) then
        return rec(val1:=false,
          val2:=_);
      fi;
    fi;
  fi;
  #   turn the matrices A1, A2 into upper triangular matrices in quadratic case
  if type in 
     ["orthogonalplus","orthogonalminus","orthogonal","orthogonalcircle"] and 
     p=2 then
    for i in [1..n] do
      for j in [i+1..n] do
        A1[i][j]:=A1[i][j]+A1[j][i];
        A2[i][j]:=A2[i][j]+A2[j][i];
        A1[j][i]:=0;
        A2[j][i]:=0;
      od;
    od;
  fi;
  PreserveElements:=[];
  #   create conjugating element in GO / Sp / GU
  Y:=ZeroMatrix(F,n,n);
  pos:=1;
  i:=1;
  while i <= Size(c1) do
    f:=c1[i][1];
    d:=Sum(c1[i][2]);
    deg:=Degree(f);
    if f=ConjPol(f) and Degree(f)=1 then
      B1:=Submatrix(A1,pos,pos,d,d);
      B2:=Submatrix(A2,pos,pos,d,d);
      type1:=type;
      if type<>"unitary" and type<>"symplectic" then
        type1:=IndicateType@(B1);
      fi;
      m1:=TransformForm(B1,type1:Restore:=false);
      m2:=TransformForm(B2,type1:Restore:=false);
      if IsSemisimple(Submatrix(varX,pos,pos,d,d)) then
        InsertBlock(Y,m1*m2^-1,pos,pos); # actually TildeY!!! TODO
      else
        Y1:=m1^-1*Submatrix(varX,pos,pos,d,d)*m1;
        Y2:=m2^-1*Submatrix(varX,pos,pos,d,d)*m2;
        if type1="orthogonalplus" then
          H:=GOPlus(d,F);
          H.ClassicalType:="GO+";
        elif type1="orthogonalminus" then
          H:=GOMinus(d,F);
          H.ClassicalType:="GO-";
        elif type1="orthogonal" then
          H:=GO(d,F);
          H.ClassicalType:="GO";
        elif type1="symplectic" then
          H:=SP(d,F);
          H.ClassicalType:="Sp";
        elif type1="unitary" then
          H:=GU(d,F);
          H.ClassicalType:="GU";
        fi;
        #    Y1 is not unipotent, but -ConstantCoefficient (f)^-1*Y1 is. Result
        #  z is the same
        # =v= MULTIASSIGN =v=
        z:=InternalUnipotentIsConjugate@(H,(-ConstantCoefficient(f)^-1*Y1)
         *FORCEOne(Generic(H)),(-ConstantCoefficient(f)^-1*Y2)
         *FORCEOne(Generic(H)));
        vero:=z.val1;
        z:=z.val2;
        # =^= MULTIASSIGN =^=
        if vero then
          z:=m1*z*m2^-1;
          InsertBlock(Y,z,pos,pos); # actually TildeY!!! TODO
        else
          return rec(val1:=false,
            val2:=_);
        fi;
      fi;
      pos:=pos+d;
    elif f<>ConjPol(f) then
      ni:=Degree(f)*d;
      Y1:=Submatrix(A1,pos,pos+ni,ni,ni);
      Y2:=Submatrix(A2,pos,pos+ni,ni,ni);
      Y1:=Y1*Y2^-1;
      Y1:=DirectSumMat(Y1,IdentityMatrix(F,ni));
      InsertBlock(Y,Y1,pos,pos); # actually TildeY!!! TODO
      pos:=pos+2*ni;
    else
      ni:=deg*d;
      R:=CompanionMat(f);
      H:=GL(Degree(f),F);
      # =v= MULTIASSIGN =v=
      T:=IsConjugate(H,R*FORCEOne(H)^-1,Star(R)*FORCEOne(H));
      forgetvar1:=T.val1;
      T:=T.val2;
      # =^= MULTIASSIGN =^=
      if DeterminantMat(T+sgn*Star(T))=0 then
        T:=R*T+sgn*Star(R*T);
      else
        T:=T+sgn*Star(T);
      fi;
      T:=DirectSumMat(List([1..d],j->T));
      B1:=Submatrix(A1,pos,pos,ni,ni)*T^-1;
      B2:=Submatrix(A2,pos,pos,ni,ni)*T^-1;
      if type<>"unitary" and type<>"symplectic" and p=2 then
        B1:=B1+TransposedMat(Submatrix(A1,pos,pos,ni,ni))*T^-1;
        B2:=B2+TransposedMat(Submatrix(A2,pos,pos,ni,ni))*T^-1;
      fi;
      if IsSemisimple(Submatrix(varX,pos,pos,ni,ni)) then
        Y1:=SwitchMatrix@(B1,B2,f);
        InsertBlock(Y,Y1,pos,pos); # actually TildeY!!! TODO
      else
        K:=ExtStructure(F,f);
        # Implicit generator Assg from previous line.
        a:=K.1;
        s1:=ZeroMatrix(K,d,d);
        s2:=ZeroMatrix(K,d,d);
        #  changed: for j1, j2 in [1..d] do
        for j1 in [1..d] do
          for j2 in [1..d] do
            s1[j1][j2]:=Sum(List([1..deg],k->a^(k-1)*B1[deg*(j1-1)+1][deg*(j2-1)
             +k]));
            s2[j1][j2]:=Sum(List([1..deg],k->a^(k-1)*B2[deg*(j1-1)+1][deg*(j2-1)
             +k]));
          od;
        od;
        m1:=TransformForm(s1,"unitary":Restore:=false);
        m2:=TransformForm(s2,"unitary":Restore:=false);
        suss:=ScalarMat(d,a);
        pos1:=1;
        for c3 in c1[i][2] do
          for j in [1..c3-1] do
            suss[pos1][pos1+1]:=1;
            pos1:=pos1+1;
          od;
          pos1:=pos1+1;
        od;
        suss:=a^-1*suss;
        #   so it becomes unipotent and z is the same
        MyH:=GU(d,K);
        MyH.ClassicalType:="GU";
        # =v= MULTIASSIGN =v=
        z:=InternalUnipotentIsConjugate@(MyH,(m1^-1*suss*m1)
         *FORCEOne(Generic(MyH)),(m2^-1*suss*m2)*FORCEOne(Generic(MyH)));
        forgetvar1:=z.val1;
        z:=z.val2;
        # =^= MULTIASSIGN =^=
        z:=m1*z*m2^-1;
        varZ:=BlockMatrix(d,d,Concatenation(List([1..d],
          j1->List([1..d],
            j2->Sum(List([1..deg],k->R^(k-1)*Eltseq(z[j1][j2],F)[k])))));
        InsertBlock(Y,varZ,pos,pos); # actually TildeY!!! TODO
      fi;
      pos:=pos+ni;
    fi;
    i:=i+1;
  od;
  #   in the special case, if det (Z) ne 1, then Z need to be multiplied by Y
  #   such that x1 Y = Y x1 and det (Y) = det (Z)^-1
  varZ:=d2^-1*Y^-1*d1;
  if special or IsOmega then
    detZ:=DeterminantMat(varZ);
    if detZ<>1 then
      GCD:=List(c1,c3->Gcd(c3[2]));
      if type="unitary" then
        det:=detZ^-1;
        if Log(w^((p^e-1)*Gcd(Gcd(GCD),p^e+1)),detZ)=-1 then
          #   the determinant of Y cannot be corrected to 1
          return rec(val1:=false,
            val2:=_);
        fi;
        #   ArrayElements contains elements in the centralizer of the
        #   el.div. with determinant not equal to 1
        ArrayElements:=[];
        pos:=1;
        for i in [1..Size(c1)] do
          c3:=c1[i];
          f:=c3[1];
          deg:=Degree(f);
          d:=Sum(c3[2]);
          if f=ConjPol(f) and deg=1 then
            B1:=Submatrix(A1,pos,pos,d,d);
            y:=Submatrix(varX,pos,pos,d,d)*(-ConstantCoefficient(f))^-1;
            #   y is the unipotent part (the centralizer is the same)
            if d=1 then
              Add(ArrayElements,[w^(p^e-1)*IdentityMatrix(F,1),w^(p^e-1)]);
            else
              m:=TransformForm(B1,"unitary":Restore:=false);
              y:=ElementOfMaxDeterminant@(y,B1,m,"unitary");
              Add(ArrayElements,[y,DeterminantMat(y)]);
            fi;
            pos:=pos+d;
          elif f<>ConjPol(f) then
            # =v= MULTIASSIGN =v=
            Dety:=MatrixInCentralizerNE@(F,f,pos,A1,d,deg,c3,type);
            suss:=Dety.val1;
            Dety:=Dety.val2;
            # =^= MULTIASSIGN =^=
            Add(ArrayElements,[suss,Norm(Dety,F)^(1-p^e)]);
            pos:=pos+2*d*deg;
          else
            # =v= MULTIASSIGN =v=
            DetS:=MatrixInCentralizerEQ@(F,f,pos,sgn,A1,d,deg,c3,type);
            suss:=DetS.val1;
            DetS:=DetS.val2;
            # =^= MULTIASSIGN =^=
            Add(ArrayElements,[suss,Norm(DetS,F)]);
            pos:=pos+d*deg;
          fi;
        od;
        R:=(Integers mod (p^e+1));
        SetLog:=List(ArrayElements,y->(QuoInt(Log(w,y[2]),(p^e-1)))*FORCEOne(R))
         ;
        num:=Size(ArrayElements);
        A:=MatrixByEntries(R,num,1,SetLog);
        W:=MatrixByEntries(R,1,1,[QuoInt(Log(w,det),(p^e-1))]);
        # =v= MULTIASSIGN =v=
        v:=SolutionMat(A,W);
        forgetvar1:=v.val1;
        v:=v.val2;
        # =^= MULTIASSIGN =^=
        Y:=DirectSumMat(List( # <-list:
          [1..num],i->ArrayElements[i][1]^(Int(v[1][i]))));
        Y:=d1^-1*Y*d1;
        varZ:=varZ*Y;
      else
        if c1[1][1]<>t-1 and c1[1][1]<>t+1 then
          return rec(val1:=false,
            val2:=_);
        else
          i:=1;
          pos:=1;
          split:=false;
          if IsOddInt(GCD[1]) then
            split:=true;
            d:=Sum(c1[1][2]);
          else
            if Size(GCD) > 1 and c1[2][1] in [t-1,t+1] and IsOddInt(GCD[2]) 
               then
              split:=true;
              i:=2;
              pos:=pos+Sum(c1[1][2]);
              d:=Sum(c[2][2]);
            fi;
          fi;
          if split then
            Y:=IdentityMatrix(F,n);
            B1:=Submatrix(A1,pos,pos,d,d);
            y:=Submatrix(varX,pos,pos,d,d)*(-ConstantCoefficient(c[i][1]));
            if IsOddInt(d) then
              y:=-IdentityMatrix(F,d);
            elif IsSquare((-1*FORCEOne(F))^(QuoInt(d,2))*DeterminantMat(B1)) 
               then
              m:=TransformForm(B1,"orthogonalplus":Restore:=false);
              # =v= MULTIASSIGN =v=
              C:=ElementOfMaxDeterminant@(y,B1,m,"orthogonalplus");
              y:=C.val1;
              forgetvar2:=C.val2;
              C:=C.val3;
              # =^= MULTIASSIGN =^=
              C:=[i,C,m];
            else
              m:=TransformForm(B1,"orthogonalminus":Restore:=false);
              # =v= MULTIASSIGN =v=
              C:=ElementOfMaxDeterminant@(y,B1,m,"orthogonalminus");
              y:=C.val1;
              forgetvar2:=C.val2;
              C:=C.val3;
              # =^= MULTIASSIGN =^=
            fi;
            InsertBlock(Y,y,pos,pos); # actually TildeY!!! TODO
            #   YX=XY, detY = -1
            Y:=d1^-1*Y*d1;
            varZ:=varZ*Y;
          else
            return rec(val1:=false,
              val2:=_);
          fi;
        fi;
      fi;
    fi;
  fi;
  #   in the omega case, if SpinorNorm (Z) ne 0, then need to be multiplied by 
   Y
  #   such that x1 Y = Y x1 and SpinorNorm (Y) ne 0
  if IsOmega then
    if SpinN@(varZ*FORCEOne(GL(n,F)),Q,p)<>0 then
      if IsEvenInt(p) then
        if c1[1][1]<>t+1 then
          return rec(val1:=false,
            val2:=_);
        else
          Y:=IdentityMatrix(F,n);
          d:=Sum(c1[1][2]);
          B1:=Submatrix(A1,1,1,d,d);
          type1:=IndicateType@(B1);
          if type1="orthogonalplus" then
            m:=TransformForm(B1,"orthogonalplus":Restore:=false);
            minv:=m^-1;
            MyH:=GOPlus(d,F);
            MyH.ClassicalType:="GO+";
            Cent:=InternalUnipotentCentralizer@(MyH,(minv*Submatrix(varX,1,1,d,
             d)*m)*FORCEOne(GL(d,F)));
          else
            m:=TransformForm(B1,"orthogonalminus":Restore:=false);
            minv:=m^-1;
            MyH:=GOMinus(d,F);
            MyH.ClassicalType:="GO-";
            Cent:=InternalUnipotentCentralizer@(MyH,(minv*Submatrix(varX,1,1,d,
             d)*m)*FORCEOne(GL(d,F)));
          fi;
          split:=false;
          for i in [1..Ngens(Cent)] do
            if SpinN@(m*Cent.i*minv,B1,p)=1 then
              split:=true;
              InsertBlock(Y,m*Cent.i*minv,1,1); # actually TildeY!!! TODO
              break i;
            fi;
          od;
          if split then
            Y:=d1^-1*Y*d1;
            varZ:=varZ*Y;
          else
            return rec(val1:=false,
              val2:=_);
          fi;
        fi;
      else
        split:=false;
        Y:=IdentityMatrix(F,n);
        #   an element in DoesNotSplit is <y, SpinorNorm (y)>
        DoesNotSplit:=[];
        i:=1;
        pos:=1;
        while split=false and i <= Size(c1) do
          f:=c1[i][1];
          d:=Sum(c1[i][2]);
          deg:=Degree(f);
          if f=t-1 or f=t+1 then
            B1:=Submatrix(A1,pos,pos,d,d);
            s:=-ConstantCoefficient(f);
            X1:=s*Submatrix(varX,pos,pos,d,d);
            if true in List( # {-list:
              c1[i][2],y->IsOddInt(y)) then
              if List(Filtered(c1[i][2],y->IsOddInt(y)),y->Multiplicity(c1[i][2]
                 ,y))<>Set([1]) then
                split:=true;
                if IsBound((C)) and C[1]=i then
                  y:=ElementOfSpinorNorm1@(X1,B1:special:=true,C:=C[2],m:=C[3])
                   ;
                else
                  y:=ElementOfSpinorNorm1@(X1,B1:special:=true);
                fi;
                InsertBlock(Y,y,pos,pos); # actually TildeY!!! TODO
              else
                if IsBound((C)) and C[1]=i then
                  # =v= MULTIASSIGN =v=
                  ThereIs:=ElementOfSpinorNorm1@(X1,B1:C:=C[2],m:=C[3]);
                  y:=ThereIs.val1;
                  ThereIs:=ThereIs.val2;
                  # =^= MULTIASSIGN =^=
                else
                  # =v= MULTIASSIGN =v=
                  ThereIs:=ElementOfSpinorNorm1@(X1,B1);
                  y:=ThereIs.val1;
                  ThereIs:=ThereIs.val2;
                  # =^= MULTIASSIGN =^=
                fi;
                if ThereIs then
                  if DeterminantMat(y)=1 then
                    split:=true;
                    InsertBlock(Y,y,pos,pos); # actually TildeY!!! TODO
                  else
                    Add(DoesNotSplit,[y,1]);
                  fi;
                else
                  #   in this case y has determinant -1 and Spinor Norm 0
                  Add(DoesNotSplit,[y,0]);
                fi;
              fi;
            fi;
            pos:=pos+d;
          else
            if true in List( # {-list:
              c1[i][2],y->IsOddInt(y)) then
              split:=true;
              if f<>ConjPol(f) then
                suss:=MatrixInCentralizerNE@(F,f,pos,A1,d,deg,c1[i],type);
                InsertBlock(Y,suss,pos,pos); # actually TildeY!!! TODO
              else
                suss:=MatrixInCentralizerEQ@(F,f,pos,sgn,A1,d,deg,c1[i],type);
                InsertBlock(Y,suss,pos,pos); # actually TildeY!!! TODO
              fi;
            else
              if f<>ConjPol(f) then
                pos:=pos+2*d*deg;
              else
                pos:=pos+d*deg;
              fi;
            fi;
          fi;
          i:=i+1;
        od;
        if split=false and List( # {-list:
          DoesNotSplit,y->y[2])=Set([0,1]) then
          split:=true;
          InsertBlock(Y,DirectSumMat(List( # <-list: # actually TildeY!!! TODO
            DoesNotSplit,y->y[1])),1,1);
        fi;
        if split then
          Y:=d1^-1*Y*d1;
          varZ:=varZ*Y;
        else
          return rec(val1:=false,
            val2:=_);
        fi;
      fi;
    fi;
  fi;
  return rec(val1:=true,
    val2:=varZ*FORCEOne(GL(n,F)));
end);

ValidTypes@:=Set(["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+",
 "SO-","SO","GO+","GO-","GO"]);
IsClassicalIsConjugateApplicable@:=function(G,g,h)
#  -> ,BoolElt  Does the ClassicalIsConjugate intrinsic function apply to this
#  group
local F,V,apply,d,even,flag,form,form_type,type;
  d:=Degree(G);
  F:=BaseRing(G);
  if Type(F)<>FldFin or (d=2 and Size(F) <= 97) then
    return false;
  fi;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not flag or not (type in ValidTypes@) or not 
     MyIsIn@(G,g:Add:=Set(["SL","GL"])) or not MyIsIn@(G,h:Add:=Set(["SL","GL"])
     ) then
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
    apply:=DicksonInvariant(V,g)=0 and DicksonInvariant(V,h)=0;
    if not apply then
      return false;
    fi;
  fi;
  return true;
end;

ClassicalIsConjugate@:=function(G,g,h)
#  -> ,BoolElt ,GrpMatElt  If g and h are conjugate in classical group G ,
#  return true and a conjugating element , else false
local CB,F,Gr,d,flag,type,x;
  if not Generic(Parent(g))=Generic(G) and Generic(Parent(h))=Generic(G) then
    Error("Elements not in input group");
  fi;
  if not MyIsIn@(G,g:Add:=Set(["GL","SL"])) and MyIsIn@(G,h:Add:=Set(["GL","SL"]
     )) then
    Error("Elements not in input group");
  fi;
  if g=h then
    return rec(val1:=true,
      val2:=G.0);
  fi;
  if IsAbelian(G) then
    return rec(val1:=false,
      val2:=_);
  fi;
  if Order(g)<>Order(h) then
    return rec(val1:=false,
      val2:=_);
  fi;
  d:=Degree(G);
  F:=BaseRing(G);
  if d=2 and Size(F) <= 4 then
    return IsConjugate(G,g,h);
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
    if type="SL" then
      # =v= MULTIASSIGN =v=
      x:=SLIsConjugate@(G,g,h);
      flag:=x.val1;
      x:=x.val2;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      x:=GLIsConjugate@(G,g,h);
      flag:=x.val1;
      x:=x.val2;
      # =^= MULTIASSIGN =^=
    fi;
    if flag then
      return rec(val1:=true,
        val2:=x);
    else
      return rec(val1:=false,
        val2:=_);
    fi;
  fi;
  CB:=TransformMatrix@(G);
  Gr:=G^CB;
  Gr.ClassicalType:=G.ClassicalType;
  if (IsSemisimple(g) and IsSemisimple(h)) then
    # =v= MULTIASSIGN =v=
    x:=SSIsConjugate@(Gr,g^CB,h^CB);
    flag:=x.val1;
    x:=x.val2;
    # =^= MULTIASSIGN =^=
  elif (IsUnipotent(g) and IsUnipotent(h)) then
    # =v= MULTIASSIGN =v=
    x:=InternalUnipotentIsConjugate@(Gr,g^CB,h^CB);
    flag:=x.val1;
    x:=x.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    x:=GenIsConjugate@(Gr,g^CB,h^CB);
    flag:=x.val1;
    x:=x.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if flag then
    return rec(val1:=true,
      val2:=x^(CB^-1));
  else
    return rec(val1:=false,
      val2:=_);
  fi;
end;


