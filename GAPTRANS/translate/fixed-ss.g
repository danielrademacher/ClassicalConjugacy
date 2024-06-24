#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AddClass, Append, BaseRing, BlockMatrix,
#  CartesianProduct, Ceiling, ChangeClassLabel, ChangeLabel, Characteristic,
#  CompanionMatrix, ConjPol, ConstantCoefficient, Degree, Determinant,
#  DiagonalJoin, Eltseq, Exclude, FactoredOrder, Factorization, FrobeniusImage,
#  GF, GL, GU, Gcd, IdentityMatrix, Include, InsertBlock, Integers,
#  IsDivisibleBy, IsEven, IsOdd, IsSquare, LabelHomogenize, Lcm, Log,
#  MatrixAlgebra, Maximum, Multiplicity, Multiset, Nrows, OmegaMinus,
#  OmegaPlus, Order, Partitions, PolynomialRing, PrimitiveElement, ReverseRows,
#  Sort, StandardAlternatingForm, StandardHermitianForm, StandardQuadraticForm,
#  StandardSymmetricForm, TransformForm, Transpose, Type, UnipotentClasses,
#  ZeroMatrix

#  Defines: AddClass, AllUnipotentElementsOfS, ChangeClassLabel, ChangeLabel,
#  LabelHomogenize

DeclareGlobalFunction("AllUnipotentElementsOfS@");

DeclareGlobalFunction("ChangeClassLabel@");

#   make a label for an el. div. of type 1 or 2
#   similar to that for el. div. of type 0
LabelHomogenize@:=function(L,F,type)
local L1,varZ;
  if type in ["SU","GU"] then
    L1:=Multiset(List(L,a->a));
  elif IsEvenInt(Size(F)) then
    varZ:=Integers();
    L1:=[Sort(List(L,a->a)),[],[],[],1];
  else
    L1:=Multiset(List(L,a->[a,1*FORCEOne(F)]));
  fi;
  return L1;
end;

#   return the label of the other class in GO with same Jordan form
InstallGlobalFunction(ChangeClassLabel@,
function(L,F,pr)
local arr_dim,set_dim,setl,x;
  setl:=L;
  arr_dim:=List(Filtered(L,x->IsOddInt(x[1])),x->x[1]);
  set_dim:=List( # {-list:
    arr_dim,x->[x,Multiplicity(arr_dim,x)]);
  for x in set_dim do
    if IsOddInt(x[2]) then
      if [x[1],pr] in setl then
        RemoveSet(TILDEsetl,[x[1],pr]);
        UniteSet(TILDEsetl,[x[1],1*FORCEOne(F)]);
      else
        RemoveSet(TILDEsetl,[x[1],1*FORCEOne(F)]);
        UniteSet(TILDEsetl,[x[1],pr]);
      fi;
    fi;
  od;
  return setl;
end);

#   change the label of a unipotent element in GO (n, q) for odd n
#   by switching all the discriminants
#   if DoIt eq false, then return L without changing it
ChangeLabel@:=function(L,F,pr,DoIt)
local setl;
  if not DoIt then
    return L;
  else
    setl:=ChangeClassLabel@(L[3],F,pr);
    return [L[1],L[2],Multiset(setl)];
  fi;
end;

#   return an element in GO with determinant -1 in the centralizer
#   of the semisimple part defined by c, where c, L are the lists
#   described in AllUnipotentElementsOfS
AddClass@:=function(type,L,c,m,F,n)
local C,varE,IsOmega,Y,_,d,done,e,f,forgetvar1,i,k,l,pos,pr,q,w,y,z;
  IsOmega:=ValueOption("IsOmega");
  if IsOmega=fail then
    IsOmega:=false;
  fi;
  pos:=1;
  done:=false;
  Y:=IdentityMatrix(F,n);
  for i in [1..Size(c)] do
    if L[i][3]=0 then
      if IsOmega then
        d:=L[i][2];
        z:=IdentityMatrix(F,d);
        if d=1 then
          pos:=pos+1;
        elif d=2 then
          z:=SOElement(2,F:Minus:=IndicateType@(c[i][4])="orthogonalminus");
          InsertBlock(TILDEY,z,pos,pos);
          done:=true;
          break i;
        else
          if IsOddInt(Size(F)) then
            pr:=PrimitiveElement(F);
            z[1][1]:=pr;
            z[d][d]:=pr^-1;
          else
            z[1][1]:=0;
            z[d][d]:=0;
            z[d][1]:=1;
            z[1][d]:=1;
          fi;
          InsertBlock(TILDEY,z,pos,pos);
          done:=true;
          break i;
        fi;
      elif type="SU" then
        w:=PrimitiveElement(F);
        # =v= MULTIASSIGN =v=
        q:=IsSquare(Size(F));
        forgetvar1:=q.val1;
        q:=q.val2;
        # =^= MULTIASSIGN =^=
        k:=L[i][2];
        if k=1 then
          Y[1][1]:=w^(q-1);
        else
          Y[1][1]:=w^q;
          Y[k][k]:=w^-1;
        fi;
        done:=true;
        break i;
      else
        if L[i][2]=2 then
          z:=GOElement(2,F:Minus:=IndicateType@(c[i][4])="orthogonalminus");
          InsertBlock(TILDEY,z,pos,pos);
        else
          #   an element of det -1
          Y[pos][pos]:=0;
          Y[pos+L[i][2]-1][pos+L[i][2]-1]:=0;
          Y[pos][pos+L[i][2]-1]:=1;
          Y[pos+L[i][2]-1][pos]:=1;
        fi;
        done:=true;
        break i;
      fi;
    elif L[i][3]=1 then
      if IsOmega or type="SU" then
        f:=L[i][1];
        d:=Degree(f);
        C:=CompanionMat(f);
        varE:=ExtStructure(F,f:Optimize:=false);
        # Implicit generator Assg from previous line.
        l:=varE.1;
        w:=PrimitiveElement(varE);
        y:=Sum(List([1..d],j->Eltseq(w,F)[j]*C^(j-1)));
        InsertBlock(TILDEY,y,pos,pos);
        if type="SU" then
          e:=QuoInt(Degree(F),2);
          InsertBlock(TILDEY,TransposedMat(FrobeniusImage(y^-1,e)),pos+L[i][2]
           *d,pos+L[i][2]*d);
        else
          InsertBlock(TILDEY,TransposedMat(y^-1),pos+L[i][2]*d,pos+L[i][2]*d);
        fi;
        done:=true;
        break i;
      else
        pos:=pos+2*L[i][2]*Degree(L[i][1]);
      fi;
    else
      if IsOmega or type="SU" then
        f:=L[i][1];
        d:=Degree(f);
        k:=L[i][2];
        C:=CompanionMat(f);
        varE:=ExtStructure(F,f:Optimize:=false);
        # Implicit generator Assg from previous line.
        l:=varE.1;
        w:=PrimitiveElement(varE);
        if type="SU" then
          # =v= MULTIASSIGN =v=
          q:=IsSquare(Size(F));
          forgetvar1:=q.val1;
          q:=q.val2;
          # =^= MULTIASSIGN =^=
          q:=q^d;
        else
          q:=(Size(F))^(QuoInt(d,2));
        fi;
        if k=1 then
          w:=w^(q-1);
          y:=Sum(List([1..d],j->Eltseq(w,F)[j]*C^(j-1)));
          InsertBlock(TILDEY,y,pos,pos);
        else
          y:=Sum(List([1..d],j->Eltseq(w^q,F)[j]*C^(j-1)));
          InsertBlock(TILDEY,y,pos,pos);
          y:=Sum(List([1..d],j->Eltseq(w^-1,F)[j]*C^(j-1)));
          InsertBlock(TILDEY,y,pos+d*(k-1),pos+d*(k-1));
        fi;
        done:=true;
        break i;
      else
        pos:=pos+L[i][2]*Degree(L[i][1]);
      fi;
    fi;
  od;
  #   this happens only when x^2-1 is nonsingular and IsOmega eq false
  if done=false then
    if n=2 then
      Y:=GOElement(2,F:Minus:=type in ["SO-","Omega-"]);
    else
      Y[1][1]:=0;
      Y[1][n]:=1;
      Y[n][1]:=1;
      Y[n][n]:=0;
    fi;
  else
    Y:=m^-1*Y*m;
  fi;
  return Y;
end;

#   L is a vector [ <f1, m1>, <f2, m2>, ... , <fk, mk>],
#   where f_i irreducible polynomial, m_i its multiplicity;
#   if f_i neq f_i*, the function provides automatically
#   to put the elementary divisor f_i*;
#   elements of L could also have the form <fi, mi, type, Bi>,
#   with type = 0, 1, 2 (resp. (t pm 1), ff* and f=f*) and
#   Bi matrix of the form preserved by f_i
#   if missing, this data is added at the start of the code;
#   the function returns all conjugacy classes having semisimple part
#   described by L in the standard MAGMA copy;
#   if the parameter SameSSPart is true, then the semisimple part is
#   the same for all the representatives.
#   Assumptions:
#   StandardSymmetricForm (n, q: Variant := "Default")
#   for odd n and q the determinant is GF(q) ! ((-1)^((n-1) div 2) * (1/2))

#   _, _, _, _, Forms := UnipotentClasses ("GO", n, q);
#   for odd n and odd q, the elements in Forms have square determinant
#   this is checked in UnipotentClasses
InstallGlobalFunction(AllUnipotentElementsOfS@,
function(type,L)
local 
   AddClasses,AddClassesOmega,B,C,Card,CardOfG,ConjClasses,ConjLabel,ConjPol,
   DataArray,DetForm,DoIt,Double,F,Form,GCD,H,IsMinus,K,L,L1,M,MultToChange,P,
   P1,PosMinus,PosPlus,R,R1,R1label,Repr,S,SN,SameSSPart,Sm,Sp,
   SplitClassesOmega,SplitClassesSO,StdForm,Stdform1,T,ThereIsMinus,ThereIsPlus,
   TypeOfMinus,TypeOfPlus,UC,UCForm,UCL,UCRepr,UCT,UCm,UCmForm,UCmL,UCmRepr,
   UCmT,UCp,UCpForm,UCpL,UCpRepr,UCpT,XLabel,Y,_,c,c1,card,card1,coeff,d,delta,
   det,e,f,forgetvar1,h,i,ind,information,is2sq,is_omega,j,l,label,lambda,m,n,
   ord,ord1,p,pos,pr,q,quadratic,s,sgn,sign,special,t,temp,type,type1,typeofx,u,
   unitary,w,x,y,z;
  SameSSPart:=ValueOption("SameSSPart");
  if SameSSPart=fail then
    SameSSPart:=false;
  fi;
  DataArray:=ValueOption("DataArray");
  if DataArray=fail then
    DataArray:=[];
  fi;
  CardOfG:=ValueOption("CardOfG");
  if CardOfG=fail then
    CardOfG:=1;
  fi;
  F:=BaseRing(L[1][1]);
  q:=Size(F);
  p:=Characteristic(F);
  e:=QuoInt(Degree(F),2);
  unitary:=1;
  if type in ["GU","SU"] then
    # =v= MULTIASSIGN =v=
    q:=IsSquare(q);
    forgetvar1:=q.val1;
    q:=q.val2;
    # =^= MULTIASSIGN =^=
    unitary:=q;
    #  Star := func<M : exp := e | Transpose (FrobeniusImage (M, exp))>;
  else
    #  Star := func<M | Transpose (M)>;
  fi;
  pr:=PrimitiveElement(F);
  t:=PolynomialRing(F).1;
  ConjPol:=ConjugatePolynomial@(unitary=q);
  #   add information if L is incomplete
  information:=false;
  if Size(L[1])=4 then
    information:=true;
  fi;
  if information=false then
    L1:=# [*-list:
    [];
    for x in L do
      f:=x[1];
      if f=ConjPol(f) then
        if Degree(f)=1 then
          y:=[f,x[2],0,IdentityMatrix(F,1)];
        else
          y:=[f,x[2],2,FormForCompanionMatrix@(f,type)];
        fi;
      else
        y:=[f,x[2],1,IdentityMatrix(F,2)];
      fi;
      #   the value of y[4] is important only if y[3]=2
      Add(L1,y);
    od;
    L:=L1;
  fi;
  n:=Sum(List(L,x->Degree(x[1])*x[2]*(1+x[3] mod 2)));
  #   dimension
  #   AddClasses = matrix in GU(n, q) with determinant w^(q-1)
  if type="Sp" then
    sgn:=-1*FORCEOne(F);
  else
    sgn:=1*FORCEOne(F);
  fi;
  if type="SU" then
    det:=1;
    for x in L do
      if x[3]=1 then
        det:=det*DeterminantMat(CompanionMat(x[1]))^((1-q)*x[2]);
      else
        det:=det*DeterminantMat(CompanionMat(x[1]))^x[2];
      fi;
    od;
    if det<>1 then
      return rec(val1:=# [*-list:
      [],
        val2:=# [*-list:
      []);
    else
      AddClasses:=IdentityMatrix(F,n);
      AddClasses[1][1]:=pr^-1;
      AddClasses[n][n]:=pr^q;
    fi;
  fi;
  if type="GO+" or (type="SO+" and IsEvenInt(q)) then
    type:="O+";
  fi;
  if type="GO-" or (type="SO-" and IsEvenInt(q)) then
    type:="O-";
  fi;
  if type="GO" then
    type:="O";
  fi;
  quadratic:=false;
  if type in ["O+","O-","Omega+","Omega-"] and IsEvenInt(q) then
    quadratic:=true;
  fi;
  #   need this constant for 1-dimensional symmetric forms
  # rewritten select statement
  if SameSSPart then
    Stdform1:=2;
  else
    Stdform1:=1;
  fi;
  #   AddClasses = matrix in GO(n, q) with determinant -1
  special:=false;
  if type in ["SO","SO+","SO-","Omega","Omega+","Omega-"] then
    special:=true;
    if n=2 then
      AddClasses:=GOElement(2,F:Minus:=type in ["SO-","Omega-"]);
    else
      AddClasses:=IdentityMatrix(F,n);
      AddClasses[1][1]:=0;
      AddClasses[n][n]:=0;
      AddClasses[1][n]:=1;
      AddClasses[n][1]:=1;
    fi;
  fi;
  R:=[];
  Double:=false;
  if type in ["O+","O-","O","SO+","SO-","SO","Omega+","Omega-","Omega"] then
    ThereIsPlus:=false;
    ThereIsMinus:=false;
    sign:=1;
    for x in L do
      if x[3]=0 then
        if ConstantCoefficient(x[1])=1 then
          ThereIsMinus:=true;
          if special and IsOddInt(x[2]) then
            return rec(val1:=# [*-list:
            [],
              val2:=# [*-list:
            []);
          fi;
        else
          ThereIsPlus:=true;
        fi;
      elif x[3]=2 then
        sign:=sign*(-1)^x[2];
      fi;
    od;
    if ThereIsPlus and ThereIsMinus then
      R1:=[];
      R1label:=[];
      #   corresponding to the two types of subspaces of t+1 and t-1
      Double:=true;
    fi;
  fi;
  #   check if the semisimple part is in Omega
  if type in ["Omega","Omega+","Omega-"] and IsOddInt(q) then
    SN:=0*FORCEOne(GF(2));
    #   spinor norm
    for i in [1..Size(L)] do
      x:=L[i];
      if x[3]=0 then
        if ConstantCoefficient(x[1])=1 then
          if ThereIsPlus then
            PosMinus:=i;
          else
            if (sign=-1xortype="Omega+")xorIsEvenInt(QuoInt(x[2]*(q-1),4)) then
              SN:=SN+1;
            fi;
          fi;
        else
          if ThereIsMinus then
            PosPlus:=i;
          fi;
        fi;
      elif x[3]=1 and IsOddInt(x[2]) then
        C:=CompanionMat(x[1]);
        if not IsSquare(DeterminantMat(C)) then
          SN:=SN+1;
        fi;
      elif x[3]=2 and IsOddInt(x[2]) then
        C:=CompanionMat(x[1]);
        if not IsDivisibleBy(QuoInt((q^(QuoInt(Degree(x[1]),2))+1),2),Order(C)) 
           then
          SN:=SN+1;
        fi;
      fi;
    od;
    if not Double and SN=1 then
      #   in such a case the semisimple part has spinor norm 1
      return rec(val1:=# [*-list:
      [],
        val2:=# [*-list:
      []);
    fi;
    if Double then
      # rewritten select statement
      if (SN=0xorIsOddInt(QuoInt((q-1)*L[PosMinus][2],4))) then
        TypeOfMinus:="plus";
      else
        TypeOfMinus:="minus";
      fi;
      # rewritten select statement
      if ((type="Omega+"xorsign=-1)xorTypeOfMinus="minus") then
        TypeOfPlus:="plus";
      else
        TypeOfPlus:="minus";
      fi;
    fi;
  fi;
  is_omega:=false;
  if type in ["Omega","Omega+","Omega-"] then
    is_omega:=true;
    z:=IdentityMatrix(F,n);
    if n=2 then
      z:=SOElement(2,F:Minus:=type="Omega-");
    else
      if IsOddInt(q) then
        z[1][1]:=pr;
        z[n][n]:=pr^-1;
      else
        z[1][1]:=0;
        z[n][n]:=0;
        z[n][1]:=1;
        z[1][n]:=1;
      fi;
    fi;
    AddClassesOmega:=z;
  fi;
  #   save unipotent classes
  if type in ["O+","O-","O","SO+","SO-","SO","Omega+","Omega-","Omega"] then
    UCp:=DataArray[1];
    UCpRepr:=DataArray[2];
    UCpForm:=DataArray[3];
    UCpT:=DataArray[4];
    UCpL:=DataArray[5];
    UCm:=DataArray[6];
    UCmRepr:=DataArray[7];
    UCmForm:=DataArray[8];
    UCmT:=DataArray[9];
    UCmL:=DataArray[10];
    if IsOddInt(q) and not (type in ["SO+","SO-","Omega+","Omega-"]) then
      UC:=DataArray[11];
      UCRepr:=DataArray[12];
      UCForm:=DataArray[13];
      UCT:=DataArray[14];
      UCL:=DataArray[15];
    fi;
  elif type in ["Sp","SU","GU"] then
    UC:=DataArray[1];
    UCRepr:=DataArray[2];
    UCForm:=DataArray[3];
    UCT:=DataArray[4];
    UCL:=DataArray[5];
  fi;
  #   multiply by a non-square scalar the form corresponding to f = t \pm 1
  #  with even multiplicity
  #   whenever the discriminant of the global assembled form does not fit the
  #  discriminant of the standard Magma form;
  #   without this passage, the unipotent label computed on the eigenspace(f)
  #  would switch classes when f^d has odd multiplicity for
  #   at least two odd values of d
  if type in ["O","SO","Omega"] then
    DetForm:=1;
    #   1 if square, -1 otherwise
    MultToChange:=0;
    for l in L do
      if q mod 4=1 then
        if l[3]=2 and IsOddInt(l[2]) then
          DetForm:=DetForm*-1;
        fi;
      else
        if IsOddInt(l[2]) and ((l[3]=2 and Degree(l[1]) mod 4=0) or (l[3]=1 and 
           IsOddInt(Degree(l[1])))) then
          DetForm:=DetForm*-1;
        fi;
      fi;
      if l[3]=0 and IsEvenInt(l[2]) then
        MultToChange:=l[2];
      fi;
    od;
    #   condition for Determinant(StandardSymmetricForm(n,q)) to be a square
    if (((q mod 8 in [1,3] and n mod 4=3) or (q mod 8 in [1,7] and n mod 4=1))
       xorDetForm=-1)xor(q mod 4=3 and MultToChange mod 4=2) then
      for i in [1..Size(UCmForm)] do
        for j in [1..Size(UCmForm[i])] do
          UCmForm[i][j]:=UCmForm[i][j]*pr;
        od;
      od;
    else
      for i in [1..Size(UCpForm)] do
        for j in [1..Size(UCpForm[i])] do
          UCpForm[i][j]:=UCpForm[i][j]*pr;
        od;
      od;
    fi;
  fi;
  if type="Sp" then
    UCL:=List( # <-list:
      UCL,l->List( # {@-list:
      l,x->[x]));
  fi;
  #   add "ns" for consistency with the others
  #   CardOfG: cardinality of the group of isometries
  #   computed if not passed as parameter
  if Type(CardOfG)=RngIntElt then
    CardOfG:=IsometryGroupCardinality@(type,n,q);
  fi;
  #   TypeOfMinus := sign of the form correspondent to the el.div. t+1
  #   TypeOfPlus := sign of the form correspondent to the el.div. t-1
  #   if both t+1 and t-1 are el.div., then SN is the spinor norm of the part
  #  of degree gt 1
  #   AddClassesOmega = element in SO with SpinorNorm 1 to write classes in SO
  #  splitting in Omega
  ConjClasses:=# [*-list:
  [];
  ConjLabel:=# [*-list:
  [];
  for x in L do
    f:=x[1];
    ind:=x[3];
    if ind=0 then
      d:=x[2];
      w:=-ConstantCoefficient(x[1]);
      if type in ["GU","SU"] then
        M:=MatrixAlgebra(F,d);
        ord:=Order(w);
        card:=CardinalityOfClassicalGroup@("GU",d,q);
        if SameSSPart then
          Repr:=UC[d];
          T:=UCT[d];
          B:=StandardHermitianForm(d,q);
          Form:=List([1..Size(Repr)],j->B);
          label:=UCL[d];
        else
          Repr:=UCRepr[d];
          Form:=UCForm[d];
          T:=UCT[d];
          label:=UCL[d];
        fi;
        label:=List( # {@-list:
          label,l->LabelHomogenize@(l,F,type));
        label:=List( # {@-list:
          label,l->[0,f,l]);
        if type="SU" then
          S:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2],card],w*Repr[j]
           [3]*FORCEOne(M),Form[j],Gcd(T[j]),label[j]]);
        else
          S:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2],card],w*Repr[j]
           [3]*FORCEOne(M),Form[j],label[j]]);
        fi;
        Add(R,S);
      elif quadratic then
        if type in ["O+","Omega+"]xorsign=-1 then
          if is_omega and d=2 then
            label:=[0,f,UCpL[1][1]];
            #  these three
            S:=[[1,[1,FactoredOrder(OmegaPlus(2,q))],IdentityMatrix(F,2)
             ,StandardQuadraticForm(2,q:Variant:="Default"),label]];
          else
            if SameSSPart then
              Repr:=UCp[QuoInt(d,2)];
              StdForm:=StandardQuadraticForm(d,q:Variant:="Default");
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCpL[QuoInt(d,2)],l->[0,f,l]);
            else
              Repr:=UCpRepr[QuoInt(d,2)];
              Form:=UCpForm[QuoInt(d,2)];
              label:=List( # {@-list:
                UCpL[QuoInt(d,2)],l->[0,f,l]);
            fi;
            if is_omega then
              card:=CardinalityOfClassicalGroup@("Omega+",d,q);
            else
              card:=CardinalityOfClassicalGroup@("GO+",d,q);
            fi;
            S:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j][3]
             ,Form[j],Repr[j][1],label[j]]);
          fi;
        else
          if is_omega and d=2 then
            label:=[0,f,UCmL[1][1]];
            S:=[[1,[1,FactoredOrder(OmegaMinus(2,q))],IdentityMatrix(F,2)
             ,StandardQuadraticForm(2,q:Minus:=true,Variant:="Default"),label]]
             ;
          else
            if SameSSPart then
              Repr:=UCm[QuoInt(d,2)];
              StdForm:=StandardQuadraticForm(d,q:Minus:=true,Variant:="Default")
               ;
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCmL[QuoInt(d,2)],l->[0,f,l]);
            else
              Repr:=UCmRepr[QuoInt(d,2)];
              Form:=UCmForm[QuoInt(d,2)];
              label:=List( # {@-list:
                UCmL[QuoInt(d,2)],l->[0,f,l]);
            fi;
            if is_omega then
              card:=CardinalityOfClassicalGroup@("Omega-",d,q);
            else
              card:=CardinalityOfClassicalGroup@("GO-",d,q);
            fi;
            S:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j][3]
             ,Form[j],label[j]]);
          fi;
        fi;
        Add(R,S);
      elif type in ["Omega+","Omega-"] then
        if (w=1 and ThereIsMinus) or (w=-1 and ThereIsPlus) then
          # rewritten select statement
          if w=1 then
            typeofx:=TypeOfPlus;
          else
            typeofx:=TypeOfMinus;
          fi;
          if typeofx="plus" then
            Repr:=UCpRepr[QuoInt(d,2)];
            Form:=UCpForm[QuoInt(d,2)];
            T:=UCpT[QuoInt(d,2)];
            label:=List( # {@-list:
              UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
            type1:="orthogonalplus";
            IsMinus:=false;
          else
            Repr:=UCmRepr[QuoInt(d,2)];
            Form:=UCmForm[QuoInt(d,2)];
            T:=UCmT[QuoInt(d,2)];
            label:=List( # {@-list:
              UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
            type1:="orthogonalminus";
            IsMinus:=true;
          fi;
        else
          if type="Omega+"xorsign=-1 then
            Repr:=UCpRepr[QuoInt(d,2)];
            Form:=UCpForm[QuoInt(d,2)];
            T:=UCpT[QuoInt(d,2)];
            label:=List( # {@-list:
              UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
            type1:="orthogonalplus";
            IsMinus:=false;
          else
            Repr:=UCmRepr[QuoInt(d,2)];
            Form:=UCmForm[QuoInt(d,2)];
            T:=UCmT[QuoInt(d,2)];
            label:=List( # {@-list:
              UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
            type1:="orthogonalminus";
            IsMinus:=true;
          fi;
        fi;
        card:=CardinalityOfClassicalGroup@(type1,d,q);
        if SameSSPart then
          S:=[];
          StdForm:=StandardSymmetricForm(d,q:Minus:=IsMinus,Variant:="Default")
           ;
          for j in [1..Size(Repr)] do
            m:=TransformForm(Form[j],type1:Restore:=false);
            if w=1 then
              Add(S,[Repr[j][1],[Repr[j][2],card],Repr[j][3],Form[j],T[j]
               ,m^-1*Repr[j][3]*m,StdForm,label[j]]);
            else
              Add(S,[2*Repr[j][1],[Repr[j][2],card],-Repr[j][3],Form[j],T[j]
               ,-m^-1*Repr[j][3]*m,StdForm,label[j]]);
            fi;
          od;
        else
          if w=1 then
            S:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j][3]
             ,Form[j],T[j],label[j]]);
          else
            S:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card],-Repr[j]
             [3],Form[j],T[j],label[j]]);
          fi;
        fi;
        Add(R,S);
      elif type in ["O+","O-","SO+","SO-"] then
        if (w=-1 and ThereIsPlus) or (w=1 and ThereIsMinus) then
          if d=1 then
            # rewritten select statement
            if SameSSPart or q mod 8 in [1,7] then
              is2sq:=1*FORCEOne(F);
            else
              is2sq:=pr;
            fi;
            #   2 is a square in GF(q) iff q mod 8 = 1 or 7
            if w=1 then
              lvarSp:=[[1,[1,Factorization(2)],IdentityMatrix(F,1)
               ,Stdform1*IdentityMatrix(F,1),[1],[0,f,[[1,is2sq]]]]];
              Sm:=[[1,[1,Factorization(2)],IdentityMatrix(F,1)
               ,Stdform1*pr*IdentityMatrix(F,1),[1],[0,f,[[1,pr/is2sq]]]]];
            else
              lvarSp:=[[2,[1,Factorization(2)],-IdentityMatrix(F,1)
               ,Stdform1*IdentityMatrix(F,1),[1],[0,f,[[1,is2sq]]]]];
              Sm:=[[2,[1,Factorization(2)],-IdentityMatrix(F,1)
               ,Stdform1*pr*IdentityMatrix(F,1),[1],[0,f,[[1,pr/is2sq]]]]];
            fi;
          elif IsEvenInt(d) then
            if SameSSPart then
              Repr:=UCp[QuoInt(d,2)];
              T:=UCpT[QuoInt(d,2)];
              StdForm:=StandardSymmetricForm(d,q:Variant:="Default");
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
            else
              Repr:=UCpRepr[QuoInt(d,2)];
              Form:=UCpForm[QuoInt(d,2)];
              T:=UCpT[QuoInt(d,2)];
              label:=List( # {@-list:
                UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
            fi;
            card:=CardinalityOfClassicalGroup@("GO+",d,q);
            if w=1 then
              lvarSp:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card]
               ,Repr[j][3],Form[j],T[j],label[j]]);
            else
              lvarSp:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card]
               ,-Repr[j][3],Form[j],T[j],label[j]]);
            fi;
            if SameSSPart then
              Repr:=UCm[QuoInt(d,2)];
              T:=UCmT[QuoInt(d,2)];
              StdForm:=StandardSymmetricForm(d,q:Minus:=true,Variant:="Default")
               ;
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
            else
              Repr:=UCmRepr[QuoInt(d,2)];
              Form:=UCmForm[QuoInt(d,2)];
              T:=UCmT[QuoInt(d,2)];
              label:=List( # {@-list:
                UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
            fi;
            card:=CardinalityOfClassicalGroup@("GO-",d,q);
            if w=1 then
              Sm:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j]
               [3],Form[j],T[j],label[j]]);
            else
              Sm:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card]
               ,-Repr[j][3],Form[j],T[j],label[j]]);
            fi;
          else
            if SameSSPart then
              Repr:=UC[QuoInt(d,2)+1];
              T:=UCT[QuoInt(d,2)+1];
              StdForm:=StandardSymmetricForm(d,q:Variant:="Default");
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCL[QuoInt(d,2)+1],l->[0,f,l[1]]);
            else
              Repr:=UCRepr[QuoInt(d,2)+1];
              Form:=UCForm[QuoInt(d,2)+1];
              T:=UCT[QuoInt(d,2)+1];
              label:=List( # {@-list:
                UCL[QuoInt(d,2)+1],l->[0,f,l[1]]);
            fi;
            # rewritten select statement
            if SameSSPart then
              delta:=1;
            else
              delta:=(-1)^(QuoInt(d,2));
            fi;
            DoIt:=q mod 4=3 and d mod 4=3;
            #   equivalent condition to not IsSquare (Determinant
            #  (delta*Form[j]))
            card:=CardinalityOfClassicalGroup@("GO",d,q);
            if w=1 then
              lvarSp:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card]
               ,Repr[j][3],delta*Form[j],T[j],ChangeLabel@(label[j],F,pr,DoIt)])
               ;
              Sm:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j]
               [3],delta*pr*Form[j],T[j],ChangeLabel@(label[j],F,pr,not DoIt)])
               ;
            else
              lvarSp:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card]
               ,-Repr[j][3],delta*Form[j],T[j],ChangeLabel@(label[j],F,pr,DoIt)]
               );
              Sm:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card]
               ,-Repr[j][3],delta*pr*Form[j],T[j],ChangeLabel@(label[j]
               ,F,pr,not DoIt)]);
            fi;
          fi;
          if w=1 or ((type in ["O+","SO+"]xorsign=-1)xor(q mod 4=3 and 
             IsOddInt(d))) then
            Add(R,lvarSp);
            Add(R1,Sm);
          else
            Add(R,Sm);
            Add(R1,lvarSp);
          fi;
        else
          if type in ["O+","SO+"]xorsign=-1 then
            if SameSSPart then
              Repr:=UCp[QuoInt(d,2)];
              T:=UCpT[QuoInt(d,2)];
              StdForm:=StandardSymmetricForm(d,q:Variant:="Default");
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
            else
              Repr:=UCpRepr[QuoInt(d,2)];
              Form:=UCpForm[QuoInt(d,2)];
              T:=UCpT[QuoInt(d,2)];
              label:=List( # {@-list:
                UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
            fi;
            card:=CardinalityOfClassicalGroup@("GO+",d,q);
            if w=1 then
              S:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j]
               [3],Form[j],T[j],label[j]]);
            else
              S:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card]
               ,-Repr[j][3],Form[j],T[j],label[j]]);
            fi;
            Add(R,S);
          else
            if SameSSPart then
              Repr:=UCm[QuoInt(d,2)];
              T:=UCmT[QuoInt(d,2)];
              StdForm:=StandardSymmetricForm(d,q:Minus:=true,Variant:="Default")
               ;
              Form:=List([1..Size(Repr)],i->StdForm);
              label:=List( # {@-list:
                UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
            else
              Repr:=UCmRepr[QuoInt(d,2)];
              Form:=UCmForm[QuoInt(d,2)];
              T:=UCmT[QuoInt(d,2)];
              label:=List( # {@-list:
                UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
            fi;
            card:=CardinalityOfClassicalGroup@("GO-",d,q);
            if w=1 then
              S:=List([1..Size(Repr)],j->[Repr[j][1],[Repr[j][2],card],Repr[j]
               [3],Form[j],T[j],label[j]]);
            else
              S:=List([1..Size(Repr)],j->[2*Repr[j][1],[Repr[j][2],card]
               ,-Repr[j][3],Form[j],T[j],label[j]]);
            fi;
            Add(R,S);
          fi;
        fi;
      else
        w:=-ConstantCoefficient(f);
        if d=1 then
          # rewritten select statement
          if q mod 8 in [1,7] then
            lambda:=1*FORCEOne(F);
          else
            lambda:=pr;
          fi;
          # rewritten select statement
          if type in ["SU","GU"] then
            temp:=1;
          else
            temp:=[1,lambda];
          fi;
          S:=[[Order(w),[1,Factorization(2)],w*IdentityMatrix(F,1)
           ,IdentityMatrix(F,1),[1],[0,f,[temp]]]];
        else
          ord:=Order(w);
          if type="Sp" then
            type1:="Sp";
          elif type in ["GU","SU"] then
            type1:="GU";
          else
            type1:="GO";
          fi;
          M:=MatrixAlgebra(F,d);
          if type in ["O","SO","Omega"] and IsEvenInt(d) then
            lvarSp:=[];
            Sm:=[];
            if type="Omega" then
              if TypeOfMinus="plus" then
                Repr:=UCpRepr[QuoInt(d,2)];
                Form:=UCpForm[QuoInt(d,2)];
                T:=UCpT[QuoInt(d,2)];
                label:=List( # {@-list:
                  UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
                card:=CardinalityOfClassicalGroup@("GO+",d,q);
                if SameSSPart then
                  StdForm:=StandardSymmetricForm(d,q:Variant:="Default");
                  for j in [1..Size(Repr)] do
                    m:=TransformForm(Form[j],"orthogonalplus":Restore:=false);
                    Add(lvarSp,[ord*Repr[j][1],[Repr[j][2],card],w*Repr[j][3]
                     *FORCEOne(M),Form[j],T[j],w*(m^-1*Repr[j][3]*m)*FORCEOne(M)
                     ,StdForm,label[j]]);
                  od;
                else
                  lvarSp:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2]
                   ,card],w*Repr[j][3]*FORCEOne(M),Form[j],T[j],label[j]]);
                fi;
              else
                Repr:=UCmRepr[QuoInt(d,2)];
                Form:=UCmForm[QuoInt(d,2)];
                T:=UCmT[QuoInt(d,2)];
                label:=List( # {@-list:
                  UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
                card:=CardinalityOfClassicalGroup@("GO-",d,q);
                if SameSSPart then
                  StdForm:=StandardSymmetricForm(d,q:Minus:=true,
                   Variant:="Default");
                  for j in [1..Size(Repr)] do
                    m:=TransformForm(Form[j],"orthogonalminus":Restore:=false);
                    Add(lvarSp,[ord*Repr[j][1],[Repr[j][2],card],w*Repr[j][3]
                     *FORCEOne(M),Form[j],T[j],w*(m^-1*Repr[j][3]*m)*FORCEOne(M)
                     ,StdForm,label[j]]);
                  od;
                else
                  lvarSp:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2]
                   ,card],w*Repr[j][3]*FORCEOne(M),Form[j],T[j],label[j]]);
                fi;
              fi;
            else
              if SameSSPart then
                Repr:=UCp[QuoInt(d,2)];
                T:=UCpT[QuoInt(d,2)];
                label:=List( # {@-list:
                  UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
                StdForm:=StandardSymmetricForm(d,q:Variant:="Default");
                Form:=List([1..Size(Repr)],i->StdForm);
              else
                Repr:=UCpRepr[QuoInt(d,2)];
                Form:=UCpForm[QuoInt(d,2)];
                T:=UCpT[QuoInt(d,2)];
                label:=List( # {@-list:
                  UCpL[QuoInt(d,2)],l->[0,f,l[1]]);
              fi;
              card:=CardinalityOfClassicalGroup@("GO+",d,q);
              lvarSp:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2],card]
               ,w*Repr[j][3]*FORCEOne(M),Form[j],T[j],label[j]]);
              if SameSSPart then
                Repr:=UCm[QuoInt(d,2)];
                T:=UCmT[QuoInt(d,2)];
                StdForm:=StandardSymmetricForm(d,q:Minus:=true,
                 Variant:="Default");
                Form:=List([1..Size(Repr)],i->StdForm);
                label:=List( # {@-list:
                  UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
              else
                Repr:=UCmRepr[QuoInt(d,2)];
                Form:=UCmForm[QuoInt(d,2)];
                T:=UCmT[QuoInt(d,2)];
                label:=List( # {@-list:
                  UCmL[QuoInt(d,2)],l->[0,f,l[1]]);
              fi;
              card:=CardinalityOfClassicalGroup@("GO-",d,q);
              Sm:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2],card]
               ,w*Repr[j][3]*FORCEOne(M),Form[j],T[j],label[j]]);
            fi;
            S:=Concatenation(lvarSp,Sm);
          else
            if SameSSPart then
              if type="Omega" then
                Repr:=UCRepr[QuoInt(d,2)+1];
                Form:=UCForm[QuoInt(d,2)+1];
                T:=UCT[QuoInt(d,2)+1];
                label:=List( # {@-list:
                  UCL[QuoInt(d,2)+1],l->[0,f,l[1]]);
                S:=[];
                if (q mod 8 in [1,3] and d mod 4=3) or (q mod 8 in [1,7] and d 
                   mod 4=1) then
                  coeff:=1;
                else
                  coeff:=pr;
                fi;
                #   multiplication by coeff needed to have
                #  Discriminant(StdForm) = square
                StdForm:=coeff*StandardSymmetricForm(d,q:Variant:="Default");
                card:=CardinalityOfClassicalGroup@("GO",d,q);
                for j in [1..Size(Repr)] do
                  m:=TransformForm(Form[j],"orthogonal":Restore:=false);
                  Add(S,[ord*Repr[j][1],[Repr[j][2],card],w*Repr[j][3]
                   *FORCEOne(M),Form[j],T[j],w*(m^-1*Repr[j][3]*m)*FORCEOne(M)
                   ,StdForm,label[j]]);
                od;
              else
                if type1="Sp" then
                  Repr:=UC[QuoInt(d,2)];
                  T:=UCT[QuoInt(d,2)];
                  StdForm:=StandardAlternatingForm(d,q);
                  Form:=List([1..Size(Repr)],i->StdForm);
                  label:=List( # {@-list:
                    UCL[QuoInt(d,2)],l->[0,f,l[1]]);
                elif type1="GU" then
                  StdForm:=StandardHermitianForm(d,q);
                  Form:=List([1..Size(Repr)],i->StdForm);
                  label:=List( # {@-list:
                    UCL[QuoInt(d,2)],l->[0,f,l[1]]);
                else
                  Repr:=UC[QuoInt(d,2)+1];
                  T:=UCT[QuoInt(d,2)+1];
                  StdForm:=StandardSymmetricForm(d,q:Variant:="Default");
                  Form:=List([1..Size(Repr)],i->StdForm);
                  label:=List( # {@-list:
                    UCL[QuoInt(d,2)+1],l->[0,f,l[1]]);
                fi;
              fi;
            else
              Repr:=UCRepr[QuoInt((d+1),2)];
              Form:=UCForm[QuoInt((d+1),2)];
              T:=UCT[QuoInt((d+1),2)];
              label:=List( # {@-list:
                UCL[QuoInt((d+1),2)],l->[0,f,l[1]]);
            fi;
            if not SameSSPart or type<>"Omega" then
              card:=CardinalityOfClassicalGroup@(type1,d,q);
              S:=List([1..Size(Repr)],j->[ord*Repr[j][1],[Repr[j][2],card]
               ,w*Repr[j][3]*FORCEOne(M),Form[j],T[j],label[j]]);
            fi;
          fi;
        fi;
        Add(R,S);
      fi;
    elif ind=1 then
      h:=Degree(f);
      C:=CompanionMat(f);
      ord:=Order(C);
      d:=x[2];
      #   multiplicity in the semisimple part
      S:=[];
      if type="Sp" then
        Form:=BlockMatrix(2,2,[0,IdentityMatrix(F,d*h),-IdentityMatrix(F,d*h),0]
         );
      elif quadratic then
        Form:=BlockMatrix(2,2,[0,IdentityMatrix(F,d*h),0,0]);
      else
        Form:=BlockMatrix(2,2,[0,IdentityMatrix(F,d*h),IdentityMatrix(F,d*h),0])
         ;
      fi;
      # =v= MULTIASSIGN =v=
      T:=UnipotentClasses@("GL",d,(Size(F))^h);
      Repr:=T.val1;
      T:=T.val2;
      # =^= MULTIASSIGN =^=
      card:=CardinalityOfClassicalGroup@("GL",d,(Size(F))^h);
      for i in [1..Size(Repr)] do
        Y:=BlockMatrix(d,d,Concatenation(List([1..d],
          j1->List([1..d],
            j2->IdentityMatrix(F,h)*Repr[i][3][j1][j2])));
        for j in [1..d] do
          InsertBlock(TILDEY,C,h*(j-1)+1,h*(j-1)+1);
        od;
        if type in ["GU","SU"] then
          Y:=DirectSumMat(Y,TransposedMat(FrobeniusImage(Y,e)^-1));
        else
          Y:=DirectSumMat(Y,TransposedMat(Y^-1));
        fi;
        ord1:=Repr[i][1]*ord;
        label:=[1,f*ConjPol(f),LabelHomogenize@(T[i],F,type)];
        Add(S,[ord1,[Repr[i][2],card],Y,Form,Gcd(T[i]),label]);
      od;
      Add(R,S);
      if Double then
        Add(R1,S);
      fi;
    elif ind=2 then
      h:=Degree(f);
      C:=CompanionMat(f);
      H:=GL(h,F);
      d:=x[2];
      P:=Partitions(d);
      S:=[];
      K:=ExtStructure(F,f:Optimize:=false);
      # Implicit generator Assg from previous line.
      w:=K.1;
      ord:=Order(w);
      if type in ["GU","SU"] then
        card:=CardinalityOfClassicalGroup@("GU",d,q^h);
      else
        card:=CardinalityOfClassicalGroup@("GU",d,q^(QuoInt(h,2)));
      fi;
      for P1 in P do
        if SameSSPart then
          u:=DirectSumMat(List( # <-list:
            P1,j->GUUnipotentBlock@(j,K)));
          B:=DirectSumMat(List( # <-list:
            P1,j->ReverseRows(IdentityMatrix(K,j))));
          card1:=UnipotentCentralizerOrder@("GU",GU(d,K),u,B:JF:=P1);
          m:=TransformForm(B,"unitary":Restore:=false);
          u:=m^-1*u*m;
          Y:=BlockMatrix(d,d,Concatenation(List([1..d],
            j1->List([1..d],
              j2->Sum(List([1..h],k->C^(k-1)*Eltseq(u[j1][j2],F)[k])))));
          Y:=Y*DirectSumMat(List([1..d],i->C));
          Form:=ZeroMatrix(F,d*h,d*h);
          for i in [1..d] do
            InsertBlock(TILDEForm,x[4],h*(i-1)+1,(d-i)*h+1);
          od;
        else
          Y:=DirectSumMat(List( # <-list:
            P1,j->GUUnipotentBlock@(j,K)));
          B:=DirectSumMat(List( # <-list:
            P1,j->ReverseRows(IdentityMatrix(K,j))));
          card1:=UnipotentCentralizerOrder@("GU",GU(d,K),Y,B:JF:=P1);
          Y:=w*Y;
          Y:=BlockMatrix(d,d,Concatenation(List([1..d],
            j1->List([1..d],
              j2->Sum(List([1..h],k->C^(k-1)*Eltseq(Y[j1][j2],F)[k])))));
          Form:=ZeroMatrix(F,d*h,d*h);
          pos:=1;
          for i in P1 do
            for j in [1..i] do
              InsertBlock(TILDEForm,x[4],pos+h*(j-1),pos+h*(i-j));
            od;
            pos:=pos+i*h;
          od;
        fi;
        ord1:=ord*p^Ceiling(Log(p,Maximum(P1)));
        label:=[2,f,LabelHomogenize@(P1,F,type)];
        Add(S,[ord1,[Int((card/card1)),card],Y,Form,Gcd(P1),label]);
      od;
      Add(R,S);
      if Double then
        Add(R1,S);
      fi;
    fi;
  od;
  C:=CartesianProduct(R);
  for c in C do
    c1:=c;
    Card:=CardOfG;
    #   elements of c1 are assembled in the representatives,
    #   elements of c: need to check if the class splits into two classes in
    #  Omega
    for i in [1..Size(c1)] do
      if Size(c1[i])=8 then
        c1[i][3]:=c1[i][6];
        c1[i][4]:=c1[i][7];
      fi;
      Card:=Card/c1[i][2][2];
    od;
    Repr:=DirectSumMat(List( # <-list:
      [1..Size(L)],i->c1[i][3]));
    Form:=DirectSumMat(List( # <-list:
      [1..Size(L)],i->c1[i][4]));
    XLabel:=List( # {*-list:
      [1..Size(L)],i->c1[i][Size(c1[i])]);
    ord:=Lcm(List([1..Size(L)],i->c1[i][1]));
    card:=Product((List([1..Size(L)],i->c1[i][2][1])));
    card:=card*Int(Card);
    if type="Sp" then
      m:=TransformForm(Form,"symplectic":Restore:=false);
    elif type in ["SU","GU"] then
      m:=TransformForm(Form,"unitary":Restore:=false);
    elif type in ["O","SO","Omega"] then
      m:=TransformForm(Form,"orthogonal":Restore:=false);
    elif type in ["O+","SO+","Omega+"] then
      m:=TransformForm(Form,"orthogonalplus":Restore:=false);
    else
      m:=TransformForm(Form,"orthogonalminus":Restore:=false);
    fi;
    if type="SU" then
      GCD:=Gcd(List([1..Size(L)],i->c[i][5]));
      GCD:=Gcd(GCD,q+1);
      QuoInt(card,#NOP
      ):=GCD;
      Repr:=m^-1*Repr*m;
      #   modify AddClasses: we want AddClass in the centralizer
      #   of the semisimple part to maintain the same semisimple part
      if SameSSPart then
        s:=AddClass@(type,L,c1,m,F,Length(Repr));
      else
        s:=AddClasses;
      fi;
      for i in [0..GCD-1] do
        Add(ConjClasses,[ord,card,s^-i*Repr*s^i]);
        Add(ConjLabel,[XLabel,i]);
      od;
    elif type in ["Omega+","Omega-"] and IsEvenInt(q) then
      if Set([ThereIsPlus,ThereIsMinus])=Set([false]) then
        Add(ConjClasses,[ord,card,
         AddClassesOmega^-1*m^-1*Repr*m*AddClassesOmega]);
        Add(ConjLabel,[XLabel,"t"]);
        Add(ConjLabel,[XLabel,"id"]);
      else
        Add(ConjLabel,[XLabel,"ns"]);
      fi;
      Add(ConjClasses,[ord,card,m^-1*Repr*m]);
    elif special and type<>"SO" then
      if type="Omega" then
        SplitClassesSO:=false;
      else
        SplitClassesSO:=true;
        for i in [1..Size(L)] do
          if L[i][3]=0 then
            if false in List( # {-list:
              c[i][5],y->IsEvenInt(y)) then
              SplitClassesSO:=false;
              break i;
            fi;
          fi;
        od;
      fi;
      s:=AddClasses;
      SplitClassesOmega:=false;
      if type in ["Omega+","Omega","Omega-"] then
        SplitClassesOmega:=CheckSplitOmega@(c,F,L);
        #   modify AddClasses: we want AddClass in the centralizer
        #   of the semisimple part to maintain the same ss part
        if SameSSPart then
          z:=AddClass@(type,L,c1,m,F,Length(Repr):IsOmega:=true);
        else
          z:=AddClassesOmega;
        fi;
      fi;
      if SplitClassesSO then
        #   modify AddClasses: we want AddClass in the centralizer
        #   of the semisimple part to maintain the same ss part
        QuoInt(card,#NOP
        ):=2;
        if SameSSPart then
          s:=AddClass@(type,L,c1,m,F,Length(Repr));
        fi;
        if SplitClassesOmega then
          QuoInt(card,#NOP
          ):=2;
          Add(ConjClasses,[ord,card,z^-1*m^-1*Repr*m*z]);
          Add(ConjClasses,[ord,card,s^-1*z^-1*m^-1*Repr*m*z*s]);
          Add(ConjLabel,[XLabel,"t"]);
          Add(ConjLabel,[XLabel,"ts"]);
        fi;
        Add(ConjClasses,[ord,card,m^-1*Repr*m]);
        Add(ConjClasses,[ord,card,s^-1*m^-1*Repr*m*s]);
        Add(ConjLabel,[XLabel,"id"]);
        Add(ConjLabel,[XLabel,"s"]);
      else
        if SplitClassesOmega then
          QuoInt(card,#NOP
          ):=2;
          Add(ConjClasses,[ord,card,z^-1*m^-1*Repr*m*z]);
          Add(ConjLabel,[XLabel,"t"]);
          Add(ConjLabel,[XLabel,"id"]);
        else
          Add(ConjLabel,[XLabel,"ns"]);
        fi;
        Add(ConjClasses,[ord,card,m^-1*Repr*m]);
      fi;
    else
      Add(ConjClasses,[ord,card,m^-1*Repr*m]);
      if special then
        XLabel:=[XLabel,"ns"];
      fi;
      Add(ConjLabel,XLabel);
    fi;
  od;
  if Double and type in ["O+","O-","SO+","SO-"] then
    C:=CartesianProduct(R1);
    for c in C do
      Card:=CardOfG;
      for i in [1..Size(L)] do
        Card:=Card/c[i][2][2];
      od;
      Repr:=DirectSumMat(List( # <-list:
        [1..Size(L)],i->c[i][3]));
      Form:=DirectSumMat(List( # <-list:
        [1..Size(L)],i->c[i][4]));
      XLabel:=List( # {*-list:
        [1..Size(L)],i->c[i][Size(c[i])]);
      ord:=Lcm(List([1..Size(L)],i->c[i][1]));
      card:=Product((List([1..Size(L)],i->c[i][2][1])));
      card:=card*Int(Card);
      if type in ["O+","SO+"] then
        m:=TransformForm(Form,"orthogonalplus":Restore:=false);
      else
        m:=TransformForm(Form,"orthogonalminus":Restore:=false);
      fi;
      Add(ConjClasses,[ord,card,m^-1*Repr*m]);
      if special then
        XLabel:=[XLabel,"ns"];
      fi;
      Add(ConjLabel,XLabel);
    od;
  fi;
  ConjClasses:=List(ConjClasses,c->[c[1],c[2],c[3]*FORCEOne(GL(n,F))]);
  return rec(val1:=ConjClasses,
    val2:=ConjLabel);
end);


