#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BaseRing, Characteristic, Classes, ConjPol,
#  Degree, FrobeniusImage, GL, Generic, InternalSemisimpleIsConjugate,
#  IsAbelian, IsEven, IsOdd, IsSemisimple, IsTrivial, JordanForm, Max,
#  MultiplicativeJordanDecomposition, Parent, TransformForm, Transpose

#  Defines: ClassesForFixedSemisimple

ClassesForFixedSemisimple@:=function(G,x)
#  -> ,] ,{@ ,@}  Given a semisimple element x of classical group G which
#  preserves a form , return representatives and labels of conjugacy classes in
#  G with semisimple part x
local 
   B,C,ConjPol,DataArray,F,IsOmega,L1,MaxMult,Q,Star,ThereIsNot,UC,UCForm,UCL,
   UCRepr,UCT,UCm,UCmForm,UCmL,UCmRepr,UCmT,UCp,UCpForm,UCpL,UCpRepr,UCpT,
   ValidTypes@,varX,X_labels,Y,_,a,c,e,f,fd,flag,forgetvar1,forgetvar2,gp_type,
   i,j,m,n,p,q,s,sgn,special,type,type1,y,z;
  if not IsSemisimple(x) then
    Error("Input element is not semisimple");
  fi;
  if not Generic(Parent(x))=Generic(G) then
    Error("Input element is not in group");
  fi;
  #   require x in G: "Element not in group";
  if not MyIsIn@(G,x) then
    Error("Input element is not in group");
  fi;
  if IsTrivial(G) then
    return rec(val1:=[[1,1,G.0]],
      val2:=_);
  fi;
  F:=BaseRing(G);
  if IsAbelian(G) and Degree(G)=2 and Size(F) in [2,3] and Size(G)=2 then
    if Size(F)=3 then
      return rec(val1:=[[1,1,x]],
        val2:=_);
    else
      C:=Classes(G);
      C:=List([1..Size(C)],i->C[i]);
      return rec(val1:=C,
        val2:=_);
    fi;
  fi;
  # =v= MULTIASSIGN =v=
  gp_type:=GroupType@(G);
  flag:=gp_type.val1;
  gp_type:=gp_type.val2;
  # =^= MULTIASSIGN =^=
  if flag and gp_type in ["GL","SL"] then
    Error("Input group is one of GL or SL");
  fi;
  ValidTypes@:=Set(["Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-","SO",
   "GO+","GO-","GO"]);
  if not flag and gp_type in ValidTypes@ then
    Error(["Type must be one of ",ValidTypes@]);
  fi;
  n:=Degree(G);
  F:=BaseRing(G);
  if IsOddInt(n) and IsEvenInt(Size(F)) and gp_type="GO" then
    Error("Function does not apply to this case");
  fi;
  #   data for unipotent classes is computed just once
  #   and passed as argument to AllUnipotentElementsOfS
  # =v= MULTIASSIGN =v=
  Q:=DetermineForm@(G,x);
  B:=Q.val1;
  type:=Q.val2;
  sgn:=Q.val3;
  special:=Q.val4;
  IsOmega:=Q.val5;
  Q:=Q.val6;
  # =^= MULTIASSIGN =^=
  # rewritten select statement
  if type="unitary" then
    e:=QuoInt(Degree(F),2);
  else
    e:=0;
  fi;
  p:=Characteristic(F);
  # rewritten select statement
  if type="unitary" then
    q:=p^e;
  else
    q:=Size(F);
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
  c:=JordanForm(x);
  forgetvar1:=c.val1;
  forgetvar2:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  L1:=[[c[1][1],c[1][2]]];
  for i in [2..Size(c)] do
    ThereIsNot:=true;
    f:=c[i][1];
    fd:=ConjPol(f);
    for j in [1..Size(L1)] do
      if L1[j][1]=f then
        ThereIsNot:=false;
        L1[j][2]:=L1[j][2]+c[i][2];
        break j;
      elif L1[j][1]=fd then
        ThereIsNot:=false;
      fi;
    od;
    if ThereIsNot then
      Add(L1,[c[i][1],c[i][2]]);
    fi;
  od;
  MaxMult:=0;
  #   max multiplicity of elementary divisors f=f*, deg (f)=1
  for c in L1 do
    f:=c[1];
    if Degree(f)=1 and f=ConjPol(f) then
      MaxMult:=Max(MaxMult,c[2]);
    fi;
  od;
  if type="unitary" then
    type1:="GU";
    if special then
      type1:="SU";
    fi;
    # =v= MULTIASSIGN =v=
    UCL:=UCComputation@("GU",MaxMult,q);
    UC:=UCL.val1;
    UCRepr:=UCL.val2;
    UCForm:=UCL.val3;
    UCT:=UCL.val4;
    UCL:=UCL.val5;
    # =^= MULTIASSIGN =^=
    DataArray:=[UC,UCRepr,UCForm,UCT,UCL];
  elif type="symplectic" then
    type1:="Sp";
    # =v= MULTIASSIGN =v=
    UCL:=UCComputation@("Sp",MaxMult,q);
    UC:=UCL.val1;
    UCRepr:=UCL.val2;
    UCForm:=UCL.val3;
    UCT:=UCL.val4;
    UCL:=UCL.val5;
    # =^= MULTIASSIGN =^=
    DataArray:=[UC,UCRepr,UCForm,UCT,UCL];
  elif type="orthogonalplus" then
    type1:="GO+";
    if special then
      type1:="SO+";
    fi;
    if IsOmega then
      type1:="Omega+";
    fi;
    if IsOmega and IsEvenInt(p) then
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("Omega+",MaxMult,q);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("Omega-",MaxMult,q);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("O+",MaxMult,q);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("O-",MaxMult,q);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    fi;
    if not special and IsOddInt(p) then
      # =v= MULTIASSIGN =v=
      UCL:=UCComputation@("O",MaxMult,q);
      UC:=UCL.val1;
      UCRepr:=UCL.val2;
      UCForm:=UCL.val3;
      UCT:=UCL.val4;
      UCL:=UCL.val5;
      # =^= MULTIASSIGN =^=
      DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL,
       UC,UCRepr,UCForm,UCT,UCL];
    else
      DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL];
    fi;
  elif type="orthogonalminus" then
    type1:="GO-";
    if special then
      type1:="SO-";
    fi;
    if IsOmega then
      type1:="Omega-";
    fi;
    if IsOmega and IsEvenInt(p) then
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("Omega+",MaxMult,q);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("Omega-",MaxMult,q);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("O+",MaxMult,q);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("O-",MaxMult,q);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    fi;
    if not special and IsOddInt(p) then
      # =v= MULTIASSIGN =v=
      UCL:=UCComputation@("O",MaxMult,q);
      UC:=UCL.val1;
      UCRepr:=UCL.val2;
      UCForm:=UCL.val3;
      UCT:=UCL.val4;
      UCL:=UCL.val5;
      # =^= MULTIASSIGN =^=
      DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL,
       UC,UCRepr,UCForm,UCT,UCL];
    else
      DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL];
    fi;
  elif type="orthogonal" or type="orthogonalcircle" then
    type1:="GO";
    if special then
      type1:="SO";
    fi;
    if IsOmega then
      type1:="Omega";
    fi;
    # =v= MULTIASSIGN =v=
    UCpL:=UCComputation@("O+",MaxMult,q);
    UCp:=UCpL.val1;
    UCpRepr:=UCpL.val2;
    UCpForm:=UCpL.val3;
    UCpT:=UCpL.val4;
    UCpL:=UCpL.val5;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    UCmL:=UCComputation@("O-",MaxMult,q);
    UCm:=UCmL.val1;
    UCmRepr:=UCmL.val2;
    UCmForm:=UCmL.val3;
    UCmT:=UCmL.val4;
    UCmL:=UCmL.val5;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    UCL:=UCComputation@("O",MaxMult,q);
    UC:=UCL.val1;
    UCRepr:=UCL.val2;
    UCForm:=UCL.val3;
    UCT:=UCL.val4;
    UCL:=UCL.val5;
    # =^= MULTIASSIGN =^=
    DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL,UC,
     UCRepr,UCForm,UCT,UCL];
  fi;
  # =v= MULTIASSIGN =v=
  X_labels:=AllUnipotentElementsOfS@(type1,L1:SameSSPart:=true,
   DataArray:=DataArray);
  varX:=X_labels.val1;
  X_labels:=X_labels.val2;
  # =^= MULTIASSIGN =^=
  #   orthogonal in characteristic 2?
  if IsBound(Q) and p=2 then
    m:=TransformForm(Q,type:Restore:=false);
  else
    m:=TransformForm(B,type:Restore:=false);
  fi;
  for i in [1..Size(varX)] do
    y:=varX[i][3];
    if IsSemisimple(y) then
      # =v= MULTIASSIGN =v=
      z:=InternalSemisimpleIsConjugate@(G,x,m*y*m^-1);
      flag:=z.val1;
      z:=z.val2;
      # =^= MULTIASSIGN =^=
      if flag then
        break i;
      fi;
    fi;
  od;
  if type in ["unitary","symplectic"] then
    Y:=List(varX,a->[a[1],a[2],(z*m*a[3]*m^-1*z^-1)*FORCEOne(GL(n,F))]);
  else
    #   in the orthogonal case AllUnipotentElementsOfS returns both
    #   semisimple classes in GO, so we need to pick only one of them
    Y:=[];
    for a in varX do
      y:=z*m*a[3]*m^-1*z^-1;
      s:=MultiplicativeJordanDecomposition(y);
      if s=x then
        #   s = semisimple part of y
        Add(Y,[a[1],a[2],y]);
      fi;
    od;
  fi;
  return rec(val1:=Y,
    val2:=List( # {@-list:
    X_labels,l->l));
end;


