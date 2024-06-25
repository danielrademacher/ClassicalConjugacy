#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AllClasses, Append, BaseRing, Classes,
#  ClassicalGroupType, ConjugacyClasses, Degree, GF, GL, ISA, IsEven, IsOdd,
#  IsPrimePower, IsTrivial, IsometryGroupCardinality, ParallelSort, SL,
#  SequenceToFactorization, Type, UCComputation, UnipotentClasses, fn

#  Defines: AllClasses, ClassicalConjugacyClasses, IsometryGroupCardinality,
#  UCComputation

DeclareGlobalFunction("IsometryGroupCardinality@");

DeclareGlobalFunction("UCComputation@");

#   data about unipotent classes are computed just once and
#   passed as argument to AllUnipotentElementsOfS
InstallGlobalFunction(UCComputation@,
function(type,dim,q0)
local Form,L,Repr,Rewrite,T,UC,UCForm,UCL,UCRepr,UCT,Y,forgetvar3,j,temp;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  UC:=[];
  UCRepr:=[];
  UCForm:=[];
  UCT:=[];
  UCL:=[];
  if type in ["Omega","Omega+","Omega-"] and IsOddInt(q0) then
    Rewrite:=false;
  fi;
  if type="GU" or type="SU" then
    for j in [1..dim] do
      # =v= MULTIASSIGN =v=
      Form:=UnipotentClasses@("GU",j,q0:Rewrite:=Rewrite);
      Y:=Form.val1;
      T:=Form.val2;
      forgetvar3:=Form.val3;
      Repr:=Form.val4;
      Form:=Form.val5;
      # =^= MULTIASSIGN =^=
      Add(UC,Y);
      Add(UCRepr,Repr);
      Add(UCForm,Form);
      Add(UCT,T);
      Add(UCL,T);
    od;
  elif type="Sp" then
    for j in [2,2+2..dim] do
      # =v= MULTIASSIGN =v=
      Form:=UnipotentClasses@("Sp",j,q0:Rewrite:=Rewrite);
      Y:=Form.val1;
      T:=Form.val2;
      L:=Form.val3;
      Repr:=Form.val4;
      Form:=Form.val5;
      # =^= MULTIASSIGN =^=
      if IsOddInt(q0) then
        temp:=L;
        L:=T;
        T:=temp;
      fi;
      Add(UC,Y);
      Add(UCRepr,Repr);
      Add(UCForm,Form);
      Add(UCT,T);
      if IsEvenInt(q0) then
        Add(UCL,T);
      else
        Add(UCL,L);
      fi;
    od;
  elif type="O" or type="Omega" then
    for j in [1,1+2..dim] do
      # =v= MULTIASSIGN =v=
      Form:=UnipotentClasses@(type,j,q0:Rewrite:=Rewrite);
      Y:=Form.val1;
      T:=Form.val2;
      L:=Form.val3;
      Repr:=Form.val4;
      Form:=Form.val5;
      # =^= MULTIASSIGN =^=
      if IsOddInt(q0) then
        temp:=L;
        L:=T;
        T:=temp;
      fi;
      Add(UC,Y);
      Add(UCRepr,Repr);
      Add(UCForm,Form);
      Add(UCT,T);
      if IsEvenInt(q0) then
        Add(UCL,T);
      else
        Add(UCL,L);
      fi;
    od;
  elif type="O+" or type="Omega+" or type="O-" or type="Omega-" then
    for j in [2,2+2..dim] do
      # =v= MULTIASSIGN =v=
      Form:=UnipotentClasses@(type,j,q0:Rewrite:=Rewrite);
      Y:=Form.val1;
      T:=Form.val2;
      L:=Form.val3;
      Repr:=Form.val4;
      Form:=Form.val5;
      # =^= MULTIASSIGN =^=
      if IsOddInt(q0) then
        temp:=L;
        L:=T;
        T:=temp;
      fi;
      Add(UC,Y);
      Add(UCRepr,Repr);
      Add(UCForm,Form);
      Add(UCT,T);
      if IsEvenInt(q0) then
        Add(UCL,T);
      else
        Add(UCL,L);
      fi;
    od;
  fi;
  return rec(val1:=UC,
    val2:=UCRepr,
    val3:=UCForm,
    val4:=UCT,
    val5:=UCL);
end);

#   cardinality of group of isometries
InstallGlobalFunction(IsometryGroupCardinality@,
function(type,d,q)
local CardOfG;
  if type="Sp" then
    CardOfG:=CardinalityOfClassicalGroup@("Sp",d,q);
  elif type="GU" or type="SU" then
    CardOfG:=CardinalityOfClassicalGroup@("GU",d,q);
  elif type="O+" or type="GO+" or type="SO+" or type="Omega+" then
    CardOfG:=CardinalityOfClassicalGroup@("GO+",d,q);
  elif type="O" or type="GO" or type="SO" or type="Omega" then
    CardOfG:=CardinalityOfClassicalGroup@("GO",d,q);
  elif type="O-" or type="GO-" or type="SO-" or type="Omega-" then
    CardOfG:=CardinalityOfClassicalGroup@("GO-",d,q);
  fi;
  if IsEvenInt(q) and type in ["Omega+","Omega-"] then
    CardOfG:=CardOfG/SequenceToFactorization([[2,1]]);
  fi;
  return CardOfG;
end);

#   returns list of representatives for conjugacy classes in symplectic,
#   orthogonal and unitary groups (in the standard MAGMA copy)
AllClasses@:=function(type,d,q)
local 
   CardOfG,DataArray,L,L1,SameSSPart,TIP,UC,UCForm,UCL,UCRepr,UCT,UCm,UCmForm,
   UCmL,UCmRepr,UCmT,UCp,UCpForm,UCpL,UCpRepr,UCpT,VarRewrite,varX,Xlabel,i,j,
   sign,x,y,ylabel;
  SameSSPart:=ValueOption("SameSSPart");
  if SameSSPart=fail then
    SameSSPart:=false;
  fi;
  varX:=[];
  Xlabel:=[];
  CardOfG:=IsometryGroupCardinality@(type,d,q);
  if type in ["GU","SU"] then
    L:=SSClassesGU(d,q:OnlyPolynomials:=true);
    # =v= MULTIASSIGN =v=
    UCL:=UCComputation@("GU",d,q:Rewrite:=SameSSPart);
    UC:=UCL.val1;
    UCRepr:=UCL.val2;
    UCForm:=UCL.val3;
    UCT:=UCL.val4;
    UCL:=UCL.val5;
    # =^= MULTIASSIGN =^=
    DataArray:=[UC,UCRepr,UCForm,UCT,UCL];
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  elif type in ["GO","O","SO","Omega"] then
    L:=GOClasses(d,q:OnlyPolynomials:=true);
    VarRewrite:=SameSSPart;
    if type="Omega" then
      VarRewrite:=false;
    fi;
    # =v= MULTIASSIGN =v=
    UCpL:=UCComputation@("O+",d,q:Rewrite:=VarRewrite);
    UCp:=UCpL.val1;
    UCpRepr:=UCpL.val2;
    UCpForm:=UCpL.val3;
    UCpT:=UCpL.val4;
    UCpL:=UCpL.val5;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    UCmL:=UCComputation@("O-",d,q:Rewrite:=VarRewrite);
    UCm:=UCmL.val1;
    UCmRepr:=UCmL.val2;
    UCmForm:=UCmL.val3;
    UCmT:=UCmL.val4;
    UCmL:=UCmL.val5;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    UCL:=UCComputation@("O",d,q:Rewrite:=VarRewrite);
    UC:=UCL.val1;
    UCRepr:=UCL.val2;
    UCForm:=UCL.val3;
    UCT:=UCL.val4;
    UCL:=UCL.val5;
    # =^= MULTIASSIGN =^=
    DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL,UC,
     UCRepr,UCForm,UCT,UCL];
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  elif type in ["O+","GO+","SO+","Omega+"] and IsOddInt(q) then
    L:=GOpmClasses(d,q,"plus":OnlyPolynomials:=true);
    VarRewrite:=SameSSPart;
    if type="Omega+" then
      VarRewrite:=false;
    fi;
    # =v= MULTIASSIGN =v=
    UCpL:=UCComputation@("O+",d,q:Rewrite:=VarRewrite);
    UCp:=UCpL.val1;
    UCpRepr:=UCpL.val2;
    UCpForm:=UCpL.val3;
    UCpT:=UCpL.val4;
    UCpL:=UCpL.val5;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    UCmL:=UCComputation@("O-",d,q:Rewrite:=VarRewrite);
    UCm:=UCmL.val1;
    UCmRepr:=UCmL.val2;
    UCmForm:=UCmL.val3;
    UCmT:=UCmL.val4;
    UCmL:=UCmL.val5;
    # =^= MULTIASSIGN =^=
    if type in ["GO+","O+"] then
      # =v= MULTIASSIGN =v=
      UCL:=UCComputation@("O",d,q:Rewrite:=VarRewrite);
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
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  elif type in ["O-","GO-","SO-","Omega-"] and IsOddInt(q) then
    L:=GOpmClasses(d,q,"minus":OnlyPolynomials:=true);
    VarRewrite:=SameSSPart;
    if type="Omega-" then
      VarRewrite:=false;
    fi;
    # =v= MULTIASSIGN =v=
    UCpL:=UCComputation@("O+",d,q:Rewrite:=VarRewrite);
    UCp:=UCpL.val1;
    UCpRepr:=UCpL.val2;
    UCpForm:=UCpL.val3;
    UCpT:=UCpL.val4;
    UCpL:=UCpL.val5;
    # =^= MULTIASSIGN =^=
    # =v= MULTIASSIGN =v=
    UCmL:=UCComputation@("O-",d,q:Rewrite:=VarRewrite);
    UCm:=UCmL.val1;
    UCmRepr:=UCmL.val2;
    UCmForm:=UCmL.val3;
    UCmT:=UCmL.val4;
    UCmL:=UCmL.val5;
    # =^= MULTIASSIGN =^=
    if type in ["GO-","O-"] then
      # =v= MULTIASSIGN =v=
      UCL:=UCComputation@("O",d,q:Rewrite:=VarRewrite);
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
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  elif type="Sp" then
    L:=SSClassesSp(d,q:OnlyPolynomials:=true);
    # =v= MULTIASSIGN =v=
    UCL:=UCComputation@("Sp",d,q);
    UC:=UCL.val1;
    UCRepr:=UCL.val2;
    UCForm:=UCL.val3;
    UCT:=UCL.val4;
    UCL:=UCL.val5;
    # =^= MULTIASSIGN =^=
    DataArray:=[UC,UCRepr,UCForm,UCT,UCL];
    #   UC := <UnipotentClasses ("Sp", s, q: Rewrite := SameSSPart): s in [2..d
    #  by 2]>;
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  elif type in ["O+","GO+","SO+","Omega+"] and IsEvenInt(q) then
    #   the function GOpm2Classes does not support the parameter
    #  "OnlyPolynomials",
    #   so L needs to be defined starting by SpClasses, with a little change
    L1:=SSClassesSp(d,q:OnlyPolynomials:=true);
    if type="Omega+" then
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("Omega+",d,q:Rewrite:=SameSSPart);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("Omega-",d,q:Rewrite:=SameSSPart);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("O+",d,q:Rewrite:=SameSSPart);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("O-",d,q:Rewrite:=SameSSPart);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    fi;
    DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL];
    L:=# [*-list:
    [];
    for x in L1 do
      sign:=0*FORCEOne(GF(2));
      #   TIP = There Is PlusMinus (i.e. there is the elementary divisor t+1)
      TIP:=false;
      for y in x do
        if y[3]=0 then
          TIP:=true;
        elif y[3]=2 then
          sign:=sign+y[2];
        fi;
      od;
      if TIP or sign=0 then
        Add(L,List(x,y->[y[1],y[2]]));
      fi;
    od;
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  elif type in ["O-","GO-","SO-","Omega-"] and IsEvenInt(q) then
    L1:=SSClassesSp(d,q:OnlyPolynomials:=true);
    if type="Omega-" then
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("Omega+",d,q:Rewrite:=SameSSPart);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("Omega-",d,q:Rewrite:=SameSSPart);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      UCpL:=UCComputation@("O+",d,q:Rewrite:=SameSSPart);
      UCp:=UCpL.val1;
      UCpRepr:=UCpL.val2;
      UCpForm:=UCpL.val3;
      UCpT:=UCpL.val4;
      UCpL:=UCpL.val5;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      UCmL:=UCComputation@("O-",d,q:Rewrite:=SameSSPart);
      UCm:=UCmL.val1;
      UCmRepr:=UCmL.val2;
      UCmForm:=UCmL.val3;
      UCmT:=UCmL.val4;
      UCmL:=UCmL.val5;
      # =^= MULTIASSIGN =^=
    fi;
    DataArray:=[UCp,UCpRepr,UCpForm,UCpT,UCpL,UCm,UCmRepr,UCmForm,UCmT,UCmL];
    L:=# [*-list:
    [];
    for x in L1 do
      sign:=0*FORCEOne(GF(2));
      #   TIP = There Is PlusMinus (i.e. there is the elementary divisor t+1)
      TIP:=false;
      for y in x do
        if y[3]=0 then
          TIP:=true;
        elif y[3]=2 then
          sign:=sign+y[2];
        fi;
      od;
      if TIP or sign=1 then
        Add(L,List(x,y->[y[1],y[2]]));
      fi;
    od;
    for i in [1..Size(L)] do
      # =v= MULTIASSIGN =v=
      ylabel:=AllUnipotentElementsOfS@(type,L[i]
       :SameSSPart:=SameSSPart,DataArray:=DataArray,CardOfG:=CardOfG);
      y:=ylabel.val1;
      ylabel:=ylabel.val2;
      # =^= MULTIASSIGN =^=
      for j in [1..Size(y)] do
        Add(varX,y[j]);
        Add(Xlabel,ylabel[j]);
      od;
    od;
  else
    Error("Input type is wrong");
  fi;
  #   sort classes and labels: increasing order and sizes
  ParallelSort(varX,Xlabel); # actually TILDEvarX, TILDEXlabel!!! TODO
  #   return labels as indexed set, not sequence
  return rec(val1:=varX,
    val2:=List( # {@-list:
    Xlabel,x->x));
end;

ClassicalConjugacyClasses@:=function(type,d,q)
#  -> ,] ,{@ ,@}  Conjugacy classes and their class invariants ( labels ) for
#  the standard classical group of supplied type and rank defined over field of
#  given size ; labels are not returned for the general or special linear group
local C,G,Orthogonal,ValidTypes@;
  Orthogonal:=Set(["Omega+","Omega-","Omega","O+","O-","O","SO+","SO-","SO",
   "GO+","GO-","GO"]);
  ValidTypes@:=Union(Set(["SL","GL","Sp","SU","GU"]),Orthogonal);
  if not type in ValidTypes@ then
    Error(["Type must be one of",ValidTypes@]);
  fi;
  if not d >= 1 then
    Error("Degree must be positive");
  fi;
  if not IsPrimePower(q) then
    Error("Invalid field size");
  fi;
  if type in ["O","GO","SO","Omega"] then
    if IsEvenInt(q) then
      Error("Case of odd dimension and even characteristic not considered");
    fi;
      if not IsOddInt(d) and d >= 3 then
      Error("Degree must be odd and at least 3");
    fi;
  elif type in Union(Set(["Sp"])
     ,Difference(Orthogonal,Set(["GO","SO","Omega","O"]))) then
      if not IsEvenInt(d) then
      Error("Degree must be even");
    fi;
  fi;
  if type="GL" then
    G:=GL(d,q);
    C:=Classes(G);
    return rec(val1:=C,
      val2:=_);
  elif type="SL" then
    G:=SL(d,q);
    C:=Classes(G);
    return rec(val1:=C,
      val2:=_);
  else
    return AllClasses@(type,d,q);
  fi;
end;

ClassicalConjugacyClasses@:=function(G)
#  -> ,] ,{@ ,@}  Conjugacy classes and their class invariants ( labels ) for
#  the classical group G in its natural representation ; if G has order at most
#  100 , or it := the general or special linear group , then labels are not
#  returned
local F,L,ValidTypes@,cc,d,flag,fn,tp;
  F:=BaseRing(G);
  if not ISA(Type(F),FldFin) then
    Error("Base ring is not a finite field");
  fi;
  d:=Degree(G);
  if (IsTrivial(G) or (d=2 and Size(F) <= 4)) then
    cc:=ConjugacyClasses(G);
    return rec(val1:=cc,
      val2:=_);
  fi;
  # =v= MULTIASSIGN =v=
  tp:=ClassicalGroupType@(G);
  flag:=tp.val1;
  tp:=tp.val2;
  # =^= MULTIASSIGN =^=
  #   allow GL and SL for consistency
  ValidTypes@:=Set(["GL","SL","Sp","SU","GU","Omega+","Omega-","Omega","O+",
   "O-","O","SO+","SO-","SO","GO+","GO-","GO"]);
  if not flag and tp in ValidTypes@ then
    Error(["Type of group must be one of ",ValidTypes@]);
  fi;
  cc:=ConjugacyClasses(G);
  if not IsBound(G.Labels_A) and not IsBound(G.Labels_S) then
    return rec(val1:=cc,
      val2:=_);
  fi;
  if not IsBound(G.Labels_A) then
    if IsBound(G.Labels_S) then
      if tp="Sp" then
        fn:=tagToNameSp@;
      elif tp in ["GO","GO+","GO-"] then
        fn:=tagToNameO@;
      elif tp in ["SO","SO+","SO-"] then
        fn:=tagToNameSO@;
      elif tp="GU" then
        fn:=tagToNameGU@;
      elif tp="SU" then
        fn:=tagToNameSU@;
      else
        Error("labels not available for this group of type",tp);
      fi;
      G.Labels_A:=List( # {@-list:
        G.Labels_S,mu->fn(mu));
    else
      #   error "labels not available for this group of type", tp;
    fi;
  fi;
  L:=G.Labels_A;
  return rec(val1:=cc,
    val2:=L);
end;

#   ClassicalClasses has been made a synonym of ClassicalConjugacyClasses in
#  the bind file c.b

