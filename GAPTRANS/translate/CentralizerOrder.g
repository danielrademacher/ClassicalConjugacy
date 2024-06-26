#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Centraliser, Characteristic,
#  CheckSplitOmega, CheckWhetherChanged, ClassicalGroupType, Degree,
#  FactoredOrder, Factorization, GF, Gcd, Generic, IdentityMatrix, Include,
#  IsCentral, IsEven, IsOdd, IsSquare, MultisetToSequence, MyCentraliserOrder,
#  Nrows, Parent, Set, TurnLabelToJordan

#  Defines: CheckSplitOmega, CheckWhetherChanged, ClassicalCentraliserOrder,
#  MyCentraliserOrder, TurnLabelToJordan

DeclareGlobalFunction("MyCentraliserOrder"); # there was an @!!! TODO

TurnLabelToJordan:=function(L,type) # there was an @!!! TODO
local Risp,a;
  Risp:=[];
  if type="Sp" then
    for a in L do
      UniteSet(Risp,a[1]); # actually TILDERisp!!! TODO
      if IsOddInt(a[1]) then
        UniteSet(Risp,a[1]); # actually TILDERisp!!! TODO
      fi;
    od;
  else
    for a in L do
      UniteSet(Risp,a[1]); # actually TILDERisp!!! TODO
      if IsEvenInt(a[1]) then
        UniteSet(Risp,a[1]); # actually TILDERisp!!! TODO
      fi;
    od;
  fi;
  return Risp;
end;

#   returns 3 values: |C_GO:C_SO|>1, |C_SO:C_Omega|>1 , values of b_i(-1)^k_i
CheckSplitOmega:=function(L,icl) # there was an @!!! TODO
#  /out: icl = IsChangedLabel
local set;
  set:=List(Filtered(L,x->IsOddInt(x[1])),x->x[1]);
  if Size(set)=0 then
    return rec(val1:=false,
      val2:=false,
      val3:=_);
  fi;
  if Size(set)<>Size(Set(set)) then
    return rec(val1:=true,
      val2:=true,
      val3:=_);
  fi;
  set:=List(Filtered(L,x->IsOddInt(x[1])),x->IsSquare(x[2]*(-1)^(QuoInt((x[1]-1)
   ,2))));
  if icl and IsEvenInt(Sum(List(L,x->x[1]))) then
    set:=List(set,f->not f);
  fi;
  if Size(Set(set)) > 1 then
    return rec(val1:=true,
      val2:=true,
      val3:=_);
  else
    return rec(val1:=true,
      val2:=false,
      val3:=set[1]);
  fi;
end;

#   check whether the label of t \pm 1 with even multiplicity in Omega(odd, q)
#  corresponds or it has changed
#   by multiplying the form by a non-square when assembling in file fixed-ss.m
CheckWhetherChanged:=function(L,n,q) # there was an @!!! TODO
local DetForm,is_square,l;
  is_square:=((q mod 8 in [1,3] and n mod 4=3) or (q mod 8 in [1,7] and n mod 
   4=1));
  #   det (StdForm) is a square or not
  DetForm:=1;
  #   1 if square, -1 otherwise
  for l in L do
    if l[1]=0 and IsEvenInt(Sum(List(l[3],y->y[1]))) then
      if not IsSquare(Product((Concatenation([1*FORCEOne(GF(q))]
         ,List(Filtered(l[3],x->IsOddInt(x[1])),x->2*x[2]*(-1)^(QuoInt((x[1]-1)
         ,2))))))) then
        DetForm:=DetForm*-1;
      fi;
    elif l[1]=1 then
      if q mod 4=3 and IsOddInt(Degree(l[2])) and IsOddInt(Sum(List(l[3],y->y[1]
         ))) then
        DetForm:=DetForm*-1;
      fi;
    else
      if q mod 4=1 then
        if IsOddInt(Sum(List(l[3],y->y[1]))) and Degree(l[2]) mod 4=2 then
          DetForm:=DetForm*-1;
        fi;
      else
        if IsOddInt(Sum(List(l[3],y->y[1]))) and Degree(l[2]) mod 4=0 then
          DetForm:=DetForm*-1;
        fi;
      fi;
    fi;
  od;
  if is_squarexorDetForm=1 then
    return true;
  else
    return false;
  fi;
end;

#   compute the cardinality of the centralizer using only the label L
#   of the element g; the label L is that returned by ClassicalClasses but
#   can be the complete label returned by IsometryGroupClassLabel
InstallGlobalFunction(MyCentraliserOrder, # there was an @!!! TODO
function(type,g)
local 
   Card,D,F,IsChangedLabel,JF,L,L1,SpecialCase2,SplitOmega,SplitSO,T,
   ValuesOmegapm,W,card,e,is_omega,l,p,q,r,special,v1,v2,v3;
  L:=ValueOption("L");
  if L=fail then
    L:=[];
  fi;
  special:=false;
  is_omega:=false;
  F:=BaseRing(g);
  q:=Size(F);
  p:=Characteristic(F);
  e:=Degree(F);
  if type in ["SU","GU"] then
    q:=p^(QuoInt(e,2));
  fi;
  SpecialCase2:=false;
  SplitSO:=false;
  #   true if |C_GO : C_SO| > 1
  SplitOmega:=false;
  #   true if |C_SO : C_Omega| > 1
  if type in ["Omega","Omega+","Omega-"] then
    is_omega:=true;
    if IsOddInt(p) then
      special:=true;
    fi;
    ValuesOmegapm:=Set([]);
  elif type in ["SO","SO+","SO-"] and IsOddInt(p) then
    special:=true;
  elif type="SU" then
    special:=true;
  fi;
  if IsEvenInt(q) and type in ["Sp","GO+","GO-","SO+","SO-","Omega+","Omega-"] 
     then
    SpecialCase2:=true;
  fi;
  Card:=Factorization(1);
  if L=[] then
    L1:=GenericLabel(type,g); # there was an @!!! TODO
  else
    L1:=L;
    if special or is_omega then
      L1:=L[1];
    fi;
  fi;
  if is_omega then
    if type="Omega" then
      IsChangedLabel:=CheckWhetherChanged(L1,Length(g),q); # there was an @!!! TODO
    else
      IsChangedLabel:=false;
    fi;
  fi;
  for l in L1 do
    if l[1]=0 then
      if type="Sp" then
        if IsEvenInt(q) then
          T:=l[3];
          card:=Factorization(SpUnipotentCentraliserOrder(T,[],q)); # there was an @!!! TODO
        else
          T:=TurnLabelToJordan(l[3],"Sp"); # there was an @!!! TODO
          W:=MultisetToSequence(l[3]);
          card:=Factorization(SpUnipotentCentraliserOrder(T,W,q)); # there was an @!!! TODO
        fi;
      elif type in ["SU","GU"] then
        JF:=List(l[3],a->a);
        card:=UnipotentCentraliserOrder("GU",[],IdentityMatrix(F,2),[]:JF:=JF) # there was an @!!! TODO
         ;
      else
        if IsEvenInt(q) then
          T:=l[3];
          card:=Factorization(OrthogonalUnipotentCentraliserOrder("GO+",T,[] # there was an @!!! TODO
           ,false,q));
        else
          T:=TurnLabelToJordan(l[3],"GO"); # there was an @!!! TODO
          W:=MultisetToSequence(l[3]);
          if is_omega then
            # =v= MULTIASSIGN =v=
            v3:=CheckSplitOmega(W,IsChangedLabel); # there was an @!!! TODO
            v1:=v3.val1;
            v2:=v3.val2;
            v3:=v3.val3;
            # =^= MULTIASSIGN =^=
            if v1 then
              SplitSO:=true;
              if v2 then
                SplitOmega:=true;
              else
                UniteSet(ValuesOmegapm,v3); # actually TILDEValuesOmegapm!!! TODO
              fi;
            fi;
          elif special and true in List( # {-list:
            l[3],x->IsOddInt(x[1])) then
            SplitSO:=true;
          fi;
          card:=Factorization(OrthogonalUnipotentCentraliserOrder("GO+",T,W, # there was an @!!! TODO
           false,q));
        fi;
      fi;
    elif l[1]=1 then
      if SpecialCase2 then
        JF:=l[3][1];
      elif type in ["GU","SU"] then
        JF:=List(l[3],h->h);
      else
        JF:=List(l[3],h->h[1]);
      fi;
      card:=UnipotentCentraliserOrder("GL",[] # there was an @!!! TODO
       ,IdentityMatrix(GF(p^(QuoInt(e*Degree(l[2]),2))),2),[]:JF:=JF);
      if is_omega and true in List( # {-list:
        JF,h->IsOddInt(h)) then
        SplitOmega:=true;
      fi;
    elif l[1]=2 then
      if SpecialCase2 then
        JF:=l[3][1];
      elif type in ["GU","SU"] then
        JF:=List(l[3],h->h);
      else
        JF:=List(l[3],h->h[1]);
      fi;
      card:=UnipotentCentraliserOrder("GU",[] # there was an @!!! TODO
       ,IdentityMatrix(GF(p^(e*Degree(l[2]))),2),[]:JF:=JF);
      if is_omega and true in List( # {-list:
        JF,h->IsOddInt(h)) then
        SplitOmega:=true;
      fi;
    fi;
    Card:=Card*card;
  od;
  D:=Factorization(1);
  #   divide the centralizer cardinality by D
  if is_omega then
    if IsEvenInt(q) then
      for l in L1 do
        if l[1]=0 then
          if l[3][2]<>[] or l[3][3]<>[] or l[3][4]<>[] or List( # {-list:
            l[3][1],x->IsEvenInt(x))<>Set([true]) then
            D:=Factorization(2);
            break l;
          fi;
        fi;
      od;
    else
      if SplitSO then
        D:=D*Factorization(2);
        SplitOmega:=SplitOmega or Size(ValuesOmegapm) > 1;
      fi;
      if SplitOmega then
        D:=D*Factorization(2);
      fi;
    fi;
  elif special then
    if type="SU" then
      r:=Gcd(q+1,Gcd(List(L1,x->Gcd(x[3]))));
      r:=QuoInt((q+1),r);
      D:=Factorization(r);
    else
      if SplitSO then
        D:=Factorization(2);
      fi;
    fi;
  fi;
  return Card/D;
end);

ClassicalCentraliserOrder:=function(G,g) # there was an @!!! TODO
#  -> ,RngIntEltFact  Return the factored order of the centraliser of g in the
#  standard classical group G of the given type
local CB,F,ValidTypes,d,flag,tp; # there was an @!!! TODO
  if not (Generic(Parent(g))=Generic(G)) then
    Error("Input element is not in group");
  fi;
  #   require g in G: "Element not in group";
  if not MyIsIn(G,g:Add:=Set(["GL","SL"])) then # there was an @!!! TODO
    Error("Input element is not in group");
  fi;
  if IsCentral(G,g) then
    return FactoredOrder(G);
  fi;
  d:=Degree(G);
  F:=BaseRing(G);
  if (d=2 and Size(F) <= 4) then
    return FactoredOrder(Centraliser(G,g));
  fi;
  # =v= MULTIASSIGN =v=
  tp:=ClassicalGroupType(G); # there was an @!!! TODO
  flag:=tp.val1;
  tp:=tp.val2;
  # =^= MULTIASSIGN =^=
  ValidTypes:=Set(["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+", # there was an @!!! TODO
   "SO-","SO","GO+","GO-","GO"]);
  if not flag and tp in ValidTypes then # there was an @!!! TODO
    Error(["Type of group must be one of ",ValidTypes]); # there was an @!!! TODO
  fi;
  if tp="GO" and IsOddInt(d) and IsEvenInt(Size(F)) then
    Error("Function does not apply to this case");
  fi;
  if tp="GL" then
    return GLCentralizerOrder(G,g); # there was an @!!! TODO
  elif tp="SL" then
    return SLCentralizerOrder(G,g); # there was an @!!! TODO
  else
    CB:=TransformMatrix(G); # there was an @!!! TODO
    return MyCentraliserOrder(tp,g^CB); # there was an @!!! TODO
  fi;
end;


