#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Degree, Embed, Factorisation, GL, Generic,
#  InternalUnipotentCentralizer, IsCentral, IsStandardGF, IsUnipotent,
#  LMGCentralizer, LMGFactoredOrder, Lcm, Ngens, Nrows, Order, Parent

#  Defines: InternalUnipotentCentraliser, InternalUnipotentCentralizer

InternalUnipotentCentralizer:=function(G,x) # there was an @!!! TODO
#  -> ,GrpMat  Centraliser of unipotent element in classical group
local C,CH,F,H,K,O,d,f,fac,flag,phi,x,y;
  if not Generic(G)=Generic(Parent(x)) then
    Error("Element is not in group");
  fi;
  if not IsUnipotent(x) then
    Error("Element must be unipotent");
  fi;
  if IsCentral(G,x) then
    return G;
  fi;
  d:=Length(x);
  F:=BaseRing(x);
  #   "\n In InternalUnipotentCentralizer", Degree (G), Order (x);
  x:=x*FORCEOne(GL(d,F));
  if Degree(G)=1 then
    O:=Lcm(List([1..Ngens(G)],i->Order(G.i)));
    fac:=CollectedFactors(O);
    G.FactoredOrder:=fac;
    G.Order:=O;
    return G;
  else
    if not IsStandardGF(F) then
      # =v= MULTIASSIGN =v=
      phi:=Embed(G);
      H:=phi.val1;
      phi:=phi.val2;
      # =^= MULTIASSIGN =^=
      if IsBound(G.ClassicalType) then
        H.ClassicalType:=G.ClassicalType;
      fi;
      K:=BaseRing(H);
      y:=Embed(x,K);
      # =v= MULTIASSIGN =v=
      CH:=MyUnipotentCentraliser(H,y*FORCEOne(Generic(H)));
      flag:=CH.val1;
      CH:=CH.val2;
      # =^= MULTIASSIGN =^=
      if flag then
        C:=Embed(CH,F);
        C.FactoredOrder:=CH.FactoredOrder;
        C.Order:=CH.Order;
      fi;
    else
      # =v= MULTIASSIGN =v=
      C:=MyUnipotentCentraliser(G,x*FORCEOne(Generic(G)));
      flag:=C.val1;
      C:=C.val2;
      # =^= MULTIASSIGN =^=
    fi;
    if flag then
      return C;
    fi;
    C:=LMGCentralizer(G,x*FORCEOne(Generic(G)));
    f:=LMGFactoredOrder(C);
    return C;
  fi;
end;

InternalUnipotentCentraliser:=function(G,x) # there was an @!!! TODO
#  -> ,GrpMat  bla
return InternalUnipotentCentralizer(G,x); # there was an @!!! TODO
end;


