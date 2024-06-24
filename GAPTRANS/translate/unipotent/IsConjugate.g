#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Embed, Generic, IsStandardGF, IsUnipotent,
#  Order, Parent

#  Defines: InternalUnipotentIsConjugate

InternalUnipotentIsConjugate@:=function(G,x,y)
#  -> ,GrpMatElt  if unipotent elements x and y are conjugate in classical
#  group G , then return true and conjugating element , else false
local F,H,K,a,b,flag,z;
  if not Generic(G)=Generic(Parent(x)) then
    Error("Element is not in group");
  fi;
  if not Generic(G)=Generic(Parent(y)) then
    Error("Element is not in group");
  fi;
  if not IsUnipotent(x) and IsUnipotent(y) then
    Error("Elements must be unipotent");
  fi;
  if x=y then
    return rec(val1:=true,
      val2:=G.0);
  fi;
  if Order(x)<>Order(y) then
    return rec(val1:=false,
      val2:=_);
  fi;
  F:=BaseRing(G);
  if not IsStandardGF(F) then
    H:=Embed(G);
    if IsBound(G.ClassicalType) then
      H.ClassicalType:=G.ClassicalType;
    fi;
    K:=BaseRing(H);
    a:=Embed(x,K);
    b:=Embed(y,K);
    # =v= MULTIASSIGN =v=
    z:=MyUnipotentIsConjugate(H,a,b);
    flag:=z.val1;
    z:=z.val2;
    # =^= MULTIASSIGN =^=
    if flag then
      z:=Embed(z,F);
    fi;
  else
    # =v= MULTIASSIGN =v=
    z:=MyUnipotentIsConjugate(G,x,y);
    flag:=z.val1;
    z:=z.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if flag then
    return rec(val1:=flag,
      val2:=z);
  else
    return rec(val1:=flag,
      val2:=_);
  fi;
end;


