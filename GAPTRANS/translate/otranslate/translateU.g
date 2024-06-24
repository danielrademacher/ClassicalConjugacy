#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Degree, Explode, Include, IsIrreducible,
#  tagToNameGU

#  Defines: tagToNameGU, tagToNameSU

tagToNameGU@:=function(mu)
local F,e,f,label,lambda,m,polpart,pp,q,tag,tp;
  tag:=[];
  F:=BaseRing(mu[1][1]);
  q:=Size(F);
  for polpart in mu do
    # =v= MULTIASSIGN =v=
    lambda:=Explode(polpart);
    f:=lambda.val1;
    lambda:=lambda.val2;
    # =^= MULTIASSIGN =^=
    # rewritten select statement
    if (Degree(f)=1) then
      tp:=0;
    else
      # rewritten select statement
      if IsIrreducible(f) then
        tp:=2;
      else
        tp:=1;
      fi;
    fi;
    label:=[];
    for pp in lambda do
      # =v= MULTIASSIGN =v=
      m:=Explode(pp);
      e:=m.val1;
      m:=m.val2;
      # =^= MULTIASSIGN =^=
      UniteSet(TILDElabel,e^^m);
    od;
    UniteSet(TILDEtag,[tp,f,label]);
  od;
  return tag;
end;

# FOLLOWING COMMAND IS `WHERE` 
# =v= MULTIASSIGN =v=
ndx:=Explode(xi);
mu:=ndx.val1;
ndx:=ndx.val2;
# =^= MULTIASSIGN =^=
tagToNameSU@:=function(xi)
return [tagToNameGU@(mu),ndx];
end;


