#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BaseRing, Coefficient, Degree, Error,
#  Explode, Include, IsEven, IsIrreducible, IsOdd, PrimitiveElement, Rep, Sort,
#  sgnSp

#  Defines: nameToTagSp, sgnSp, tagToNameSp

#   2020-11-14
#  * Translation between my conjugacy class names and those of Giovanni
#  * for finite symplectic groups

#   The sign of the unipotent or negative unipotent of type <e,m> in GF(q)
#   The argument u is true for unipotents, false for the negative of unipotents
sgnSp:=function(u,e,m,q)
local val;
  if not IsEvenInt(e) then
    Print("e must be even");
  fi;
  if m mod 4=0 or q mod 8=1 then
    return 1;
  fi;
  if u then
    if q mod 8=3 then
      # rewritten select statement
      if (m+e) mod 4=3 then
        val:=1;
      else
        val:=-1;
      fi;
    elif q mod 8=5 then
      # rewritten select statement
      if m mod 4=2 then
        val:=1;
      else
        val:=-1;
      fi;
    elif q mod 8=7 then
      # rewritten select statement
      if (m+e) mod 4=1 then
        val:=1;
      else
        val:=-1;
      fi;
    fi;
  else
    if q mod 8=3 then
      # rewritten select statement
      if (m+e) mod 4=1 then
        val:=1;
      else
        val:=-1;
      fi;
    elif q mod 8=5 then
      # rewritten select statement
      if m mod 4=2 then
        val:=1;
      else
        val:=-1;
      fi;
    elif q mod 8=7 then
      # rewritten select statement
      if (m+e) mod 4=3 then
        val:=1;
      else
        val:=-1;
      fi;
    fi;
  fi;
  return val;
end;

#   From Milnor symplectic signed partitions to Giovanni De Franceschi names
tagToNameSp:=function(mu)
local F,a0,e,f,label,lambda,m,polpart,pp,q,ss,tag,tp,z;
  tag:=[];
  F:=BaseRing(mu[1][1]);
  q:=Size(F);
  z:=PrimitiveElement(F);
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
      if tp > 0 then
        UniteSet(label,[e,1*FORCEOne(F)]^^m); # actually Tildelabel!!! TODO
      elif IsOddInt(e) then
        UniteSet(label,[e,0*FORCEOne(F)]^^(QuoInt(m,2))); # actually Tildelabel!!! TODO
      else
        a0:=Coefficient(f,0);
        ss:=sgnSp(a0<>1*FORCEOne(F),e,m,q); # there was an @!!! TODO
        if ss=1 then
          if e > 0 then
            UniteSet(label,[e,1*FORCEOne(F)]^^m); # actually Tildelabel!!! TODO
          else
            UniteSet(label,[-e,z]); # actually Tildelabel!!! TODO
            if m > 1 then
              UniteSet(label,[-e,1*FORCEOne(F)]^^(m-1)); # actually Tildelabel!!! TODO
            fi;
          fi;
        else
          if e < 0 then
            UniteSet(label,[-e,1*FORCEOne(F)]^^m); # actually Tildelabel!!! TODO
          else
            UniteSet(label,[e,z]); # actually Tildelabel!!! TODO
            if m > 1 then
              UniteSet(label,[e,1*FORCEOne(F)]^^(m-1)); # actually Tildelabel!!! TODO
            fi;
          fi;
        fi;
      fi;
    od;
    UniteSet(tag,[tp,f,label]); # actually Tildetag!!! TODO
  od;
  return tag;
end;

#   From Giovanni De Franceschi names to Milnor symplectic signed partitions
nameToTagSp:=function(nm)
local F,a0,alpha,e,eam,f,m,mm,mu,prev,ptn,q,ss,tag,term,tp;
  tag:=# {@-list:
  [];
  F:=BaseRing(Rep(nm)[2]);
  q:=Size(F);
  for term in nm do
    ptn:=[];
    # =v= MULTIASSIGN =v=
    mu:=Explode(term);
    tp:=mu.val1;
    f:=mu.val2;
    mu:=mu.val3;
    # =^= MULTIASSIGN =^=
    #   Convert mu to triples < e, alpha, m >
    #  labels := [ Append(pp,m) : pp -> m in mu ];
    Error("labels := [ Append(pp,m) : pp -> m in mu ];");
    Sort(labels); # Actually Tildelabels!!! TODO
    prev:=[0,0];
    #   previous value of <e,m>
    for eam in labels do
      # =v= MULTIASSIGN =v=
      m:=Explode(eam);
      e:=m.val1;
      alpha:=m.val2;
      m:=m.val3;
      # =^= MULTIASSIGN =^=
      if tp > 0 then
        Add(ptn,[e,m]);
      elif IsOddInt(e) then
        Add(ptn,[e,2*m]);
      else
        a0:=Coefficient(f,0);
        ss:=sgnSp(a0<>1*FORCEOne(F),e,m,q); # there was an @!!! TODO
        if e=prev[1] then
          mm:=prev[2]+m;
          ss:=sgnSp(a0<>1*FORCEOne(F),e,mm,q); # there was an @!!! TODO
          #   replace the top of the stack
          ptn[Size(ptn)]:=[-ss*e,mm];
          prev:=[0,0];
        elif alpha=1 then
          if ss > 0 then
            Add(ptn,[e,m]);
          else
            Add(ptn,[-e,m]);
          fi;
          prev:=[e,m];
        else
          if ss > 0 then
            Add(ptn,[-e,m]);
          else
            Add(ptn,[e,m]);
          fi;
          prev:=[e,m];
        fi;
      fi;
    od;
    UniteSet(tag,[f,ptn]); # actually Tildetag!!! TODO
  od;
  return tag;
end;


