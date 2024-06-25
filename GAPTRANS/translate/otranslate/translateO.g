#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AbelianGroup, Abs, Append, BaseRing, Degree, Error,
#  Explode, Include, IsEven, IsIrreducible, IsOdd, Parent, PrimitiveElement,
#  Rep, Sort, Type, changeSign, invToWittType, nmDim, sgnO, tagDim, tagToNameO,
#  theSign, toNameEven, toTag

#  Defines: changeSign, invToWittType, nameToTagO, nmDim, sgnO, sigil, tagDim,
#  tagToNameO, tagToNameSO, theSign, toNameEven, toTag

#   2021-01-14
#  * Translation between my conjugacy class names and those of Giovanni
#  * for finite orthognal groups
#  *
#  * Use  tagToNameO(mu)  to convert my name to Giovanni's
#  * Use  nameToTagO(nm)  to convert Giovanni's name to mine
#  *

#   The sign of the unipotent or negative unipotent of type <e,m> in GF(q)
#   for orthogonal groups
sgnO@:=function(e,m,q)
local val;
  if IsEvenInt(e) then
    Print("e must be odd");
  fi;
  if IsEvenInt(q) then
    Print("q must be odd");
  fi;
  if m mod 4=0 or q mod 8=1 then
    return 1;
  fi;
  if q mod 8=3 then
    # rewritten select statement
    if m mod 4=3 then
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
    if m mod 4=1 then
      val:=1;
    else
      val:=-1;
    fi;
  fi;
  return val;
end;

changeSign@:=function(mu)
local f,newlst,nu,plist,polpart;
  nu:=# {@-list:
  [];
  for polpart in mu do
    # =v= MULTIASSIGN =v=
    plist:=Explode(polpart);
    f:=plist.val1;
    plist:=plist.val2;
    # =^= MULTIASSIGN =^=
    # FOLLOWING COMMAND IS `WHERE` 
    # =v= MULTIASSIGN =v=
    m:=Explode(em);
    e:=m.val1;
    m:=m.val2;
    # =^= MULTIASSIGN =^=
    # rewritten select statement
    if (Degree(f) > 1) then
      newlst:=plist;
    else
      # rewritten select statement
      if IsOddInt(e*m) then
        newlst:=List(Filtered(plist,em->true),em->[-e,m]);
      else
        newlst:=Filtered(plist,em->true);
      fi;
    fi;
    UniteSet(nu,[f,newlst]); # actually Tildenu!!! TODO
  od;
  return nu;
end;

#   The functions invToWittType and theSign have been copied from GOConjugacy.m
#   import "GOConjugacy.m" : invToWittType, theSign
invToWittType@:=function(inv)
local W,e,f,lambda,m,mu,omega,pol_part,q,qmod4,w;
  q:=Size(BaseRing(Parent(inv[1][1])));
  qmod4:=q mod 4=1;
  # rewritten select statement
  if qmod4 then
    W:=AbelianGroup(GrpAb,[2,2]);
  else
    W:=AbelianGroup(GrpAb,[4]);
  fi;
  w:=0*FORCEOne(W);
  # rewritten select statement
  if qmod4 then
    omega:=W.1+W.2;
  else
    omega:=2*W.1;
  fi;
  for pol_part in inv do
    # =v= MULTIASSIGN =v=
    lambda:=Explode(pol_part);
    f:=lambda.val1;
    lambda:=lambda.val2;
    # =^= MULTIASSIGN =^=
    if IsIrreducible(f) then
      for mu in lambda do
        # =v= MULTIASSIGN =v=
        m:=Explode(mu);
        e:=m.val1;
        m:=m.val2;
        # =^= MULTIASSIGN =^=
        if Degree(f)=1 then
          if IsOddInt(e) then
            if IsEvenInt(m) then
              if e < 0 then
                w:=w+omega;
              fi;
            else
              if e > 0 then
                w:=w+W.1;
              else
                w:=w+# rewritten select statement
                function(xxx)if xxx then return W.2;else return 
                 3*W.1;fi;end(qmod4);
              fi;
            fi;
          fi;
        else
          #   Degree(f) greater than 1
          w:=w+e*m*omega;
        fi;
      od;
    fi;
  od;
  return w;
end;

theSign@:=function(inv)
local W,w;
  w:=invToWittType@(inv);
  W:=Parent(w);
  return # rewritten select statement
  function(xxx)if xxx then return 1;else return -1;fi;end(w in [0*FORCEOne(W)
   ,W.1]);
end;

tagDim@:=function(mu)
local d,d_,e,em,f,lambda,m,polpart;
  d:=0;
  for polpart in mu do
    # =v= MULTIASSIGN =v=
    lambda:=Explode(polpart);
    f:=lambda.val1;
    lambda:=lambda.val2;
    # =^= MULTIASSIGN =^=
    d_:=0;
    for em in lambda do
      # =v= MULTIASSIGN =v=
      m:=Explode(em);
      e:=m.val1;
      m:=m.val2;
      # =^= MULTIASSIGN =^=
      d_:=d_+Abs(e)*m;
    od;
    d:=d+Degree(f)*d_;
  od;
  return d;
end;

nmDim@:=function(nm)
local a,d,d_,e,eam,f,m,mu,term,tp;
  d:=0;
  for term in nm do
    # =v= MULTIASSIGN =v=
    mu:=Explode(term);
    tp:=mu.val1;
    f:=mu.val2;
    mu:=mu.val3;
    # =^= MULTIASSIGN =^=
    #  labels := [ Append(pp,m) : pp -> m in mu ];
    Error("labels := [ Append(pp,m) : pp -> m in mu ];");
    d_:=0;
    for eam in labels do
      # =v= MULTIASSIGN =v=
      m:=Explode(eam);
      e:=m.val1;
      a:=m.val2;
      m:=m.val3;
      # =^= MULTIASSIGN =^=
      if tp=0 and IsEvenInt(e) then
        m:=m*2;
      fi;
      d_:=d_+e*m;
    od;
    d:=d+Degree(f)*d_;
  od;
  return d;
end;

#   The De Franceschi label of a set mu of pairs <f,pi>, where f is a
#  *-irreducible
#   polynomial and pi is a (signed) partition for an even dimensional 
 orthogonal
#   group over GF(q), q odd
toNameEven@:=function(mu)
local F,e,ee,f,label,lambda,m,name,polpart,pp,q,ss,tp,z;
  name:=[];
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
      elif IsEvenInt(e) then
        UniteSet(label,[e,0*FORCEOne(F)]^^(QuoInt(m,2))); # actually Tildelabel!!! TODO
      else
        ee:=Abs(e);
        ss:=sgnO@(ee,m,q);
        if e*ss > 0 then
          UniteSet(label,[ee,1*FORCEOne(F)]^^m); # actually Tildelabel!!! TODO
        else
          UniteSet(label,[ee,z]); # actually Tildelabel!!! TODO
          if m > 1 then
            UniteSet(label,[ee,1*FORCEOne(F)]^^(m-1)); # actually Tildelabel!!! TODO
          fi;
        fi;
      fi;
    od;
    UniteSet(name,[tp,f,label]); # actually Tildename!!! TODO
  od;
  return name;
end;

tagToNameO@:=function(mu)
local F,label,n;
  n:=tagDim@(mu);
  if IsEvenInt(n) then
    return toNameEven@(mu);
  fi;
  F:=BaseRing(mu[1][1]);
  label:=toNameEven@(mu);
  return TurnCorrectLabel@(label,n,F);
  #   g := RepresentativeMatrixO(mu);
  #   return IsometryGroupClassLabel("GO",g);
end;

sigil@:=["s","ns","id"];
tagToNameSO@:=function(mu)
local nm,sgn,xi;
  if Type(mu)=Tup then
    # =v= MULTIASSIGN =v=
    sgn:=Explode(mu);
    xi:=sgn.val1;
    sgn:=sgn.val2;
    # =^= MULTIASSIGN =^=
    nm:=[tagToNameO@(xi),sigil@[sgn+2]];
  else
    nm:=[tagToNameO@(mu),"ns"];
  fi;
  return nm;
end;

#   The sequence representing the function from *-irreducible polynomials to
#   signed partitions corresponding to the De Franceschi label nm in an
#   orthogonal group over GF(q), q odd.  If the dimension is odd, further
#   processing is necessary.
toTag@:=function(nm)
local F,alpha,e,eam,f,m,mm,mu,prev,ptn,q,ss,tag,term,tp;
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
    Sort(TILDElabels);
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
      elif IsEvenInt(e) then
        Add(ptn,[e,2*m]);
      else
        ss:=sgnO@(e,m,q);
        if e=prev[1] then
          mm:=prev[2]+m;
          ss:=sgnO@(e,mm,q);
          #   replace the top of the stack
          ptn[Size(ptn)]:=[-ss*e,mm];
          prev:=[0,0];
        elif alpha=1 then
          Add(ptn,[ss*e,m]);
          prev:=[e,m];
        else
          Add(ptn,[-ss*e,m]);
          prev:=[e,m];
        fi;
      fi;
    od;
    UniteSet(tag,[f,ptn]); # actually Tildetag!!! TODO
  od;
  return tag;
end;

nameToTagO@:=function(nm)
local tag;
  tag:=toTag@(nm);
  if IsOddInt(nmDim@(nm)) then
    if theSign@(tag)=-1 then
      tag:=changeSign@(tag);
    fi;
  fi;
  return tag;
end;


