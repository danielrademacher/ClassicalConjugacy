#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AssociativeArray, BaseRing, Classes, ClassesForSpO,
#  ClassicalCentraliser, ClassicalClassMap, ClassicalClasses,
#  ClassicalConjugacyClasses, ClassicalGroupType, ClassicalIsConjugate, Degree,
#  Divisors, GCD, GF, Generic, HasBSGS, IdentityHomomorphism, Include,
#  IsDivisibleBy, IsEven, IsOdd, IsPrimePower, IsTrivial, Isqrt,
#  LMGHomomorphism, Ngens, Order, ParallelSort, Position, PrimitiveElement,
#  RandomSchreier, ScalarMatrix, f, phi, tau

#  Defines: ClassesForSpO, ClassicalCentreOrder,
#  ProjectiveClassicalCentraliser, ProjectiveClassicalClasses,
#  ProjectiveClassicalIsConjugate

#  
#  $Id: ProjClasses.m 65133 2021-11-21 02:56:51Z don $

#   functions prepared with Derek Holt and Don Taylor
ClassicalCentreOrder@:=AssociativeArray();
ClassicalCentreOrder@["GL"]:=function(d,q)
return q-1;
end;

ClassicalCentreOrder@["SL"]:=function(d,q)
return Gcd(d,q-1);
end;

ClassicalCentreOrder@["GU"]:=function(d,q)
return q+1;
end;

ClassicalCentreOrder@["SU"]:=function(d,q)
return Gcd(d,q+1);
end;

ClassicalCentreOrder@["Sp"]:=function(d,q)
return Gcd(2,q-1);
end;

ClassicalCentreOrder@["GO"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return 2;fi;end(IsEvenInt(q));
end;

ClassicalCentreOrder@["SO"]:=function(d,q)
return 1;
end;

ClassicalCentreOrder@["Omega"]:=function(d,q)
return 1;
end;

ClassicalCentreOrder@["GO+"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return 2;fi;end(IsEvenInt(q));
end;

ClassicalCentreOrder@["SO+"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return 2;fi;end(IsEvenInt(q));
end;

ClassicalCentreOrder@["Omega+"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return (# rewritten select statement
  function(xxx)if xxx then return 2;else return 
   1;fi;end(IsEvenInt(QuoInt(d*(q-1),4))));fi;end(IsEvenInt(q));
end;

ClassicalCentreOrder@["GO-"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return 2;fi;end(IsEvenInt(q));
end;

ClassicalCentreOrder@["SO-"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return 2;fi;end(IsEvenInt(q));
end;

ClassicalCentreOrder@["Omega-"]:=function(d,q)
return # rewritten select statement
  function(xxx)if xxx then return 1;else return (# rewritten select statement
  function(xxx)if xxx then return 2;else return 1;fi;end(IsOddInt(QuoInt(d*(q-1)
   ,4))));fi;end(IsEvenInt(q));
end;

#   tau is hom from standard classical group G to its projective copy G / <z>
ClassesForSpO@:=function(G,tau,z)
local C,CL,MatricesOnly,cno,g,i,index,known,mm,phi,projclasslen,projclassrep;
  MatricesOnly:=ValueOption("MatricesOnly");
  if MatricesOnly=fail then
    MatricesOnly:=false;
  fi;
  C:=ClassicalConjugacyClasses@(G);
  if Order(z)=1 then
    mm:=List([1..Size(C)],i->[C[i][1],C[i][2],C[i][3]]);
    if MatricesOnly then
      return rec(val1:=mm,
        val2:=_);
    else
      return rec(val1:=List([1..Size(C)],i->[C[i][1],C[i][2],tau(C[i][3])]),
        val2:=mm);
    fi;
  fi;
  phi:=ClassicalClassMap@(G);
  projclassrep:=List([1..Size(C)],i->i);
  projclasslen:=[];
  known:=Set([]);
  for i in [1..Size(C)] do
    if i in known then
      continue;
    fi;
    g:=C[i][3];
    if not ClassicalIsConjugate@(G,g,g*z) then
      #   length of the class of the image of g in the projective
      #  group is C[i][2] if this condition holds and C[i][2]/2
      #  otherwise.  
      cno:=phi(g*z);
      UniteSet(TILDEknown,cno);
      projclassrep[cno]:=i;
      projclasslen[i]:=C[i][2];
    else
      projclasslen[i]:=QuoInt(C[i][2],2);
    fi;
  od;
  index:=Filtered([1..Size(projclassrep)],i->projclassrep[i]=i);
  mm:=List(index,i->[Order(C[i][3]),projclasslen[i],C[i][3]]);
  if MatricesOnly then
    return rec(val1:=mm,
      val2:=_);
  else
    CL:=List(index,i->[Order(C[i][3]),projclasslen[i],tau(C[i][3])]);
    return rec(val1:=CL,
      val2:=mm);
  fi;
end;

#  ============================================================================
#  =
ProjectiveClassicalClasses@:=function(type,n,q)
#  -> ,SeqEnum ,GrpPerm ,HomGrp ,SeqEnum  The conjugacy classes of the
#  projective classical group P of supplied type ; return the classes , P , the
#  homomorphism f from the classical group G to P , and preimages of the class
#  representatives in G
local 
   C,F,G,MatricesOnly,P,UseLMGHom,ValidTypes@,available,c,cc,count,d,f,flg,g,h,
   i,index,k,m,mm,pClassSz,phi,xi,z;
  UseLMGHom:=ValueOption("UseLMGHom");
  if UseLMGHom=fail then
    UseLMGHom:=false;
  fi;
  MatricesOnly:=ValueOption("MatricesOnly");
  if MatricesOnly=fail then
    MatricesOnly:=false;
  fi;
  ValidTypes@:=["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-",
   "SO","GO+","GO-","GO"];
  if not type in ValidTypes@ then
    Error(["Type must be one of ",ValidTypes@]);
  fi;
  if not IsPrimePower(q) then
    Error("Invalid field size");
  fi;
  if not n > 1 then
    Error("Degree must be at least 2");
  fi;
  if type in ["GO","SO","Omega"] then
      if not IsOddInt(n) and n > 2 then
      Error("Degree must be odd and at least 3");
    fi;
      if not IsOddInt(q) then
      Error("Field size must be odd");
    fi;
  elif type in ["Sp","Omega+","SO+","GO+","Omega-","SO-","GO-"] then
      if not IsEvenInt(n) then
      Error("Degree must be even");
    fi;
  fi;
  # =v= MULTIASSIGN =v=
  P:=StandardGroup@(type,n,q:Projective:=true);
  G:=P.val1;
  P:=P.val2;
  # =^= MULTIASSIGN =^=
  if IsTrivial(P) then
    #   e.g. POmegaPlus (2, 2)
    mm:=[[1,1,G.0]];
    if MatricesOnly then
      return rec(val1:=mm,
        val2:=_,
        val3:=_,
        val4:=_);
    else
      f:=GroupHomomorphismByImages(G,P,
        GeneratorsOfGroup(G),List([1..Ngens(G)],i->P.0));
      return rec(val1:=Classes(P),
        val2:=P,
        val3:=f,
        val4:=mm);
    fi;
  elif n=2 and q=3 and type="GO+" then
    mm:=[[1,1,G.0],[2,1,G.2]];
    if MatricesOnly then
      return rec(val1:=mm,
        val2:=_,
        val3:=_,
        val4:=_);
    else
      f:=GroupHomomorphismByImages(G,P,
        GeneratorsOfGroup(G),[P.0,P.1]);
      return rec(val1:=Classes(P),
        val2:=P,
        val3:=f,
        val4:=mm);
    fi;
  fi;
  d:=ClassicalCentreOrder@[type](n,q);
  # rewritten select statement
  if type in ["GU","SU"] then
    F:=GF(q^2);
  else
    F:=GF(q);
  fi;
  xi:=PrimitiveElement(F);
  z:=ScalarMat(F,n,xi);
  z:=(z^(QuoInt((Size(F)-1),d)))*FORCEOne(Generic(G));
  if not MatricesOnly then
    #   basic checks before setting up homomorphism
    Assert(1,Ngens(P)=Ngens(G));
    Assert(1,ForAll([1..Ngens(G)],i->Order(G.i) mod Order(P.i)=0));
    RandomSchreier(P);
    if not UseLMGHom or HasBSGS(G) then
      f:=GroupHomomorphismByImages(G,P,
        GeneratorsOfGroup(G),List([1..Ngens(G)],i->P.i));
    else
      f:=LMGHomomorphism(G,List([1..Ngens(G)],i->P.i));
    fi;
  fi;
  if not (type in ["GL","SL","GU","SU"]) then
    if MatricesOnly then
      f:=IdentityHomomorphism(G);
      mm:=ClassesForSpO@(G,f,z:MatricesOnly:=true);
      return rec(val1:=mm,
        val2:=_,
        val3:=_,
        val4:=_);
    else
      # =v= MULTIASSIGN =v=
      mm:=ClassesForSpO@(G,f,z);
      cc:=mm.val1;
      mm:=mm.val2;
      # =^= MULTIASSIGN =^=
      P.Classes:=cc;
      C:=Classes(P);
      index:=List([1..Size(cc)],i->Position(C,cc[i]));
      ParallelSort(TILDEindex,TILDEmm);
      return rec(val1:=C,
        val2:=P,
        val3:=f,
        val4:=mm);
    fi;
  fi;
  cc:=ClassicalClasses(G);
  phi:=ClassicalClassMap@(G);
  if d=1 then
    mm:=List(cc,c->[c[1],c[2],c[3]]);
    if not MatricesOnly then
      cc:=List(cc,c->[c[1],c[2],f(c[3])]);
    fi;
  else
    pClassSz:=List([1..Size(cc)],i->0);
    available:=List([1..Size(cc)],i->true);
    #  changed:for i -> c in cc do
    for i in [1..Size(cc)] do
      c:=cc[i];
      if available[i] then
        g:=c[3];
        count:=1;
        for k in [1..d-1] do
          h:=g*z^k;
          if not ClassicalIsConjugate@(G,g,h) then
            available[phi(h)]:=false;
          else
            count:=count+1;
          fi;
        od;
        # =v= MULTIASSIGN =v=
        m:=IsDivisibleBy(c[2],count);
        flg:=m.val1;
        m:=m.val2;
        # =^= MULTIASSIGN =^=
        Assert(1,flg);
        pClassSz[i]:=m;
      fi;
    od;
    mm:=List(Filtered([1..Size(cc)],i->available[i]),i->[cc[i][1],pClassSz[i]
     ,cc[i][3]]);
    if not MatricesOnly then
      # FOLLOWING COMMAND IS `WHERE` 
      x:=f(cc[i][3]);
      cc:=List(Filtered([1..Size(cc)],i->available[i]),i->[Order(x),pClassSz[i]
       ,x]);
    fi;
  fi;
  if MatricesOnly then
    return rec(val1:=mm,
      val2:=_,
      val3:=_,
      val4:=_);
  else
    P.Classes:=cc;
    C:=Classes(P);
    index:=List([1..Size(cc)],i->Position(C,cc[i]));
    ParallelSort(TILDEindex,TILDEmm);
    return rec(val1:=C,
      val2:=P,
      val3:=f,
      val4:=mm);
  fi;
end;

ProjectiveClassicalCentraliser@:=function(G,g)
#  -> ,Grp  return preimage in the classical group G of centraliser of image of
#  g in the central quotient of G
local C,D,F,ValidTypes@,varZ,c,d,f,i,n,o,q,type,xi,z;
  ValidTypes@:=["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-",
   "SO","GO+","GO-","GO"];
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  f:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not type in ValidTypes@ then
    Error(["Function does not apply to classical group of type",type]);
  fi;
  n:=Degree(G);
  F:=BaseRing(G);
  # rewritten select statement
  if type in ["GU","SU"] then
    q:=RootInt(Size(F));
  else
    q:=Size(F);
  fi;
  d:=ClassicalCentreOrder@[type](n,q);
  xi:=PrimitiveElement(F);
  z:=ScalarMat(F,n,xi);
  z:=(z^(QuoInt((Size(F)-1),d)))*FORCEOne(Generic(G));
  varZ:=SubStructure(Generic(G),z);
  C:=ClassicalCentraliser(G,g);
  if IsTrivial(varZ) then
    return C;
  fi;
  o:=Size(varZ);
  D:=DivisorsInt(o);
  for i in [1..Size(D)-1] do
    # =v= MULTIASSIGN =v=
    c:=ClassicalIsConjugate@(G,g,g*z^D[i]);
    f:=c.val1;
    c:=c.val2;
    # =^= MULTIASSIGN =^=
    if f then
      return SubStructure(Generic(G),C,#TODO CLOSURE
        c);
    fi;
  od;
  return C;
end;

ProjectiveClassicalIsConjugate@:=function(G,g,h)
#  -> ,BoolElt ,GrpMatElt  if the images of g and h are conjugate in the
#  central quotient of the classical group G , then return true and preimage in
#  G of a conjugating element , else return false
local F,ValidTypes@,varZ,c,d,f,i,n,o,q,type,xi,z;
  ValidTypes@:=["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-",
   "SO","GO+","GO-","GO"];
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  f:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not type in ValidTypes@ then
    Error(["Function does not apply to classical group of type",type]);
  fi;
  n:=Degree(G);
  F:=BaseRing(G);
  # rewritten select statement
  if type in ["GU","SU"] then
    q:=RootInt(Size(F));
  else
    q:=Size(F);
  fi;
  d:=ClassicalCentreOrder@[type](n,q);
  xi:=PrimitiveElement(F);
  z:=ScalarMat(F,n,xi);
  z:=(z^(QuoInt((Size(F)-1),d)))*FORCEOne(Generic(G));
  varZ:=SubStructure(Generic(G),z);
  if IsTrivial(varZ) then
    # =v= MULTIASSIGN =v=
    c:=ClassicalIsConjugate@(G,g,h);
    f:=c.val1;
    c:=c.val2;
    # =^= MULTIASSIGN =^=
    if f then
      return rec(val1:=f,
        val2:=c);
    else
      return rec(val1:=f,
        val2:=_);
    fi;
  fi;
  o:=Size(varZ);
  for i in [0..o-1] do
    # =v= MULTIASSIGN =v=
    c:=ClassicalIsConjugate@(G,g,h*z^i);
    f:=c.val1;
    c:=c.val2;
    # =^= MULTIASSIGN =^=
    if f then
      return rec(val1:=f,
        val2:=c);
    fi;
  od;
  return rec(val1:=false,
    val2:=_);
end;

#  ----------------------------------------------------------------------------
#  -

