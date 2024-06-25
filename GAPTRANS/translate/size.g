#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BSGS, BaseRing, Characteristic, Class,
#  ClassicalGroupType, ClassicalType, ConjPol, Degree, Determinant,
#  DicksonInvariant, DirectSum, EnsureUpperTriangular, FactoredOrder,
#  Factorisation, Factorization, FormsReducibleCase, GCD, GF, GL, GO, GOMinus,
#  GOPlus, GU, Gcd, Generators, Generic, GroupType, IdentifyGroup, Identity,
#  Include, Integers, InvariantBilinearForms, InvariantQuadraticForms,
#  IsApplicable, IsCentral, IsEmpty, IsEven, IsIrreducible, IsOdd,
#  IsQuadFormSimilarity, IsSemisimple, IsSquare, IsTrivial, IsUnipotent, Isqrt,
#  JordanForm, KMatrixSpace, LCM, LMGOrder, LieType, MatrixAlgebra,
#  MultisetToSequence, MyIsIn, Ngens, Omega, OmegaMinus, OmegaPlus, Order,
#  OrderCGO, OrderCGOMinus, OrderCGOPlus, OrthogonalType, Parent,
#  QuadraticForm, QuadraticSpace, RecogniseGOEven, RecognizeClassical, SL, SU,
#  SemiInvariantQuadraticForms, Sp, SpinorNorm, StandardQuadraticForm,
#  SymmetricBilinearFormType, SymmetricToQuadraticForm, SymplecticForm,
#  Transpose, Type, UnitGroup, UnitaryClassSize, UnitaryForm, Universe,
#  VectorSpace, p1, p2

#  Defines: ClassicalClassSize, ClassicalGroupType, FormsReducibleCase,
#  GroupType, IsApplicable, MyIsIn, OrthogonalType, RecogniseGOEven,
#  UnitaryClassSize

DeclareGlobalFunction("GroupType@");

DeclareGlobalFunction("MyIsIn@");

#   code prepared by Eamonn O'Brien and Don Taylor
#   builds on RecogniseClassical returning boolean and precise name
#   return quadratic form when G is orthogonal and reducible
FormsReducibleCase@:=function(G,type)
local F,J,MA,S,d,flag;
  F:=BaseRing(G);
  #   assert #F gt 2;
  d:=Degree(G);
  Assert(1,d=2);
  if IsEvenInt(Size(F)) then
    J:=InvariantQuadraticForms(G);
    Assert(1,Size(J)=1);
    return rec(val1:=true,
      val2:=J[1]);
  fi;
  J:=InvariantBilinearForms(G);
  MA:=MatrixAlgebra(F,d);
  S:=SubStructure(KMatrixSpace(F,d,d),J);
  flag:=s:=ForAny(S,s->DeterminantMat(s)<>0 and 
   SymmetricBilinearFormType(s*FORCEOne(MA))=type);
  if flag then
    return rec(val1:=true,
      val2:=SymmetricToQuadraticForm(s*FORCEOne(MA)));
  else
    return rec(val1:=false,
      val2:=_);
  fi;
end;

#   return "GO+", "SO+", "Omega+" as type for G; same for O- and O
OrthogonalType@:=function(G)
local F,J,U,V,varX,d,factors,form,gord,m,ord,phi,preserves_form,q,qforms,type;
  type:=ClassicalType(G);
  if Type(type)=BoolElt or not (type in 
     ["orthogonalminus","orthogonalplus","orthogonalcircle"]) then
    return rec(val1:=false,
      val2:=_);
  fi;
  Info(InfoClassical,2,"+entering OrthogonalType");
  d:=Degree(G);
  F:=BaseRing(G);
  q:=Size(F);
  if IsIrreducible(G) then
    # =v= MULTIASSIGN =v=
    form:=QuadraticForm(G);
    preserves_form:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    form:=FormsReducibleCase@(G,type);
    preserves_form:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if preserves_form then
    if IsOddInt(q) then
      J:=form+TransposedMat(form);
      V:=VectorSpace(GF(2),2);
      varX:=SubStructure(V,List(Generators(G),g->DicksonInvariant(g)
       *V.1+SpinorNorm(g,J)*V.2));
      m:=Size(varX);
      if not IsBound(G.FactoredOrder) then
        ord:=# translated case< statement
        function(xxx)
          if xxx="orthogonalplus" then return FactoredOrder(OmegaPlus(d,q));
          elif xxx="orthogonalminus" then return FactoredOrder(OmegaMinus(d,q))
         ;
          elif xxx=default then return FactoredOrder(Omega(d,q));
        else Error();fi;end(type);
        G.FactoredOrder:=ord*CollectedFactors(m);
      fi;
      if m=4 then
        type:=# translated case< statement
        function(xxx)
          if xxx="orthogonalplus" then return "GO+";
          elif xxx="orthogonalminus" then return "GO-";
          elif xxx=default then return "GO";
        else Error();fi;end(type);
      elif m=1 then
        type:=# translated case< statement
        function(xxx)
          if xxx="orthogonalplus" then return "Omega+";
          elif xxx="orthogonalminus" then return "Omega-";
          elif xxx=default then return "Omega";
        else Error();fi;end(type);
      else
        if ForAll(Generators(G),g->DicksonInvariant(g)=0) then
          type:=# translated case< statement
          function(xxx)
            if xxx="orthogonalplus" then return "SO+";
            elif xxx="orthogonalminus" then return "SO-";
            elif xxx=default then return "SO";
          else Error();fi;end(type);
        else
          type:=# translated case< statement
          function(xxx)
            if xxx="orthogonalplus" then return "ExtOmega+";
            elif xxx="orthogonalminus" then return "ExtOmega-";
            elif xxx=default then return "ExtOmega";
          else Error();fi;end(type);
        fi;
      fi;
    else
      #   characteristic 2.  GO == SO.  If d is odd, GO == SO == Omega
      J:=form;
      if IsOddInt(d) then
        #   this will never happen (trapped by ClassicalType)
        type:="GO";
        if not IsBound(G.FactoredOrder) then
          G.FactoredOrder:=FactoredOrder(GO(d,q));
        fi;
      elif ForAll(Generators(G),g->DicksonInvariant(g)=0) then
        if not IsBound(G.FactoredOrder) then
          G.FactoredOrder:=# translated case< statement
          function(xxx)
            if xxx="orthogonalplus" then return FactoredOrder(OmegaPlus(d,q));
            elif xxx="orthogonalminus" then return FactoredOrder(OmegaMinus(d,q)
           );
            elif xxx=default then return FactoredOrder(Omega(d,q));
          else Error();fi;end(type);
        fi;
        type:=# translated case< statement
        function(xxx)
          if xxx="orthogonalplus" then return "Omega+";
          elif xxx="orthogonalminus" then return "Omega-";
          elif xxx=default then return "";
        else Error();fi;end(type);
      else
        if not IsBound(G.FactoredOrder) then
          G.FactoredOrder:=# translated case< statement
          function(xxx)
            if xxx="orthogonalplus" then return FactoredOrder(GOPlus(d,q));
            elif xxx="orthogonalminus" then return FactoredOrder(GOMinus(d,q));
            elif xxx=default then return FactoredOrder(GO(d,q));
          else Error();fi;end(type);
        fi;
        type:=# translated case< statement
        function(xxx)
          if xxx="orthogonalplus" then return "GO+";
          elif xxx="orthogonalminus" then return "GO-";
          elif xxx=default then return "";
        else Error();fi;end(type);
      fi;
    fi;
  else
    qforms:=SemiInvariantQuadraticForms(G);
    if IsEmpty(qforms) then
      return rec(val1:=false,
        val2:=_);
    fi;
    form:=qforms[1][2][1];
    factors:=qforms[1][1];
    if IsOddInt(d) and IsEvenInt(q) then
      #   this will never happen (trapped by ClassicalType)
      # =v= MULTIASSIGN =v=
      phi:=UnitGroup(F);
      U:=phi.val1;
      phi:=phi.val2;
      # =^= MULTIASSIGN =^=
      varX:=SubStructure(U,List([1..Ngens(G)],i->factors[i]@@phi));
      # rewritten select statement
      if (Size(varX)=q-1) then
        type:="CGO";
      else
        type:="ExtOmega";
      fi;
    else
      # rewritten select statement
      if IsEvenInt(q) then
        J:=form;
      else
        J:=form+TransposedMat(form);
      fi;
      if IsBound(G.ClassicalName) and G.ClassicalName in 
         ["ConformalOrthogonal","ConformalOrthogonalPlus",
         "ConformalOrthogonalMinus"] then
        type:=# translated case< statement
        function(xxx)
          if xxx="ConformalOrthogonalPlus" then return "CGO+";
          elif xxx="ConformalOrthogonalMinus" then return "CGO-";
          elif xxx=default then return "CGO";
        else Error();fi;end(G.ClassicalName);
      else
        ord:=# translated case< statement
        function(xxx)
          if xxx="orthogonalplus" then return OrderCGOPlus(d,q);
          elif xxx="orthogonalminus" then return OrderCGOMinus(d,q);
          elif xxx=default then return OrderCGO(d,q);
        else Error();fi;end(type);
        # rewritten select statement
        if IsBound(G.Order) then
          gord:=G.Order;
        else
          gord:=LMGOrder(G);
        fi;
        # rewritten select statement
        if (ord=gord) then
          type:=# translated case< statement
          function(xxx)
            if xxx="orthogonalplus" then return "CGO+";
            elif xxx="orthogonalminus" then return "CGO-";
            elif xxx=default then return "CGO";
          else Error();fi;end(type);
        else
          type:=# translated case< statement
          function(xxx)
            if xxx="orthogonalplus" then return "ExtOmega+";
            elif xxx="orthogonalminus" then return "ExtOmega-";
            elif xxx=default then return "ExtOmega";
          else Error();fi;end(type);
        fi;
      fi;
    fi;
  fi;
  return rec(val1:=type,
    val2:=J);
end;

#   return type GL / SL / GU / SU / Sp / GO+ / SO+ / Omega+ / ... for G
InstallGlobalFunction(GroupType@,
function(G)
local 
   D,F,F0,Limit,U,U0,varX,d,factors,flag,form,m,nmr,ok,p1,p2,phi,psi,q,q0,type;
  if IsBound(G.ClassicalType) then
    return rec(val1:=true,
      val2:=G.ClassicalType);
  fi;
  d:=Degree(G);
  F:=BaseRing(G);
  q:=Size(F);
  if d=1 then
    if not IsSquare(q) then
      return rec(val1:=true,
        val2:="GL");
    fi;
    flag:=UnitaryForm(G);
    if flag then
      return rec(val1:=true,
        val2:="GU");
    else
      return rec(val1:=true,
        val2:="GL");
    fi;
  fi;
  if d <= 8 and q <= 9 then
    Limit:=4;
  else
    Limit:=2;
  fi;
  nmr:=0;
  repeat
    flag:=RecognizeClassical(G:NumberOfElements:=30);
    nmr:=nmr+1;
    
  until flag or nmr >= Limit;
  if not flag then
    Info(InfoClassical,1,"Input group appears not to be classical");
    return rec(val1:=false,
      val2:=_);
  fi;
  type:=ClassicalType(G);
  if type in ["orthogonalminus","orthogonalplus","orthogonalcircle"] then
    type:=OrthogonalType@(G);
    if Type(type)=BoolElt then
      return rec(val1:=false,
        val2:=_);
    fi;
  elif d=2 and type="linear" and SymplecticForm(G) then
    if not IsBound(G.FactoredOrder) then
      G.FactoredOrder:=FactoredOrder(SP(d,q));
    fi;
    type:="Sp";
  elif type="unitary" then
    #   G contains SU
    # =v= MULTIASSIGN =v=
    q0:=IsSquare(q);
    ok:=q0.val1;
    q0:=q0.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,ok);
    if UnitaryForm(G) then
      #   GU contains G
      m:=LCM(List(Generators(G),g->Order(DeterminantMat(g))));
      if not IsBound(G.FactoredOrder) then
        G.FactoredOrder:=FactoredOrder(SU(d,q0))*CollectedFactors(m);
      fi;
      type:=# translated case< statement
      function(xxx)
        if xxx=1 then return "SU";
        elif xxx=q0+1 then return "GU";
        elif xxx=default then return "ExtSU";
      else Error();fi;end(m);
    else
      # =v= MULTIASSIGN =v=
      factors:=UnitaryForm(G:Scalars:=true);
      flag:=factors.val1;
      form:=factors.val2;
      factors:=factors.val3;
      # =^= MULTIASSIGN =^=
      Assert(1,flag);
      F0:=Universe(factors);
      # =v= MULTIASSIGN =v=
      phi:=UnitGroup(F);
      U:=phi.val1;
      phi:=phi.val2;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      psi:=UnitGroup(F0);
      U0:=psi.val1;
      psi:=psi.val2;
      # =^= MULTIASSIGN =^=
      # =v= MULTIASSIGN =v=
      p2:=DirectSum(U0,U);
      D:=p2.val1;
      p1:=p2.val2;
      p2:=p2.val3;
      # =^= MULTIASSIGN =^=
      varX:=SubStructure(D,List([1..Ngens(G)],i->p1(factors[i]@@psi)
       +p2(DeterminantMat(G.i)@@phi)));
      m:=Size(varX);
      if not IsBound(G.FactoredOrder) then
        G.FactoredOrder:=FactoredOrder(SU(d,q0))*CollectedFactors(m);
      fi;
      type:=# translated case< statement
      function(xxx)
        if xxx=q-1 then return "CGU";
        elif xxx=Gcd(d,q0-1) then return "CSU";
        elif xxx=default then return "AltSU";
      else Error();fi;end(m);
    fi;
  elif type="symplectic" then
    if SymplecticForm(G) then
      if not IsBound(G.FactoredOrder) then
        G.FactoredOrder:=FactoredOrder(SP(d,q));
      fi;
      type:="Sp";
    else
      # =v= MULTIASSIGN =v=
      factors:=SymplecticForm(G:Scalars:=true);
      flag:=factors.val1;
      form:=factors.val2;
      factors:=factors.val3;
      # =^= MULTIASSIGN =^=
      Assert(1,flag);
      m:=LCM(List(factors,f->Order(f)));
      if not IsBound(G.FactoredOrder) then
        G.FactoredOrder:=FactoredOrder(SP(d,q))*CollectedFactors(m);
      fi;
      # rewritten select statement
      if (m=q-1) then
        type:="CSp";
      else
        type:="ExtSp";
      fi;
    fi;
  elif type="linear" then
    m:=LCM(List(Generators(G),g->Order(DeterminantMat(g))));
    if not IsBound(G.FactoredOrder) then
      G.FactoredOrder:=FactoredOrder(SL(d,q))*CollectedFactors(m);
    fi;
    type:=# translated case< statement
    function(xxx)
      if xxx=1 then return "SL";
      elif xxx=q-1 then return "GL";
      elif xxx=default then return "ExtSL";
    else Error();fi;end(m);
  fi;
  G.ClassicalType:=type;
  return rec(val1:=true,
    val2:=type);
end);

RecogniseGOEven@:=function(G)
local F,Q,Q_,U,varX,d,factors,flag,forms,g,i,m,p,phi,q,qforms,tp,type;
  d:=Degree(G);
  F:=BaseRing(G);
  q:=Size(F);
  p:=Characteristic(F);
  #   difficult cases
  if q=2 then
    if d=3 then
      BSGS(G);
      if Size(G)=6 and IdentifyGroup(G)=[6,1] then
        G.ClassicalType:="GO";
        return rec(val1:=true,
          val2:="GO");
      fi;
    fi;
    if d=5 then
      BSGS(G);
      if Size(G)=720 and IdentifyGroup(G)=[720,763] then
        G.ClassicalType:="GO";
        return rec(val1:=true,
          val2:="GO");
      fi;
    fi;
  fi;
  #   check that G is isomorphic to Sp(d - 1, q)
  # =v= MULTIASSIGN =v=
  type:=LieType(G,p);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if d=3 then
    if not (flag and type=["A",QuoInt(d,2),q]) then
      return rec(val1:=false,
        val2:=_);
    fi;
  else
    if not (flag and type=["C",QuoInt(d,2),q]) then
      return rec(val1:=false,
        val2:=_);
    fi;
  fi;
  forms:=InvariantQuadraticForms(G);
  if not IsEmpty(forms) then
    tp:="GO";
    if not IsBound(G.FactoredOrder) then
      G.FactoredOrder:=FactoredOrder(GO(d,q));
    fi;
  else
    #   quick check if G is standard
    Q:=StandardQuadraticForm(d,q);
    if ForAll(Generators(G),g->IsQuadFormSimilarity(Q,g)) then
      factors:=[];
      for i in [1..Ngens(G)] do
        g:=G.i;
        Q_:=EnsureUpperTriangular(g*Q*TransposedMat(g));
        Assert(1,Tuple([j,k]):=ForAny([1..d],
          k->ForAny([1..k],
            j->Q[j][k]<>0)));
        Add(factors,Q_[j][k]/Q[j][k]);
      od;
    else
      qforms:=SemiInvariantQuadraticForms(G);
      if IsEmpty(qforms) then
        return rec(val1:=false,
          val2:=_);
      fi;
      factors:=qforms[1][1];
    fi;
    # =v= MULTIASSIGN =v=
    phi:=UnitGroup(F);
    U:=phi.val1;
    phi:=phi.val2;
    # =^= MULTIASSIGN =^=
    varX:=SubStructure(U,List([1..Ngens(G)],i->factors[i]@@phi));
    m:=Size(varX);
    if not IsBound(G.FactoredOrder) then
      G.FactoredOrder:=FactoredOrder(GO(d,q))*CollectedFactors(m);
    fi;
    # rewritten select statement
    if (m=q-1) then
      tp:="CGO";
    else
      tp:="ExtOmega";
    fi;
  fi;
  G.ClassicalType:=tp;
  return rec(val1:=true,
    val2:=tp);
end;

ClassicalGroupType@:=function(G)
#  -> ,BoolElt ,MonStgElt  if G := identified as a classical group in its
#  natural representation , then return true and classical type of group
local F,d,flag,gord,q,type;
  Info(InfoClassical,2,"+entering ClassicalGroupType");
  if IsBound(G.ClassicalType) then
    return rec(val1:=true,
      val2:=G.ClassicalType);
  fi;
  if IsTrivial(G) then
    Info(InfoClassical,1,"Group is trivial -- cannot decide type");
    return rec(val1:=false,
      val2:=_);
  fi;
  d:=Degree(G);
  F:=BaseRing(G);
  q:=Size(F);
  if d <= 3 and q <= 4 then
    BSGS(G);
  fi;
  if d=2 and q <= 4 then
    type:=ClassicalType(G);
    if type=false then
      Info(InfoClassical,1,"Group appears not to be classical");
      return rec(val1:=false,
        val2:=_);
    fi;
    gord:=Size(G);
    if gord=2 then
      if q=2 and type="orthogonalplus" then
        G.ClassicalType:="SO+";
        return rec(val1:=true,
          val2:="SO+");
      elif q=3 and type="orthogonalminus" then
        G.ClassicalType:="Omega-";
        return rec(val1:=true,
          val2:="Omega-");
      fi;
    elif gord=3 then
      if q=2 and type="orthogonalminus" then
        G.ClassicalType:="Omega-";
        return rec(val1:=true,
          val2:="Omega-");
      elif q=4 and type="orthogonalplus" then
        G.ClassicalType:="Omega+";
        return rec(val1:=true,
          val2:="Omega+");
      fi;
    elif gord=4 then
      if q=3 and type="orthogonalminus" and IdentifyGroup(G)=[4,1] then
        G.ClassicalType:="SO-";
        return rec(val1:=true,
          val2:="SO-");
      elif q=3 and type="orthogonalplus" and IdentifyGroup(G)=[4,2] then
        G.ClassicalType:="GO+";
        return rec(val1:=true,
          val2:="GO+");
      fi;
    elif gord=5 then
      #   q must be 4, only one class of subgroups of order 5
      G.ClassicalType:="Omega-";
      return rec(val1:=true,
        val2:="Omega-");
    elif gord=6 then
      if q=2 then
        G.ClassicalType:="GL";
        return rec(val1:=true,
          val2:="GL");
      elif q=4 then
        if G=GOPlus(2,4) then
          G.ClassicalType:="GO+";
          return rec(val1:=true,
            val2:="GO+");
        elif G=SU(2,2) then
          G.ClassicalType:="SU";
          return rec(val1:=true,
            val2:="SU");
        else
          Info(InfoClassical,1,"Cannot decide type");
          return rec(val1:=false,
            val2:=_);
        fi;
      fi;
    elif gord=8 then
      #   q must be 3, three classes of subgroups of order 8
      if type="orthogonalminus" then
        G.ClassicalType:="GO-";
        return rec(val1:=true,
          val2:="GO-");
      fi;
    elif gord=10 then
      #   q must be 4, only one class of subgroups of order 10
      G.ClassicalType:="GO-";
      return rec(val1:=true,
        val2:="GO-");
    elif q=4 and IsIrreducible(G) and IdentifyGroup(G)=[18,3] then
      G.ClassicalType:="GU";
      return rec(val1:=true,
        val2:="GU");
    elif gord=24 then
      #   q must be 3
      G.ClassicalType:="SL";
      return rec(val1:=true,
        val2:="SL");
    elif q in [3,4] and IsIrreducible(G) and IdentifyGroup(G) in [[48,29]
       ,[180,19]] and type="linear" then
      G.ClassicalType:="GL";
      return rec(val1:=true,
        val2:="GL");
    fi;
    Info(InfoClassical,1,"Cannot decide type");
    return rec(val1:=false,
      val2:=_);
  fi;
  #   recognise GO(2n + 1, 2^k)
  if IsOddInt(d) and IsEvenInt(q) and not IsIrreducible(G) then
    # =v= MULTIASSIGN =v=
    type:=RecogniseGOEven@(G);
    flag:=type.val1;
    type:=type.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    type:=GroupType@(G);
    flag:=type.val1;
    type:=type.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if flag then
    G.ClassicalType:=type;
    return rec(val1:=true,
      val2:=type);
  else
    Info(InfoClassical,1,"Cannot decide type");
    return rec(val1:=false,
      val2:=_);
  fi;
end;

#   G conjugate of natural copy of classical group
#   decide if x is in G
InstallGlobalFunction(MyIsIn@,
function(G,x)
local Add,CB,H,ValidTypes@,d,flag,q,q0,type;
  lvarAdd:=ValueOption("lvarAdd");
  if lvarAdd=fail then
    lvarAdd:=Set([]);
  fi;
  if IsTrivial(G) then
    return x in G;
  fi;
  d:=Degree(G);
  q:=Size(BaseRing(G));
  if d=2 and q <= 4 then
    return x in G;
  fi;
  if d=2 and not IsIrreducible(G) then
    return x in G;
  fi;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  ValidTypes@:=Set(["Sp","SU","GU","Omega+","Omega-","Omega","O+","O-","O",
   "SO+","SO-","SO","GO+","GO-","GO"]);
  if (not flag) or (flag and not (type in Union(ValidTypes@,lvarAdd))) then
    Error("Type of input group must be one of ",ValidTypes@);
  fi;
  if IsOddInt(d) and IsEvenInt(q) and type="GO" then
    Error("Function does not apply to this case");
  fi;
  if type="GL" then
    return DeterminantMat(x)<>0;
  elif type="SL" then
    return DeterminantMat(x)=1;
  fi;
  CB:=TransformMatrix@(G);
  # rewritten select statement
  if type in ["SU","GU"] then
    q0:=RootInt(q);
  else
    q0:=q;
  fi;
  H:=StandardGroup@(type,d,q0);
  return x^CB in H;
end);

#   we are not able to write down centralisers for elements outside
#   of Omega in even char
IsApplicable@:=function(G,g,type)
local V,flag,form,type;
  if not (type in ["SO+","SO-","SO","GO+","GO-","GO"]) then
    return true;
  fi;
  if IsOddInt(Size(BaseRing(G))) then
    return true;
  fi;
  # =v= MULTIASSIGN =v=
  type:=QuadraticForm(G);
  flag:=type.val1;
  form:=type.val2;
  type:=type.val3;
  # =^= MULTIASSIGN =^=
  V:=QuadraticSpace(form);
  return DicksonInvariant(V,g)=0;
end;

#   size of conjugacy class of g in GU or SU
UnitaryClassSize@:=function(g,special)
local ConjPol,G1,JF,SPoly,SPoly1,varX,_,b,c,f,forgetvar1,forgetvar2,gcd,q;
  c:=Factorization(1);
  # =v= MULTIASSIGN =v=
  b:=JordanForm(g);
  forgetvar1:=b.val1;
  forgetvar2:=b.val2;
  b:=b.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  q:=IsSquare(Size(BaseRing(g)));
  forgetvar1:=q.val1;
  q:=q.val2;
  # =^= MULTIASSIGN =^=
  ConjPol:=ConjugatePolynomial@(true);
  JF:=[];
  SPoly1:=List( # {-list:
    b,x->x[1]);
  SPoly:=Set([]);
  for f in SPoly1 do
    if f=ConjPol(f) then
      UniteSet(SPoly,f); # actually TildeSPoly!!! TODO
    else
      if not (ConjPol(f) in SPoly) then
        UniteSet(SPoly,f); # actually TildeSPoly!!! TODO
      fi;
    fi;
  od;
  gcd:=0;
  for f in SPoly do
    JF:=List(Filtered(b,x->x[1]=f),x->x[2]);
    #   the values passed to UnipotentCentraliserOrder are not important,
    #  except for JF
    if f=ConjPol(f) then
      G1:=GU(2,q^Degree(f));
      varX:=Identity(G1);
      c:=c*UnipotentCentraliserOrder@("GU",G1,varX,
       varX:JF:=MultisetToSequence(JF));
    else
      G1:=GL(2,q^(2*Degree(f)));
      varX:=Identity(G1);
      c:=c*UnipotentCentraliserOrder@("GL",G1,varX,
       varX:JF:=MultisetToSequence(JF));
    fi;
    gcd:=Gcd(gcd,Gcd(JF));
  od;
  if special then
    gcd:=Gcd(gcd,q+1);
    c:=c*Factorization(gcd);
    c:=c/Factorization(q+1);
  fi;
  return c;
end;

ClassicalClassSize@:=function(G,g)
#  -> ,RngIntElt  Size of conjugacy class of g in classical group G
local CB,Gr,ValidTypes@,_,c,d,flag,forgetvar1,form,q,type;
  if not Generic(Parent(g))=Generic(G) then
    Error("Input element is not in group");
  fi;
  if not MyIsIn@(G,g:Add:=Set(["GL","SL"])) then
    Error("Input element is not in group");
  fi;
  if IsCentral(G,g) then
    return 1;
  fi;
  d:=Degree(G);
  q:=Size(BaseRing(G));
  if d=2 and q <= 4 then
    return Size(Class(G,g));
  fi;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType@(G);
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  ValidTypes@:=Set(["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+",
   "SO-","SO","GO+","GO-","GO"]);
  if not flag and type in ValidTypes@ then
    Error(["Type of group must be one of ",ValidTypes@]);
  fi;
  if type="GO" and IsOddInt(d) and IsEvenInt(q) then
    Error("Function does not apply to this case");
  fi;
  CB:=TransformMatrix@(G);
  if type="SL" then
    c:=SLCentralizerOrder@(G,g);
  elif type="GL" then
    c:=GLCentralizerOrder@(G,g);
  elif type in ["GU","SU"] then
    c:=UnitaryClassSize@(g^CB,type="SU");
  elif IsSemisimple(g) then
    #   Gr := G^CB; Gr`ClassicalType := G`ClassicalType;
    #   unitary case considered above so q is correct
    Gr:=StandardGroup@(type,d,q);
    Gr.ClassicalType:=G.ClassicalType;
    c:=SSCentralizerOrder(Gr,g^CB);
  elif IsUnipotent(g) and type="Sp" then
    # =v= MULTIASSIGN =v=
    form:=SymplecticForm(G);
    forgetvar1:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    c:=UnipotentCentraliserOrder@("Sp",G,g,form);
  elif IsUnipotent(g) and IsApplicable@(G,g,type) then
    # =v= MULTIASSIGN =v=
    form:=OrthogonalType@(G);
    type:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    c:=UnipotentCentraliserOrder@(type,G,g,form);
  else
    c:=MyCentraliserOrder@(type,g^CB);
  fi;
  return Int((FactoredOrder(G)/c));
end;


