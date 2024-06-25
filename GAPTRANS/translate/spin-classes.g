#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AddAttribute, Append, BaseRing, CMfn, CartesianPower,
#  Centraliser, Centralizer, CheckTauAndPhi, ClassCentralizer, Classes,
#  ClassicalClassMap, ClassicalClasses, ClassicalIsConjugate, Codomain,
#  CompositionTree, CompositionTreeElementToWord, CompositionTreeNiceGroup,
#  CompositionTreeSeries, CompositionTreeVerify, ConjugacyClasses, Dimension,
#  Evaluate, FormType, Function, Generators, Generic, HasAttribute, Id, IsEven,
#  LMGCentre, Ngens, Order, ParallelSort, Random, SanityChecks, Set,
#  SpinCentraliser, SpinClasses, phi, tau

#  Defines: CheckTauAndPhi, SanityChecks, SpinCentraliser, SpinCentralizer,
#  SpinClassMap, SpinClasses, SpinConjugacyClasses, SpinIsConjugate

DeclareGlobalFunction("CheckTauAndPhi@");

DeclareGlobalFunction("SanityChecks@");

AddAttribute(GrpMat,"SpinHom");
AddAttribute(GrpMat,"SpinInvHom");
AddAttribute(GrpMat,"SpinHomImage");
AddAttribute(GrpMat,"SpinCentre");
AddAttribute(GrpMat,"SpinLifts");
#  Forward declaration of CheckTauAndPhi
#  Forward declaration of SanityChecks
SpinClasses@:=function(G)
#  -> ,SeqEnum ,SeqEnum  Conjugacy classes of spin group G
local 
   C,H,HClassCt,R,S,T,TH,ZG,ZH,a,b,c,cG,ccH,cent,centord,centralizerGens,cents,
   cl,classes,havehoms,invlifts,phi,reps,sG,splits,tau,x,xG,z;
  if HasAttribute(G,"Classes") then
    cl:=Classes(G);
    return rec(val1:=cl,
      val2:=List([1..Size(cl)],i->ClassCentralizer(G,i)));
  fi;
  havehoms:=IsBound(G.SpinHom) and IsBound(G.SpinInvHom) and 
   IsBound(G.SpinHomImage) and IsBound(G.SpinCentre);
  if havehoms then
    tau:=G.SpinHom;
    phi:=G.SpinInvHom;
    H:=G.SpinHomImage;
    ZG:=G.SpinCentre;
  else
    T:=CompositionTree(G);
    Info(InfoClasses,1,"Got composition tree");
    # =v= MULTIASSIGN =v=
    b:=CompositionTreeSeries(G);
    S:=b.val1;
    a:=b.val2;
    b:=b.val3;
    # =^= MULTIASSIGN =^=
    phi:=b[Size(b)];
    tau:=a[Size(a)];
    ZG:=LMGCentre(G);
    H:=Codomain(tau);
    TH:=CompositionTree(H);
    ZH:=LMGCentre(H);
    SanityChecks@(G,H,ZG,ZH);
    if Size(ZH) > 1 then
      CheckTauAndPhi@(G,H,ZG,ZH,tau,phi); # actually Tildetau, TILDEphi!!! TODO
    fi;
    G.SpinHom:=tau;
    G.SpinInvHom:=phi;
    G.SpinHomImage:=H;
    G.SpinCentre:=ZG;
  fi;
  #  if havehoms
  repeat
    z:=Random(ZG);
    
  until z<>G.0 and Function(tau)(z)=H.0;
  ccH:=ConjugacyClasses(H);
  reps:=[];
  HClassCt:=0;
  Info(InfoClasses,1,Size(ccH),"classes of orthogonal group to lift");
  invlifts:=[];
  for c in ccH do
    HClassCt:=HClassCt+1;
    Info(InfoClasses,2,"lifting class number",HClassCt);
    C:=Centralizer(H,c[3]);
    cG:=Function(phi)(c[3]);
    splits:=true;
    centralizerGens:=[];
    for x in Generators(C) do
      xG:=Function(phi)(x);
      if Comm(cG,xG)<>G.0 then
        if splits then
          sG:=xG;
          centralizerGens:=Concatenation(centralizerGens,List(centralizerGens,
           cg->sG*cg*sG^-1));
          splits:=false;
        else
          Add(centralizerGens,xG*sG^-1);
        fi;
        Add(centralizerGens,xG^2);
      else
        Add(centralizerGens,xG);
        if not splits then
          Add(centralizerGens,sG*xG*sG^-1);
        fi;
      fi;
    od;
    Info(InfoClasses,2,"Does this class split?",splits);
    cent:=SubStructure(Generic(G),ZG,#TODO CLOSURE
      centralizerGens);
    if splits then
      centord:=2*Size(C);
      Add(reps,[cG,c[2],cent,HClassCt]);
      Add(reps,[z*cG,c[2],cent,HClassCt]);
    else
      centord:=Size(C);
      Add(reps,[cG,2*c[2],cent,HClassCt]);
    fi;
    cent.Order:=centord;
  od;
  Info(InfoClasses,1,"Group has",Size(reps),"classes");
  R:=List(reps,r->[Order(r[1]),r[2],r[1],r[3],r[4]]);
  S:=List([1..Size(R)],i->[R[i][1],R[i][2]]);
  ParallelSort(S,R); # actually TildeS, TildeR!!! TODO
  classes:=List(R,r->[r[1],r[2],r[3]]);
  cents:=List(R,r->r[4]);
  G.SpinLifts:=List([1..Size(ccH)],hno->Filtered([1..Size(classes)],i->R[i][5]
   =hno));
  G.Classes:=[classes,cents];
  return rec(val1:=classes,
    val2:=cents);
end;

SpinConjugacyClasses@:=function(G)
#  -> ,SeqEnum ,SeqEnum  Conjugacy classes of spin group G
return SpinClasses@(G);
end;

SpinIsConjugate@:=function(G,g,h)
#  -> ,BoolElt ,GrpMatElt  Are elements g , h of spin group G conjugate in G ?
local CH,H,S,T,TH,ZG,ZH,a,b,celt1,elt,g,gen,havehoms,isc,phi,tau;
  havehoms:=IsBound(G.SpinHom) and IsBound(G.SpinInvHom) and 
   IsBound(G.SpinHomImage);
  if havehoms then
    tau:=G.SpinHom;
    phi:=G.SpinInvHom;
    H:=G.SpinHomImage;
  else
    T:=CompositionTree(G);
    Info(InfoClasses,1,"Got composition tree");
    # =v= MULTIASSIGN =v=
    b:=CompositionTreeSeries(G);
    S:=b.val1;
    a:=b.val2;
    b:=b.val3;
    # =^= MULTIASSIGN =^=
    phi:=b[Size(b)];
    tau:=a[Size(a)];
    ZG:=LMGCentre(G);
    H:=Codomain(tau);
    TH:=CompositionTree(H);
    ZH:=LMGCentre(H);
    SanityChecks@(G,H,ZG,ZH);
    if Size(ZH) > 1 then
      CheckTauAndPhi@(G,H,ZG,ZH,tau,phi); # actually Tildetau, Tildephi!!! TODO
    fi;
    G.SpinHom:=tau;
    G.SpinInvHom:=phi;
    G.SpinHomImage:=H;
    G.SpinCentre:=ZG;
  fi;
  #  if havehoms
  tau:=Function(tau);
  phi:=Function(phi);
  # =v= MULTIASSIGN =v=
  elt:=ClassicalIsConjugate@(H,tau(g),tau(h));
  isc:=elt.val1;
  elt:=elt.val2;
  # =^= MULTIASSIGN =^=
  if not isc then
    return rec(val1:=false,
      val2:=_);
  fi;
  celt1:=phi(elt);
  g:=g^celt1;
  #  not tau(g) = tau(h)
  CH:=Centraliser(H,tau(h));
  #  if g and h are conjugate then they are conjugate by generator of CH
  for gen in Generators(CH) do
    if g^phi(gen)=h then
      return rec(val1:=true,
        val2:=celt1*phi(gen));
    fi;
  od;
  return rec(val1:=false,
    val2:=_);
end;

SpinCentraliser@:=function(G,g)
#  -> ,GrpMat  Centraliser of element g of spin group G
local CH,H,S,T,TH,ZG,ZH,a,b,cG,cH,centralizerGens,havehoms,phi,sG,splits,tau;
  havehoms:=IsBound(G.SpinHom) and IsBound(G.SpinInvHom) and 
   IsBound(G.SpinHomImage) and IsBound(G.SpinCentre);
  if havehoms then
    tau:=G.SpinHom;
    phi:=G.SpinInvHom;
    H:=G.SpinHomImage;
    ZG:=G.SpinCentre;
  else
    T:=CompositionTree(G);
    Info(InfoClasses,1,"Got composition tree");
    # =v= MULTIASSIGN =v=
    b:=CompositionTreeSeries(G);
    S:=b.val1;
    a:=b.val2;
    b:=b.val3;
    # =^= MULTIASSIGN =^=
    phi:=b[Size(b)];
    tau:=a[Size(a)];
    ZG:=LMGCentre(G);
    H:=Codomain(tau);
    TH:=CompositionTree(H);
    ZH:=LMGCentre(H);
    SanityChecks@(G,H,ZG,ZH);
    if Size(ZH) > 1 then
      CheckTauAndPhi@(G,H,ZG,ZH,tau,phi); # actually Tildetau, Tildephi!!! TODO
    fi;
    G.SpinHom:=tau;
    G.SpinInvHom:=phi;
    G.SpinHomImage:=H;
    G.SpinCentre:=ZG;
  fi;
  #  if havehoms
  tau:=Function(tau);
  phi:=Function(phi);
  CH:=Centraliser(H,tau(g));
  centralizerGens:=[];
  splits:=true;
  for cH in Generators(CH) do
    cG:=phi(cH);
    if Comm(cG,g)<>G.0 then
      if splits then
        sG:=cG;
        centralizerGens:=Concatenation(centralizerGens,List(centralizerGens,
         cg->sG*cg*sG^-1));
        splits:=false;
      else
        Add(centralizerGens,cG*sG^-1);
      fi;
      Add(centralizerGens,cG^2);
    else
      Add(centralizerGens,cG);
      if not splits then
        Add(centralizerGens,sG*cG*sG^-1);
      fi;
    fi;
  od;
  Info(InfoClasses,2,"Does this class split?",splits);
  return SubStructure(Generic(G),ZG,#TODO CLOSURE
    centralizerGens);
end;

SpinCentralizer@:=function(G,g)
#  -> ,GrpMat  Centraliser of element g of spin group G
return SpinCentraliser@(G,g);
end;

SpinClassMap@:=function(G)
#  -> ,Map  The class map of spin group G
local CMH,CMfn,H,ZG,cl,clH,lifts,phi,tau,z;
  cl:=SpinClasses@(G);
  tau:=G.SpinHom;
  phi:=G.SpinInvHom;
  H:=G.SpinHomImage;
  ZG:=G.SpinCentre;
  lifts:=G.SpinLifts;
  repeat
    z:=Random(ZG);
    
  until z<>G.0 and Function(tau)(z)=H.0;
  clH:=ClassicalClasses(H);
  CMH:=ClassicalClassMap@(H);
  CMfn:=function(g)
  local clno,cnoh,elt,g,h,hrep,isc,poss;
    h:=Function(tau)(g);
    cnoh:=Function(CMH)(h);
    hrep:=clH[cnoh][3];
    # =v= MULTIASSIGN =v=
    elt:=ClassicalIsConjugate@(H,h,hrep);
    isc:=elt.val1;
    elt:=elt.val2;
    # =^= MULTIASSIGN =^=
    Assert(1,isc);
    g:=g^Function(phi)(elt);
    poss:=lifts[cnoh];
    for clno in poss do
      if g=cl[clno][3] then
        return clno;
      fi;
    od;
    Assert(1,Size(poss)=1 and g*z=cl[poss[1]][3]);
    return poss[1];
  end;

  return GroupGeneralMappingByFunction(Generic(G),[1..Size(cl)],
    x->CMfn(x));
end;

InstallGlobalFunction(CheckTauAndPhi@,
function(G,H,ZG,ZH,tau,phi)
#  /out:make sure tau is a homomorphism
local 
   CZH,Grels,NG,NH,cg,flag,i,ims,invims,ishom,isinv,izh,newims,ng,nh,phi,tau;
  Info(InfoClasses,2,"testing if tau is a homomorphism");
  # =v= MULTIASSIGN =v=
  Grels:=CompositionTreeVerify(G);
  flag:=Grels.val1;
  Grels:=Grels.val2;
  # =^= MULTIASSIGN =^=
  Assert(1,flag);
  NG:=CompositionTreeNiceGroup(G);
  ng:=Ngens(NG);
  ims:=List([1..ng],i->Function(tau)(NG.i));
  ishom:=Set(Evaluate(Grels,ims))=Set([One(H)]);
  if not ishom then
    Info(InfoClasses,2,"tau is not a homomorphism");
    CZH:=CartesianPower(ZH,ng);
    for cg in CZH do
      newims:=List([1..ng],i->ims[i]*cg[i]);
      ishom:=Set(Evaluate(Grels,newims))=Set([One(H)]);
      if ishom then
        # FOLLOWING COMMAND IS `WHERE` 
        # =v= MULTIASSIGN =v=
        w:=CompositionTreeElementToWord(G,g);
        _:=w.val1;
        w:=w.val2;
        # =^= MULTIASSIGN =^=
        tau:=GroupGeneralMappingByFunction(Generic(G),Generic(H),
          g->Evaluate(w,newims));
        Info(InfoClasses,2,"tau is now a homomorphism");
        break;
      fi;
    od;
  fi;
  #  make sure phi is inverse of tau
  Info(InfoClasses,2,"testing if phi is an inverse of tau");
  isinv:=true;
  repeat
    izh:=Random(ZG);
    
  until Function(tau)(izh)<>H.0;
  NH:=CompositionTreeNiceGroup(H);
  nh:=Ngens(NH);
  invims:=List([1..nh],i->Function(phi)(NH.i));
  for i in [1..nh] do
    if Function(tau)(invims[i])<>NH.i then
      Info(InfoClasses,2,"phi is not an inverse of tau");
      isinv:=false;
      invims[i]:=invims[i]*izh;
    fi;
  od;
  if not isinv then
    # FOLLOWING COMMAND IS `WHERE` 
    # =v= MULTIASSIGN =v=
    w:=CompositionTreeElementToWord(H,g);
    _:=w.val1;
    w:=w.val2;
    # =^= MULTIASSIGN =^=
    phi:=GroupGeneralMappingByFunction(Generic(H),Generic(G),
      g->Evaluate(w,invims));
  fi;
  Info(InfoClasses,2,"phi is now an inverse to tau");
end);

InstallGlobalFunction(SanityChecks@,
function(G,H,ZG,ZH)
#  basic sanity cheks
  if DimensionOfMatrixGroup(H) < 7 then
    Error("Dimension of spin group must be at least 7");
  fi;
  if IsEvenInt(Size(BaseRing(H))) then
    Error("Characteristic of spin group must be odd");
  fi;
  if not FormType(H) in ["orthogonalplus","orthogonalminus","orthogonalcircle"] 
     then
    Error("Wrong form type for spin group");
  fi;
  if Size(G)<>Size(H)*2 or Size(ZG)<>Size(ZH)*2 then
    Error("This is not a spin group");
  fi;
end);


