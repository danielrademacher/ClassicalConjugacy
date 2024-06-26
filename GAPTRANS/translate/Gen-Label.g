#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: AdaptForm, Append, BaseRing, CaseSplits,
#  Characteristic, ClassMap, Classes, ClassicalGroupType, ConjPol,
#  ConstantCoefficient, Degree, Determinant, DetermineTransformMatrix,
#  FrobeniusImage, GL, GO, GOMinus, GOPlus, GU, Generic, GenericLabel, Include,
#  Integers, InternalConjugacyInvariantGU, InternalConjugacyInvariantO,
#  InternalConjugacyInvariantSp, IsEven, IsIrreducible, IsOdd, IsSquare,
#  IsTrivial, JordanForm, Multiset, MyClassIndex, Nrows, Omega, OmegaMinus,
#  OmegaPlus, OrthogonalForm, PGL, PGO, PGOMinus, PGOPlus, PGU, POmega,
#  POmegaMinus, POmegaPlus, PSL, PSO, PSOMinus, PSOPlus, PSU, PSp, Parent,
#  Position, PrimitiveElement, QuadraticForm, SL, SO, SOMinus, SOPlus, SU,
#  Sort, Sp, StandardAlternatingForm, StandardGroup, StandardHermitianForm,
#  StandardQuadraticForm, StandardSymmetricForm, Star, Submatrix,
#  SymplecticForm, TransformForm, TransformMatrix, Transpose, UnitaryForm, fn,
#  trans

#  Defines: AdaptForm, CaseSplits, ClassicalClassMap, DetermineTransformMatrix,
#  GenericLabel, IsometryGroupClassLabel, MyClassIndex, StandardGroup,
#  TransformMatrix

DeclareGlobalFunction("GenericLabel"); # there was an @!!! TODO

DeclareGlobalFunction("StandardGroup"); # there was an @!!! TODO

DeclareGlobalFunction("TransformMatrix"); # there was an @!!! TODO

#   G is natural copy of classical group
#   determine matrix to conjugate G to standard copy
DetermineTransformMatrix:=function(G) # there was an @!!! TODO
local CB,F,f,flag,form,ind,type;
  # =v= MULTIASSIGN =v=
  type:=ClassicalGroupType(G); # there was an @!!! TODO
  f:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if type in ["SL","GL"] then
    CB:=G.0;
  elif type in ["SU","GU"] then
    # =v= MULTIASSIGN =v=
    form:=UnitaryForm(G);
    flag:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    CB:=TransformForm(form,"unitary");
  elif type in ["GO+","GO-","SO+","SO-","Omega+","Omega-","GO","SO","Omega"] 
     then
    F:=BaseRing(G);
    if IsEvenInt(Size(F)) then
      # =v= MULTIASSIGN =v=
      ind:=QuadraticForm(G);
      flag:=ind.val1;
      form:=ind.val2;
      ind:=ind.val3;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      form:=OrthogonalForm(G);
      flag:=form.val1;
      ind:=form.val2;
      form:=form.val3;
      # =^= MULTIASSIGN =^=
    fi;
    CB:=TransformForm(form,ind);
  elif type in ["Sp"] then
    # =v= MULTIASSIGN =v=
    form:=SymplecticForm(G);
    flag:=form.val1;
    form:=form.val2;
    # =^= MULTIASSIGN =^=
    CB:=TransformForm(form,"symplectic");
  fi;
  G.TransformCB:=CB;
  return CB;
end;

InstallGlobalFunction(TransformMatrix, # there was an @!!! TODO
function(G)
if IsBound(G.TransformCB) then
    return G.TransformCB;
  else
    return DetermineTransformMatrix(G); # there was an @!!! TODO
  fi;
end);

InstallGlobalFunction(StandardGroup, # there was an @!!! TODO
function(type,n,q)
local G,P,Projective;
  Projective:=ValueOption("Projective");
  if Projective=fail then
    Projective:=false;
  fi;
  if type="GO+" then
    G:=GOPlus(n,q);
    G.ClassicalType:="GO+";
    if Projective then
      P:=PGOPlus(n,q);
    fi;
  elif type="GO" then
    G:=GO(n,q);
    G.ClassicalType:="GO";
    if Projective then
      P:=PGO(n,q);
    fi;
  elif type="GO-" then
    G:=GOMinus(n,q);
    G.ClassicalType:="GO-";
    if Projective then
      P:=PGOMinus(n,q);
    fi;
  elif type="SO+" then
    G:=SOPlus(n,q);
    G.ClassicalType:="SO+";
    if Projective then
      P:=PSOPlus(n,q);
    fi;
  elif type="SO" then
    G:=SO(n,q);
    G.ClassicalType:="SO";
    if Projective then
      P:=PSO(n,q);
    fi;
  elif type="SO-" then
    G:=SOMinus(n,q);
    G.ClassicalType:="SO-";
    if Projective then
      P:=PSOMinus(n,q);
    fi;
  elif type="Omega+" then
    G:=OmegaPlus(n,q);
    G.ClassicalType:="Omega+";
    if Projective then
      P:=POmegaPlus(n,q);
    fi;
  elif type="Omega" then
    G:=Omega(n,q);
    G.ClassicalType:="Omega";
    if Projective then
      P:=POmega(n,q);
    fi;
  elif type="Omega-" then
    G:=OmegaMinus(n,q);
    G.ClassicalType:="Omega-";
    if Projective then
      P:=POmegaMinus(n,q);
    fi;
  elif type="Sp" then
    G:=SP(n,q);
    G.ClassicalType:="Sp";
    if Projective then
      P:=PSp(n,q);
    fi;
  elif type="GU" then
    G:=GU(n,q);
    G.ClassicalType:="GU";
    if Projective then
      P:=PGU(n,q);
    fi;
  elif type="SU" then
    G:=SU(n,q);
    G.ClassicalType:="SU";
    if Projective then
      P:=PSU(n,q);
    fi;
  elif type="SL" then
    G:=SL(n,q);
    G.ClassicalType:="SL";
    if Projective then
      P:=PSL(n,q);
    fi;
  elif type="GL" then
    G:=GL(n,q);
    G.ClassicalType:="GL";
    if Projective then
      P:=PGL(n,q);
    fi;
  fi;
  if Projective then
    return rec(val1:=G,
      val2:=P);
  else
    return rec(val1:=G,
      val2:=fail); # there was an _
  fi;
end);

#   turn the matrix of an orthogonal form into an upper triangular matrix
#   This is necessary because TransformForm (B, "orthogonalminus") fails if
#   B = Matrix (GF (2), 2, 2, [1, 0, 1, 1])
AdaptForm:=function(A) # there was an @!!! TODO
local i,j,n;
  n:=Length(A);
  for i in [1..n] do
    for j in [i+1..n] do
      A[i][j]:=A[i][j]+A[j][i];
      A[j][i]:=0;
    od;
  od;
  return A;
end;

#   for even char, does GO-class split into two classes in Omega+?
CaseSplits:=function(L) # there was an @!!! TODO
return Size(L) > 0 and Size(L[1]) > 0 and ForAll(L[1],x->IsEvenInt(x)) and 
   ForAll([2..4],i->Size(L[i])=0);
end;

#  
#  Consider first labels for Sp in odd characteristic.
#  The label corresponding to a single elementary divisor f is
#  <type, f, {* <d1, t1>, <d2, t2>, <d3, t3>, ... *}>
#  where type = 0, 1, 2 according to the type of "f".
#  -- type = 0 for f=f* & deg(f) = 1;
#  -- type = 1 for f=gg* (g ne g*, g el. div.);
#  -- type = 2 for f=f* & deg(f) > 1.
#  
#  If type = 0 (f = f* & deg(f) = 1 so f = t+1 or t-1), then for every
#  Jordan block of even dimension J_{2n} there is only one conjugacy class
#  in Sp with Jordan form J_{2n}, but there are two classes for Jordan blocks
#  of odd dimension. So d1, d2, d3,... are the dimensions of the Jordan blocks,
#  and we record <d_i, t_i>, where t_i = 0 if d_i is even, and t_i = 1 or a
#  primitive element for GF(q) if d_i is odd (according to the type of Jordan
#  block).
#  
#  If type = 1 or 2, then for uniformity the third element of the label remains
#  {* <d1, 1>, <d2, 1>, <d3, 1>, ... *} since in GL and GU there is only one
#  class for each Jordan block.
#  
#  A label for a class is a multiset {* <type, f, L>: f elementary divisor of x
#  *}.
#  
#  For orthogonal groups in odd characteristic, the same conventions apply --
#  but we must swap the roles of odd and even dimensional Jordan blocks.
#  
#  For symplectic and orthogonal in even char L = {v1, v2, v3, v4 }, where
#  v1, v2, v3, v4 record the dimensions of the blocks W, V, W_alpha, V_alpha
#  -- see Gonshaw-Liebeck-O'Brien paper for their definitions.
#  
#  For type 1 and 2, we simply designate all blocks to have type W.
#  
#  For unitary in every char, L = Multiset of dimensions of Jordan blocks.
#  
#  If type is a Special or Omega group, the label is <L1, symbol>, where L1 is
#  the
#  label in the isometry group, and symbol identifies the class in SO/Omega/SU.
#  For SO and Omega, the symbols are "ns" (= not split), "id", "t", "s", "st"
#  [see GLO'B].
#  For SU, it assumes integer values from 0 to d-1, where d is the number of
#  SU-classes which are mutually conjugate in GU.

InstallGlobalFunction(GenericLabel, # there was an @!!! TODO
function(type,x)
local 
   A,Arr,B,ClassLabels,ConjPol,Done,ElemF,F,FormF,Gr,L,L_omega,LabelNumber,
   SplitsOmega2,Star,TypeForTF,varX,a,b,c,cp_f,deg,dim,e,f,i,indexinc,l,m,mult,
   n,newone,omega,p,pos,pr,q,special,tf2m,tf2p,tsq;
  varX:=ValueOption("varX");
  if varX=fail then
    varX:=[];
  fi;
  ClassLabels:=ValueOption("ClassLabels");
  if ClassLabels=fail then
    ClassLabels:=[];
  fi;
  F:=BaseRing(x);
  pr:=PrimitiveElement(F);
  p:=Characteristic(F);
  n:=Length(x);
  # rewritten select statement
  if type in ["SU","GU"] then
    e:=QuoInt(Degree(F),2);
  else
    e:=0;
  fi;
  # rewritten select statement
  if type in ["SU","GU"] then
    q:=p^e;
  else
    q:=Size(F);
  fi;
  LabelNumber:=0;
  #  conjugate transpose matrix
  Star:=function(M)
  local exp;
    exp:=e;
    return TransposedMat(FrobeniusImage(M,exp));
  end;

  #  conjugate polynomial
  ConjPol:=ConjugatePolynomial(e<>0); # there was an @!!! TODO
  # =v= MULTIASSIGN =v=
  c:=JordanForm(x);
  a:=c.val1;
  b:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  special:=false;
  omega:=false;
  if type="SO+" and IsEvenInt(p) then
    type:="GO+";
  fi;
  if type="SO-" and IsEvenInt(p) then
    type:="GO-";
  fi;
  if type in ["GO+","SO+","Omega+"] then
    # rewritten select statement
    if IsOddInt(q) then
      B:=StandardSymmetricForm(n,F:Variant:="Default");
    else
      B:=StandardQuadraticForm(n,F:Variant:="Default");
    fi;
  elif type in ["GO","SO","Omega"] then
    B:=StandardSymmetricForm(n,F:Variant:="Default");
  elif type in ["GO-","SO-","Omega-"] then
    # rewritten select statement
    if IsOddInt(q) then
      B:=StandardSymmetricForm(n,F:Minus:=true,Variant:="Default");
    else
      B:=StandardQuadraticForm(n,F:Minus:=true,Variant:="Default");
    fi;
  elif type="Sp" then
    B:=StandardAlternatingForm(n,F);
    TypeForTF:="symplectic";
  elif type in ["GU","SU"] then
    B:=StandardHermitianForm(n,F);
    TypeForTF:="unitary";
  fi;
  if not (type in ["SU","GU","Sp"]) then
    if (q mod 4)=1 then
      tf2p:=1*FORCEOne(F);
      tf2m:=pr;
    else
      tf2p:=pr;
      tf2m:=1*FORCEOne(F);
    fi;
  fi;
  A:=b*B*Star(b);
  #   A = form preserved by JordanForm (x)
  if type in ["SO+","SO","SO-","SU","Omega","Omega+","Omega-"] then
    special:=true;
    if type in ["Omega+","Omega","Omega-"] then
      omega:=true;
      #   does the orthogonal class split into 2 classes in Omega (only even
      #  char)?
      SplitsOmega2:=false;
      if IsEvenInt(p) then
        special:=false;
      fi;
    fi;
  fi;
  L:=[];
  Done:=Set([]);
  #   if f ne f*, we put ff* as elementary divisor
  pos:=1;
  indexinc:=1;
  while indexinc <= Size(c) do
    f:=c[indexinc][1];
    deg:=Degree(f);
    if deg=1 and f=ConjPol(f) then
      dim:=0;
      while indexinc <= Size(c) and c[indexinc][1]=f do
        dim:=dim+deg*c[indexinc][2];
        indexinc:=indexinc+1;
      od;
      FormF:=Submatrix(A,pos,pos,dim,dim);
      ElemF:=(-ConstantCoefficient(f)^-1*Submatrix(a,pos,pos,dim,dim))
       *FORCEOne(GL(dim,F));
      if not (type in ["SU","GU","Sp"]) then
        TypeForTF:=IndicateType(FormF); # there was an @!!! TODO
        if IsEvenInt(q) then
          FormF:=AdaptForm(FormF); # there was an @!!! TODO
        fi;
      fi;
      m:=TransformForm(FormF,TypeForTF);
      if TypeForTF="unitary" then
        l:=UnipotentLabel(GU(dim,q),m^-1*ElemF*m:type:=type); # there was an @!!! TODO
        if special then
          l:=l[1];
        fi;
      elif TypeForTF="orthogonalplus" then
        if dim=2 then
          if IsOddInt(q) then
            l:=[[1,1*FORCEOne(F)],[1,tf2p]];
          elif ElemF[1][2]=0 then
            #   if there are 2 Jordan blocks of dimension 1
            l:=[[1],[],[],[],1];
          else
            l:=[[],[1],[],[],1];
          fi;
        else
          if IsOddInt(q) then
            l:=UnipotentLabel(GOPlus(dim,q),m^-1*ElemF*m:type:="GO+"); # there was an @!!! TODO
            l:=l[1];
          else
            if omega then
              l:=UnipotentLabel(OmegaPlus(dim,q),m^-1*ElemF*m:type:="Omega+"); # there was an @!!! TODO
            else
              l:=UnipotentLabel(GOPlus(dim,q),m^-1*ElemF*m:type:="GO+"); # there was an @!!! TODO
            fi;
            SplitsOmega2:=CaseSplits(l); # there was an @!!! TODO
          fi;
        fi;
      elif TypeForTF="orthogonal" then
        if dim=1 then
          # rewritten select statement
          if q mod 8 in [1,7] then
            tsq:=1*FORCEOne(F);
          else
            tsq:=pr;
          fi;
          l:=[[1,tsq]];
        else
          l:=UnipotentLabel(GO(dim,q),m^-1*ElemF*m:type:="GO"); # there was an @!!! TODO
          if IsOddInt(q) then
            l:=l[1];
          fi;
        fi;
        if IsEvenInt(n) and not IsSquare(DeterminantMat(FormF)) then
          l:=ChangeClassLabel(l,F,pr); # there was an @!!! TODO
        fi;
      elif TypeForTF="orthogonalminus" then
        if dim=2 then
          if IsOddInt(q) then
            l:=[[1,1*FORCEOne(F)],[1,tf2m]];
          elif ElemF[1][2]=0 then
            #   i.e. if there are 2 Jordan blocks of dimension 1
            l:=[[],[],[1],[],1];
          else
            l:=[[],[],[],[1],1];
          fi;
        else
          if IsOddInt(q) then
            l:=UnipotentLabel(GOMinus(dim,q),m^-1*ElemF*m:type:="GO-"); # there was an @!!! TODO
            l:=l[1];
          else
            if omega then
              l:=UnipotentLabel(OmegaMinus(dim,q),m^-1*ElemF*m:type:="Omega-") # there was an @!!! TODO
               ;
            else
              l:=UnipotentLabel(GOMinus(dim,q),m^-1*ElemF*m:type:="GO-"); # there was an @!!! TODO
            fi;
            SplitsOmega2:=CaseSplits(l); # there was an @!!! TODO
          fi;
        fi;
      elif TypeForTF="symplectic" then
        l:=UnipotentLabel(SP(dim,q),m^-1*ElemF*m:type:=type); # there was an @!!! TODO
      fi;
      pos:=pos+dim;
      Add(L,[0,f,l]);
    else
      #   here I just use the Jordan block structure
      l:=[];
      dim:=0;
      #   need this only in orthogonal case, odd dimension
      while indexinc <= Size(c) and c[indexinc][1]=f do
        if not (type in ["GU","SU"]) and IsOddInt(q) then
          newone:=[c[indexinc][2],1*FORCEOne(F)];
          dim:=dim+deg*c[indexinc][2];
        else
          newone:=c[indexinc][2];
        fi;
        Add(l,newone);
        pos:=pos+deg*c[indexinc][2];
        indexinc:=indexinc+1;
      od;
      if not (type in ["GU","SU"]) and IsEvenInt(q) then
        l:=[Sort(l),[],[],[],1];
      else
        l:=Multiset(l);
      fi;
      cp_f:=ConjPol(f);
      if f<>cp_f then
        if cp_f in Done then
          Add(L,[1,f*cp_f,l]);
          #   the form preserved by f has non-square determinant
        else
          UniteSet(Done,f); # actually TildeDone!!! TODO
        fi;
      else
        Add(L,[2,f,l]);
        if type in ["GO","SO","Omega"] then
          mult:=Sum(List(l,r->r[1]));
          if XOR(IsOddInt(mult), (q mod 4=3 and IsOddInt(QuoInt(dim,2)))) then
          fi;
          #   the form preserved by f has non-square determinant
        fi;
      fi;
    fi;
  od;
  if omega and SplitsOmega2 then
    i:=Filtered([1..Size(L)],j->L[j][1]=0)[1];
    L_omega:=L;
    L_omega[i][3][5]:=L_omega[i][3][5]*-1;
    L_omega:=Multiset(L_omega);
  fi;
  L:=Multiset(L);
  if special or omega then
    Gr:=StandardGroup(type,n,q); # there was an @!!! TODO
    Arr:=Filtered([1..Size(ClassLabels)],i->ClassLabels[i][1]=L);
    if omega and SplitsOmega2 then
      Arr:=Concatenation(Arr,Filtered([1..Size(ClassLabels)],i->ClassLabels[i]
       [1]=L_omega));
    fi;
    if Size(Arr)=1 then
      if type="SU" then
        L:=[L,0];
      else
        L:=[L,"ns"];
      fi;
      LabelNumber:=Arr[1];
    else
      for i in Arr do
        if GenIsConjugate(Gr,x,varX[i][3]:Checks:=false) then # there was an @!!! TODO
          L:=ClassLabels[i];
          LabelNumber:=i;
          break;
        fi;
      od;
    fi;
  fi;
  return rec(val1:=L,
    val2:=LabelNumber);
end);

#  changed intrinsic IsometryGroupClassLabel (type :: MonStgElt, g:: GrpMatElt)
#  -> {* *}
IsometryGroupClassLabel:=function(type,g) # there was an @!!! TODO
local F,G,d,flag,label,mu,q,tp,trans,types;
  types:=["GU","Sp","O+","O-","GO+","GO-","O","GO"];
  if not type in types then
    Error(["type must be one ",types]);
  fi;
  if type="O" then
    type:="GO";
  fi;
  if type="O+" then
    type:="GO+";
  fi;
  if type="O-" then
    type:="GO-";
  fi;
  d:=Length(g);
  F:=BaseRing(g);
  if type="GU" then
    # =v= MULTIASSIGN =v=
    q:=IsSquare(Size(F));
    flag:=q.val1;
    q:=q.val2;
    # =^= MULTIASSIGN =^=
      if not flag then
      Error("Field must be of even degree");
    fi;
  else
    q:=Size(F);
  fi;
  G:=StandardGroup(type,d,q); # there was an @!!! TODO
  if not g in G then
    Error("Element not in standard isometry group");
  fi;
  if IsOddInt(q) or type="GU" then
    if type in ["GO","GO+","GO-"] then
      tp:="O";
    else
      tp:=type;
    fi;
    mu:=# translated case< statement
    function(xxx)
      if xxx="Sp" then return InternalConjugacyInvariantSp(g);
      elif xxx="GU" then return InternalConjugacyInvariantGU(g);
      elif xxx="O" then return type=# rewritten select statement
    function(xxx)if xxx then return InternalConjugacyInvariantO(g:Minus:=true)
     ;else return InternalConjugacyInvariantO(g);fi;end("GO-");
      elif xxx=default then return false;
    else Error();fi;end(tp);
    trans:=# translated case< statement
    function(xxx)
      if xxx="Sp" then return tagToNameSp; # there was an @!!! TODO
      elif xxx="O" then return tagToNameO; # there was an @!!! TODO
      elif xxx="GU" then return tagToNameGU; # there was an @!!! TODO
      elif xxx=default then return false;
    else Error();fi;end(tp);
    label:=trans(mu);
  else
    label:=GenericLabel(type,g); # there was an @!!! TODO
  fi;
  return label;
end;

#   C is sequence of classes and L is sequence of labels;
#    return index of conjugacy class containing element g
MyClassIndex:=function(G,g,C,L) # there was an @!!! TODO
local l,n,type;
  type:=ValueOption("type");
  if type=fail then
    type:=false;
  fi;
  if Generic(G)<>Generic(Parent(g)) then
    Error("Element not in group");
  fi;
  # =v= MULTIASSIGN =v=
  n:=GenericLabel(type,g:varX:=C,ClassLabels:=L); # there was an @!!! TODO
  l:=n.val1;
  n:=n.val2;
  # =^= MULTIASSIGN =^=
  if n=0 then
    n:=Position(L,l);
  fi;
  return n;
end;

ClassicalClassMap:=function(G,C,L) # there was an @!!! TODO
#  -> ,Map  C and L are output of ClassicalClasses , where C := sequence of
#  classes and L := list of corresponding labels ; return class map for G
local CB,D,ValidTypes,flag,type; # there was an @!!! TODO
  type:=ValueOption("type");
  if type=fail then
    type:=false;
  fi;
  if IsBound(G.Classes) then
      if not G.Classes=C then
      Error("Supplied classes are inconsistent with stored classes");
    fi;
  else
      if not Generic(G)=Generic(Parent(C[1][3])) then
      Error("Classes do not belong to G");
    fi;
    #   require forall{c : c in C | c[3] in G}: "Not all supplied classes
    #  belong to G";
      if not ForAll(C,c->MyIsIn(G,c[3])) then # there was an @!!! TODO
      Error("Not all supplied classes belong to G");
    fi;
      if not Sum(List(C,c->c[2])=Size(G)) then
      Error("Wrong number of supplied classes");
    fi;
      if not Size(C)=Size(L) then
      Error("Number of classes differs from number of labels");
    fi;
    G.Classes:=C;
    G.Labels_A:=L;
  fi;
  if IsTrivial(G) then
    return ClassMap(G);
  fi;
  if type<>false then
    if type in ["GO","O"] then
      type:="GO";
    fi;
    if type in ["GO+","O+"] then
      type:="GO+";
    fi;
    if type in ["GO-","O-"] then
      type:="GO-";
    fi;
  fi;
  ValidTypes:=Set(["Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-","SO", # there was an @!!! TODO
   "GO+","GO-","GO"]);
  if IsBound(G.ClassicalType) then
    if type<>false then
          if not type=G.ClassicalType then
        Error("supplied type is incorrect");
      fi;
    else
      type:=G.ClassicalType;
    fi;
  elif type=false then
    # =v= MULTIASSIGN =v=
    type:=GroupType(G); # there was an @!!! TODO
    flag:=type.val1;
    type:=type.val2;
    # =^= MULTIASSIGN =^=
      if not flag then
      Error("For this case, you must supply type");
    fi;
  fi;
  if not type in ValidTypes then # there was an @!!! TODO
    Error(["Type must be one of ",ValidTypes]); # there was an @!!! TODO
  fi;
  G.ClassicalType:=type;
  if Degree(G)=2 and IsIrreducible(G)=false then
    return ClassMap(G);
  fi;
  CB:=TransformMatrix(G); # there was an @!!! TODO
  if CB<>CB^0 then
    D:=List([1..Size(C)],i->[C[i][1],C[i][2],C[i][3]^CB]);
    return GroupGeneralMappingByFunction(G,[1..Size(C)],
      g->MyClassIndex(G,g^CB,D,L:type:=G.ClassicalType)); # there was an @!!! TODO
  else
    return GroupGeneralMappingByFunction(G,[1..Size(C)],
      g->MyClassIndex(G,g,C,L:type:=G.ClassicalType)); # there was an @!!! TODO
  fi;
end;

ClassicalClassMap:=function(G) # there was an @!!! TODO
#  -> ,Map  The class map for the classical group G
local C,CB,D,F,L,ValidTypes,_,d,flag,fn,tp; # there was an @!!! TODO
  if IsTrivial(G) then
    return ClassMap(G);
  fi;
  d:=Degree(G);
  F:=BaseRing(G);
  if not (d=2 and Size(F) <= 4) then
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
    if tp="GO" and IsEvenInt(Size(F)) then
      Error("Function does not apply to this case");
    fi;
  fi;
  if not IsBound(G.Classes) then
    _:=Classes(G);
  fi;
  C:=G.Classes;
  if not IsBound(G.Labels_A) then
    if IsBound(G.Labels_S) then
      if tp="Sp" then
        fn:=tagToNameSp; # there was an @!!! TODO
      elif tp in ["GO","GO+","GO-"] then
        fn:=tagToNameO; # there was an @!!! TODO
      elif tp in ["SO","SO+","SO-"] then
        fn:=tagToNameSO; # there was an @!!! TODO
      elif tp="GU" then
        fn:=tagToNameGU; # there was an @!!! TODO
      elif tp="SU" then
        fn:=tagToNameSU; # there was an @!!! TODO
      else
        Error("Labels not available for this group of type",tp);
      fi;
      G.Labels_A:=List( # {-list: # there was an @!!! TODO
        G.Labels_S,mu->fn(mu));
    else
      Info(InfoClasses,1,"No labels, so using the standard ClassMap");
      return ClassMap(G);
    fi;
  fi;
  L:=G.Labels_A;
  if Degree(G)=2 and IsIrreducible(G)=false then
    return ClassMap(G);
  fi;
  CB:=TransformMatrix(G); # there was an @!!! TODO
  if CB<>CB^0 then
    D:=List([1..Size(C)],i->[C[i][1],C[i][2],C[i][3]^CB]);
    return GroupGeneralMappingByFunction(G,[1..Size(C)],
      g->MyClassIndex(G,g^CB,D,L:type:=G.ClassicalType)); # there was an @!!! TODO
  else
    return GroupGeneralMappingByFunction(G,[1..Size(C)],
      g->MyClassIndex(G,g,C,L:type:=G.ClassicalType)); # there was an @!!! TODO
  fi;
end;


