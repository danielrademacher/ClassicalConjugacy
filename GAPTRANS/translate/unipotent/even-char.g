#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Abs, Append, ClassReps, DiagonalJoin, Exclude,
#  FormForIdentity, GF, GL, GOMinus, GOPlus, Identity, InsertBlock, Integers,
#  IsEven, IsGoodType, IsOdd, MatrixAlgebra, Multiplicity, Multiset, Nrows,
#  OForm, OParameters, OmegaMinus, OmegaPlus, Order,
#  OrthogonalUnipotentClassSize_Even, Partitions, Reverse, SOMinus, SOPlus,
#  Set, SetupRep, Sort, Sp, SpForm, SpUnipotentClassSize_Even,
#  StandardAlternatingForm, StandardQuadraticForm, TransformForm, V_beta_even,
#  W_even, W_even_dash, W_odd, Zero

#  Defines: ClassReps, ClassesSplit, EvenUnipotentReps, FormForIdentity,
#  IsGoodType, OForm, OParameters, OrthogonalUnipotentClassSize_Even, SetupRep,
#  SpForm, SpUnipotentClassSize_Even, V_beta_even, W_even, W_even_dash, W_odd

SpUnipotentClassSize_Even@:=function(G,T,q)
return QuoInt(Size(G),SpUnipotentCentraliserOrder_Even@(T,q));
end;

OrthogonalUnipotentClassSize_Even@:=function(type,G,T,q)
return QuoInt(Size(G),OrthogonalUnipotentCentraliserOrder_Even@(type,T,q));
end;

#   building blocks
V_beta_even@:=function(k,q,beta)
local I,J,M,MA,R,i,j;
  MA:=MatrixAlgebra(GF(q),2*k);
  if k=1 then
    R:=Identity(MA);
    R[1][2]:=1;
  else
    M:=MatrixAlgebra(GF(q),k);
    R:=Zero(MA);
    I:=Identity(M);
    for i in [1..Length(I)] do
      for j in [i+1..Length(I)] do
        I[i][j]:=1;
      od;
    od;
    InsertBlock(R,I,1,1); # actually TildeR!!! TODO
    J:=JordanBlock@(k,q);
    InsertBlock(R,J,k+1,k+1); # actually TildeR!!! TODO
    for i in [1..k-1] do
      R[i][k+1]:=1;
      R[i][k+2]:=beta;
    od;
    R[k][k+1]:=1;
  fi;
  return R*FORCEOne(GL(2*k,q));
end;

W_even@:=function(k,q)
local MA,i,j,w;
  MA:=MatrixAlgebra(GF(q),2*k);
  w:=Zero(MA);
  for i in [1..k-1] do
    w[i][i]:=1;
    w[i][i+1]:=1;
  od;
  w[k][k]:=1;
  for i in [k+1..2*k] do
    for j in [i..2*k] do
      w[i][j]:=1;
    od;
  od;
  return w*FORCEOne(GL(2*k,q));
end;

W_even_dash@:=function(k,q)
local MA,i,j,w;
  MA:=MatrixAlgebra(GF(q),2*k);
  w:=Zero(MA);
  for i in [1..k-2] do
    w[i][i]:=1;
    w[i][i+1]:=1;
  od;
  w[k-1][k-1]:=1;
  w[k-1][k+1]:=1;
  w[k][k]:=1;
  for i in [k+2..2*k] do
    w[k][i]:=1;
  od;
  w[k+1][k+1]:=1;
  for i in [k+2..2*k] do
    for j in [i..2*k] do
      w[i][j]:=1;
    od;
  od;
  return w*FORCEOne(GL(2*k,q));
end;

W_odd@:=function(k,q,beta)
local I,MA,ell,i,j,w;
  Assert(1,IsOddInt(k));
  MA:=MatrixAlgebra(GF(q),2*k);
  if k=1 then
    I:=Identity(MA);
    return I*FORCEOne(GL(2*k,q));
  fi;
  ell:=QuoInt(k,2);
  w:=Zero(MA);
  #   Revision EOB May 2016
  for i in [1..k-1] do
    w[i][i]:=1;
    w[i][i+1]:=1;
    if i in [ell-1,ell] then
      w[i][2*k-ell+1]:=beta;
    fi;
  od;
  w[k][k]:=1;
  for i in [1..k] do
    if i >= ell+2 then
      w[2*k-i+1][ell+2]:=beta;
    fi;
    for j in [k+i..2*k] do
      w[k+i][j]:=1;
    od;
  od;
  return w*FORCEOne(GL(2*k,q));
end;

SpForm@:=function(k,q)
local MA,form,i;
  MA:=MatrixAlgebra(GF(q),2*k);
  form:=Zero(MA);
  for i in [1..2*k] do
    form[i][2*k+1-i]:=1;
  od;
  return form;
end;

#   "O" form is satisfied by V_beta_even
#   "Omega" form is satisfied by W_alpha
OForm@:=function(type,k,q,b)
local MA,Q,i,l,nmr;
  nmr:=ValueOption("nmr");
  if nmr=fail then
    nmr:=0;
  fi;
  MA:=MatrixAlgebra(GF(q),2*k);
  Q:=Zero(MA);
  if type="O" then
    Q[k][k]:=b;
    if nmr=0 then
      Q[k+1][k+1]:=1;
    fi;
    for i in [1..k] do
      Q[i][2*k-i+1]:=1;
    od;
  elif type="Omega" then
    #   EOB -- change of form June 2017
    #   if k eq 1 then return MA![b, b, 0, 1]; end if;
    if k=1 then
      return [b,1,0,b]*FORCEOne(MA);
    fi;
    Assert(1,IsOddInt(k));
    l:=QuoInt(k,2);
    for i in [l..l+1] do
      Q[i][i]:=b;
    od;
    Q[2*k-l][2*k-l]:=b;
    for i in [1..k] do
      Q[i][2*k-i+1]:=1;
    od;
  fi;
  return Q;
end;

SetupRep@:=function(type,q,w,v,w_alpha,v_alpha,nmr)
local 
   A,B,MA,V,V_alpha,W,W_alpha,alpha,d,form,formV,formV_alpha,formW,formW_alpha,
   r,t,z;
  alpha:=ChooseAlpha@(q);
  MA:=MatrixAlgebra(GF(q),0);
  z:=Zero(MA);
  V:=z;
  W:=z;
  W_alpha:=z;
  V_alpha:=z;
  formW:=z;
  formV:=z;
  formW_alpha:=z;
  formV_alpha:=z;
  if Size(w) > 0 then
    if nmr=-1 then
      A:=W_even_dash@(w[1],q);
      if Size(w) > 1 then
        B:=DirectSumMat(List( # <-list:
          [2..Size(w)],i->W_even@(w[i],q)));
        W:=DirectSumMat(A,B);
      else
        W:=A;
      fi;
    else
      W:=DirectSumMat(List( # <-list:
        w,k->W_even@(k,q)));
    fi;
    if type="Sp" then
      formW:=DirectSumMat(List( # <-list:
        w,k->SpForm@(k,q)));
    else
      formW:=DirectSumMat(List( # <-list:
        w,k->OForm@("O",k,q,0:nmr:=1)));
    fi;
  fi;
  if Size(v) > 0 then
    V:=DirectSumMat(List( # <-list:
      v,k->V_beta_even@(k,q,0)));
    if type="Sp" then
      formV:=DirectSumMat(List( # <-list:
        v,k->SpForm@(k,q)));
    else
      formV:=DirectSumMat(List( # <-list:
        v,k->OForm@("O",k,q,0)));
    fi;
  fi;
  if Size(w_alpha) > 0 then
    W_alpha:=DirectSumMat(List( # <-list:
      w_alpha,k->W_odd@(k,q,alpha)));
    if type="Sp" then
      formW_alpha:=DirectSumMat(List( # <-list:
        w_alpha,k->SpForm@(k,q)));
    else
      formW_alpha:=DirectSumMat(List( # <-list:
        w_alpha,k->OForm@("Omega",k,q,alpha:nmr:=1)));
    fi;
  fi;
  if Size(v_alpha) > 0 then
    V_alpha:=DirectSumMat(List( # <-list:
      v_alpha,k->V_beta_even@(k,q,alpha)));
    if type="Sp" then
      formV_alpha:=DirectSumMat(List( # <-list:
        v_alpha,k->SpForm@(k,q)));
    else
      formV_alpha:=DirectSumMat(List( # <-list:
        v_alpha,k->OForm@("O",k,q,alpha)));
    fi;
  fi;
  t:=[W,V,W_alpha,V_alpha];
  r:=DirectSumMat(t);
  d:=Length(r);
  r:=r*FORCEOne(GL(d,q));
  form:=DirectSumMat([formW,formV,formW_alpha,formV_alpha]);
  return rec(val1:=r,
    val2:=form);
end;

ClassReps@:=function(type,q,T)
local F,R,f,nmr,r,t,v,v_alpha,w,w_alpha;
  R:=[];
  F:=[];
  for t in T do
    w:=t[1];
    v:=t[2];
    w_alpha:=t[3];
    v_alpha:=t[4];
    nmr:=t[5];
    # =v= MULTIASSIGN =v=
    f:=SetupRep@(type,q,w,v,w_alpha,v_alpha,nmr);
    r:=f.val1;
    f:=f.val2;
    # =^= MULTIASSIGN =^=
    Add(R,r);
    Add(F,f);
  od;
  return rec(val1:=R,
    val2:=F);
end;

IsGoodType@:=function(type,m,w,v,w_alpha,v_alpha)
#  /out: sum of entries = m
local b,nmr,s,t;
  t:=Concatenation(v,w,w_alpha,v_alpha);
  if Sum(t<>m) then
    return rec(val1:=false,
      val2:=0,
      val3:=Sum(t));
  fi;
  if type in ["Omega+","Omega-"] and IsOddInt(Size(v)+Size(v_alpha)) then
    return rec(val1:=false,
      val2:=0,
      val3:=Sum(t));
  fi;
  #   each case defines identity matrix
  if Set(w)=Set([1]) and Sum(w=m) then
    return rec(val1:=false,
      val2:=0,
      val3:=Sum(t));
  fi;
  s:=Concatenation(w,w_alpha);
  if Set(s)=Set([1]) and Sum(s=m) then
    return rec(val1:=false,
      val2:=0,
      val3:=Sum(t));
  fi;
  if Size(v_alpha) > 0 then
    for b in v_alpha do
      if b in v then
        if Size(Filtered(v,x->x=b)) > 1 then
          return rec(val1:=false,
            val2:=0,
            val3:=Sum(t));
        fi;
      fi;
      if ForAny(v,a->(b-a)=1) then
        #   now enforced in setting up V_alpha
        #   or exists{a : a in v_alpha | (b - a) eq 1} then
        return rec(val1:=false,
          val2:=0,
          val3:=Sum(t));
      fi;
    od;
  fi;
  if Size(w_alpha) > 0 then
    for b in w_alpha do
      if ForAny(v,a->Abs(b-2*a)=1) or ForAny(v_alpha,a->Abs(b-2*a)=1) then
        return rec(val1:=false,
          val2:=0,
          val3:=Sum(t));
      fi;
    od;
  fi;
  nmr:=1;
  if type in ["Omega+"] then
    if Sum(w=m and ForAll(w,x->IsEvenInt(x))) then
      #   "*** Split class", w;
      nmr:=2;
    fi;
  fi;
  if type in ["O-","Omega-"] and (IsOddInt(Size(w_alpha)+Size(v_alpha))) then
    return rec(val1:=true,
      val2:=nmr,
      val3:=Sum(t));
  elif type in ["O+","Omega+"] and (IsEvenInt(Size(w_alpha)+Size(v_alpha))) 
     then
    return rec(val1:=true,
      val2:=nmr,
      val3:=Sum(t));
  elif type="Sp" then
    return rec(val1:=true,
      val2:=nmr,
      val3:=Sum(t));
  else
    return rec(val1:=false,
      val2:=0,
      val3:=Sum(t));
  fi;
end;

#   set up form preserved by identity element
FormForIdentity@:=function(type,d,q)
local form;
  Assert(1,IsEvenInt(q));
  if type in ["O+","Omega+"] then
    form:=StandardQuadraticForm(d,q:Variant:="Default");
  elif type in ["O-","Omega-"] then
    form:=StandardQuadraticForm(d,q:Minus:=true,Variant:="Default");
  elif type="Sp" then
    form:=StandardAlternatingForm(d,q);
  fi;
  return form;
end;

#   given type, rank and even field size, write down unipotent class reps
#   as elements of magma copy of corresponding SX (dim, q)
#   applies to Sp, Omega
EvenUnipotentReps@:=function(type,dim,q)
#  /out: "Applies to even characteristic only";
local 
   C,D,F,G,P,R,Rewrite,S,T,V,V_alpha,W,W_alpha,flag,forms,i,id_form,id_rep,j,k,
   l,m,n,nmr,reps,size,sum,tf,tr,x;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  Assert(1,IsEvenInt(q));
  Assert(1,IsEvenInt(dim));
  m:=QuoInt(dim,2);
  F:=GF(q);
  G:=GL(2*m,q);
  if type="Sp" then
    tf:="symplectic";
  fi;
  if type in ["Omega+","O+"] then
    tf:="orth+";
  fi;
  if type in ["Omega-","O-"] then
    tf:="orth-";
  fi;
  S:=[];
  for j in [1..m] do
    P:=Partitions(j);
    S:=Concatenation(S,List(P,p->Multiset(p)));
  od;
  W:=S;
  W:=Concatenation([[]],List(W,s->List(s,x->x)));
  #   V rules
  V:=Filtered(S,s->ForAll(s,x->Multiplicity(s,x) <= 2));
  V:=Concatenation([[]],List(V,s->List(s,x->x)));
  #   W_alpha rules
  W_alpha:=Filtered(S,x->Size(Set(x))=Size(x) and ForAll(x,y->IsOddInt(y)));
  if type="Sp" then
    W_alpha:=Filtered(W_alpha,x->ForAll(x,y->y >= 3));
  fi;
  W_alpha:=Concatenation([[]],List(W_alpha,s->List(s,x->x)));
  #   V_alpha rules
  V_alpha:=[];
  for x in S do
    if Size(Set(x))<>Size(x) or ForAny(x,
      b->ForAny(x,
        a->Abs(b-a)=1)) then
      continue;
    fi;
    Add(V_alpha,x);
  od;
  if type="Sp" then
    V_alpha:=Filtered(V_alpha,x->ForAll(x,y->y >= 2));
  fi;
  V_alpha:=Concatenation([[]],List(V_alpha,s->List(s,x->x)));
  T:=[];
  #   "length #W is ", #W, #V, #W_alpha, #V_alpha;
  for i in [1..Size(W)] do
    #   "i = ", i;
    for j in [1..Size(V)] do
      x:=Concatenation(W[i],V[j]);
      if Sum(x > m) then
        break j;
      fi;
      for k in [1..Size(W_alpha)] do
        x:=Concatenation(W[i],V[j],W_alpha[k]);
        if Sum(x > m) then
          break k;
        fi;
        for l in [1..Size(V_alpha)] do
          # =v= MULTIASSIGN =v=
          sum:=IsGoodType@(type,m,W[i],V[j],W_alpha[k],V_alpha[l]);
          flag:=sum.val1;
          nmr:=sum.val2;
          sum:=sum.val3;
          # =^= MULTIASSIGN =^=
          if sum > m then
            break l;
          fi;
          #   if nmr gt 0 then "nmr is ", nmr; end if;
          if flag then
            Add(T,[W[i],V[j],W_alpha[k],V_alpha[l],1]);
            #   "last is ", #T, T[#T];
            if nmr > 1 then
              Add(T,[W[i],V[j],W_alpha[k],V_alpha[l],-1]);
              #   "now last is ", #T, T[#T];
            fi;
          fi;
        od;
      od;
    od;
  od;
  # =v= MULTIASSIGN =v=
  forms:=ClassReps@(type,q,T);
  reps:=forms.val1;
  forms:=forms.val2;
  # =^= MULTIASSIGN =^=
  R:=[];
  if Rewrite then
    for i in [1..Size(reps)] do
      tr:=TransformForm(forms[i],tf:Restore:=false)*FORCEOne(GL(dim,q));
      Add(R,reps[i]^tr);
    od;
    Add(R,Identity(G));
  fi;
  #   add the identity element
  id_rep:=Identity(GL(dim,q));
  id_form:=FormForIdentity@(type,dim,q);
  reps:=Concatenation(reps,[id_rep]);
  forms:=Concatenation(forms,[id_form]);
  if type="Sp" then
    Add(T,[List([1..m],i->1),[],[],[],1]);
  elif type in ["GO-","O-","SO-","Omega-"] then
    Add(T,[List([1..m-1],i->1),[],[1],[],1]);
  elif type in ["GO+","O+","SO+","Omega+"] then
    Add(T,[List([1..m],i->1),[],[],[],1]);
  fi;
  Assert(1,Size(T)=Size(reps));
  #   set up class list
  #   first set up standard parent group
  n:=dim;
  if type="Sp" then
    G:=SP(n,q);
  elif type in ["O-","GO-"] then
    G:=GOMinus(n,q);
  elif type in ["O+","GO+"] then
    G:=GOPlus(n,q);
  elif type in ["SO-","SO-"] then
    G:=SOMinus(n,q);
  elif type in ["SO+","SO+"] then
    G:=SOPlus(n,q);
  elif type in ["Omega-"] then
    G:=OmegaMinus(n,q);
  elif type in ["Omega+"] then
    G:=OmegaPlus(n,q);
  fi;
  #   set up class list
  C:=[];
  D:=[];
  for i in [1..Size(reps)] do
    # rewritten select statement
    if type="Sp" then
      size:=SpUnipotentClassSize_Even@(G,T[i],q);
    else
      size:=OrthogonalUnipotentClassSize_Even@(type,G,T[i],q);
    fi;
    if Rewrite then
      Add(C,[Order(R[i]),size,R[i]]);
    fi;
    Add(D,[Order(reps[i]),size,reps[i]]);
  od;
  T:=List( # {@-list:
    T,t->t);
  return rec(val1:=C,
    val2:=D,
    val3:=forms,
    val4:=T);
end;

#   s, t, delta parameters for element of T
OParameters@:=function(type,T)
local S,V,W,delta,s,t;
  W:=Concatenation(T[1],T[1],T[3],T[3]);
  Sort(W); # actually TildeW!!! TODO
  Reversed(W); # actually TildeW!!! TODO
  V:=Concatenation(T[2],T[4]);
  Sort(V); # actually TildeV!!! TODO
  S:=Filtered(W,w->IsOddInt(w) and ForAll(V,v->Abs(w-2*v)<>1));
  if type="Sp" then
    RemoveSet(S,1); # actually TildeS!!! TODO
  fi;
  s:=Size(S);
  t:=Size(Filtered([1..Size(V)-1],j->V[j+1]-V[j] >= 2));
  # rewritten select statement
  if (Size(V)=0) or (type="Sp" and 1 in V) then
    delta:=0;
  else
    delta:=1;
  fi;
  return rec(val1:=s,
    val2:=t,
    val3:=delta);
end;

#   given type and description of class over algebraically closed field,
#   how many classes does it split into over finite field?
ClassesSplit@:=function(type,T)
local W,delta,s,t;
  W:=Concatenation(T[1],T[3]);
  if Size((Concatenation(T[2],T[4])))=0 and ForAll(W,w->IsEvenInt(w)) then
    if type in ["Omega-","O-"] then
      return 0;
    fi;
    if type="O+" then
      return 1;
    fi;
    if type="Omega+" then
      return 2;
    fi;
  fi;
  # =v= MULTIASSIGN =v=
  delta:=OParameters@(type,T);
  s:=delta.val1;
  t:=delta.val2;
  delta:=delta.val3;
  # =^= MULTIASSIGN =^=
  if type="Sp" then
    return 2^(s+t+delta);
  else
    return 2^(s+t+delta-1);
  fi;
end;


