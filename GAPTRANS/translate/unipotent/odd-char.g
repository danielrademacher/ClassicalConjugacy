#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, Determinant, DiagonalJoin, GF, GL, GO,
#  GOMinus, GOPlus, Identity, Include, IsEven, IsOdd, IsReflection, IsSquare,
#  IsometryGroup, MatrixAlgebra, MultiplicativeGroup, Multiplicity, Multiset,
#  Ngens, Omega, OmegaMinus, OmegaPlus, Order, Original_Reflection, Original_s,
#  OrthogonalUnipotentClassSize_Odd, Partitions, PrimitiveElement,
#  QuadraticSpace, SO, SOMinus, SOPlus, Set, Sort, SymmetricToQuadraticForm,
#  TestSplit, TransformForm, Zero

#  Defines: MyReflection, Original_Reflection, Original_s,
#  OrthogonalUnipotentClassSize_Odd, OrthogonalUnipotentReps, TestSplit

OrthogonalUnipotentClassSize_Odd@:=function(G,type,T,VBeta,split,q)
return QuoInt(Size(G),OrthogonalUnipotentCentraliserOrder@(type,T,VBeta,split,q)
   );
end;

TestSplit@:=function(Data,K,q,S,phi)
local Beta,K,Split,i,j,split;
  Split:=[];
  K:=List(K,x->QuoInt((x-1),2));
  for i in [1..Size(Data)] do
    Beta:=Data[i];
    split:=false;
    for j in [1..Size(Beta)] do
      split:=(Beta[j]*((-1)^(K[1]+K[j])*Beta[1])^-1)@@phi in S;
      if not split then
        break j;
      fi;
    od;
    Split[i]:=split;
  od;
  return Split;
end;

#   reflection for Magma form
MyReflection@:=function(n,q)
local MA,i,r;
  MA:=MatrixAlgebra(GF(q),n);
  r:=Zero(MA);
  r[1][n]:=-1;
  r[n][1]:=-1;
  for i in [2..n-1] do
    r[i][i]:=1;
  od;
  return r*FORCEOne(GL(n,q));
end;

#   reflection in group preserving supplied orthogonal form
Original_Reflection@:=function(form)
local H,Q,V;
  Q:=SymmetricToQuadraticForm(form);
  V:=QuadraticSpace(Q);
  H:=IsometryGroup(V);
  Assert(1,j:=ForAny([1..Ngens(H)],j->IsReflection(H.j)));
  return H.j;
end;

#   element in SO but not in Omega
Original_s@:=function(form)
local H,Q,V;
  Q:=SymmetricToQuadraticForm(form);
  V:=QuadraticSpace(Q);
  H:=IsometryGroup(V);
  Assert(1,i:=ForAny([1..Ngens(H)],i->MySpinorNorm@(H.i,form)=1));
  return H.i;
end;

#   given type, rank and odd field size, write down unipotent class reps
#   as elements of corresponding orthogonal group;
#   default for: n odd G = SO(n, q) and n even G = GO(n, q)
#   Special: reps in SOPlus(n, q), SOMinus(n, q)
#   Perfect: reps in Omega(n, q)
OrthogonalUnipotentReps@:=function(n,q,epsilon)
local 
   A,B,B_val,C,C_form,D,F,Forms,Fstar,G,L,LL,M,P,Params,Perfect,Reps,Rewrite,S,
   SP,Shapes,Special,Split,Squares,T,VBeta,varX,Y,alpha,form_A,form_B,form_type,
   forms,i,index,k,l,list,m,odd,omega,one,orig_s,orig_t,original,params,phi,r,
   reps,s,shape,shapes,size,special,split,t,temp,total,tr,two,type,value,varrep,
   w;
  Special:=ValueOption("Special");
  if Special=fail then
    Special:=false;
  fi;
  Perfect:=ValueOption("Perfect");
  if Perfect=fail then
    Perfect:=false;
  fi;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  F:=GF(q);
  #   case n=1 dealt manually
  if n=1 then
    G:=GL(1,q);
    return rec(val1:=[[1,1,Identity(G)]],
      val2:=[[1,1,Identity(G)]],
      val3:=[[1]*FORCEOne(MatrixAlgebra(F,1))],
      val4:=[[1^^1]],
      val5:=[[[[1,1]],"id"]]);
  fi;
  #   "Applies to odd characteristic only";
  Assert(1,IsOddInt(q));
  k:=QuoInt(n,2);
  F:=GF(q);
  w:=PrimitiveElement(F);
  # =v= MULTIASSIGN =v=
  phi:=MultiplicativeGroup(F);
  Fstar:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  Squares:=SubStructure(Fstar,(w^2)@@phi);
  #   assert {x  @ phi : x in Squares} eq {x^2: x in F | x ne 0};
  if Perfect=true then
    Special:=true;
  fi;
  P:=Partitions(n);
  S:=List(P,p->Multiset(p));
  T:=[];
  for s in S do
    t:=List( # {-list:
      s,x->x);
    if ForAny(t,x->IsEvenInt(x) and IsOddInt(Multiplicity(s,x))) then
      continue;
    fi;
    Add(T,s);
  od;
  S:=T;
  type:="Omega";
  total:=0;
  omega:=Set([]);
  alpha:=NonSquare@(F);
  Reps:=[];
  Forms:=[];
  Shapes:=[];
  special:=[];
  Params:=[];
  for i in [1..Size(S)] do
    s:=S[i];
    T:=Set(s);
    T:=List(T,x->x);
    Sort(TILDET);
    M:=MatrixAlgebra(F,0);
    A:=Zero(M);
    form_A:=Zero(M);
    B:=Zero(M);
    form_B:=Zero(M);
    B_val:=[];
    for t in T do
      m:=Multiplicity(s,t);
      if IsEvenInt(t) then
        k:=QuoInt(t,2);
        one:=Zero(M);
        one:=A_beta_even@(2*k,q,0,type);
        one:=DirectSumMat(List([1..QuoInt(m,2)],i->one));
        A:=DirectSumMat(A,one);
        B_val:=Concatenation(B_val,List([1..(QuoInt(m,2))],i->[2*k,0]));
        one:=A_beta_even_form@(2*k,q,type);
        one:=DirectSumMat(List([1..QuoInt(m,2)],i->one));
        form_A:=DirectSumMat(form_A,one);
      else
        k:=QuoInt((t-1),2);
        two:=Zero(M);
        if m > 1 then
          temp:=A_beta_odd@(k,q,-1*FORCEOne(F),-2*FORCEOne(F),type);
          temp:=DirectSumMat(List([1..m-1],i->temp));
          two:=DirectSumMat(two,temp);
        fi;
        B:=DirectSumMat(B,two);
        B_val:=Concatenation(B_val,List([1..(m-1)],i->[t,1]));
        if m > 1 then
          two:=A_beta_odd_form@(k,q,2,type);
          two:=DirectSumMat(List([1..m-1],i->two));
        fi;
        form_B:=DirectSumMat(form_B,two);
      fi;
    od;
    odd:=Filtered(T,x->IsOddInt(x));
    r:=Size(odd);
    params:=[];
    if r=0 then
      total:=total+1;
    else
      total:=total+2^(r-1);
    fi;
    if Size(odd) > 0 then
      # rewritten select statement
      if ForAny(T,t->IsOddInt(t)) then
        L:=[1,alpha];
      else
        L:=[1];
      fi;
      list:=BackTrack@(List([1..Size(odd)],i->Size(L)));
      varX:=List(Filtered(T,t->IsOddInt(t))
       ,t->List(L,beta->A_beta_odd@(QuoInt(t,2),q,-beta,-2*beta,type)));
      params:=List(Filtered(T,t->IsOddInt(t)),t->List(L,beta->[t,beta]));
      Y:=List(Filtered(T,t->IsOddInt(t))
       ,t->List(L,beta->A_beta_odd_form@(QuoInt(t,2),q,2*beta,type)));
      C:=List(list,l->DirectSumMat(List( # <-list:
        [1..Size(varX)],i->varX[i][l[i]])));
      params:=List(list,l->List([1..Size(varX)],i->params[i][l[i]]));
      Split:=TestSplit@(List(list,i->L[i]),odd,q,Squares,phi);
      C_form:=List(list,l->DirectSumMat(List( # <-list:
        [1..Size(varX)],i->Y[i][l[i]])));
      C:=List(C,c->DirectSumMat([c,A]));
      C_form:=List(C_form,c->DirectSumMat([c,form_A]));
      C:=List(C,c->DirectSumMat([c,B]));
      params:=List([1..Size(params)],i->Concatenation(params[i],B_val));
      C_form:=List(C_form,c->DirectSumMat([c,form_B]));
    else
      C:=[DirectSumMat([A,B])];
      params:=Concatenation(params,[B_val]);
      C_form:=[DirectSumMat([form_A,form_B])];
      if epsilon=1 and Special=true then
        UniteSet(TILDEspecial,Size(Reps)+1);
      fi;
    fi;
    if epsilon in [1,-1] then
      k:=QuoInt(n,2);
      # rewritten select statement
      if epsilon=1 then
        value:=true;
      else
        value:=false;
      fi;
      index:=Filtered([1..Size(C)],i->IsSquare((-1)^k*DeterminantMat(C_form[i]))
       =value);
    else
      index:=Filtered([1..Size(C)],i->IsSquare(DeterminantMat(C_form[i])));
      Assert(1,QuoInt(Size(C),2)=Size(index));
    fi;
    params:=List(index,i->params[i]);
    Add(Params,params);
    #   classes split in Omega?
    m:=List( # {-list:
      odd,t->Multiplicity(s,t));
    if Perfect then
      split:=[];
      if m=Set([]) then
        split:=List( # {-list:
          [Size(Reps)+1..Size(Reps)+Size(index)],i->i);
        Union(omega,#NOP
        ):=split;
      elif m=Set([1]) then
        split:=Filtered([1..Size(index)],i->Split[index[i]]=true);
        Union(omega,#NOP
        ):=List( # {-list:
          split,i->Size(Reps)+i);
      fi;
    fi;
    reps:=List(index,i->C[i]*FORCEOne(GL(n,F)));
    forms:=List(index,i->C_form[i]*FORCEOne(GL(n,F)));
    shape:=List([1..Size(index)],k->s);
    Reps:=Concatenation(Reps,reps);
    Forms:=Concatenation(Forms,forms);
    Shapes:=Concatenation(Shapes,shape);
  od;
  Params:=Concatenation(Params);
  if epsilon=0 then
    form_type:="orthogonal";
  else
    # rewritten select statement
    if epsilon=1 then
      form_type:="orthogonalplus";
    else
      form_type:="orthogonalminus";
    fi;
  fi;
  reps:=[];
  original:=[];
  forms:=[];
  shapes:=[];
  Split:=[];
  VBeta:=[];
  L:=[];
  for i in [1..Size(Reps)] do
    Add(original,Reps[i]);
    lvarSP:=[[Params[i],"id"]];
    Add(forms,Forms[i]);
    Add(shapes,Shapes[i]);
    Add(VBeta,Params[i]);
    Assert(1,Size(original)=Size(VBeta));
    if Rewrite then
      tr:=TransformForm(Forms[i],form_type:Restore:=false);
    fi;
    if epsilon=1 and Size(special) > 0 then
      orig_t:=Original_Reflection@(Forms[i]);
      if Rewrite then
        t:=orig_t^tr;
      fi;
    fi;
    if Perfect then
      orig_s:=Original_s@(Forms[i]);
      if Rewrite then
        s:=orig_s^tr;
      fi;
    fi;
    if Rewrite then
      varrep:=Reps[i]^tr;
      Add(reps,varrep);
    fi;
    if Perfect and i in omega then
      Add(forms,Forms[i]);
      Add(shapes,Shapes[i]);
      if Rewrite then
        Add(reps,varrep^s);
      fi;
      Add(original,Reps[i]^orig_s);
      Add(lvarSP,[Params[i],"s"]);
      Add(VBeta,Params[i]);
      Assert(1,Size(original)=Size(VBeta));
      Add(Split,Size(shapes)-1);
      Add(Split,Size(shapes));
    fi;
    if epsilon=1 and (Special and i in special) then
      Add(forms,Forms[i]);
      Add(shapes,Shapes[i]);
      if Rewrite then
        Add(reps,varrep^t);
      fi;
      Add(original,Reps[i]^orig_t);
      Add(lvarSP,[Params[i],"t"]);
      Add(VBeta,Params[i]);
      Assert(1,Size(original)=Size(VBeta));
      if Perfect and i in omega then
        Add(forms,Forms[i]);
        Add(shapes,Shapes[i]);
        if Rewrite then
          Add(reps,(varrep^t)^s);
        fi;
        Add(original,(Reps[i]^orig_t)^orig_s);
        Add(lvarSP,[Params[i],"ts"]);
        Add(VBeta,Params[i]);
        Assert(1,Size(original)=Size(VBeta));
        Add(Split,Size(shapes)-1);
        Add(Split,Size(shapes));
      fi;
    fi;
    Add(L,lvarSP);
  od;
  #   set up class list
  #   first set up parent group
  if Special=false then
    if epsilon=0 then
      G:=GO(n,q);
      type:="GO";
    else
      # rewritten select statement
      if epsilon=1 then
        G:=GOPlus(n,q);
      else
        G:=GOMinus(n,q);
      fi;
      # rewritten select statement
      if epsilon=1 then
        type:="GO+";
      else
        type:="GO-";
      fi;
    fi;
  elif Special=true and Perfect=false then
    if epsilon=0 then
      G:=SO(n,q);
      type:="SO";
    else
      # rewritten select statement
      if epsilon=1 then
        G:=SOPlus(n,q);
      else
        G:=SOMinus(n,q);
      fi;
      # rewritten select statement
      if epsilon=1 then
        type:="SO+";
      else
        type:="SO-";
      fi;
    fi;
  else
    if epsilon=0 then
      G:=Omega(n,q);
      type:="Omega";
    else
      # rewritten select statement
      if epsilon=1 then
        G:=OmegaPlus(n,q);
      else
        G:=OmegaMinus(n,q);
      fi;
      # rewritten select statement
      if epsilon=1 then
        type:="Omega+";
      else
        type:="Omega-";
      fi;
    fi;
  fi;
  #   EOB change April 8, 2020 -- identify non-split classes
  LL:=[];
  for i in [1..Size(L)] do
    l:=L[i];
    if Size(l)=1 then
      l[1][2]:="ns";
    fi;
    Add(LL,l);
  od;
  L:=LL;
  L:=Concatenation((L));
  L:=List( # {@-list:
    L,x->[Multiset(x[1]),x[2]]);
  #   set up class list
  C:=[];
  D:=[];
  for i in [1..Size(original)] do
    size:=OrthogonalUnipotentClassSize_Odd@(G,type,shapes[i],VBeta[i],i in 
     Split,q);
    if Rewrite then
      Add(C,[Order(reps[i]),size,reps[i]]);
    fi;
    Add(D,[Order(original[i]),size,original[i]]);
  od;
  return rec(val1:=C,
    val2:=D,
    val3:=forms,
    val4:=shapes,
    val5:=L);
end;


