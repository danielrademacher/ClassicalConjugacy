#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: A_beta_even, A_beta_even_form, A_beta_odd,
#  A_beta_odd_form, Append, BackTrack, Ceiling, Characteristic, D_rep, Degree,
#  Determinant, DiagonalJoin, FactoredOrder, FrobeniusImage, GF, GL, GU,
#  GUUnipotentBlock, Gcd, Hilbert90, Identity, IdentityMatrix, InsertBlock,
#  Integers, IsEven, IsOdd, Isqrt, Log, Matrix, MatrixAlgebra, Maximum,
#  Minimum, MultiplicativeGroup, Multiplicity, Multiset, MyJordanBlock, Nrows,
#  Order, Partitions, PrimitiveElement, Prune, Root, Roots, SL,
#  SLUnipotentClassSize, SU, SUUnipotentClassSize, Set, Sort, Sp,
#  SpUnipotentClassSize_Odd, StandardHermitianForm, TransformForm, Transpose,
#  UnitaryForm, Zero

#  Defines: A_beta, A_beta_even, A_beta_even_form, A_beta_odd, A_beta_odd_form,
#  BackTrack, D_rep, GLUnipotentReps, GUUnipotentBlock, GUUnipotentReps,
#  MyJordanBlock, SLUnipotentClassSize, SLUnipotentReps, SUUnipotentClassSize,
#  SUUnipotentReps, SpUnipotentClassSize_Odd, SpUnipotentReps

DeclareGlobalFunction("GUUnipotentBlock@");

SLUnipotentClassSize@:=function(G,g)
return QuoInt(Size(G),Int(UnipotentCentraliserOrder@("SL",G,g,[])));
end;

SpUnipotentClassSize_Odd@:=function(G,T,VBeta,q)
return QuoInt(Size(G),SpUnipotentCentraliserOrder@(T,VBeta,q));
end;

SUUnipotentClassSize@:=function(type,G,g)
return QuoInt(Size(G),Int(UnipotentCentraliserOrder@(type,G,g,[])));
end;

#   unipotent reps for GL, SL, GU, SU in all characteristics;
#   and for Sp in odd characteristic
#   all integer sequences whose i-th entry is in the
#   range [1..M[i] by 1] for i in [1..#M]
BackTrack@:=function(M)
local IndexList,Solns,index,len,m,min,n,offset,original;
  if Set(M)=Set([1]) then
    return [M];
  fi;
  offset:=1;
  n:=Size(M);
  m:=Concatenation(List([1..Size(M)],i->1),[1]);
  original:=m;
  min:=Minimum(m);
  IndexList:=Filtered([1..Size(M)],i->M[i] >= min);
  len:=Size(IndexList);
  Add(IndexList,n+1);
  Solns:=[];
  repeat
    index:=1;
    m[IndexList[index]]:=m[IndexList[index]]+offset;
    while (index <= len and m[IndexList[index]] > M[IndexList[index]]) do
      m[IndexList[index]]:=original[IndexList[index]];
      index:=index+1;
      m[IndexList[index]]:=m[IndexList[index]]+offset;
    od;
    Add(Solns,Prune(m));
    
  until (index > len);
  return Solns;
end;

#   building blocks
MyJordanBlock@:=function(d,q,beta)
local A,M,i,sgn;
  sgn:=ValueOption("sgn");
  if sgn=fail then
    sgn:=1;
  fi;
  M:=MatrixAlgebra(GF(q),d);
  A:=Identity(M);
  for i in [1..d-1] do
    A[i][i+1]:=sgn*1;
  od;
  if d > 1 then
    A[1][2]:=beta;
  fi;
  return A;
end;

#   given rank and field size, write down unipotent class reps
#   as elements of corresponding SL (n, q)
SLUnipotentReps@:=function(n,q)
local 
   A,B,C,F,G,L,M,MA,N,P,Q,Reps,S,T,beta,e,i,m,n1,parameters,phi,reps,s,size,t,
   tau,three,two,w;
  F:=GF(q);
  G:=SL(n,q);
  P:=Partitions(n);
  S:=List(P,p->Multiset(p));
  N:=List(S,s->List(Set(s),x->x));
  T:=List(N,n->Gcd(Concatenation(n,[q-1])));
  # =v= MULTIASSIGN =v=
  phi:=MultiplicativeGroup(GF(q));
  M:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  L:=[];
  for t in T do
    # =v= MULTIASSIGN =v=
    tau:=
    # QUOTIENT
    M/t;
    Q:=tau.val1;
    tau:=tau.val2;
    # =^= MULTIASSIGN =^=
    reps:=List(Q,x->(x@@tau)@phi);
    Add(L,reps);
  od;
  parameters:=Concatenation((L));
  e:=Degree(F);
  w:=PrimitiveElement(GF(q));
  Reps:=[];
  for i in [1..Size(S)] do
    s:=S[i];
    T:=Set(s);
    T:=List(T,x->x);
    Sort(T); # actually TildeT!!! TODO
    n1:=Minimum(T);
    MA:=MatrixAlgebra(F,0);
    A:=Zero(MA);
    B:=Zero(MA);
    for t in T do
      if t=n1 then
        m:=Multiplicity(s,n1);
        if m > 1 then
          two:=MyJordanBlock@(n1,q,1);
          A:=DirectSumMat(List([1..m-1],i->two));
        fi;
      else
        m:=Multiplicity(s,t);
        three:=MyJordanBlock@(t,q,1);
        three:=DirectSumMat(List([1..m],i->three));
        B:=DirectSumMat(B,three);
      fi;
    od;
    reps:=L[i];
    for beta in reps do
      C:=MyJordanBlock@(n1,q,beta);
      C:=DirectSumMat(C,A);
      C:=DirectSumMat(C,B);
      Add(Reps,[C,s]);
    od;
  od;
  T:=List(Reps,r->r[2]);
  Reps:=List(Reps,r->r[1]*FORCEOne(GL(n,q)));
  C:=[];
  for i in [1..Size(Reps)] do
    size:=SLUnipotentClassSize@(G,Reps[i]);
    C[i]:=[Order(Reps[i]),size,Reps[i]];
  od;
  T:=List( # {@-list:
    [1..Size(T)],i->[T[i],parameters[i]]);
  return rec(val1:=C,
    val2:=T);
end;

GLUnipotentReps@:=function(n,q)
local C,Card,F,G,P,P1,Partition,T,Y,card,i,j,ord,p,pos;
  lvarPartition:=ValueOption("lvarPartition");
  if lvarPartition=fail then
    lvarPartition:=[];
  fi;
  F:=GF(q);
  p:=Characteristic(F);
  G:=GL(n,q);
  Card:=FactoredOrder(G);
  C:=[];
  T:=[];
  if Size(lvarPartition)=0 then
    P:=Partitions(n);
  else
    P:=lvarPartition;
  fi;
  for P1 in P do
    Y:=IdentityMatrix(F,n);
    pos:=1;
    ord:=p^Ceiling(Log(p,Maximum(P1)));
    for i in P1 do
      for j in [1..i-1] do
        Y[pos][pos+1]:=1;
        pos:=pos+1;
      od;
      pos:=pos+1;
    od;
    card:=UnipotentCentraliserOrder@("GL",G,Y,Y:JF:=P1);
    card:=Int((Card/card));
    Add(C,[ord,card,Y*FORCEOne(G)]);
    Add(T,Multiset(P1));
  od;
  return rec(val1:=C,
    val2:=List( # {@-list:
    T,t->t));
end;

A_beta_even@:=function(k,q,beta,type)
local F,I,J,M,MA,R,i,j;
  # rewritten select statement
  if type="SU" then
    F:=GF(q^2);
  else
    F:=GF(q);
  fi;
  if type="SU" then
    Assert(1,beta+beta^q=0*FORCEOne(F));
  fi;
  MA:=MatrixAlgebra(F,2*k);
  if k=1 then
    R:=Identity(MA);
    R[1][2]:=beta;
  else
    M:=MatrixAlgebra(F,k);
    R:=Zero(MA);
    I:=Identity(M);
    for i in [1..Length(I)] do
      for j in [i+1..Length(I)] do
        I[i][j]:=1;
      od;
    od;
    InsertBlock(R,I,1,1); # actually TildeR!!! TODO
    J:=MyJordanBlock@(k,Size(F),-1:sgn:=-1);
    InsertBlock(R,J,k+1,k+1); # actually TildeR!!! TODO
    for i in [1..k] do
      R[i][k+1]:=beta;
    od;
  fi;
  return R*FORCEOne(GL(2*k,F));
end;

A_beta_odd@:=function(k,q,gamma,delta,type)
local F,I,J,M,MA,R,i,j;
  # rewritten select statement
  if type="SU" then
    F:=GF(q^2);
  else
    F:=GF(q);
  fi;
  if type="SU" then
    Assert(1,delta=-1*FORCEOne(F));
    Assert(1,gamma+gamma^q=-1*FORCEOne(F));
  fi;
  MA:=MatrixAlgebra(F,2*k+1);
  if k=0 then
    R:=Identity(MA);
  else
    M:=MatrixAlgebra(F,k);
    R:=Zero(MA);
    I:=Identity(M);
    for i in [1..Length(I)] do
      for j in [i+1..Length(I)] do
        I[i][j]:=1;
      od;
    od;
    InsertBlock(R,I,1,1); # actually TildeR!!! TODO
    J:=MyJordanBlock@(k,Size(F),-1:sgn:=-1);
    InsertBlock(R,J,k+2,k+2); # actually TildeR!!! TODO
    for i in [1..k] do
      R[i][k+1]:=1;
      R[i][k+2]:=gamma;
    od;
    R[k+1][k+1]:=1;
    R[k+1][k+2]:=delta;
  fi;
  return R*FORCEOne(GL(2*k+1,F));
end;

A_beta@:=function(k,q,beta,gamma,delta,type)
if IsEvenInt(k) then
    return A_beta_even@(k,q,beta,type);
  else
    return A_beta_odd@(k,q,gamma,delta,type);
  fi;
end;

A_beta_even_form@:=function(k,q,type)
local F,MA,e,form,i,sign;
  # rewritten select statement
  if type="SU" then
    F:=GF(q^2);
  else
    F:=GF(q);
  fi;
  e:=Degree(F);
  MA:=MatrixAlgebra(F,2*k);
  form:=Zero(MA);
  for i in [1..k] do
    form[i][2*k+1-i]:=1;
  od;
  # rewritten select statement
  if type in ["SU","Omega"] then
    sign:=1;
  else
    sign:=-1;
  fi;
  for i in [k+1..2*k] do
    form[i][2*k+1-i]:=sign;
  od;
  return form;
end;

A_beta_odd_form@:=function(k,q,beta,type)
local F,MA,e,form,i,sign;
  # rewritten select statement
  if type="SU" then
    F:=GF(q^2);
  else
    F:=GF(q);
  fi;
  e:=Degree(F);
  MA:=MatrixAlgebra(F,2*k+1);
  form:=Zero(MA);
  for i in [1..k] do
    form[i][2*k+2-i]:=1;
  od;
  form[k+1][k+1]:=beta;
  # rewritten select statement
  if type in ["SU","Omega"] then
    sign:=1;
  else
    sign:=-1;
  fi;
  for i in [k+2..2*k+1] do
    form[i][2*k+2-i]:=sign;
  od;
  return form;
end;

D_rep@:=function(n,q,alpha)
local D,F,MA,f,lambda;
  F:=GF(q^2);
  # =v= MULTIASSIGN =v=
  lambda:=Hilbert90(alpha^-1,q);
  f:=lambda.val1;
  lambda:=lambda.val2;
  # =^= MULTIASSIGN =^=
  MA:=MatrixAlgebra(F,n);
  D:=Identity(MA);
  D[1][1]:=lambda;
  D[n][n]:=(lambda^-1)^q;
  Assert(1,DeterminantMat(D)=alpha);
  return D*FORCEOne(GL(n,F));
end;

#   return element in standard copy of GU(n,F) with single Jordan block J_n
InstallGlobalFunction(GUUnipotentBlock@,
function(n,F)
local Y,b,d,i,j,m,q,w;
  q:=RootInt(Size(F));
  w:=F.1;
  if IsOddInt(q) then
    b:=w-(w+w^q)/2;
    #   element of trace =0
    d:=(q-1)*FORCEOne(F)/2;
    #   element of trace =-1
  else
    b:=w^(q+1);
    #   element of trace =0
    d:=w/(w+w^q);
    #   element of trace =1
  fi;
  if n=1 then
    return IdentityMatrix(F,1);
  fi;
  if n=2 then
    return MatrixByEntries(F,2,2,[1,b,0,1]);
  fi;
  if IsOddInt(n) then
    m:=QuoInt(n,2);
    Y:=IdentityMatrix(F,n);
    for i in [1..m+1] do
      for j in [i+1..m+1] do
        Y[i][j]:=1;
      od;
      Y[i][m+2]:=d;
    od;
    for i in [m+2..n-1] do
      Y[i][i+1]:=-1;
    od;
    Y[m+1][m+2]:=-1;
  else
    Y:=IdentityMatrix(F,n);
    m:=QuoInt(n,2);
    for i in [1..m] do
      Y[i][m+1]:=b;
      for j in [i+1..m] do
        Y[i][j]:=1;
      od;
    od;
    for i in [m+1..n-1] do
      Y[i][i+1]:=-1;
    od;
  fi;
  return Y;
end);

#   unipotent classes in GU(n, q)
GUUnipotentReps@:=function(n,q)
local B,C,D,F,Forms,G,Orig,P,Partition,Reps,Rewrite,T,VectorForms,Y,i,m,p,size;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  lvarPartition:=ValueOption("lvarPartition");
  if lvarPartition=fail then
    lvarPartition:=[];
  fi;
  F:=GF(q^2);
  G:=GL(n,q^2);
  VectorForms:=List( # <-list:
    [1..n],i->StandardHermitianForm(i,q));
  Reps:=[];
  Orig:=[];
  Forms:=[];
  T:=[];
  if Size(lvarPartition)=0 then
    P:=Partitions(n);
  else
    P:=lvarPartition;
  fi;
  for p in P do
    Y:=DirectSumMat(List( # <-list:
      p,i->GUUnipotentBlock@(i,F)));
    B:=DirectSumMat(List( # <-list:
      p,i->VectorForms[i]));
    Add(Orig,Y*FORCEOne(G));
    Add(Forms,B);
    Add(T,Multiset(p));
    if Rewrite then
      m:=TransformForm(B,"unitary":Restore:=false);
      Add(Reps,(m^-1*Y*m)*FORCEOne(G));
    fi;
  od;
  C:=[];
  D:=[];
  for i in [1..Size(Orig)] do
    size:=SUUnipotentClassSize@("GU",GU(n,q),Orig[i]);
    D[i]:=[Order(Orig[i]),size,Orig[i]];
    if Rewrite then
      C[i]:=[Order(Reps[i]),size,Reps[i]];
    fi;
  od;
  return rec(val1:=C,
    val2:=D,
    val3:=Forms,
    val4:=List( # {@-list:
    T,t->t));
end;

#   given type, rank and field size, write down unipotent class reps
#   as elements of corresponding SU (n, q)
SUUnipotentReps@:=function(n,q)
local 
   A,B,C,D,F,FixedRoot,Forms,G,JF,L,M,N,Orig,P,Params,Q,Reps,Rewrite,S,T,Verify,
   varZ,_,beta,conj,delta,e,forgetvar1,form,form_A,form_B,forms,i,k,m,nmr,one,
   params,phi,reps,s,size,t,tau,tr,two,type,varrep,w,z;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  Verify:=ValueOption("Verify");
  if Verify=fail then
    Verify:=false;
  fi;
  e:=Degree(GF(q));
  F:=GF(q^2);
  G:=SU(n,q);
  # =v= MULTIASSIGN =v=
  form:=UnitaryForm(G);
  forgetvar1:=form.val1;
  form:=form.val2;
  # =^= MULTIASSIGN =^=
  P:=Partitions(n);
  S:=List(P,p->Multiset(p));
  N:=List(S,s->List(Set(s),x->x));
  T:=List(N,n->Gcd(Concatenation(n,[q+1])));
  #   Same Jordan Form for each related collection of parameters
  JF:=Concatenation(List([1..Size(T)],i->List([1..T[i]],j->S[i])));
  nmr:=Sum(T);
  #   "Nmr of classes is ", nmr;
  L:=[];
  # =v= MULTIASSIGN =v=
  phi:=MultiplicativeGroup(F);
  M:=phi.val1;
  phi:=phi.val2;
  # =^= MULTIASSIGN =^=
  z:=(QuoInt(Order(M.1),(q+1)))*M.1;
  Assert(1,Order(z)=q+1);
  varZ:=SubStructure(M,z);
  T:=List(N,n->Gcd(n));
  for t in T do
    # =v= MULTIASSIGN =v=
    tau:=
    # QUOTIENT
    varZ/t*varZ.1;
    Q:=tau.val1;
    tau:=tau.val2;
    # =^= MULTIASSIGN =^=
    reps:=List(Q,x->(x@@tau)@phi);
    Add(L,reps);
  od;
  e:=QuoInt(Degree(F),2);
  w:=PrimitiveElement(GF(q));
  FixedRoot:=function(f)
  local roots;
    roots:=RootsOfUPol(f);
    roots:=List(roots,r->r[1]);
    Sort(roots); # actually Tilderoots!!! TODO
    return rec(val1:=roots[1],
      val2:=roots);
  end;

  #   R<x>:= PolynomialRing (F);
  #   time gamma := FixedRoot (x + x^q + 1);
  Assert(1,gamma:=ForAny(F,x->x<>0 and x+x^q=-1));
  beta:=Root(-1*FORCEOne(F),q-1);
  #   assert exists(beta) {x : x in F | x ne 0 and x + x^q eq 0};
  delta:=-1*FORCEOne(F);
  type:="SU";
  Reps:=[];
  Forms:=[];
  Orig:=[];
  Params:=[];
  for i in [1..Size(S)] do
    s:=S[i];
    T:=Set(s);
    T:=List(T,x->x);
    Sort(T); # actually TildeT!!! TODO
    M:=MatrixAlgebra(F,0);
    A:=Zero(M);
    form_A:=Zero(M);
    B:=Zero(M);
    form_B:=Zero(M);
    for t in T do
      m:=Multiplicity(s,t);
      k:=QuoInt(t,2);
      if IsEvenInt(t) then
        one:=A_beta_even@(k,q,beta,type);
        one:=DirectSumMat(List([1..m],i->one));
        A:=DirectSumMat(A,one);
        one:=A_beta_even_form@(k,q,type);
        one:=DirectSumMat(List([1..m],i->one));
        form_A:=DirectSumMat(form_A,one);
      else
        two:=A_beta_odd@(k,q,gamma,delta,type);
        two:=DirectSumMat(List([1..m],i->two));
        B:=DirectSumMat(B,two);
        two:=A_beta_odd_form@(k,q,1,type);
        two:=DirectSumMat(List([1..m],i->two));
        form_B:=DirectSumMat(form_B,two);
      fi;
    od;
    varrep:=DirectSumMat(A,B)*FORCEOne(GL(n,F));
    form:=DirectSumMat(form_A,form_B)*FORCEOne(GL(n,F));
    if Verify then
      Assert(1,varrep*form*TransposedMat(FrobeniusImage(varrep,e))=form);
    fi;
    conj:=List(L[i],alpha->D_rep@(n,q,alpha));
    reps:=List(conj,c->varrep^c);
    Add(Orig,reps);
    forms:=List(conj,c->c^-1*form*TransposedMat(FrobeniusImage(c^-1,e)));
    Add(Forms,forms);
    params:=List([1..Size(conj)],i->conj[i][1][1]);
    Add(Params,params);
    if Rewrite then
      tr:=TransformForm(form,"unitary":Restore:=false);
      varrep:=varrep^tr;
      reps:=List(conj,c->varrep^c);
      Add(Reps,reps);
    fi;
  od;
  Reps:=Concatenation((Reps));
  Orig:=Concatenation((Orig));
  Forms:=Concatenation((Forms));
  Reps:=List(Reps,r->r*FORCEOne(GL(n,q^2)));
  C:=[];
  D:=[];
  for i in [1..Size(Orig)] do
    size:=SUUnipotentClassSize@("SU",SU(n,q),Orig[i]);
    D[i]:=[Order(Orig[i]),size,Orig[i]];
    if Rewrite then
      C[i]:=[Order(Reps[i]),size,Reps[i]];
    fi;
  od;
  Params:=Concatenation((Params));
  JF:=List( # {@-list:
    [1..Size(JF)],i->[JF[i],Params[i]]);
  return rec(val1:=C,
    val2:=D,
    val3:=Forms,
    val4:=JF,
    val5:=Params);
end;

#   given type, rank and odd field size, write down unipotent class reps
#   as elements of corresponding Sp (n, q)
SpUnipotentReps@:=function(n,q)
#  /out: "*** Applies to odd characteristic only";
local 
   A,A_val,B,C,C_form,D,F,Forms,G,L,List_T,M,Nmr,P,Params,Reps,Rewrite,S,T,varX,
   Y,alpha,even,form_A,form_B,i,k,list,m,one,original_reps,params,r,reps,s,size,
   t,temp,tr,two,type,varrep;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  Assert(1,IsEvenInt(n));
  Assert(1,IsOddInt(q));
  k:=QuoInt(n,2);
  F:=GF(q);
  G:=SP(n,q);
  P:=Partitions(n);
  S:=List(P,p->Multiset(p));
  #   W rules
  T:=[];
  for s in S do
    t:=List( # {-list:
      s,x->x);
    if ForAny(t,x->IsOddInt(x) and IsOddInt(Multiplicity(s,x))) then
      continue;
    fi;
    Add(T,s);
  od;
  S:=T;
  List_T:=[];
  type:="Sp";
  alpha:=NonSquare@(F);
  Reps:=[];
  Forms:=[];
  original_reps:=[];
  Params:=[];
  Nmr:=0;
  for i in [1..Size(S)] do
    s:=S[i];
    T:=Set(s);
    T:=List(T,x->x);
    Sort(T); # actually TildeW!!! TODO
    M:=MatrixAlgebra(F,0);
    A:=Zero(M);
    form_A:=Zero(M);
    B:=Zero(M);
    form_B:=Zero(M);
    A_val:=[];
    for t in T do
      m:=Multiplicity(s,t);
      k:=QuoInt(t,2);
      if IsEvenInt(t) then
        one:=Zero(M);
        if m > 1 then
          temp:=A_beta_even@(k,q,1,type);
          temp:=DirectSumMat(List([1..m-1],i->temp));
          one:=DirectSumMat(one,temp);
        fi;
        A:=DirectSumMat(A,one);
        A_val:=Concatenation(A_val,List([1..(m-1)],i->[t,1]));
        if m > 1 then
          one:=A_beta_even_form@(k,q,type);
          one:=DirectSumMat(List([1..m-1],i->one));
        fi;
        form_A:=DirectSumMat(form_A,one);
      else
        two:=A_beta_even@(2*k+1,q,0,type);
        two:=DirectSumMat(List([1..QuoInt(m,2)],i->two));
        B:=DirectSumMat(B,two);
        A_val:=Concatenation(A_val,List([1..QuoInt(m,2)],i->[2*k+1,0]));
        two:=A_beta_even_form@(2*k+1,q,type);
        two:=DirectSumMat(List([1..QuoInt(m,2)],i->two));
        form_B:=DirectSumMat(form_B,two);
      fi;
    od;
    even:=Filtered(T,x->IsEvenInt(x));
    Nmr:=Nmr+2^Size(even);
    params:=[];
    if Size(even) > 0 then
      # rewritten select statement
      if ForAny(T,t->IsEvenInt(t)) then
        L:=[1,alpha];
      else
        L:=[1];
      fi;
      list:=BackTrack@(List([1..Size(even)],i->Size(L)));
      varX:=List(Filtered(T,t->IsEvenInt(t))
       ,t->List(L,beta->A_beta_even@(QuoInt(t,2),q,beta,type)));
      params:=List(Filtered(T,t->IsEvenInt(t)),t->List(L,beta->[t,beta]));
      Y:=List(Filtered(T,t->IsEvenInt(t))
       ,t->List(L,beta->A_beta_even_form@(QuoInt(t,2),q,type)));
      C:=List(list,l->DirectSumMat(List( # <-list:
        [1..Size(varX)],i->varX[i][l[i]])));
      params:=List(list,l->List([1..Size(varX)],i->params[i][l[i]]));
      C_form:=List(list,l->DirectSumMat(List( # <-list:
        [1..Size(varX)],i->Y[i][l[i]])));
      C:=List(C,c->DirectSumMat([c,A]));
      params:=List([1..Size(params)],i->Concatenation(params[i],A_val));
      C_form:=List(C_form,c->DirectSumMat([c,form_A]));
      C:=List(C,c->DirectSumMat([c,B]));
      C_form:=List(C_form,c->DirectSumMat([c,form_B]));
    else
      C:=[DirectSumMat([A,B])];
      params:=Concatenation(params,[A_val]);
      C_form:=[DirectSumMat([form_A,form_B])];
    fi;
    List_T:=Concatenation(List_T,List([1..Size(C)],j->S[i]));
    reps:=[];
    if Rewrite=true then
      for r in [1..Size(C)] do
        varrep:=C[r]*FORCEOne(GL(n,F));
        tr:=TransformForm(C_form[r],"symplectic":Restore:=false)
         *FORCEOne(GL(n,F));
        varrep:=varrep^tr;
        Add(reps,varrep);
      od;
    fi;
    Reps:=Concatenation(Reps,reps);
    original_reps:=Concatenation(original_reps,C);
    Forms:=Concatenation(Forms,C_form);
    Add(Params,params);
  od;
  Assert(1,Size(original_reps)=Nmr);
  Assert(1,Size(List_T)=Nmr);
  T:=List_T;
  Params:=Concatenation((Params));
  Params:=List( # {@-list:
    Params,x->Multiset(x));
  C:=[];
  D:=[];
  for i in [1..Size(original_reps)] do
    r:=original_reps[i];
    size:=SpUnipotentClassSize_Odd@(G,T[i],Params[i],q);
    D[i]:=[Order(r),size,r];
    if Rewrite then
      C[i]:=[Order(r),size,Reps[i]];
    fi;
  od;
  return rec(val1:=C,
    val2:=D,
    val3:=Forms,
    val4:=T,
    val5:=Params);
end;


