#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Abs, Append, CentraliserDimension_Even,
#  CentraliserStructure_Even, ChevalleyGroup, ChevalleyGroupOrder, Determinant,
#  DiagonalMatrix, Floor, GF, GO, GOCentraliserDimension_Odd, GOMinus, GOPlus,
#  GO_ConvertT, GO_SSOrder_Odd, Integers, IsEven, IsIntegral, IsOdd, IsSquare,
#  Multiplicity, Multiset, MultisetToSequence, Nrows,
#  OrthogonalUnipotentCentraliserOrder_Even,
#  OrthogonalUnipotentCentraliserOrder_Odd, Orthogonal_Dimension_Even,
#  Orthogonal_MyBlockDimension, Orthogonal_MyDimension, Orthogonal_Order,
#  ParallelSort, Position, Reverse, Set, Sort, SpBlockDimension,
#  SpCentraliserDimension_Even, SpCentraliserDimension_Odd, SpConvertT,
#  SpMyDimension, SpSSOrder_Odd, SpUnipotentCentraliserOrder_Even,
#  SpUnipotentCentraliserOrder_Odd

#  Defines: CentraliserDimension_Even, CentraliserStructure_Even,
#  GOCentraliserDimension_Odd, GO_ConvertT, GO_SSOrder_Odd,
#  OrthogonalUnipotentCentraliserOrder,
#  OrthogonalUnipotentCentraliserOrder_Even,
#  OrthogonalUnipotentCentraliserOrder_Odd, Orthogonal_Dimension_Even,
#  Orthogonal_MyBlockDimension, Orthogonal_MyDimension, Orthogonal_Order,
#  SpBlockDimension, SpCentraliserDimension_Even, SpCentraliserDimension_Odd,
#  SpConvertT, SpMyDimension, SpSSOrder_Odd, SpUnipotentCentraliserOrder,
#  SpUnipotentCentraliserOrder_Even, SpUnipotentCentraliserOrder_Odd

DeclareGlobalFunction("OrthogonalUnipotentCentraliserOrder@");

DeclareGlobalFunction("SpUnipotentCentraliserOrder@");

#   orders of centralisers in semisimple and orthogonal groups
#   GO -- generators for semisimple piece
GO_SSOrder_Odd@:=function(VBeta,T,q)
local C,M,V,W,a,beta,d,epsilon,ord,order,type,values_V;
  order:=1;
  W:=T[1];
  for a in Set(W) do
    d:=Size(Filtered(W,x->x=a));
    C:=ChevalleyGroup("C",d,q);
    order:=order*Size(C);
  od;
  V:=T[2];
  V:=List(V,x->2*x+1);
  values_V:=List(Set(V),v->v);
  Sort(TILDEvalues_V);
  for a in values_V do
    beta:=List(Filtered(VBeta,b->b[1]=a),b->b[2]);
    M:=DiagonalMat(GF(q),beta);
    if Length(M) > 1 then
      if IsEvenInt(Length(M)) then
        epsilon:=(-1)^(QuoInt(Length(M),2))*DeterminantMat(M);
        # rewritten select statement
        if IsSquare(epsilon) then
          type:="plus";
        else
          type:="minus";
        fi;
        # rewritten select statement
        if type="plus" then
          ord:=Size(GOPlus(Length(M),q));
        else
          ord:=Size(GOMinus(Length(M),q));
        fi;
      else
        ord:=Size(GO(Length(M),q));
      fi;
      order:=order*ord;
    else
      order:=order*2;
    fi;
  od;
  return order;
end;

GOCentraliserDimension_Odd@:=function(m)
local a,b,c,d,dim,i,mult,x;
  dim:=List([1..Size(m)],i->m[i][1]);
  mult:=List([1..Size(m)],i->m[i][2]);
  ParallelSort(TILDEdim,TILDEmult);
  a:=List(Filtered([1..Size(m)],i->IsOddInt(dim[i])),i->(dim[i]-1)*mult[i]^2);
  # rewritten select statement
  if Size(a) > 0 then
    a:=Sum(a/2);
  else
    a:=0;
  fi;
  b:=List(Filtered([1..Size(m)],i->IsEvenInt(dim[i])),i->(dim[i]-1)*mult[i]^2);
  # rewritten select statement
  if Size(b) > 0 then
    b:=Sum(b/2);
  else
    b:=0;
  fi;
  c:=List(Filtered([1..Size(m)],i->IsEvenInt(dim[i])),i->mult[i]);
  # rewritten select statement
  if Size(c) > 0 then
    c:=Sum(c/2);
  else
    c:=0;
  fi;
  d:=0;
  for i in [1..Size(m)] do
    x:=List([i+1..Size(m)],j->dim[i]*mult[i]*mult[j]);
    d:=d+Size(x)=# rewritten select statement
    function(xxx)if xxx then return 0;else return Sum(x);fi;end(0);
  od;
  return Int((a+b-c+d));
end;

GO_ConvertT@:=function(T)
local V,W,a,b,m;
  V:=[];
  W:=[];
  for a in Set(T) do
    m:=Multiplicity(T,a);
    if IsOddInt(a) then
      b:=QuoInt((a-1),2);
      V:=Concatenation(V,List([1..m],i->b));
    else
      W:=Concatenation(W,List([1..QuoInt(m,2)],i->a));
    fi;
  od;
  Sort(TILDEV);
  Reversed(TILDEV);
  Sort(TILDEW);
  Reversed(TILDEW);
  return [W,V];
end;

OrthogonalUnipotentCentraliserOrder_Odd@:=function(type,VBeta,T,split,q)
local T_new,a,dim,m,o,s;
  s:=MultisetToSequence(T);
  m:=List(Set(s),x->[x,Size(Filtered(s,y->y=x))]);
  dim:=GOCentraliserDimension_Odd@(m);
  T_new:=GO_ConvertT@(T);
  a:=GO_SSOrder_Odd@(VBeta,T_new,q);
  o:=a*q^dim;
  if type in ["GO","GO+","GO-","O","O+","O-"] then
    return o;
  elif type in ["SO+","Omega+"] and ForAll(Set(T),x->IsEvenInt(x)) then
    return o;
  else
    if type in ["SO+","SO-","SO"] then
      return QuoInt(o,2);
    fi;
    if split=true then
      return QuoInt(o,2);
    fi;
    return QuoInt(o,4);
  fi;
end;

#   Sp generators for semisimple piece
SpSSOrder_Odd@:=function(VBeta,T,q)
local M,V,W,a,beta,d,epsilon,ord,order,type,values_V;
  order:=1;
  W:=T[1];
  for a in Set(W) do
    d:=Size(Filtered(W,x->x=a));
    order:=order*ChevalleyGroupOrder("C",d,q);
  od;
  V:=T[2];
  values_V:=List(Set(V),v->v);
  Sort(TILDEvalues_V);
  for a in values_V do
    beta:=List(Filtered(VBeta,b->b[1]=2*a),b->b[2]);
    M:=DiagonalMat(GF(q),beta);
    if Length(M)=1 then
      order:=order*2;
    else
      if IsEvenInt(Length(M)) then
        epsilon:=(-1)^(QuoInt(Length(M),2))*DeterminantMat(M);
        # rewritten select statement
        if IsSquare(epsilon) then
          type:="plus";
        else
          type:="minus";
        fi;
        # rewritten select statement
        if type="plus" then
          ord:=Size(GOPlus(Length(M),q));
        else
          ord:=Size(GOMinus(Length(M),q));
        fi;
      else
        ord:=Size(GO(Length(M),q));
      fi;
      order:=order*ord;
    fi;
  od;
  return order;
end;

#   dimension of unipotent subgroup of centraliser
SpCentraliserDimension_Odd@:=function(m)
local a,b,c,d,dim,i,mult,x;
  dim:=List([1..Size(m)],i->m[i][1]);
  mult:=List([1..Size(m)],i->m[i][2]);
  ParallelSort(TILDEdim,TILDEmult);
  a:=List(Filtered([1..Size(m)],i->IsOddInt(dim[i])),i->(dim[i]-1)*mult[i]^2);
  # rewritten select statement
  if Size(a) > 0 then
    a:=Sum(a/2);
  else
    a:=0;
  fi;
  b:=List(Filtered([1..Size(m)],i->IsEvenInt(dim[i])),i->(dim[i]-1)*mult[i]^2);
  # rewritten select statement
  if Size(b) > 0 then
    b:=Sum(b/2);
  else
    b:=0;
  fi;
  c:=List(Filtered([1..Size(m)],i->IsEvenInt(dim[i])),i->mult[i]);
  # rewritten select statement
  if Size(c) > 0 then
    c:=Sum(c/2);
  else
    c:=0;
  fi;
  d:=0;
  for i in [1..Size(m)] do
    x:=List([i+1..Size(m)],j->dim[i]*mult[i]*mult[j]);
    d:=d+Size(x)=# rewritten select statement
    function(xxx)if xxx then return 0;else return Sum(x);fi;end(0);
  od;
  Assert(1,IsIntegral(a+b+c+d));
  return Int((a+b+c+d));
end;

SpConvertT@:=function(T)
local V,W,a,b,m;
  V:=[];
  W:=[];
  for a in Set(T) do
    m:=Multiplicity(T,a);
    if IsEvenInt(a) then
      b:=QuoInt(a,2);
      V:=Concatenation(V,List([1..m],i->b));
    else
      W:=Concatenation(W,List([1..QuoInt(m,2)],i->QuoInt(a,2)));
    fi;
  od;
  Sort(TILDEV);
  Sort(TILDEW);
  return [W,V];
end;

SpUnipotentCentraliserOrder_Odd@:=function(T,VBeta,q)
local T,a,dim,m,s;
  s:=MultisetToSequence(T);
  m:=List(Set(s),x->[x,Size(Filtered(s,y->y=x))]);
  T:=SpConvertT@(T);
  a:=SpSSOrder_Odd@(VBeta,T,q);
  dim:=SpCentraliserDimension_Odd@(m);
  return a*q^dim;
end;

#   C_G (u) where u is determined by data in T
CentraliserDimension_Even@:=function(type,T)
local Chi,V,W,d,dim,i,pos,value;
  W:=Concatenation(T[1],T[1],T[3],T[3]);
  Sort(TILDEW);
  Reversed(TILDEW);
  V:=Concatenation(T[2],T[4]);
  V:=List(V,v->2*v);
  dim:=0;
  Chi:=[];
  for i in [1..Size(V)] do
    d:=V[i];
    # rewritten select statement
    if type="Sp" then
      value:=QuoInt(d,2);
    else
      value:=QuoInt((d+2),2);
    fi;
    Add(Chi,value);
  od;
  for i in [1..Size(W)] do
    d:=W[i];
    pos:=Position(V,d);
    if pos<>0 then
      # rewritten select statement
      if type="Sp" then
        value:=QuoInt(d,2);
      else
        value:=QuoInt((d+2),2);
      fi;
      Add(Chi,value);
    else
      # rewritten select statement
      if type="Sp" then
        value:=Floor((W[i]-1)/2);
      else
        value:=Floor((W[i]+1)/2);
      fi;
      Add(Chi,value);
    fi;
  od;
  V:=Concatenation(V,W);
  Assert(1,Size(Chi)=Size(V));
  ParallelSort(TILDEV,TILDEChi);
  Reversed(TILDEV);
  Reversed(TILDEChi);
  dim:=Sum(List([1..Size(V)],i->i*V[i]-Chi[i]));
  return rec(val1:=dim,
    val2:=V,
    val3:=Chi);
end;

#   centraliser structure for element determined by T
CentraliserStructure_Even@:=function(type,T,q)
local A,L,M,Minus,S,T,T3,V,W,a,delta,i,name,power,sign,t;
  W:=Concatenation(T[1],T[3]);
  V:=Concatenation(T[2],T[4]);
  Sort(TILDEV);
  M:=Multiset(W);
  A:=List(Filtered(Set(M),s->IsEvenInt(s)),s->Multiplicity(M,s));
  L:=List( # [*-list:
    A,a->["C",a,q]);
  if type="Sp" then
    S:=Filtered(W,w->w=1 or (IsOddInt(w) and ForAny(V,v->Abs(w-2*v)=1)));
  else
    S:=Filtered(W,w->(IsOddInt(w) and ForAny(V,v->Abs(w-2*v)=1)));
  fi;
  A:=List(S,s->Multiplicity(M,s));
  L:=Concatenation(L,List( # [*-list:
    A,a->["C",a,q]));
  T3:=Set(T[3]);
  T:=Filtered(W,w->IsOddInt(w) and not (w in S));
  T:=List(T,t->t);
  A:=List(T,t->Multiplicity(M,t));
  for i in [1..Size(A)] do
    a:=A[i];
    t:=T[i];
    Minus:=Filtered(T3,w->w=t);
    # rewritten select statement
    if IsOddInt(Size(Minus)) then
      sign:="-";
    else
      sign:="+";
    fi;
    name:=Concatenation("O",sign);
    L:=Concatenation(L,# [*-list:
    [[name,a,q]]);
  od;
  t:=Size(Filtered([1..Size(V)-1],j->V[j+1]-V[j] >= 2));
  # rewritten select statement
  if ((Size(V)=0) or (type="Sp" and 1 in V)) then
    delta:=0;
  else
    delta:=1;
  fi;
  power:=t+delta;
  if power > 0 then
    L:=Concatenation(L,# [*-list:
    [[19,2^power,0]]);
  fi;
  return L;
end;

#   order of centraliser of unipotent element
#   in GO / Omega^\epsilon (d, q) where q is even
Orthogonal_MyDimension@:=function(str)
local q,r,type;
  type:=str[1];
  r:=str[2];
  q:=str[3];
  if type=19 then
    return 0;
  fi;
  if type="C" then
    return 2*r^2+r;
  fi;
  if type="O+" then
    return 2*r^2-r;
  fi;
  if type="O-" then
    return 2*r^2-r;
  fi;
  if type="O" then
    return 2*r^2+r;
  fi;
end;

Orthogonal_MyBlockDimension@:=function(block)
if Size(block)=0 then
    return 0;
  fi;
  return Sum(List(block,s->Orthogonal_MyDimension@(s)));
end;

Orthogonal_Dimension_Even@:=function(q,t)
local S,varX,Y;
  varX:=CentraliserDimension_Even@("Omega-",t);
  S:=CentraliserStructure_Even@("Omega-",t,q);
  Y:=Orthogonal_MyBlockDimension@(S);
  return rec(val1:=S,
    val2:=varX-Y);
end;

Orthogonal_Order@:=function(S,z,q)
local ord,order,t,tup;
  order:=q^z;
  for t in S do
    tup:=t;
    if tup[1]=19 then
      ord:=tup[2];
    elif tup[1]="O-" then
      ord:=Size(GOMinus(2*tup[2],tup[3]));
    elif tup[1]="O+" then
      ord:=Size(GOPlus(2*tup[2],tup[3]));
    else
      ord:=ChevalleyGroupOrder(tup[1],tup[2],tup[3]);
    fi;
    order:=order*ord;
  od;
  return order;
end;

OrthogonalUnipotentCentraliserOrder_Even@:=function(type,T,q)
local S,k,z;
  Assert(1,IsEvenInt(q));
  # =v= MULTIASSIGN =v=
  z:=Orthogonal_Dimension_Even@(q,T);
  S:=z.val1;
  z:=z.val2;
  # =^= MULTIASSIGN =^=
  k:=Orthogonal_Order@(S,z,q);
  if type="Omega-" then
    if T[Size(T)]=-1 then
      return k;
    else
      return QuoInt(k,2);
    fi;
  elif type="Omega+" then
    if Size(T[2])=0 and Size(T[4])=0 and Size(T[3])=0 and ForAll(Set(T[1])
       ,x->IsEvenInt(x)) then
      return k;
    fi;
    return QuoInt(k,2);
  elif type in ["O+","O-","GO-","SO-","GO+","SO+"] then
    return k;
  else
    Error("type");
  fi;
end;

InstallGlobalFunction(OrthogonalUnipotentCentraliserOrder@,
function(type,T,VBeta,split,q)
if IsEvenInt(q) then
    return OrthogonalUnipotentCentraliserOrder_Even@(type,T,q);
  else
    return OrthogonalUnipotentCentraliserOrder_Odd@(type,VBeta,T,split,q);
  fi;
end);

SpMyDimension@:=function(str)
local q,r,type;
  type:=str[1];
  r:=str[2];
  q:=str[3];
  if type=19 then
    return 0;
  fi;
  if type="C" then
    return 2*r^2+r;
  fi;
  if type="O+" then
    return 2*r^2-r;
  fi;
  if type="O-" then
    return 2*r^2-r;
  fi;
  if type="O" then
    return 2*r^2+r;
  fi;
end;

SpBlockDimension@:=function(block)
if Size(block)=0 then
    return 0;
  fi;
  return Sum(List(block,s->SpMyDimension@(s)));
end;

SpCentraliserDimension_Even@:=function(t,q)
local S,varX,Y;
  varX:=CentraliserDimension_Even@("Sp",t);
  S:=CentraliserStructure_Even@("Sp",t,q);
  Y:=SpBlockDimension@(S);
  return rec(val1:=varX-Y,
    val2:=S);
end;

SpUnipotentCentraliserOrder_Even@:=function(T,q)
local S,dim,ord,order,t,tup;
  # =v= MULTIASSIGN =v=
  S:=SpCentraliserDimension_Even@(T,q);
  dim:=S.val1;
  S:=S.val2;
  # =^= MULTIASSIGN =^=
  order:=1;
  for t in S do
    tup:=t;
    if tup[1]=19 then
      ord:=tup[2];
    elif tup[1]="O-" then
      ord:=Size(GOMinus(2*tup[2],tup[3]));
    elif tup[1]="O+" then
      ord:=Size(GOPlus(2*tup[2],tup[3]));
    else
      ord:=ChevalleyGroupOrder(tup[1],tup[2],tup[3]);
    fi;
    order:=order*ord;
  od;
  return order*q^dim;
end;

InstallGlobalFunction(SpUnipotentCentraliserOrder@,
function(T,VBeta,q)
if IsEvenInt(q) then
    return SpUnipotentCentraliserOrder_Even@(T,q);
  else
    return SpUnipotentCentraliserOrder_Odd@(T,VBeta,q);
  fi;
end);


