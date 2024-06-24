#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Characteristic, Degree, Factorization, Gcd,
#  IsEven, IsOdd, IsUnipotent, JordanForm, Jordan_Parameters, Multiplicity,
#  Multiset, SequenceToFactorization, SetToSequence, Sort

#  Defines: Jordan_Parameters, UnipotentCentraliserOrder,
#  UnipotentCentralizerOrder

DeclareGlobalFunction("Jordan_Parameters@");

DeclareGlobalFunction("UnipotentCentraliserOrder@");

DeclareGlobalFunction("UnipotentCentralizerOrder@");

#   compute cardinality of the centralizer of unipotent element g
#   in the group of type "type" preserving the supplied form;
#   JF = multiset of the sizes of the Jordan blocks;

#   in the linear and unitary case, JF is the only information
#   needed to compute the cardinality;
#   form is not required for Sp / Orthogonal in even characteristic
InstallGlobalFunction(Jordan_Parameters@,
function(g)
local _,blocks,c,forgetvar1,forgetvar2;
  # =v= MULTIASSIGN =v=
  c:=JordanForm(g);
  forgetvar1:=c.val1;
  forgetvar2:=c.val2;
  c:=c.val3;
  # =^= MULTIASSIGN =^=
  blocks:=List(c,x->x[2]);
  return Multiset(blocks);
end);

InstallGlobalFunction(UnipotentCentraliserOrder@,
function(type,G,g,form)
local Array,F,JF,L,P,T,W,_,c,card,e,exp,forgetvar1,forgetvar2,i,j,p,q,split;
  JF:=ValueOption("JF");
  if JF=fail then
    JF:=[];
  fi;
  T:=ValueOption("T");
  if T=fail then
    T:=[];
  fi;
  L:=ValueOption("L");
  if L=fail then
    L:=[];
  fi;
  split:=ValueOption("split");
  if split=fail then
    split:=false;
  fi;
  Assert(1,IsUnipotent(g));
  F:=BaseRing(g);
  q:=Size(F);
  p:=Characteristic(F);
  e:=Degree(F);
  if type in ["SU","GU"] then
    q:=p^(QuoInt(e,2));
  fi;
  if type in ["GL","SL","GU","SU"] then
    if JF=[] then
      # =v= MULTIASSIGN =v=
      c:=JordanForm(g);
      forgetvar1:=c.val1;
      forgetvar2:=c.val2;
      c:=c.val3;
      # =^= MULTIASSIGN =^=
      JF:=List(c,d->d[2]);
    fi;
    Array:=List( # {-list:
      JF,b->b);
    Array:=Sort(SetToSequence(Array));
    P:=List(Array,a->[a,Multiplicity(JF,a)]);
  fi;
  card:=Factorization(1);
  if type="GL" or type="SL" then
    for i in [1..Size(P)] do
      card:=card*CardinalityOfClassicalGroup@("linear",P[i][2],q);
    od;
    exp:=0;
    for i in [1..Size(P)] do
      exp:=exp+(P[i][1]-1)*P[i][2]^2;
      for j in [i+1..Size(P)] do
        exp:=exp+2*P[i][1]*P[i][2]*P[j][2];
      od;
    od;
    exp:=exp*e;
    if exp<>0 then
      card:=card*SequenceToFactorization([[p,exp]]);
    fi;
    if type="SL" then
      card:=card/Factorization(q-1);
      card:=card*Factorization(Gcd(q-1,Gcd(List(P,a->a[1]))));
    fi;
  elif type="GU" or type="SU" then
    for i in [1..Size(P)] do
      card:=card*CardinalityOfClassicalGroup@("unitary",P[i][2],q);
    od;
    exp:=0;
    for i in [1..Size(P)] do
      exp:=exp+(P[i][1]-1)*P[i][2]^2;
      for j in [i+1..Size(P)] do
        exp:=exp+2*P[i][1]*P[i][2]*P[j][2];
      od;
    od;
    exp:=exp*(QuoInt(e,2));
    if exp<>0 then
      card:=card*SequenceToFactorization([[p,exp]]);
    fi;
    if type="SU" then
      card:=card/Factorization(q+1);
      card:=card*Factorization(Gcd(q+1,Gcd(List(P,a->a[1]))));
    fi;
  elif type="Sp" then
    if IsEvenInt(q) then
      if Size(L)=0 then
        W:=MyUnipotentClassLabel(G,g);
        T:=WeightsToLabel(W);
      else
        T:=L;
      fi;
      card:=Factorization(SpUnipotentCentraliserOrder@(T,[],q));
    elif IsOddInt(q) then
      if Size(T)=0 then
        T:=Jordan_Parameters@(g);
      fi;
      if Size(L)=0 then
        L:=MyUnipotentClassLabel(G,g);
      fi;
      card:=Factorization(SpUnipotentCentraliserOrder@(T,L,q));
    fi;
  elif type="GO+" or type="GO-" or type="GO" or type="SO+" or type="SO-" or 
     type="SO" or type="Omega+" or type="Omega-" or type="Omega" then
    if IsEvenInt(q) then
      if Size(L)=0 then
        W:=MyUnipotentClassLabel(G,g);
        T:=WeightsToLabel(W[1]);
        T[Size(T)]:=W[2];
      else
        W:=T;
      fi;
      card:=Factorization(OrthogonalUnipotentCentraliserOrder@(type,T,[]
       ,false,q));
    elif IsOddInt(q) then
      if Size(T)=0 then
        T:=Jordan_Parameters@(g);
      fi;
      if Size(L)=0 then
        L:=MyUnipotentClassLabel(G,g);
      fi;
      if type in ["GO+","GO-","GO"] then
        card:=Factorization(OrthogonalUnipotentCentraliserOrder@(type,T,L,false,
         q));
      else
        # rewritten select statement
        if L[2]="ns" then
          split:=false;
        else
          split:=true;
        fi;
        card:=Factorization(OrthogonalUnipotentCentraliserOrder@(type,T,L[1]
         ,split,q));
      fi;
    fi;
  else
    Error("Type is incorrect");
  fi;
  return card;
end);

DeclareSynonym(UnipotentCentralizerOrder,UnipotentCentraliserOrder); #TODO: actually we have DeclareSynonym(UnipotentCentralizerOrder@,UnipotentCentraliserOrder@);


