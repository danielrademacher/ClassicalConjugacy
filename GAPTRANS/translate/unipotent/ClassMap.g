#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: BaseRing, Degree, Generic,
#  InternalUnipotentIsConjugate, IsEven, IsIrreducible, IsOdd, IsUnipotent,
#  Multiset, Parent, Position, Rep, Type, UnipotentClassIndex, UnipotentLabel

#  Defines: UnipotentClassIndex, UnipotentClassLabel, UnipotentClassMap,
#  UnipotentLabel

DeclareGlobalFunction("UnipotentLabel@");

#   label in format returned by UnipotentClasses
InstallGlobalFunction(UnipotentLabel@,
function(G,g)
local F,flag,l,label,two,type;
  type:=ValueOption("type");
  if type=fail then
    type:=false;
  fi;
  if type=false then
    # =v= MULTIASSIGN =v=
    type:=GroupType(G); # there was an @!!! TODO
    flag:=type.val1;
    type:=type.val2;
    # =^= MULTIASSIGN =^=
  fi;
  F:=BaseRing(G);
  label:=MyUnipotentClassLabel(G,g:type:=type);
  if type="GL" then
    label:=Concatenation(List(label,x->List([1..x[2]],i->x[1])));
    label:=Multiset(label);
  elif type="SL" then
    two:=label[2];
    label:=label[1];
    label:=[Multiset(label),two];
  elif type="GU" then
    label:=Multiset(label);
  elif type="SU" then
    two:=label[2];
    label:=Multiset(label[1]);
    label:=[label,two];
  elif type="Sp" then
    if IsEvenInt(Size(F)) then
      label:=WeightsToLabel(label);
    else
      label:=Multiset(label);
    fi;
  elif IsEvenInt(Size(F)) then
    #   all orthogonal cases in even char
    l:=label;
    label:=WeightsToLabel(l[1]);
    label[Size(label)]:=l[2];
  elif IsOddInt(Size(F)) and type in ["GO+","GO-","GO"] then
    label:=Multiset(label);
    label:=[label,"ns"];
  else
    #   all remaining orthogonal cases in odd char
    two:=label[2];
    label:=Multiset(label[1]);
    label:=[label,two];
  fi;
  return label;
end);

UnipotentClassLabel@:=function(G,g)
#  -> ,Any  return unipotent conjugacy class label for unipotent element g of
#  classical G ; if two elements of G have different labels , then they are not
#  conjugate ; two elements of an isometry group G are conjugate in G if and
#  only if they have same label
local Valid,flag,label,type;
  if not IsUnipotent(g) then
    Error("Element must be unipotent");
  fi;
  if not Generic(G)=Generic(Parent(g)) then
    Error("Element is not in group");
  fi;
  #   what groups do we accept?
  # =v= MULTIASSIGN =v=
  type:=GroupType(G); # there was an @!!! TODO
  flag:=type.val1;
  type:=type.val2;
  # =^= MULTIASSIGN =^=
  if not flag then
    Error("Input group must be classical");
  fi;
  Valid:=Set(["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-",
   "SO","GO+","GO-","GO","O+","O-","O"]);
  if not type in Valid then
    Error(["Classical group type is not valid, must be one of ",Valid]);
  fi;
  label:=UnipotentLabel@(G,g);
  return label;
end;

#   C is sequence of classes and L is sequence of labels;
#   return index of conjugacy class containing element g
UnipotentClassIndex@:=function(G,g,U,L,type,F)
#  /out: two cases coincide
local found,index,j,label,two,Tup; # Tup is a type in magma!!! TODO
  if type in ["GL","SL"] and Size(F)=2 then
    # rewritten select statement
    if Type(Rep(L))=Tup then
      type:="SL";
    else
      type:="GL";
    fi;
    G.ClassicalType:=type;
  fi;
  #   do we need label relative to isom group? or actual G?
  label:=UnipotentLabel@(G,g);
  if type="SU" then
    two:=label[2];
    label:=label[1];
    index:=Filtered([1..Size(L)],i->L[i][1]=label);
    if Size(index) > 1 then
      found:=false;
      #   "SU must decide conjugacy";
      #   "index is ", #index;
      for j in index do
        if InternalUnipotentIsConjugate(G,g,U[j][3]) then # there was an @!!! TODO
          two:=L[j][2];
          found:=true;
          break;
        fi;
      od;
      Assert(1,found);
    fi;
    label:=[label,two];
  elif type in ["SO+","SO-","SO","Omega+","Omega-","Omega"] and IsOddInt(Size(F)
     ) then
    #   all remaining orthogonal cases in odd char
    two:=label[2];
    label:=label[1];
    if two<>"ns" then
      index:=Filtered([1..Size(L)],i->L[i][1]=label);
      Assert(1,Size(index) > 1);
      found:=false;
      #   "Omega / SO here must decide conjugacy", type;
      #   "index is ", #index;
      for j in index do
        if InternalUnipotentIsConjugate(G,g,U[j][3]) then # there was an @!!! TODO
          two:=L[j][2];
          found:=true;
          break;
        fi;
      od;
      Assert(1,found);
    fi;
    label:=[label,two];
  fi;
  return Position(L,label);
end;

UnipotentClassMap@:=function(G,U,L)
#  -> ,Map  U and L are output of UnipotentClasses , where U := sequence of
#  unipotent class representative and L := the corresponding list of labels ;
#  return unipotent class map for G
local F,ValidTypes@,flag,type;
  type:=ValueOption("type");
  if type=fail then
    type:=false;
  fi;
  if not IsIrreducible(G) then
    Error("Input group must be irreducible");
  fi;
  ValidTypes@:=Set(["GL","SL","Sp","SU","GU","Omega+","Omega-","Omega","O","O+",
   "O-","SO+","SO-","SO","GO+","GO-","GO"]);
  if not ForAll(U,x->IsUnipotent(x[3])) then
    Error("Must supply unipotent classes");
  fi;
  if not Generic(G)=Generic(Parent(U[1][3])) then
    Error("classes do not belong to G");
  fi;
  if not ForAll(U,u->u[3] in G) then
    Error("not all supplied classes belong to G");
  fi;
  if Degree(G)=2 and Size(U)=1 then
    return GroupGeneralMappingByFunction(Generic(G),[1],
      g->1);
  fi;
  F:=BaseRing(G);
  if Degree(G)=2 then
      if not type<>false then
      Error("For this (small) case, you must supply type");
    fi;
      if not type in ValidTypes@ then
      Error(["Type must be one of ",ValidTypes@]);
    fi;
    if type="O" then
      type:="GO";
    elif type="O+" then
      type:="GO+";
    elif type="O-" then
      type:="GO+";
    fi;
    G.ClassicalType:=type;
  else
    # =v= MULTIASSIGN =v=
    type:=GroupType(G); # there was an @!!! TODO
    flag:=type.val1;
    type:=type.val2;
    # =^= MULTIASSIGN =^=
      if not flag and type in ValidTypes@ then
      Error(["Input group must be one of these types",ValidTypes@]);
    fi;
  fi;
  return GroupGeneralMappingByFunction(Generic(G),[1..Size(U)],
    g->UnipotentClassIndex@(G,g,U,L,type,F));
end;


