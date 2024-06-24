#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Degree, Exclude, GF, Include, IsOdd, IsSquare,
#  PrimitiveElement, _is_square

#  Defines: TurnCorrectLabel, _is_square

#   return true if det (StandardSymmetricForm(n,q)) is a square, false 
 otherwise
_is_square@:=function(n,q)
return ((q mod 8 in [1,3] and n mod 4=3) or (q mod 8 in [1,7] and n mod 4=1));
end;

#   if X,L = ClassRepresentativesGO(n,q) then
#   TurnCorrectLabel(toNameEven(L[i])) = IsometryGroupClassLabel("GO",X[i]) for
#  every i in [1..#X]
#   how it works: it switches the unipotent labels of the (t+1)- and
#  (t-1)-eigenspaces with ChangeClassLabel
#   the one in odd dim is switched whenever its discriminant is not a square
#   the one in even dim is switched whenever the global discriminant (before
#  the correction above)
#   is not the same as the discriminant of the standard Magma form
TurnCorrectLabel@:=function(L,n,F)
local DetForm,EvenLabelToChange,ThereIsEven,dim,discr,l,pr,q,x;
  DetForm:=1;
  #   1 if square, -1 otherwise
  q:=Size(F);
  pr:=PrimitiveElement(F);
  ThereIsEven:=false;
  for l in L do
    if l[1]=0 then
      discr:=1*FORCEOne(GF(q));
      dim:=0;
      for x in l[3] do
        if x[2]<>0 then
          discr:=discr*2*x[2]*(-1)^(QuoInt((x[1]-1),2));
        fi;
        dim:=dim+x[1];
      od;
      if IsOddInt(dim) then
        if not IsSquare(discr) then
          DetForm:=DetForm*-1;
          RemoveSet(TILDEL,l);
          UniteSet(TILDEL,[l[1],l[2],ChangeClassLabel@(l[3],F,pr)]);
        fi;
      else
        ThereIsEven:=true;
        if not IsSquare(discr) then
          DetForm:=DetForm*-1;
        fi;
        EvenLabelToChange:=l;
      fi;
    elif l[1]=1 then
      if q mod 4=3 and Degree(l[2]) mod 4=2 and IsOddInt(Sum(List(l[3],y->y[1]))
         ) then
        DetForm:=DetForm*-1;
      fi;
    elif l[1]=2 then
      if q mod 4=1 then
        if IsOddInt(Sum(List(l[3],y->y[1]))) then
          DetForm:=DetForm*-1;
        fi;
      else
        if IsOddInt(Sum(List(l[3],y->y[1]))) and Degree(l[2]) mod 4=0 then
          DetForm:=DetForm*-1;
        fi;
      fi;
    fi;
  od;
  if ThereIsEven and (_is_square@(n,q)xorDetForm=1) then
    RemoveSet(TILDEL,EvenLabelToChange);
    UniteSet(TILDEL,[EvenLabelToChange[1],EvenLabelToChange[2]
     ,ChangeClassLabel@(EvenLabelToChange[3],F,pr)]);
  fi;
  return L;
end;


