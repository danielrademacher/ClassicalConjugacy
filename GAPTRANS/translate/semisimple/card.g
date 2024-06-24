#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Factorization, IsOdd, IsPrimePower,
#  SequenceToFactorization

#  Defines: CardinalityOfClassicalGroup

DeclareGlobalFunction("CardinalityOfClassicalGroup@");

#   order of classical group
InstallGlobalFunction(CardinalityOfClassicalGroup@,
function(type,n,q)
local C,_,e,forgetvar1,i,m,p,type;
  # =v= MULTIASSIGN =v=
  e:=IsPrimePower(q);
  forgetvar1:=e.val1;
  p:=e.val2;
  e:=e.val3;
  # =^= MULTIASSIGN =^=
  m:=QuoInt(n,2);
  if IsOddInt(n) then
    if type in ["orthogonalplus","orthogonalminus","O+","O-","GO+","GO-"] then
      type:="GO";
    elif type in ["SO+","SO-"] then
      type:="SO";
    elif type in ["Omega+","Omega-"] then
      type:="Omega";
    fi;
  fi;
  C:=Factorization(1);
  if type="linear" or type="GL" or type="SL" then
    if n > 1 then
      C:=C*SequenceToFactorization([[p,QuoInt(e*n*(n-1),2)]]);
    fi;
    for i in [1..n] do
      C:=C*Factorization(q^i-1);
    od;
    if type="SL" then
      C:=C/Factorization(q-1);
    fi;
  elif type="symplectic" or type="Sp" then
    C:=C*SequenceToFactorization([[p,e*m^2]]);
    for i in [1..m] do
      C:=C*Factorization(q^(2*i)-1);
    od;
  elif type="unitary" or type="GU" or type="SU" then
    if n > 1 then
      C:=C*SequenceToFactorization([[p,QuoInt(e*n*(n-1),2)]]);
    fi;
    for i in [1..n] do
      C:=C*Factorization(q^i-(-1)^i);
    od;
    if type="SU" then
      C:=C/Factorization(q+1);
    fi;
  elif type="orthogonalplus" or type="O+" or type="GO+" or type="SO+" or 
     type="Omega+" then
    C:=C*SequenceToFactorization([[2,1]]);
    if m > 1 then
      C:=C*SequenceToFactorization([[p,e*m*(m-1)]]);
    fi;
    C:=C*Factorization(q^m-1);
    for i in [1..m-1] do
      C:=C*Factorization(q^(2*i)-1);
    od;
    if type="Omega+" then
      C:=C/SequenceToFactorization([[2,1]]);
      if IsOddInt(q) then
        C:=C/SequenceToFactorization([[2,1]]);
      fi;
    elif type="SO+" and IsOddInt(p) then
      C:=C/SequenceToFactorization([[2,1]]);
    fi;
  elif type="orthogonal" or type="orthogonalcircle" or type="O" or type="GO" or 
     type="SO" or type="Omega" then
    C:=C*SequenceToFactorization([[2,1]]);
    if m >= 1 then
      C:=C*SequenceToFactorization([[p,e*m^2]]);
    fi;
    for i in [1..m] do
      C:=C*Factorization(q^(2*i)-1);
    od;
    if type="Omega" then
      C:=C/SequenceToFactorization([[2,1]]);
      if IsOddInt(q) then
        C:=C/SequenceToFactorization([[2,1]]);
      fi;
    elif type="SO" and IsOddInt(p) then
      C:=C/SequenceToFactorization([[2,1]]);
    fi;
  elif type="orthogonalminus" or type="O-" or type="GO-" or type="SO-" or 
     type="Omega-" then
    C:=C*SequenceToFactorization([[2,1]]);
    if m > 1 then
      C:=C*SequenceToFactorization([[p,e*m*(m-1)]]);
    fi;
    C:=C*Factorization(q^m+1);
    for i in [1..m-1] do
      C:=C*Factorization(q^(2*i)-1);
    od;
    if type="Omega-" then
      C:=C/SequenceToFactorization([[2,1]]);
      if IsOddInt(q) then
        C:=C/SequenceToFactorization([[2,1]]);
      fi;
    elif type="SO-" and IsOddInt(p) then
      C:=C/SequenceToFactorization([[2,1]]);
    fi;
  fi;
  return C;
end);


