#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: GF, IsEven, IsOdd, IsPrimePower, SemisimpleClasses

#  Defines: SemisimpleClasses

SemisimpleClasses:=function(type,n,q) # there was an @!!! TODO
#  -> ,]  Semisimple conjugacy classes of the classical group of supplied type
#  , rank and field size
local F,ValidTypes; # there was an @!!! TODO
  ValidTypes:=["Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-","SO","GO+", # there was an @!!! TODO
   "GO-","GO","O+","O-","O"];
  if not type in ValidTypes then # there was an @!!! TODO
    Error(["Type must be one of ",ValidTypes]); # there was an @!!! TODO
  fi;
  if not n > 0 then
    Error("Degree must be positive");
  fi;
  if not IsPrimePower(q) then
    Error("Invalid field size");
  fi;
  if type in ["O","SO","Omega"] then
      if not IsOddInt(n) then
      Error("Degree must be odd");
    fi;
  elif type in ["GO+","O+","SO+","Omega+","GO-","O-","SO-","Omega-","Sp"] then
      if not IsEvenInt(n) then
      Error("Degree must be even");
    fi;
  fi;
  if type in ["GU","SU"] then
    F:=GF(q^2);
    if type="SU" then
      return SSClassesSU(n,F);
    else
      return SSClassesGU(n,F);
    fi;
  fi;
  F:=GF(q);
  if type="Sp" then
    return SSClassesSp(n,F);
  fi;
  if IsOddInt(q) then
    if type="GO+" or type="O+" then
      return SSClassesO(n,F);
    fi;
    if type="GO-" or type="O-" then
      return SSClassesO(n,F:Minus:=true);
    fi;
    if type="GO" or type="O" then
      return SSClassesO(n,F);
    fi;
    if type="SO+" then
      return SSClassesO(n,F:Special:=true);
    fi;
    if type="SO-" then
      return SSClassesO(n,F:Minus:=true,Special:=true);
    fi;
    if type="SO" then
      return SSClassesO(n,F:Special:=true);
    fi;
    if type="Omega+" then
      return SSClassesO(n,F:Omega:=true);
    fi;
    if type="Omega-" then
      return SSClassesO(n,F:Minus:=true,Omega:=true);
    fi;
    if type="Omega" then
      return SSClassesO(n,F:Omega:=true);
    fi;
  else
      if not IsEvenInt(n) and IsEvenInt(q) then
      Error("Odd degree and even characteristic case not considered");
    fi;
    if type in ["GO+","O+","SO+"] then
      return SSClassesO(n,F);
    fi;
    if type in ["GO-","O-","SO-"] then
      return SSClassesO(n,F:Minus:=true);
    fi;
    if type="Omega+" then
      return SSClassesO(n,F:Omega:=true);
    fi;
    if type="Omega-" then
      return SSClassesO(n,F:Minus:=true,Omega:=true);
    fi;
  fi;
end;

SemisimpleClasses:=function(type,n,F) # there was an @!!! TODO
#  -> ,]  Semisimple conjugacy classes of the classical group of supplied type
#  , rank and field
return SemisimpleClasses(type,n,Size(F)); # there was an @!!! TODO
end;


