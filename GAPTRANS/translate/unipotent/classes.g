#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Determinant, IsEven, IsOdd, IsPrimePower, IsSquare,
#  UnipotentClasses

#  Defines: UnipotentClasses

UnipotentClasses:=function(type,d,q) # there was an @!!! TODO
#  -> ,] ,[ ,] ,[ ,] ,[ ,] ,[ ,]  Unipotent conjugacy classes of the classical
#  group of supplied type and rank defined over field of given size
local L,R,Rewrite,T,ValidTypes,epsilon,forms,reps,type; # there was an @!!! TODO
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  ValidTypes:=["SL","GL","Sp","SU","GU","Omega+","Omega-","Omega","SO+","SO-", # there was an @!!! TODO
   "SO","GO+","GO-","GO","O+","O-","O"];
  if not type in ValidTypes then # there was an @!!! TODO
    Error(["Type must be one of ",ValidTypes]); # there was an @!!! TODO
  fi;
  if not d > 0 then
    Error("Degree must be positive");
  fi;
  if not IsPrimePower(q) then
    Error("Invalid field size");
  fi;
  if type="GO+" or (type="SO+" and IsEvenInt(q)) then
    type:="O+";
  fi;
  if type="GO-" or (type="SO-" and IsEvenInt(q)) then
    type:="O-";
  fi;
  if type="GO" then
    type:="O";
  fi;
  if type in ["O","SO","Omega"] then
      if not IsOddInt(d) then
      Error("Degree must be odd");
    fi;
    if IsEvenInt(q) then
      Error("Case not considered");
    fi;
  fi;
  if type in ["Omega+","SO+","O+"] then
    epsilon:=1;
      if not IsEvenInt(d) then
      Error("Degree must be even");
    fi;
  fi;
  if type in ["Omega-","SO-","O-"] then
      if not IsEvenInt(d) then
      Error("Degree must be even");
    fi;
    epsilon:=-1;
  fi;
  if type in ["Omega","SO","O"] then
      if not IsOddInt(d) then
      Error("Degree must be odd");
    fi;
    epsilon:=0;
  fi;
  if type="SL" then
    # =v= MULTIASSIGN =v=
    T:=SLUnipotentReps(d,q); # there was an @!!! TODO
    R:=T.val1;
    T:=T.val2;
    # =^= MULTIASSIGN =^=
  elif type="GL" then
    # =v= MULTIASSIGN =v=
    T:=GLUnipotentReps(d,q); # there was an @!!! TODO
    R:=T.val1;
    T:=T.val2;
    # =^= MULTIASSIGN =^=
  elif type="SU" then
    # =v= MULTIASSIGN =v=
    T:=SUUnipotentReps(d,q:Rewrite:=Rewrite); # there was an @!!! TODO
    R:=T.val1;
    reps:=T.val2;
    forms:=T.val3;
    T:=T.val4;
    # =^= MULTIASSIGN =^=
  elif type="GU" then
    # =v= MULTIASSIGN =v=
    T:=GUUnipotentReps(d,q:Rewrite:=Rewrite); # there was an @!!! TODO
    R:=T.val1;
    reps:=T.val2;
    forms:=T.val3;
    T:=T.val4;
    # =^= MULTIASSIGN =^=
  elif type="Sp" then
      if not IsEvenInt(d) then
      Error("Degree must be even");
    fi;
    if IsEvenInt(q) then
      # =v= MULTIASSIGN =v=
      T:=EvenUnipotentReps(type,d,q:Rewrite:=Rewrite); # there was an @!!! TODO
      R:=T.val1;
      reps:=T.val2;
      forms:=T.val3;
      T:=T.val4;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      L:=SpUnipotentReps(d,q:Rewrite:=Rewrite); # there was an @!!! TODO
      R:=L.val1;
      reps:=L.val2;
      forms:=L.val3;
      T:=L.val4;
      L:=L.val5;
      # =^= MULTIASSIGN =^=
    fi;
  elif type in ["Omega+","Omega","Omega-"] then
    if IsOddInt(q) then
      # =v= MULTIASSIGN =v=
      L:=OrthogonalUnipotentReps(d,q,epsilon:Special:=true,Perfect:=true, # there was an @!!! TODO
       Rewrite:=Rewrite);
      R:=L.val1;
      reps:=L.val2;
      forms:=L.val3;
      T:=L.val4;
      L:=L.val5;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      T:=EvenUnipotentReps(type,d,q:Rewrite:=Rewrite); # there was an @!!! TODO
      R:=T.val1;
      reps:=T.val2;
      forms:=T.val3;
      T:=T.val4;
      # =^= MULTIASSIGN =^=
    fi;
  elif type in ["SO+","SO-","SO"] then
    if IsOddInt(q) then
      # =v= MULTIASSIGN =v=
      L:=OrthogonalUnipotentReps(d,q,epsilon:Special:=true,Perfect:=false, # there was an @!!! TODO
       Rewrite:=Rewrite);
      R:=L.val1;
      reps:=L.val2;
      forms:=L.val3;
      T:=L.val4;
      L:=L.val5;
      # =^= MULTIASSIGN =^=
    else
      # =v= MULTIASSIGN =v=
      T:=EvenUnipotentReps(type,d,q:Rewrite:=Rewrite); # there was an @!!! TODO
      R:=T.val1;
      reps:=T.val2;
      forms:=T.val3;
      T:=T.val4;
      # =^= MULTIASSIGN =^=
    fi;
  elif type in ["O+","O-","O"] then
    if IsOddInt(q) then
      # =v= MULTIASSIGN =v=
      L:=OrthogonalUnipotentReps(d,q,epsilon:Special:=false,Perfect:=false, # there was an @!!! TODO
       Rewrite:=Rewrite);
      R:=L.val1;
      reps:=L.val2;
      forms:=L.val3;
      T:=L.val4;
      L:=L.val5;
      # =^= MULTIASSIGN =^=
      #   code for writing down all classes in fixed-ss.m assumes this!
      if type in ["O"] then
        Assert(1,ForAll(forms,f->IsSquare(DeterminantMat(f))));
      fi;
    else
      # =v= MULTIASSIGN =v=
      T:=EvenUnipotentReps(type,d,q:Rewrite:=Rewrite); # there was an @!!! TODO
      R:=T.val1;
      reps:=T.val2;
      forms:=T.val3;
      T:=T.val4;
      # =^= MULTIASSIGN =^=
    fi;
  fi;
  if type in ["GL","SL"] then
    return rec(val1:=R,
      val2:=T,
      val3:=_,
      val4:=_,
      val5:=_);
  elif type in ["Sp","O+","O-","O","SO+","SO-","SO","Omega+","Omega","Omega-"] 
     and IsOddInt(q) then
    return rec(val1:=R,
      val2:=L,
      val3:=T,
      val4:=reps,
      val5:=forms);
  else
    return rec(val1:=R,
      val2:=T,
      val3:=T,
      val4:=reps,
      val5:=forms);
  fi;
end;

UnipotentClasses:=function(type,d,F) # there was an @!!! TODO
#  -> ,] ,[ ,] ,[ ,] ,[ ,] ,[ ,]  Unipotent conjugacy classes of the classical
#  group of supplied type and rank defined over given field
local Rewrite;
  Rewrite:=ValueOption("Rewrite");
  if Rewrite=fail then
    Rewrite:=true;
  fi;
  return UnipotentClasses(type,d,Size(F)); # there was an @!!! TODO
end;


