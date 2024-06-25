#  File converted from Magma code -- requires editing and checking
#  Magma -> GAP converter, version 0.51, Jul/4/19 by AH

#  Global Variables used: Append, BaseRing, BlockMatrix, Characteristic,
#  CompanionMatrix, ConjPol, Degree, Determinant, DiagonalJoin, DiagonalMatrix,
#  Eltseq, Exclude, FrobeniusImage, GL, IdentityMatrix, InsertBlock,
#  IsConjugate, IsEven, IsOdd, IsSemisimple, IsSquare, JordanForm, Log, Matrix,
#  MatrixAlgebra, Multiplicity, Norm, Nrows, PolynomialRing, PrimitiveElement,
#  QuadraticSpace, SSIsConjugate, Star, Submatrix, SwitchMatrix, TransformForm,
#  Transpose, WittIndex, ZeroMatrix

#  Defines: InternalSemisimpleIsConjugate, SSIsConjugate, SwitchMatrix

DeclareGlobalFunction("SSIsConjugate@");

DeclareGlobalFunction("SwitchMatrix@");

#   X* := conjugate transpose of X
#   return Y s.t. B1=Y B2 Y*,
#   where Y* considered as matrix in GU(n,ext<GF(q)|f>) and not in
#  GL(n*deg(f),GF(q))
InstallGlobalFunction(SwitchMatrix@,
function(B1,B2,f)
local F,K,Y,a,d,h,i,j,k,m1,m2,n,s1,s2,suss;
  F:=BaseRing(B1);
  K:=ExtStructure(F,f:Optimize:=false);
  # Implicit generator Assg from previous line.
  a:=K.1;
  d:=Degree(K,F);
  n:=QuoInt(Length(B1),d);
  s1:=ZeroMatrix(K,n,n);
  s2:=ZeroMatrix(K,n,n);
  #  changed: for i,j in [1..n] do
  for i in [1..n] do
    for j in [1..n] do
      s1[i][j]:=Sum(List([1..d],k->a^(k-1)*B1[d*(i-1)+1][d*(j-1)+k]));
      s2[i][j]:=Sum(List([1..d],k->a^(k-1)*B2[d*(i-1)+1][d*(j-1)+k]));
    od;
  od;
  m1:=TransformForm(s1,"unitary":Restore:=false);
  m2:=TransformForm(s2,"unitary":Restore:=false);
  suss:=m1*m2^-1;
  Y:=ZeroMatrix(F,n*d,n*d);
  #  changed: for i,j in [1..n] do
  for i in [1..n] do
    for j in [1..n] do
      #  changed for h,k in [1..d] do
      for h in [1..d] do
        for k in [1..d] do
          Y[d*(i-1)+h][d*(j-1)+k]:=Eltseq((a^(h-1)*suss[i][j])*FORCEOne(K),F)[k]
           ;
        od;
      od;
    od;
  od;
  return Y;
end);

#   return z in G such that z^-1*x*z = y;
#   works only for x1,x2 semisimple
#   works for G = Sp, GU, SU, GO, SO, Omega
#   exclude orthogonal groups in odd dimension and even characteristic
InstallGlobalFunction(SSIsConjugate@,
function(G,x2,x1)
local 
   A1,A2,B,B1,B2,C,ConjPol,varE,F,H,H1,IsOmega,IsOmega2,M,N,Q,R,Set1,Set2,Star,
   T,varX,Y,Y1,Y2,varZ,_,a,a1,a2,b,b1,b2,bX,c1,c2,d,d1,d2,deg,det,e,f,
   forgetvar1,forgetvar3,i,j,j1,j2,k,l,m,m1,m2,n,ni,p,pos,q,r1,r2,sgn,special,
   special2,suss,t,type,type1,w,x,y;
  F:=BaseRing(G);
  n:=Length(x1);
  p:=Characteristic(F);
  M:=MatrixAlgebra(F,n);
  t:=PolynomialRing(F).1;
  # =v= MULTIASSIGN =v=
  Q:=DetermineForm@(G,x1);
  B:=Q.val1;
  type:=Q.val2;
  sgn:=Q.val3;
  special:=Q.val4;
  IsOmega:=Q.val5;
  Q:=Q.val6;
  # =^= MULTIASSIGN =^=
  if IsBound(Q) then
    # =v= MULTIASSIGN =v=
    IsOmega2:=IsElementOf@(G,x2,type,B,Q);
    special2:=IsOmega2.val1;
    IsOmega2:=IsOmega2.val2;
    # =^= MULTIASSIGN =^=
  else
    # =v= MULTIASSIGN =v=
    IsOmega2:=IsElementOf@(G,x2,type,B,[]);
    special2:=IsOmega2.val1;
    IsOmega2:=IsOmega2.val2;
    # =^= MULTIASSIGN =^=
  fi;
  if (special2<>special) or (IsOmega2<>IsOmega) then
    Error("Both elements do not lie in same input group");
  fi;
  # rewritten select statement
  if type="unitary" then
    e:=QuoInt(Degree(F),2);
  else
    e:=0;
  fi;
  #  conjugate transpose matrix
  Star:=function(M)
  local exp;
    exp:=e;
    return TransposedMat(FrobeniusImage(M,exp));
  end;

  #  conjugate polynomial
  ConjPol:=ConjugatePolynomial@(type="unitary");
  # =v= MULTIASSIGN =v=
  r1:=JordanForm(x1);
  a1:=r1.val1;
  b1:=r1.val2;
  r1:=r1.val3;
  # =^= MULTIASSIGN =^=
  # =v= MULTIASSIGN =v=
  r2:=JordanForm(x2);
  a2:=r2.val1;
  b2:=r2.val2;
  r2:=r2.val3;
  # =^= MULTIASSIGN =^=
  if a1<>a2 then
    return rec(val1:=false,
      val2:=_);
  fi;
  #   Little change in Jordan Form:
  #   now c1 = [<f_i,m_i>, i], with m_i = multiplicity of el. div. f_i
  #   need to put t+1 and t-1 at the end of the list
  Set1:=List( # {-list:
    r1,x->x);
  Set2:=List( # {-list:
    r2,x->x);
  c1:=List(Filtered(Set1,x->x[1]<>t-1 and x[1]<>t+1),x->[x[1],Multiplicity(r1,x)
   ]);
  c2:=List(Filtered(Set2,x->x[1]<>t-1 and x[1]<>t+1),x->[x[1],Multiplicity(r2,x)
   ]);
  for x in Set1 do
    if x[1]=t-1 or x[1]=t+1 then
      Add(c1,[x[1],Multiplicity(r1,x)]);
      Add(c2,[x[1],Multiplicity(r2,x)]);
    fi;
  od;
  varX:=ZeroMatrix(F,0,0);
  i:=1;
  while i <= Size(c1) do
    f:=c1[i][1];
    d:=c1[i][2];
    if f=ConjPol(f) then
      varX:=DirectSumMat(varX,DirectSumMat(List([1..d],j->CompanionMat(f))));
    else
      varX:=DirectSumMat(varX,DirectSumMat(List([1..d],j->CompanionMat(f))));
      varX:=DirectSumMat(varX,DirectSumMat(List([1..d],j->Star(CompanionMat(f))
       ^-1)));
      RemoveSet(c1,[ConjPol(f),d]); # actually Tildec1!!! TODO
    fi;
    i:=i+1;
  od;
  # =v= MULTIASSIGN =v=
  forgetvar3:=JordanForm(varX);
  forgetvar1:=forgetvar3.val1;
  bX:=forgetvar3.val2;
  forgetvar3:=forgetvar3.val3;
  # =^= MULTIASSIGN =^=
  d1:=bX^-1*b1;
  d2:=bX^-1*b2;
  if IsBound(Q) and IsEvenInt(p) then
    A1:=d1*Q*Star(d1);
    A2:=d2*Q*Star(d2);
  else
    A1:=d1*B*Star(d1);
    A2:=d2*B*Star(d2);
  fi;
  #   method: compute an easy form X, and compute d1, d2 s.t. d1 x1 d1^-1 = X =
  #  d2 x2 d2^-1.
  #   Thus X is isometry for A1,A2 defined above.
  #   Compute Y such that YA2Y* = A1.
  #   The conjugating element is d2^-1Y^-1d1.
  if type in 
     ["orthogonalplus","orthogonalminus","orthogonal","orthogonalcircle"] and 
     p<>2 then
    if DeterminantMat(x1*FORCEOne(M)-1)=0 and DeterminantMat(x1*FORCEOne(M)+1)
       =0 then
      k:=c1[Size(c1)][2];
      #   the last element in c1 is t-1 or t+1
      B1:=Submatrix(A1,n-k+1,n-k+1,k,k);
      B2:=Submatrix(A2,n-k+1,n-k+1,k,k);
      if not IsSquare(DeterminantMat(B1)*DeterminantMat(B2)) then
        return rec(val1:=false,
          val2:=_);
      fi;
    fi;
  fi;
  #   turn the matrices A1, A2 into upper triangular matrices in quadratic case
  if type in 
     ["orthogonalplus","orthogonalminus","orthogonal","orthogonalcircle"] and 
     p=2 then
    for i in [1..n] do
      for j in [i+1..n] do
        A1[i][j]:=A1[i][j]+A1[j][i];
        A2[i][j]:=A2[i][j]+A2[j][i];
        A1[j][i]:=0;
        A2[j][i]:=0;
      od;
    od;
  fi;
  #   create conjugating element in GO / Sp / GU
  Y:=ZeroMatrix(F,n,n);
  pos:=1;
  i:=1;
  while i <= Size(c1) do
    f:=c1[i][1];
    d:=c1[i][2];
    if f=ConjPol(f) and Degree(f)=1 then
      B1:=Submatrix(A1,pos,pos,d,d);
      B2:=Submatrix(A2,pos,pos,d,d);
      type1:=type;
      if type<>"unitary" and type<>"symplectic" then
        type1:=IndicateType@(B1);
      fi;
      m1:=TransformForm(B1,type1:Restore:=false);
      m2:=TransformForm(B2,type1:Restore:=false);
      InsertBlock(Y,m1*m2^-1,pos,pos); # actually TildeY!!! TODO
      pos:=pos+d;
    elif f<>ConjPol(f) then
      ni:=Degree(f)*d;
      if type<>"unitary" and type<>"symplectic" and p=2 then
        Y1:=Submatrix(A1,pos,pos+ni,ni,ni);
        Y2:=Submatrix(A2,pos,pos+ni,ni,ni);
      else
        Y1:=Submatrix(A1,pos,pos+ni,ni,ni);
        Y2:=Submatrix(A2,pos,pos+ni,ni,ni);
      fi;
      Y1:=Y1*Y2^-1;
      Y1:=DirectSumMat(Y1,IdentityMatrix(F,ni));
      InsertBlock(Y,Y1,pos,pos); # actually TildeY!!! TODO
      pos:=pos+2*ni;
    else
      ni:=Degree(f)*d;
      R:=CompanionMat(f);
      H:=GL(Degree(f),F);
      # =v= MULTIASSIGN =v=
      T:=IsConjugate(H,R*FORCEOne(H)^-1,Star(R)*FORCEOne(H));
      forgetvar1:=T.val1;
      T:=T.val2;
      # =^= MULTIASSIGN =^=
      if DeterminantMat(T+sgn*Star(T))=0 then
        T:=R*T+sgn*Star(R*T);
      else
        T:=T+sgn*Star(T);
      fi;
      T:=DirectSumMat(List([1..d],j->T));
      B1:=Submatrix(A1,pos,pos,ni,ni)*T^-1;
      B2:=Submatrix(A2,pos,pos,ni,ni)*T^-1;
      if type<>"unitary" and type<>"symplectic" and p=2 then
        B1:=B1+TransposedMat(Submatrix(A1,pos,pos,ni,ni))*T^-1;
        B2:=B2+TransposedMat(Submatrix(A2,pos,pos,ni,ni))*T^-1;
      fi;
      Y1:=SwitchMatrix@(B1,B2,f);
      InsertBlock(Y,Y1,pos,pos); # actually TildeY!!! TODO
      pos:=pos+ni;
    fi;
    i:=i+1;
  od;
  #   in the special case, if det Z ne 1, then need to be multiplied by Y
  #   such that x1 Y = Y x1 and det Y = det Z^-1
  varZ:=d2^-1*Y^-1*d1;
  if special or IsOmega then
    if DeterminantMat(varZ)<>1 then
      if type="unitary" then
        f:=c1[1][1];
        d:=c1[1][2];
        det:=DeterminantMat(varZ)^-1;
        deg:=Degree(f);
        Y:=IdentityMatrix(F,n);
        if f=ConjPol(f) and deg=1 then
          B1:=Submatrix(A1,1,1,d,d);
          if d=1 then
            y:=det*IdentityMatrix(F,1);
          else
            w:=PrimitiveElement(F);
            l:=QuoInt(Log(w,det),(p^e-1));
            y:=IdentityMatrix(F,d);
            y[1][1]:=w^(l*p^e);
            y[d][d]:=w^(-l);
            m:=TransformForm(B1,"unitary":Restore:=false);
            y:=m*y*m^-1;
          fi;
        elif f<>ConjPol(f) then
          B1:=Submatrix(A1,1,d*deg+1,d*deg,d*deg);
          C:=CompanionMat(f);
          varE:=ExtStructure(F,f:Optimize:=false);
          w:=PrimitiveElement(varE);
          C:=Sum(List([1..deg],i->C^(i-1)*Eltseq(w,F)[i]));
          l:=QuoInt(Log(DeterminantMat(C),det),(p^e-1));
          y:=IdentityMatrix(F,d*deg);
          InsertBlock(y,C^-l,1,1); # actually Tildey!!! TODO
          y:=DirectSumMat(y,Star(B1)*Star(y^-1)*Star(B1^-1));
        else
          C:=CompanionMat(f);
          H:=GL(deg,F);
          # =v= MULTIASSIGN =v=
          T:=IsConjugate(H,C*FORCEOne(H)^-1,Star(C)*FORCEOne(H));
          forgetvar1:=T.val1;
          T:=T.val2;
          # =^= MULTIASSIGN =^=
          if DeterminantMat(T+sgn*Star(T))=0 then
            T:=C*T+sgn*Star(C*T);
          else
            T:=T+sgn*Star(T);
          fi;
          T:=DirectSumMat(List([1..d],j->T));
          B1:=Submatrix(A1,1,1,d*deg,d*deg)*T^-1;
          varE:=ExtStructure(F,f:Optimize:=false);
          # Implicit generator Assg from previous line.
          a:=varE.1;
          #   H1 = matrix B1 over the smaller field
          H1:=ZeroMatrix(varE,d,d);
          #  changed: for j1,j2 in [1..d] do
          for j1 in [1..d] do
            for j2 in [1..d] do
              H1[j1][j2]:=Sum(List([1..deg],k->a^(k-1)*B1[deg*(j1-1)+1]
               [deg*(j2-1)+k]));
            od;
          od;
          m:=TransformForm(H1,"unitary":Restore:=false);
          w:=PrimitiveElement(varE);
          l:=Log(Norm(w^(p^(e*deg)-1),F),det);
          suss:=IdentityMatrix(varE,d);
          if d=1 then
            suss[1][1]:=w^(p^(e*deg)-1);
          else
            m:=TransformForm(H1,"unitary":Restore:=false);
            suss[1][1]:=w^(p^(e*deg));
            suss[d][d]:=w^-1;
            suss:=m*suss*m^-1;
          fi;
          suss:=suss^l;
          y:=BlockMatrix(d,d,Concatenation(List([1..d],
            j1->List([1..d],
              j2->Sum(List([1..deg],k->C^(k-1)*Eltseq(suss[j1][j2],F)[k]))))));
        fi;
        InsertBlock(Y,y,1,1); # actually TildeY!!! TODO
        Y:=d1^-1*Y*d1;
        varZ:=varZ*Y;
      else
        if DeterminantMat(x1*FORCEOne(M)-1)<>0 and DeterminantMat(x1*FORCEOne(M)
           +1)<>0 then
          return rec(val1:=false,
            val2:=_);
        else
          Y:=IdentityMatrix(F,n);
          d:=c1[Size(c1)][2];
          B1:=Submatrix(A1,n-d+1,n-d+1,d,d);
          if IsOddInt(d) then
            m:=TransformForm(B1,"orthogonal":Restore:=false);
            #   y:=IdentityMatrix(F,d);
            #   y[d div 2+1, d div 2+1]:=-1;
            #   element of determinant -1
            y:=GOElement(d,F);
            y:=m*y*m^-1;
          elif IsSquare((-1*FORCEOne(F))^(QuoInt(d,2))*DeterminantMat(B1)) then
            m:=TransformForm(B1,"orthogonalplus":Restore:=false);
            #   y:=IdentityMatrix(F,d);
            #   y[1,1]:=0; y[1,d]:=1; y[d,1]:=1; y[d,d]:=0;
            #   element of determinant -1
            y:=GOElement(d,F);
            y:=m*y*m^-1;
          else
            m:=TransformForm(B1,"orthogonalminus":Restore:=false);
            #   y:=IdentityMatrix(F,d);
            #   y[d div 2+1, d div 2+1]:=-1;
            #   element of determinant -1
            y:=GOElement(d,F:Minus:=true);
            y:=m*y*m^-1;
          fi;
          InsertBlock(Y,y,n-d+1,n-d+1); # actually TildeY!!! TODO
          #   YX=XY, detY = -1
          #   following should hold
          #   assert X*Y eq Y*X
          Y:=d1^-1*Y*d1;
          varZ:=varZ*Y;
        fi;
      fi;
    fi;
  fi;
  #   in the omega case, if SpinorNorm(Z) ne 0, then need to be multiplied by Y
  #   such that x1 Y = Y x1 and SpinorNorm(Y) ne 0
  if IsOmega then
    if SpinN@(varZ*FORCEOne(GL(n,F)),Q,p)<>0 then
      if IsEvenInt(p) then
        if DeterminantMat(x1*FORCEOne(M)+1)<>0 then
          return rec(val1:=false,
            val2:=_);
        else
          Y:=IdentityMatrix(F,n);
          d:=c1[Size(c1)][2];
          B1:=Submatrix(A1,n-d+1,n-d+1,d,d);
          w:=PrimitiveElement(F);
          if WittIndex(QuadraticSpace(B1))=QuoInt(d,2) then
            type1:="orthogonalplus";
          else
            type1:="orthogonalminus";
          fi;
          #   y in SO, y not in Omega
          if type1="orthogonalplus" then
            m:=TransformForm(B1,"orthogonalplus":Restore:=false);
            #   y:=IdentityMatrix(F,d);
            #   y[d div 2, d div 2]:=0; y[d div 2+1, d div 2+1]:=0;
            #   y[d div 2, d div 2+1]:=1; y[d div 2+1, d div 2]:=1;
            y:=SOElement(d,F);
          else
            m:=TransformForm(B1,"orthogonalminus":Restore:=false);
            #   y:=IdentityMatrix(F,d);
            #   y[d div 2+1, d div 2]:=1;
            y:=SOElement(d,F:Minus:=true);
          fi;
          y:=m*y*m^-1;
          InsertBlock(Y,y,n-d+1,n-d+1); # actually TildeY!!! TODO
          #   YX=XY, SpinorNorm(Y) = 1
          Y:=d1^-1*Y*d1;
          varZ:=varZ*Y;
        fi;
      else
        f:=c1[1][1];
        d:=c1[1][2];
        pos:=1;
        #   the case d*Degree(f)=1 is hard to manage, so better to avoid it
        if d=1 and f in [t+1,t-1] then
          f:=c1[2][1];
          d:=c1[2][2];
          pos:=2;
        fi;
        Y:=IdentityMatrix(F,n);
        if f=t+1 or f=t-1 then
          B1:=Submatrix(A1,pos,pos,d,d);
          if IsOddInt(d) then
            m:=TransformForm(B1,"orthogonal":Restore:=false);
            #   w:=PrimitiveElement(F);
            #   y:=IdentityMatrix(F,d);
            #   y[1,1]:=w;   y[d,d]:=w^-1;
            #   y in SO, y not in Omega
            y:=SOElement(d,F);
          elif IsSquare((-1*FORCEOne(F))^(QuoInt(d,2))*DeterminantMat(B1)) then
            m:=TransformForm(B1,"orthogonalplus":Restore:=false);
            w:=PrimitiveElement(F);
            y:=IdentityMatrix(F,d);
            #   y[1,1]:=w;   y[d,d]:=w^-1;
            #   y in SO, y not in Omega
            y:=SOElement(d,F);
          else
            m:=TransformForm(B1,"orthogonalminus":Restore:=false);
            y:=IdentityMatrix(F,d);
            #  generating element of SOMinus(2,q) subset SOMinus(d,q)
            w:=PrimitiveElement(F);
            varE:=ExtStructure(F,t^2-w:Optimize:=false);
            q:=Size(F);
            l:=PrimitiveElement(varE);
            T:=l+l^q;
            N:=l^(q+1);
            b:=(l-l^q)/l^(QuoInt((q+1),2));
            a1:=(T^2-2*N)/(2*N);
            a2:=T*b/(2*N);
            y[QuoInt(d,2)][QuoInt(d,2)]:=a1;
            y[QuoInt(d,2)][QuoInt(d,2)+1]:=a2;
            y[QuoInt(d,2)+1][QuoInt(d,2)]:=a2*N;
            y[QuoInt(d,2)+1][QuoInt(d,2)+1]:=a1;
            B2:=DiagonalMat(F,Concatenation(List([1..QuoInt(d,2)],i->1)
             ,List([1..QuoInt(d,2)],i->-1)));
            B2:=InsertBlock(B2,MatrixByEntries(F,2,2,[1,0,0,-l^(q+1)])
             ,QuoInt(d,2),QuoInt(d,2));
            m1:=TransformForm(B2,"orthogonalminus":Restore:=false);
            y:=m1^-1*y*m1;
          fi;
          y:=m*y*m^-1;
        elif f<>ConjPol(f) then
          B1:=Submatrix(A1,pos,d*Degree(f)+pos,d*Degree(f),d*Degree(f));
          varE:=ExtStructure(F,f:Optimize:=false);
          # Implicit generator Assg from previous line.
          a:=varE.1;
          y:=Sum(List([1..Degree(f)],i->CompanionMat(f)^(i-1)
           *Eltseq(PrimitiveElement(varE),F)[i]));
          y:=DirectSumMat(y,IdentityMatrix(F,Degree(f)*(d-1)));
          y:=DirectSumMat(y,Star(B1^-1*y^-1*B1));
        else
          C:=CompanionMat(f);
          H:=GL(Degree(f),F);
          # =v= MULTIASSIGN =v=
          T:=IsConjugate(H,C*FORCEOne(H)^-1,Star(C)*FORCEOne(H));
          forgetvar1:=T.val1;
          T:=T.val2;
          # =^= MULTIASSIGN =^=
          if DeterminantMat(T+sgn*Star(T))=0 then
            T:=C*T+sgn*Star(C*T);
          else
            T:=T+sgn*Star(T);
          fi;
          T:=DirectSumMat(List([1..d],j->T));
          B1:=Submatrix(A1,pos,pos,d*Degree(f),d*Degree(f))*T^-1;
          varE:=ExtStructure(F,f:Optimize:=false);
          # Implicit generator Assg from previous line.
          a:=varE.1;
          #   H1 = matrix B1 over the smaller field
          H1:=ZeroMatrix(varE,d,d);
          #  changed for j1,j2 in [1..d] do
          for j1 in [1..d] do
            for j2 in [1..d] do
              H1[j1][j2]:=Sum(List([1..Degree(f)],k->a^(k-1)*B1[Degree(f)*(j1-1)
               +1][Degree(f)*(j2-1)+k]));
            od;
          od;
          w:=PrimitiveElement(varE);
          suss:=IdentityMatrix(varE,d);
          if d=1 then
            suss[1][1]:=w^(Size(F)^(QuoInt(Degree(f),2))-1);
          else
            m:=TransformForm(H1,"unitary":Restore:=false);
            suss[1][1]:=w^(Size(F)^(QuoInt(Degree(f),2)));
            suss[d][d]:=w^-1;
            suss:=m*suss*m^-1;
          fi;
          y:=BlockMatrix(d,d,Concatenation(List([1..d],
            j1->List([1..d],
              j2->Sum(List([1..Degree(f)],k->C^(k-1)*Eltseq(suss[j1][j2],F)[k]))
           ))));
        fi;
        InsertBlock(Y,y,pos,pos); # actually TildeY!!! TODO
        Y:=d1^-1*Y*d1;
        varZ:=varZ*Y;
      fi;
    fi;
  fi;
  return rec(val1:=true,
    val2:=varZ*FORCEOne(GL(n,F)));
end);

InternalSemisimpleIsConjugate@:=function(G,g,h)
#  -> ,GrpMatElt  if semisimple g and h are conjugate in classical group G ,
#  return true and conjugating element , else false
if not IsSemisimple(g) and IsSemisimple(h) then
    Error("Both elements must be semisimple");
  fi;
  return SSIsConjugate@(G,g,h);
end;


