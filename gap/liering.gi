#####################################################################################
#
#  liering.gi                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 



# A Lie ring element is represented as a list [ index, cft, index, cft, ... ]


############################################################################
##
#M  ObjByExtRep( <fam>, <list> )
#M  ExtRepOfObj( <obj> )
##
InstallMethod( ObjByExtRep,
   "for family of LR elements, and list",
   true, [ IsLRElementFamily, IsList ], 0,
   function( fam, list )

    return Objectify( fam!.packedLRElementDefaultType,
                    [ Immutable(list) ] );
end );

InstallMethod( ExtRepOfObj,
   "for an LR element",
   true, [ IsLRElement ], 0,
   function( obj )

   return obj![1];

end );

###########################################################################
##
#M  PrintObj( <m> ) . . . . . . . . . . . . . . . . for an LR element
##
InstallMethod( PrintObj,
        "for LR element",
        true, [IsLRElement], 0,
        function( x )

    local   lst, n, i;

    # This function prints an element of a Lie ring.

    lst:= x![1];
    n:= Length( lst );
    if n = 0 then Print("0"); fi;
    for i in [1,3..n-1] do
        if lst[i+1] = -1 then
           Print("-");
        elif lst[i+1]<>1 then
           if i<>1 then Print("+"); fi;
           Print(lst[i+1],"*");
        elif i <> 1 then
           Print("+");
        fi;
        Print("v_",lst[i]);
    od;

end );

#############################################################################
##
#M  ZeroOp( <m> ) . . . . . . . . . . . . . . .  for a LR element
#M  \<( <m1>, <m2> ) . . . . . . . . . . . . . . for two LR elements
#M  \=( <m1>, <m2> ) . . . . . . . . . . . . . . for two LR elements
#M  \+( <m1>, <m2> ) . . . . . . . . . . . . . . for two LR elements
#M  \-( <m> )     . . . . . . . . . . . . . . for a LR element
#M  \in( <U>, <u> )  . . . . . . . . . . . . . . for LR, and element
##

InstallMethod( ZeroOp,
        "for LR element",
        true, [ IsLRElement ], 0,
        function( x )

    return ObjByExtRep( FamilyObj( x ), [ ] );

end );


InstallMethod( \<,
                "for two LR elements",
        IsIdenticalObj, [ IsLRElement ,IsLRElement  ], 0,
        function( x, y )
    return x![1]< y![1];
end );

InstallMethod( \=,
                "for two LR elements",
        IsIdenticalObj, [ IsLRElement ,IsLRElement  ], 0,
        function( x, y )
    return x![1] = y![1];
end );


InstallMethod( \+,
        "for two LR elements",
        IsIdenticalObj, [ IsLRElement ,IsLRElement ], 0,
        function( x, y )

    local   tor, sum, i;

    tor:= FamilyObj( x )!.torsion;

    sum:= ZIPPED_SUM_LISTS( x![1], y![1], 0, [ \<, \+ ] );
    for i in [2,4..Length(sum)] do
        if tor[ sum[i-1] ] <> 0 then
           sum[i]:= sum[i] mod tor[sum[i-1]];
           if sum[i] = 0 then 
              Unbind( sum[i-1] );
              Unbind( sum[i] );
           fi; 
        fi;
    od;
    sum:= Filtered( sum, x -> IsBound(x) );
    return ObjByExtRep( FamilyObj(x), sum );
    
end );


InstallMethod( AdditiveInverseSameMutability,
        "for LR element",
        true, [ IsLRElement  ], 0,
        function( x )

    local   ex,  i;

    ex:= ShallowCopy(x![1]);
    for i in [2,4..Length(ex)] do
        ex[i]:= -ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end );

InstallMethod( AdditiveInverseMutable,
        "for LR element",
        true, [ IsLRElement  ], 0,
        function( x )

    local   ex,  i;

    ex:= ShallowCopy(x![1]);
    for i in [2,4..Length(ex)] do
        ex[i]:= -ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end );

#############################################################################
##
#M  \*( <scal>, <m> ) . . . . . . . . .for a scalar and a LR element
#M  \*( <m>, <scal> ) . . . . . . . . .for a scalar and a LR element
##
InstallMethod( \*,
        "for scalar and LR element",
        true, [ IS_INT, IsLRElement ], 0,
        function( scal, x )

    local   ex,  i, tor;
    
    if IsZero( scal ) then return Zero(x); fi;
    ex:= ShallowCopy( x![1] );
    tor:= FamilyObj(x)!.torsion;
    for i in [2,4..Length(ex)] do
        ex[i]:= scal*ex[i];
        if tor[ ex[i-1] ] <> 0 then
           ex[i]:= ex[i] mod tor[ ex[i-1] ];
           if ex[i] = 0 then
              Unbind( ex[i-1] );
              Unbind( ex[i] );
           fi;
        fi;
    od;
    ex:= Filtered( ex, x -> IsBound( x ) );
    return ObjByExtRep( FamilyObj(x), ex );
end);

InstallMethod( \*,
        "for LR element and scalar",
        true, [ IsLRElement, IsScalar ], 0,
        function( x, scal )

    local   ex,  i, tor;
    
    if IsZero( scal ) then return Zero(x); fi;
    ex:= ShallowCopy( x![1] );
    tor:= FamilyObj(x)!.torsion;
    for i in [2,4..Length(ex)] do
        ex[i]:= scal*ex[i];
        if tor[ ex[i-1] ] <> 0 then
           ex[i]:= ex[i] mod tor[ ex[i-1] ];
           if ex[i] = 0 then
              Unbind( ex[i-1] );
              Unbind( ex[i] );
           fi;
        fi;
    od;
    ex:= Filtered( ex, x -> IsBound( x ) );
    return ObjByExtRep( FamilyObj(x), ex );

end);

InstallMethod( \in,
        "for LR element and Lie Ring",
        true, [ IsObject, IsLieRing ], 0,
        function( x, L )

    local B, cc;

    if not IsLRElement(x) then return false; fi;

    if IsStandardBasisOfLieRing( Basis(L) ) then
       return IsIdenticalObj( ElementsFamily( FamilyObj(L) ), FamilyObj(x) );
    else
       B:= Basis(L);
       cc:= SolutionIntMat( B!.mat, Coefficients( B!.ambient, x ) );
       if cc <> fail then return true; else return false; fi;
    fi;

end );

InstallMethod( \=,
        "for two Lie Rings",
        true, [ IsLieRing, IsLieRing ], 0,
        function( K, L )

      
     if not ForAll( GeneratorsOfAlgebra(K), x -> x in L ) then
        return false;
     else
        return ForAll( GeneratorsOfAlgebra(L), x -> x in K );
     fi;

end );


InstallMethod( PrintObj,
        "for a Lie ring",
        true, [IsLieRing], 0,
        function( L )
   Print("<Lie ring with ",Length(GeneratorsOfAlgebra(L))," generators>");
end );

InstallMethod( ViewObj,
        "for a Lie ring",
        true, [IsLieRing], 0,
        function( L )
   Print("<Lie ring with ",Length(GeneratorsOfAlgebra(L))," generators>");
end );

#############################################################################
##
#M  \*( <x>, <y> ) . . . . . . . . . . . . . . for two LR elements
##
##
InstallMethod( \*,
        "for two Lie Ring elements",
        IsIdenticalObj, [ IsLRElement, IsLRElement ], 0,
        function( x, y )
    
    local   ex,  ey,  i, j, k, tor, T, res, cc, cf, prod;
   
    ex:= ExtRepOfObj(x);
    ey:= ExtRepOfObj(y);

    tor:= FamilyObj(x)!.torsion;
    T:= FamilyObj( x )!.multTab;
    res:= [ ];  # list with holes, i-th position has cft of ith basis element in result.
    for i in [1,3..Length(ex)-1] do
        for j in [1,3..Length(ey)-1] do
            cc:= T[ex[i]][ey[j]];
            cf:= ex[i+1]*ey[j+1];
            for k in [1..Length(cc[1])] do
                if not IsBound( res[cc[1][k]] ) then 
                   res[cc[1][k]]:= cc[2][k]*cf;
                else
                   res[cc[1][k]]:= res[cc[1][k]] + cc[2][k]*cf;
                fi;
            od;
        od;
    od;        

    prod:= [ ];
    for k in [1..Length(tor)] do
        if IsBound(res[k])  then
           cf:=res[k];
           if tor[k] <> 0 then
              cf:= cf mod tor[k];
           fi;
           if cf <> 0 then
              Add( prod, k ); Add( prod, cf );
           fi;
        fi;
    od;

    return ObjByExtRep( FamilyObj(x), prod );

end);

InstallMethod( ViewObj,
        "for a Lie ring",
        true, [IsLieRing], 100,
        function( L )
   Print("<Lie ring with ",Length(GeneratorsOfLeftOperatorRing(L))," generators>");
end );



#########################################################################
##
#M  LieRingByStructureConstants( <tors>, <T> )
##
InstallMethod( LieRingByStructureConstants,
        "for structure constants table, and torsion list",
        true, [ IsList, IsList ], 0,
        function( tors, T )

    local fam, bas, L, B;

    fam:= NewFamily( "LREltFam", IsLRElement );
    fam!.packedLRElementDefaultType:= NewType( fam, IsPackedElementDefaultRep );
    fam!.torsion:= tors;
    fam!.multTab:= T;

    bas:= List( [1..Length(tors)], x -> ObjByExtRep( fam, [ x, 1 ] ) );

    L:= Objectify( NewType( CollectionsFamily( FamilyObj( bas[1] ) ),
                                IsLieRing
                            and IsAttributeStoringRep ),
                   rec() );

    B:= Objectify( NewType( FamilyObj( L ),
                      IsFiniteBasisDefault and
                      IsBasisOfLieRing and
                      IsAttributeStoringRep ),
                      rec() );

    SetLeftActingDomain( L, Integers );
    SetGeneratorsOfLeftOperatorRing( L, bas );
    SetGeneratorsOfAdditiveGroup( L, bas );

    SetUnderlyingLeftModule( B, L );  
    SetBasisVectors( B, bas );
    SetTorsion( B, tors );
    SetStructureConstantsTable( B, T );
    SetIsStandardBasisOfLieRing( B, true );

    SetBasis( L, B );

    SetParent( L, L );

    return L;

end );

InstallAccessToGenerators( IsLieRing,
                           "structure constants Lie ring",
                           Basis );


InstallMethod( Coefficients,
    "for basis of a Lie ring, and Lie ring element",
    true, [ IsBasisOfLieRing,
            IsLRElement ], 0,
    function( B, v )

      local cf, cc, k, heads, tb, cfs, y, ey, pos, a, b, r, t;

      if IsStandardBasisOfLieRing(B) then
         cf:= 0*FamilyObj( v )!.torsion;
         cc:= v![1];
         for k in [1,3..Length(cc)-1] do
             cf[cc[k]]:= cc[k+1];
         od;
         return cf;
      else

         cc:= SolutionIntMat( B!.mat, Coefficients( B!.ambient, v ) );
         cc:= cc{[1..Length(B)]};
         t:= Torsion( B );
         for k in [1..Length(t)] do
             if t[k] <> 0 then cc[k]:= cc[k] mod t[k]; fi;
         od;        
         return cc;
      fi;

end );

LRPrivateFunctions.sub_lie_ring:= function( arg )


      local B, n, bas, heads, foundbasis, newelms, x, c, cf, i, pos, a, b, 
            r, q, eqns, row, A, S, tors, Q, Qi, nb, K, BK, L, vv, is_bas, 
            start, mat, t, v;   

      L:= arg[1];
      vv:= arg[2];
      if Length(arg)=3 then
         is_bas:= true;
      else
         is_bas:= false;
      fi;

      if Length(vv)=0 then vv:= [ Zero(L) ]; fi;

      B:= Basis( Parent(L) );
      n:= Length( BasisVectors( B ) );
      bas:= TriangulizedIntegerMat( List( vv, x -> Coefficients( B, x ) ) );
      bas:= Filtered( bas, x -> x <> 0*x );

      if bas = [ ] then

         K:= Objectify( NewType( FamilyObj( L ),
                                  IsLieRing
                               and IsAttributeStoringRep ),
                      rec() );

         BK:= Objectify( NewType( FamilyObj( K ),
                         IsFiniteBasisDefault and
                         IsBasisOfLieRing and
                         IsAttributeStoringRep ),
                         rec() );

         # BK has a record component with useful information:
         #
         #  in this case it is empty

         BK!.mat:= [ ];
         BK!.ambient:= B;

         SetLeftActingDomain( K, Integers );
         SetGeneratorsOfLeftOperatorRing( K, [ ] );

         SetUnderlyingLeftModule( BK, K );  
         SetBasisVectors( BK, [ ] );
         SetTorsion( BK, [ ] );
         SetIsStandardBasisOfLieRing( BK, false );

         SetBasis( K, BK );
  
         SetParent( K, Parent(L) );

         return K;

      fi;
         

      heads:= List( bas, PositionNonZero );

      if not is_bas then

         foundbasis:= false;
         while not foundbasis do
         
            newelms:= [ ];
            for x in vv do
                for c in bas do
                    cf:= Coefficients( B, x*LinearCombination(B,c) );
                 
                    for i in [1..Length(heads)] do
                        pos:= heads[i];
                        a:= cf[ pos ]; b:= bas[i][pos];
                        r:= a mod b;
                        q:= (a-r)/b;
                        cf:= cf - q*bas[i];
                    od;
                    if cf <> 0*cf then
                       Add( newelms, cf );
                    fi;
                od;
            od;
            if newelms = [ ] then
               foundbasis:= true;
            else
               Append( bas, newelms );
               bas:= TriangulizedIntegerMat( bas );
               bas:= Filtered( bas, x -> x <> 0*x );
               heads:= List( bas, PositionNonZero );
            fi;
         od;
      fi;

      # in order to get the normal basis with have to find
      # the linear relations among the basis elements....

      eqns:= ShallowCopy( bas );
      for i in [1..n] do
          row:= List( [1..n], x -> 0 );
          row[ i ]:= Torsion(B)[i];
          Add( eqns, row );
      od;
      A:= NullspaceIntMat( eqns );
      A:= List( A, x -> x{[1..Length(bas)]} );
      A:= Filtered( A, x -> x <> 0*x );

      if Length(A) > 0 then
         S:= SmithNormalFormIntegerMatTransforms( A );   
         start:= 1;
         while start <= Length( S.normal ) and S.normal[start][start] = 1 do
             start:= start+1;
         od;

         tors:= List( [start..Length(S.normal)], x -> S.normal[x][x] );
         for i in [Length(S.normal)+1..Length(bas)] do Add( tors, 0 ); od;
         Q:= S.coltrans;
         Qi:= Q^-1;

         nb:= List( Qi{[start..Length(Qi)]}, x -> LinearCombination( bas, x ) );
         nb:= List( nb, x -> LinearCombination( B, x ) );
      else
         tors:= List( bas, x -> 0 );
         nb:= bas;
         nb:= List( nb, x -> LinearCombination( B, x ) );
      fi;


      K:= Objectify( NewType( FamilyObj( L ),
                                IsLieRing
                            and IsAttributeStoringRep ),
                   rec() );

      BK:= Objectify( NewType( FamilyObj( K ),
                      IsFiniteBasisDefault and
                      IsBasisOfLieRing and
                      IsAttributeStoringRep ),
                      rec() );

      # BK has a record component with useful information:
      #
      #  .mat is the matrix of the basis vectors with respect to the
      #   "ambient" basis, concatenated with some rows that record the
      #   torsion of the "ambient" basis elements.
      # .ambient is the basis of the "ambient" Lie ring.
 
      mat:= List( nb, x -> Coefficients( B, x ) );
      for i in [1..Length(Torsion(B))] do
          t:= Torsion(B)[i];
          if t <> 0 then
             v:= List( B, x -> 0 );
             v[i]:= t;
             Add( mat, v );
          fi;
      od;

      BK!.mat:= mat;
      BK!.ambient:= B;

      SetLeftActingDomain( K, Integers );
      SetGeneratorsOfLeftOperatorRing( K, nb );

      SetUnderlyingLeftModule( BK, K );  
      SetBasisVectors( BK, nb );
      SetTorsion( BK, tors );
      SetIsStandardBasisOfLieRing( BK, false );

      SetBasis( K, BK );

      SetParent( K, Parent(L) );

      return K;

end;


InstallMethod( SubLieRing,
    "for Lie ring and list of its elements",
    true, [ IsLieRing,
            IsList ], 0,
    function( L, vv )

    return LRPrivateFunctions.sub_lie_ring( L, vv );

end );

InstallOtherMethod( SubLieRing,
    "for Lie ring and list of its elements and string",
    true, [ IsLieRing,
            IsLRElementCollection, IsString ], 0,
    function( L, vv, str )

      if str <> "basis" then
         Error("The third argument has to be the string \"basis\".");
      fi;

      return LRPrivateFunctions.sub_lie_ring( L, vv, str );

end );

LRPrivateFunctions.ideal_lie_ring:= function( arg )


      local B, n, bas, heads, foundbasis, newelms, x, c, cf, i, pos, a, b, 
            r, q, eqns, row, A, S, tors, Q, Qi, nb, K, BK, L, vv, is_bas, 
            start, ss, mat, t, v;   
   
      L:= arg[1];
      vv:= arg[2];
      if Length(arg)=3 then
         is_bas:= true;
      else
         is_bas:= false;
      fi;

      if Length(vv)=0 then vv:= [ Zero(L) ]; fi;

      B:= Basis( Parent(L) );
      n:= Length( BasisVectors( B ) );


      bas:= TriangulizedIntegerMat( List( vv, x -> Coefficients( B, x ) ) );
      bas:= Filtered( bas, x -> x <> 0*x );

      if bas = [ ] then

         K:= Objectify( NewType( FamilyObj( L ),
                                  IsLieRing
                               and IsAttributeStoringRep ),
                      rec() );

         BK:= Objectify( NewType( FamilyObj( K ),
                         IsFiniteBasisDefault and
                         IsBasisOfLieRing and
                         IsAttributeStoringRep ),
                         rec() );

         # BK has three record components with useful information:
         #
         #  in this case all are empty

         BK!.mat:= [ ];
         BK!.ambient:= [ ];

         SetLeftActingDomain( K, Integers );
         SetGeneratorsOfLeftOperatorRing( K, [ ] );
	 SetGeneratorsOfIdeal( K, vv );

         SetUnderlyingLeftModule( BK, K );  
         SetBasisVectors( BK, [ ] );
         SetTorsion( BK, [ ] );
         SetIsStandardBasisOfLieRing( BK, false );

         SetBasis( K, BK );
  
         SetParent( K, Parent(L) );

         return K;

      fi;
         

      heads:= List( bas, PositionNonZero );

      if not is_bas then

         foundbasis:= false;
         while not foundbasis do
         
            newelms:= [ ];
            for x in Basis(L) do
                for c in bas do
                    cf:= Coefficients( B, x*LinearCombination(B,c) );
                 
                    for i in [1..Length(heads)] do
                        pos:= heads[i];
                        a:= cf[ pos ]; b:= bas[i][pos];
                        r:= a mod b;
                        q:= (a-r)/b;
                        cf:= cf - q*bas[i];
                    od;
                    if cf <> 0*cf then
                       Add( newelms, cf );
                    fi;
                od;
            od;
            if newelms = [ ] then
               foundbasis:= true;
            else
               Append( bas, newelms );
               bas:= TriangulizedIntegerMat( bas );
               bas:= Filtered( bas, x -> x <> 0*x );
               heads:= List( bas, PositionNonZero );
            fi;
         od;
      fi;

      # in order to get the normal basis with have to write the find
      # the linear relations among the basis elements....

      eqns:= ShallowCopy( bas );
      for i in [1..n] do
          row:= List( [1..n], x -> 0 );
          row[ i ]:= Torsion(B)[i];
          Add( eqns, row );
      od;
      A:= NullspaceIntMat( eqns );
      A:= List( A, x -> x{[1..Length(bas)]} );
      A:= Filtered( A, x -> x <> 0*x );

      if A = [ ] then
         Q:= IdentityMat( Length(bas) );
         Qi:= Q;
         S:= [ ];
      else
         ss:= SmithNormalFormIntegerMatTransforms( A );   
         S:= ss.normal;
         Q:= ss.coltrans;
         Qi:= Q^-1;
      fi;

      start:= 1;
      while start <= Length( S ) and S[start][start] = 1 do
          start:= start+1;
      od;

      tors:= List( [start..Length(S)], x -> S[x][x] );
      for i in [Length(S)+1..Length(bas)] do Add( tors, 0 ); od;

      nb:= List( Qi{[start..Length(Qi)]}, x -> LinearCombination( bas, x ) );
      nb:= List( nb, x -> LinearCombination( B, x ) );

      K:= Objectify( NewType( FamilyObj( L ),
                                IsLieRing
                            and IsAttributeStoringRep ),
                   rec() );

      BK:= Objectify( NewType( FamilyObj( K ),
                      IsFiniteBasisDefault and
                      IsBasisOfLieRing and
                      IsAttributeStoringRep ),
                      rec() );

      # BK has a record component with useful information:
      #
      #  .mat is the matrix of the basis vectors with respect to the
      #   "ambient" basis, concatenated with some rows that record the
      #   torsion of the "ambient" basis elements.
      # .ambient is the basis of the "ambient" Lie ring.
 
      mat:= List( nb, x -> Coefficients( B, x ) );
      for i in [1..Length(Torsion(B))] do
          t:= Torsion(B)[i];
          if t <> 0 then
             v:= List( B, x -> 0 );
             v[i]:= t;
             Add( mat, v );
          fi;
      od;

      BK!.mat:= mat;
      BK!.ambient:= B;

      SetLeftActingDomain( K, Integers );
      SetGeneratorsOfLeftOperatorRing( K, nb );
      SetGeneratorsOfIdeal( K, vv );
      SetUnderlyingLeftModule( BK, K );  
      SetBasisVectors( BK, nb );
      SetTorsion( BK, tors );
      SetIsStandardBasisOfLieRing( BK, false );

      SetBasis( K, BK );

      SetParent( K, Parent(L) );

      return K;

end;


InstallMethod( LieRingIdeal,
    "for Lie ring and list of its elements",
    true, [ IsLieRing,
            IsList ], 0,
    function( L, vv )

    return LRPrivateFunctions.ideal_lie_ring( L, vv );

end );


InstallOtherMethod( LieRingIdeal,
    "for Lie ring and list of its elements and string",
    true, [ IsLieRing,
            IsLRElementCollection, IsString ], 0,
    function( L, vv, str )

      if str <> "basis" then
         Error("The third argument has to be the string \"basis\".");
      fi;

      return LRPrivateFunctions.ideal_lie_ring( L, vv, str );

end );

InstallOtherMethod( NaturalHomomorphismByIdeal,
    "for two Lie rings",
    IsIdenticalObj,
    [ IsLieRing, IsLieRing ],
    function( K, I )

       local vv, S, start, Q, Qi, tors, i, j, k, M, bas, cc, entry, 
             imgs, ss, f, mat, e, T;

       vv:= BasisVectors( Basis(I) );

       mat:= [ ];
       tors:= Torsion( Basis(K) );
       for i in [1..Length(tors)] do
           if tors[i] <> 0 then
              e:= List( tors, x -> 0 );
              e[i]:= tors[i];
              Add( mat, e );
           fi;
       od;

       Append( mat, List( vv, x -> Coefficients( Basis(K), x ) ) );

       ss:= SmithNormalFormIntegerMatTransforms( mat );

       S:= ss.normal;
       S:= Filtered( S, x -> x <> 0*x );

       start:= 1;
       while start <= Length(S) and S[start][start] = 1 do
             start:= start+1;
       od;

       Q:= ss.coltrans;
       Qi:= Q^-1;

       tors:= List( [1..Length(S)], x -> S[x][x] );
       for i in [Length(S)+1..Length(Q)] do
           Add( tors, 0 );
       od;

       bas:= List( Qi{[start..Length(Qi)]}, x -> 
                               LinearCombination( Basis(K), x ) );

       T:= EmptySCTable( Length(bas), 0, "antisymmetric" );
       for i in [1..Length(bas)] do
           for j in [i+1..Length(bas)] do

               cc:= Coefficients( Basis(K), bas[i]*bas[j])*Q;
               for k in [1..Length(tors)] do
                   if tors[k] <> 0 then
                      cc[k]:= cc[k] mod tors[k];
                   fi;
               od;
               entry:= [ ];
               for k in [start..Length(cc)] do
                   if cc[k] <> 0 then
                      Add( entry, cc[k] );
                      Add( entry, k-start+1 );
                   fi;
               od;
               SetEntrySCTable( T, i, j, entry );
           od;
       od;

       M:= LieRingByStructureConstants( tors{[start..Length(tors)]}, T );

       imgs:= [ ];
       for i in [1..Length(Basis(K))] do
           cc:= Q[i];
           for k in [1..Length(tors)] do
               if tors[k] <> 0 then
                  cc[k]:= cc[k] mod tors[k];
               fi;
           od;
           Add( imgs, LinearCombination( Basis(M), cc{[start..Length(cc)]} ) );
       od;

    # a part from vspchom.gi, to get around the requirement of free left module...

    f:= Objectify( TypeOfDefaultGeneralMapping( K, M,
                             IsSPGeneralMapping
                         and IsLeftModuleGeneralMapping
                         and IsLinearGeneralMappingByImagesDefaultRep ),
                     rec() );

    SetMappingGeneratorsImages(f,[BasisVectors(Basis(K)),imgs]);

    SetIsSingleValued( f, true );
    SetIsTotal( f, true );


#       f:= LeftModuleHomomorphismByImagesNC( K, M, BasisVectors(Basis(K)), 
#                         imgs );

       f!.basisimage:= Basis( M );
       f!.preimagesbasisimage:= bas;

       f!.basispreimage:= Basis(K);
       f!.imagesbasispreimage:= imgs;

       return f;

end );




InstallMethod( LieLowerCentralSeries,
    "for a Lie ring",
    true, [ IsLieRing ], 0,
    function( L )

      local lc, b, done, a, x, y, S;

      lc:= [ L ];
      b:= BasisVectors( Basis(L) );
      done:= false;
      while not done do
            a:= [ ];
            for x in BasisVectors( Basis(L) ) do
                for y in b do
                    Add( a, x*y );
                od;
            od;
            S:= SubLieRing( L, a );

            if S = lc[ Length(lc) ] then
               done:= true;
            elif GeneratorsOfAlgebra(S) = [ ] then
               done:= true;
               Add( lc, S );
            else
               Add( lc, S );
            fi;
            b:= BasisVectors( Basis(S) );
      od;
      return lc;

end );


InstallMethod( LieCentre,
    "for a Lie ring",
    true, [ IsLieRing ], 0,
    function( L )

    local n, T, d, eqns, i, j, k, c, eq, sol, bas;

    n:= Length( Basis(L) );
    T:= StructureConstantsTable( Basis(L) );
    d:= Torsion( Basis(L) );

    eqns:= NullMat( n+n^2, n^2 );
    for i in [1..n] do
        for j in [1..n] do
            c:= T[i][j];
            for k in [1..Length(c[1])] do
                eqns[j][(i-1)*n+c[1][k]]:= c[2][k];
            od;
            eqns[n+(i-1)*n+j][(i-1)*n+j]:= d[j];
        od;
    od;

    sol:= NullspaceIntMat( eqns );

    bas:= List( sol, x -> LinearCombination( Basis(L), x{[1..n]} ) );

    return SubLieRing( L, bas, "basis" );


end );

InstallMethod( TensorWithField,
    "for a Lie ring and a field",
    true, [ IsLieRing, IsField ], 0,
    function( L, F )

    local p, inds, k, l, i, j, r, ckl, cf, T, dim, t;

    p:= Characteristic(F);
    inds:= [ ];  # some basis elements reduce to zero,
                 # if bas elt i goes to zero we put a zero on inds[i],
                 # otherwise we put the index of the new bas elt in the Lie algebra

    k:= 1;
    t:= Torsion( Basis(L) );
    for i in [1..Length(t)] do
        if (t[i]>0 and p=0) or (p>0 and t[i] mod p <> 0) then
           # goes to zero...
           inds[i]:= 0;
        else
           inds[i]:= k; k:= k+1;
        fi;
    od;

    dim:= k-1;
    T:= EmptySCTable( dim, Zero( F ), "antisymmetric" );
    for i in [1..Length(t)] do
        if inds[i] <> 0 then
           k:= inds[i];
           for j in [i+1..Length(t)] do
               if inds[j] <> 0 then
                  l:= inds[j];
                  ckl:= [ ];
                  cf:= Coefficients( Basis(L), Basis(L)[i]*Basis(L)[j] );
                  for r in [1..Length(cf)] do
                      if cf[r] <> 0 and inds[r] <> 0 then
                         Append( ckl, [ cf[r]*One(F), inds[r] ] );
                      fi;
                  od;
                  SetEntrySCTable( T, k, l, ckl );
               fi; 
           od;
        fi;
    od;

    return LieAlgebraByStructureConstants( F, T );

end );



InstallMethod( SmallNEngelLieRing,
    "for two integers",
    true, [ IsInt, IsInt ], 0,
    function( n, k )

    # i.e., n-engel, with k gens..
    local s, t, S, T, u;

    if not [n,k] in [ [4,3], [3,2], [3,3], [3,4], [4,2] ] then
       s:= "The ";
       Append( s, String(n) );
       Append( s, "-Engel Lie ring with " );
       Append( s, String(k) );
       Append( s, " generators is not contained in the database" );
       Error(s);
    fi;

    if [n,k] = [4,3] then
       t:= LRPrivateFunctions.n_engelLR.t43;
       S:= LRPrivateFunctions.n_engelLR.S43;
    elif [n,k] = [3,2] then
       t:= LRPrivateFunctions.n_engelLR.t32;
       S:= LRPrivateFunctions.n_engelLR.S32;
    elif [n,k] = [3,3] then
       t:= LRPrivateFunctions.n_engelLR.t33;
       S:= LRPrivateFunctions.n_engelLR.S33;
    elif [n,k] = [3,4] then
       t:= LRPrivateFunctions.n_engelLR.t34;
       S:= LRPrivateFunctions.n_engelLR.S34;
    elif [n,k] = [4,2] then
       t:= LRPrivateFunctions.n_engelLR.t42;
       S:= LRPrivateFunctions.n_engelLR.S42;
    fi;

    T:= EmptySCTable( Length(t), 0, "antisymmetric" );
    for u in S do SetEntrySCTable( T, u[1], u[2], u[3] ); od;

    return LieRingByStructureConstants( t, T );

end );




