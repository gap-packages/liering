#####################################################################################
#
#  lazard.gi                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 


LRPrivateFunctions.make_treeBCH := function( b )

   local A, k, m, cf, B, l;

   # here b is the BCH "polynomial"; we encode it as a tree.
   # at the root there is [ x, y ] with cft 1/2

   A := rec( label := 1/2, isleaf := false );
   A.left := rec( label := 0, isleaf := true );
   A.right := rec( label := 0, isleaf := true );

   for k in [ 3, 5 .. Length( b ) - 1 ] do
      m := b[ k ];
      cf := b[ k + 1 ];
      l := Length( m ) - 2; B := A;

      while B.isleaf = false do

         if m[ l ] = 1 then
            B := B.left;
         else
            B := B.right;
         fi;

         l := l - 1;
      od;

      while l <> 0 do
         B.label := 0; B.isleaf := false;
         B.left := rec( label := 0, isleaf := true );
         B.right := rec( label := 0, isleaf := true );

         if m[ l ] = 1 then
            B := B.left;
         else 
            B := B.right;
         fi;

         l := l - 1;
       od;

       B.label := cf; B.isleaf := false;
       B.left := rec( label := 0, isleaf := true );
       B.right := rec( label := 0, isleaf := true );
   od;

   return A;

end;


LRPrivateFunctions.make_treeSUM := function( b )

   local A, k, m, cf, B, l;

   # here b is the SUM "polynomial"; we encode it as a tree.
   # at the root there is [ g, h ] with exp - 1/2

   A := rec( label := - 1/2, isleaf := false );
   A.left := rec( label := 0, isleaf := true );
   A.right := rec( label := 0, isleaf := true );

   for k in [ 5, 7 .. Length( b ) - 1 ] do
      m := b[ k ];
      cf := b[ k + 1 ];
      l := Length( m ) - 2; B := A;

      while B.isleaf = false do

         if m[ l ] = 1 then
            B := B.left;
         else
            B := B.right;
         fi;

         l := l - 1;
      od;

      while l <> 0 do
         B.label := 0; B.isleaf := false;
         B.left := rec( label := 0, isleaf := true );
         B.right := rec( label := 0, isleaf := true );

         if m[ l ] = 1 then
            B := B.left;
         else 
            B := B.right;
         fi;

         l := l - 1;
       od;

       B.label := cf; B.isleaf := false;
       B.left := rec( label := 0, isleaf := true );
       B.right := rec( label := 0, isleaf := true );
   od;

   return A;

end;

LRPrivateFunctions.make_treeBRACKET := function( b )

   local A, k, m, cf, B, l;

   # here b is the BRACKET "polynomial"; we encode it as a tree.
   # at the root there is [ g, h ] with exp 1

   A := rec( label := 1, isleaf := false );
   A.left := rec( label := 0, isleaf := true );
   A.right := rec( label := 0, isleaf := true );

   for k in [ 3, 5 .. Length( b ) - 1 ] do
      m := b[ k ];
      cf := b[ k + 1 ];
      l := Length( m ) - 2; B := A;

      while B.isleaf = false do

         if m[ l ] = 1 then
            B := B.left;
         else
            B := B.right;
         fi;

         l := l - 1;
      od;

      while l <> 0 do
         B.label := 0; B.isleaf := false;
         B.left := rec( label := 0, isleaf := true );
         B.right := rec( label := 0, isleaf := true );

         if m[ l ] = 1 then
            B := B.left;
         else 
            B := B.right;
         fi;

         l := l - 1;
      od;

      B.label := cf; B.isleaf := false;
      B.left := rec( label := 0, isleaf := true );
      B.right := rec( label := 0, isleaf := true );
   od;

   return A;

end;

LRPrivateFunctions.LAZARDTrec:= rec();

LRPrivateFunctions.InitialiseLAZARD:= function()

   LRPrivateFunctions.LAZARDTrec.G_BCH := LRPrivateFunctions.make_treeBCH( LRPrivateFunctions.BCH0 );
   LRPrivateFunctions.LAZARDTrec.G_SUM := LRPrivateFunctions.make_treeSUM( LRPrivateFunctions.SUM0 );
   LRPrivateFunctions.LAZARDTrec.G_BRACKET := LRPrivateFunctions.make_treeBRACKET( LRPrivateFunctions.BRACKET0 );

end;


LRPrivateFunctions.evalBCH := function( A, L, x, y )

   local a, k, val, coef, e, T, T0, i, vall, valr;
   
   # A is the tree corr to BCH, we evaluate the formula in x, y elements of the Lie ring L

   a := x + y;

   if IsField( LeftActingDomain( L ) ) = true then 
      k := Size( LeftActingDomain( L ) );
   else 
      k := Maximum( Torsion( Basis( L ) ) );   
   fi;   
   
   val := x * y;
   e := A.label;
   if not k = infinity then
      e := e mod k;
   fi;
   a := a + e * val;
   T := [ [ A, val ] ];

   while Length( T ) > 0 do
      T0 := [ ];

      for i in [ 1 .. Length( T ) ] do

         if T[ i ][ 1 ].isleaf = false then
            val := T[ i ][ 2 ];

            if not IsZero( val ) then
               vall := x * val;
               if not IsZero(vall) then
                  e := T[ i ][ 1 ].left.label;
                  if not k = infinity then
                     e := e mod k;
                  fi;
                  a := a + e * vall;
               fi;
               Add( T0, [ T[ i ][ 1 ].left, vall ] );
               valr := y * val;
               if not IsZero( valr ) then
                  e := T[ i ][ 1 ].right.label;
                  if not k = infinity then               
                     e := e mod k;
                  fi;
                  a := a + e * valr;
               fi;
               Add( T0, [ T[ i ][ 1 ].right, valr ] );
            fi;

         fi;

      od;

      T := T0;
   od;

   return a;

end;

LRPrivateFunctions.evalBCH0 := function( A, L, x, y, redfct )

   local a, k, val, coef, e, T, T0, i, vall, valr;
   
   # A is the tree corr to BCH, we evaluate the formula in x, y elements of the Lie ring L
   # same as previous function, but now we have a function that reduces the coefficients
   # of an elt of L to a normal form, by applying p-rels..
   # (necessary because in the LieRingToPGroup, a Lie ring was made, using the lower
   # p-central series, that was of highes nilp class, if one disregards the p-rels...).

   a := x + y;
   if IsField( LeftActingDomain( L ) ) = true then 
      k := Size( LeftActingDomain( L ) );
   else 
      k := Maximum( Torsion( Basis( L ) ) );   
   fi;   
   
   val := x * y;
   e := A.label;
   if not k = infinity then
      e := e mod k;
   fi;
   a := a + e * val;
   T := [ [ A, val ] ];

   while Length( T ) > 0 do
      T0 := [ ];

      for i in [ 1 .. Length( T ) ] do

         if T[ i ][ 1 ].isleaf = false then
            val := T[ i ][ 2 ];
            val:= redfct( Coefficients( Basis(L), val ) )*Basis(L);
            if not IsZero( val ) then
               vall := x * val;
               vall:= redfct( Coefficients( Basis(L), vall ) )*Basis(L);
               if not IsZero(vall) then
                  e := T[ i ][ 1 ].left.label;
                  if not k = infinity then
                     e := e mod k;
                  fi;
                  a := a + e * vall;
               fi;
               Add( T0, [ T[ i ][ 1 ].left, vall ] );
               valr := y * val;
               valr:= redfct( Coefficients( Basis(L), valr ) )*Basis(L);
               if not IsZero( valr ) then
                  e := T[ i ][ 1 ].right.label;
                  if not k = infinity then               
                     e := e mod k;
                  fi;
                  a := a + e * valr;
               fi;
               Add( T0, [ T[ i ][ 1 ].right, valr ] );
            fi;

         fi;

      od;

      T := T0;
   od;

   return a;

end;



LRPrivateFunctions.evalSB := function( A, G, g, h )

   local cm, one, a, val, T, T0, i, vall, valr, e, exp, k;

   # A is the tree corr to SUM or BRACKET, 
   # we evaluate the formula in g, h elements of the p - group G
 
   cm := function( x, y ) return x^ - 1 * y^ - 1 * x * y; end;

   one := g^0;   
   a := one;
   val := cm( g, h );
   exp := A.label;
   k := Order( val );
   e := exp mod k;
   a := a * val^e;
   T := [ [ A, val ] ];

   while Length( T ) > 0 do
      T0 := [ ];

      for i in [ 1 .. Length( T ) ] do

         if T[ i ][ 1 ].isleaf = false then
            val := T[ i ][ 2 ];

            if val  <>  one then
               vall := cm( g, val );
               exp := T[ i ][ 1 ].left.label;
               k := Order( val );
               e := exp mod k;
               a := a * vall^e;
               Add( T0, [ T[ i ][ 1 ].left, vall ] );
               valr := cm( h, val );
               exp := T[ i ][ 1 ].right.label;
               k := Order( val );
               e := exp mod k;
               a := a * valr^e;
               Add( T0, [ T[ i ][ 1 ].right, valr ] );
            fi;

         fi;

      od;

      T := T0;
   od;

   return a;

end;


LRPrivateFunctions.lie_commutator := function( G, g, h )

   local gg, u, cf, exp, pos, v, newu;

   if not IsBound( LRPrivateFunctions.LAZARDTrec.G_BRACKET ) then
      LRPrivateFunctions.InitialiseLAZARD();
   fi;

   gg := Pcgs( G ); 
   u := LRPrivateFunctions.evalSB( LRPrivateFunctions.LAZARDTrec.G_BRACKET, G, g, h );

   # now write u as a sum .. .

   cf := List( [ 1 .. Length( gg ) ], i -> 0 );
   exp := ExponentsOfPcElement( gg, u );

   while u  <>  One( G ) do
      pos := 1; while exp[ pos ] =  0 do pos := pos + 1; od;
      cf[ pos ] := exp[ pos ];
      v := gg[ pos ]^( - exp[ pos ] );
      newu := v * u * LRPrivateFunctions.evalSB( LRPrivateFunctions.LAZARDTrec.G_SUM, G, v, u );
      u := newu;
      exp := ExponentsOfPcElement( gg, u );
   od;

   return cf;

end;


LRPrivateFunctions.multtab := function( G )

   local p, n, ex, cl, g, T, i, j, c;

   # we get the multiplication table of the gens of the Lie ring .. .

   p := PrimePowersInt( Order( G ) )[ 1 ];
   n := PrimePowersInt( Order( G ) )[ 2 ];
   ex := Exponent( G );
   cl := NilpotencyClassOfGroup( G );
   g := Pcgs( G );
   T := List( [ 1 .. Length( g ) ], i -> [ ] );

   for i in [ 1 .. Length( g ) ] do

      for j in [ i .. Length( g ) ] do

         if g[ i ] * g[ j ]  <>  g[ j ] * g[ i ] then
            c := LRPrivateFunctions.lie_commutator( G, g[ i ], g[ j ] );
         else
            c := List( [ 1 .. Length( g ) ], i -> 0 );
         fi;

         T[ i ][ j ] := c;
         T[ j ][ i ] := List( c, u -> - u );
      od;

   od;

   return T;

end;

InstallMethod( PGroupToLieRing,
   "for a p-group",
   true, [ IsGroup ], 0,
   function( G )

   local p, n, ex, cl, g, T, f, T0, i, j, list, l, L, rr,  u, cf, exp, pos, v, newu, s, len, 
         h,  w, k, d, m, e, SPQ, S, P, Q, Qi, t, nb, offset, nbT, Tmats, nT, cij, GtoL, LtoG,
         prels; 

   # G : p-group.
   # we get the Lie ring and .. .

   if not IsPGroup(G) or not IsFinite(G) then
      Error("The group G is not a finite p-group.");
   fi;

   if not IsBound( LRPrivateFunctions.LAZARDTrec.G_SUM ) then
      LRPrivateFunctions.InitialiseLAZARD();
   fi;

   p := PrimePowersInt( Order( G ) )[ 1 ];
   n := PrimePowersInt( Order( G ) )[ 2 ];
   ex := Exponent( G );
   cl := NilpotencyClassOfGroup( G );

   if cl >= p then
      Error("The nilpotency class of the group is >= the prime.");
   fi;

   g := Pcgs( G );
   T := LRPrivateFunctions.multtab( G );

   if ex  =  p then
 
      T0 := EmptySCTable( Length( g ), 0, "antisymmetric" );    
      for i in [ 1 .. Length( g ) ] do

         for j in [ i + 1 .. Length( g ) ] do
            list := [ ];
            for l in [ 1 .. Length( g ) ] do
               if T[ i ][ j ][ l ]  <>  0 then
                  Add( list, T[ i ][ j ][ l ] );
                  Add( list, l );
               fi;
            od;
            SetEntrySCTable( T0, i, j, list ); 
         od;

      od;
      L := AlgebraByStructureConstants( GF( p ), T0 );

      GtoL:= function( g0 )

          local cf, x0, i;

          cf:= ExponentsOfPcElement( g, g0 );
          x0:= cf[1]*Basis(L)[1];
          for i in [2..Dimension(L)] do
              x0:= LRPrivateFunctions.evalBCH( LRPrivateFunctions.LAZARDTrec.G_BCH, L, x0, cf[i]*Basis(L)[i] );
          od;
          return x0;

      end;

      LtoG:= function( x0 )

          local cf, exps, i;

          cf:= List( Coefficients( Basis(L), x0 ), IntFFE );
          exps:= [ ];
          for i in [1..Dimension(L)] do
              Add( exps, cf[i] );
              x0:= LRPrivateFunctions.evalBCH( LRPrivateFunctions.LAZARDTrec.G_BCH, L, -cf[i]*Basis(L)[i], x0 );
              cf:= List( Coefficients( Basis(L), x0 ), IntFFE );
          od;
          return PcElementByExponents( g, exps );

      end;

      return rec( pgroup:= G, liering := L, GtoL := GtoL, LtoG := LtoG ); 

   fi;

   rr := [ ];
   prels:= [ ];

   for i in [ 1 .. Length( g ) ] do
      u := g[ i ]^p;
      # now write u as a sum .. .
      cf := List( [ 1 .. Length( g ) ], i -> 0 );
      exp := ExponentsOfPcElement( g, u );

      while u  <>  One( G ) do
         pos := 1; while exp[ pos ] =  0 do pos := pos + 1; od; 
         cf[ pos ] := exp[ pos ];     
         v := g[ pos ]^( - exp[ pos ] );
         newu := v * u * LRPrivateFunctions.evalSB( LRPrivateFunctions.LAZARDTrec.G_SUM, G, v, u );
         u := newu;
         exp := ExponentsOfPcElement( g, u );
      od;

      Add( prels, ShallowCopy(cf) );

      cf[ i ] := cf[ i ] - p;
      Add( rr, cf );
   od;

   SPQ := SmithNormalFormIntegerMatTransforms( rr ) ;
   S := SPQ.normal;
   P := SPQ.rowtrans;
   Q := SPQ.coltrans;
   Qi := Q^-1;
   t := [ ];
   nb := [ ];

   for i in [ 1 .. Length( S ) ] do
      if S[ i ][ i ]  <>  1 then
         Add( t, S[ i ][ i ] );
         Add( nb, Qi[ i ] );
      fi;
   od;

   f := function( cf ) 
     # cf in new basis ( i.e. of length Length( t ) ), get vector in old basis .. .

      local c, i, k, a;

      c:= cf*nb;
      for i in [1..Length(c)] do
          k:= c[i] mod p;
          a:= (c[i]-k)/p;
          c[i]:= k;
          c:= c + a*prels[i];
      od;
      return c;
   end;

   offset := Length( S ) - Length( t ) + 1;

   h := function( cf ) 
      local v, i, u;
      # cf in old basis ( i.e. of length n ), get vector in new basis .. .
      v := cf * Q;
      u := List( [ offset .. n ], i -> v[ i ] ); 

      for i in [ 1 .. Length( t ) ] do

         if t[ i ]  <>  0 then
            u[ i ] := u[ i ] mod t[ i ];
         fi;

      od;

      return u;

   end;

   nbT := TransposedMat( nb );
   Tmats := List( [ 1 .. n ], m -> nb * List( [ 1 .. n ], 
                          k -> List( [ 1 .. n ], l -> T[ k ][ l ][ m ] ) ) * nbT );
   nT := List( [ 1 .. Length( t ) ], i -> [ ] );

   for i in [ 1 .. Length( t ) ] do

      for j in [ i .. Length( t ) ] do
         cij := List( [ 1 .. n ], k -> 0 );

         if j > i then
            cij := List( [ 1 .. n ], m -> Tmats[ m ][ i ][ j ] );
            nT[ i ][ j ] := h( cij );
            nT[ j ][ i ] := - nT[ i ][ j ];
         else
            nT[ i ][ j ] := h( cij );
         fi;

      od;

   od;

   T0 := EmptySCTable( Length( t ), 0, "antisymmetric" );    

   for i in [ 1 .. Length( t ) ] do

      for j in [ i + 1 .. Length( t ) ] do
         list := [ ];

         for k in [ 1 .. Length( t ) ] do

            if nT[ i ][ j ][ k ]  <>  0 then
               Add( list, nT[ i ][ j ][ k ] );
               Add( list, k );
            fi;

         od;

         SetEntrySCTable( T0, i, j, list ); 
      od;

   od;

   L := LieRingByStructureConstants( t, T0 );

      GtoL:= function( g0 )

          local cf, x0, i, v;

          cf:= ExponentsOfPcElement( g, g0 );
          v:= List( [1..Length(g)], i -> 0 );
          v[1]:= cf[1];
          x0:= LinearCombination( Basis(L), h(v) );

          for i in [2..Length(g)] do
              v:= List( [1..Length(g)], i -> 0 );
              v[i]:= cf[i];
              x0:= LRPrivateFunctions.evalBCH( LRPrivateFunctions.LAZARDTrec.G_BCH, L, x0, LinearCombination( Basis(L), h(v) ) );
          od;
          return x0;

      end;

      LtoG:= function( x0 )

          local cf, exps, i, v;

          cf:= f( Coefficients( Basis(L), x0 ) );
          exps:= [ ];
          for i in [1..Length(g)] do
              Add( exps, cf[i] );
              v:= List( [1..Length(g)], i -> 0 );
              v[i]:= -cf[i];
              x0:= LRPrivateFunctions.evalBCH( LRPrivateFunctions.LAZARDTrec.G_BCH, L, LinearCombination( Basis(L), h(v) ), x0 );
              cf:= f( Coefficients( Basis(L), x0 ) );
          od;
          return PcElementByExponents( g, exps );

      end;


   return rec( pgroup:= G, liering := L, GtoL := GtoL, LtoG := LtoG ); 

end );


LRPrivateFunctions.pgroupA := function( L )

   local D, lc, k, bas, sp, b, v, B, T, K, d, p, F, rels, i, j, l, v1, v2, v3, u, c, x0, 
         y0, z0, w, G_BCH, g, GtoL, LtoG, G;

   #  L : a Lie algebra
   #  we get the group

   if not IsBound( LRPrivateFunctions.LAZARDTrec.G_BCH ) then
      LRPrivateFunctions.InitialiseLAZARD();
   fi;
   G_BCH:= LRPrivateFunctions.LAZARDTrec.G_BCH;

   D := LeftActingDomain( L );
   lc := LieLowerCentralSeries( L );
   k := Length( lc ) - 1;
   bas := List( Basis( lc[ k ] ), u -> u );  
   sp := VectorSpace( D, List( [ 1 .. Length( bas ) ], u -> bas[ u ] ) );

   while k > 1 do
      k := k - 1;
      b := CanonicalBasis( lc[ k ] );

      for v in b do

         if not v in sp then
            Add( bas, v );
            sp := VectorSpace( D, List( [ 1 .. Length( bas ) ], u -> bas[ u ] ) );
         fi;

      od;

   od;

   B := Basis( L, Reversed( bas ) );
   T := StructureConstantsTable( B );
   K := LieAlgebraByStructureConstants( D, T );
   d := Dimension( K );
   p := Characteristic( LeftActingDomain( K ) );
   F := FreeGroup( d );
   rels := List( [ 1 .. d ], i -> F.( i )^p );

   for i in [ 1 .. d - 1 ] do

      for j in [ i + 1 .. d ] do
         v1 := LRPrivateFunctions.evalBCH( G_BCH, K, Basis( K )[ j ], Basis( K )[ i ] );
         v2 := LRPrivateFunctions.evalBCH( G_BCH, K, - Basis( K )[ j ], - Basis( K )[ i ] );
         v3 := LRPrivateFunctions.evalBCH( G_BCH, K, v2, v1 );             
         u := ShallowCopy( Coefficients( Basis( K ), v3 ) );
         c := [ ];  

         for l in [ 1 .. d ] do
            Add( c, u[ l ] );            
            y0 := Sum( [ 1 .. d ], t -> u[ t ] * Basis( K )[ t ] );
            x0 := - u[ l ] * Basis( K )[ l ];
            z0 := LRPrivateFunctions.evalBCH( G_BCH, K, x0, y0 );
            u := Coefficients( Basis( K ), z0 );
         od;   

         w := Product( [ 1 .. d ], s -> F.( s )^( IntFFE( c[ s ] ) ) );
         w := F.( j ) * w;
         Add( rels, F.( j )^F.( i )/( w ) );
      od;

   od;

   G:= PcGroupFpGroupNC( F/rels );
   g:= Pcgs(G );

      GtoL:= function( g0 )

          local cf, x0, i;

          cf:= ExponentsOfPcElement( g, g0 );
          x0:= cf[1]*Basis(K)[1];
          for i in [2..Dimension(K)] do
              x0:= LRPrivateFunctions.evalBCH( LRPrivateFunctions.LAZARDTrec.G_BCH, K, x0, cf[i]*Basis(K)[i] );
          od;
          return LinearCombination( B, Coefficients( Basis(K), x0 ) );

      end;

      LtoG:= function( x0 )

          local cf, exps, i;

          cf:= Coefficients( B, x0 );
          x0:= LinearCombination( Basis(K), cf );
          cf:= List( cf, IntFFE );
          exps:= [ ];
          for i in [1..Dimension(K)] do
              Add( exps, cf[i] );
              x0:= LRPrivateFunctions.evalBCH( LRPrivateFunctions.LAZARDTrec.G_BCH, K, -cf[i]*Basis(K)[i], x0 );
              cf:= List( Coefficients( Basis(K), x0 ), IntFFE );
          od;
          return PcElementByExponents( g, exps );

      end;

      return rec( pgroup:= G, liering:= L, LtoG:= LtoG, GtoL:= GtoL );

end;

InstallMethod( LieLowerPCentralSeries,
   "for Lie ring and a prime",
   true, [ IsLieRing, IsInt ], 0,
   function( L, p )

   local lc, b, done, a, x, y, S;

   # p :  .. .
   # we get .. .

   if not IsPrime(p) then
      Error("The integer p is not prime.");
   fi;

   lc := [ L ];
   b := BasisVectors( Basis( L ) );
   done := false;

   while not done do
      a := [ ];

      for x in BasisVectors( Basis( L ) ) do
         for y in b do
            Add( a, x * y );
         od;
      od;
      for y in b do
         Add( a, p * y );
      od;

      S := SubLieRing( L, a );
      if S =  lc[ Length( lc ) ] then
         done := true;
      elif GeneratorsOfAlgebra( S ) =  [ ] then
         done := true;
         Add( lc, S );
      else
         Add( lc, S );
      fi;
      b := BasisVectors( Basis( S ) );
   od;

   return lc;

end );


LRPrivateFunctions.pgroupR := function( L )

   local t, fc, p, lc, q, vv, torv, i, k, torsmat, v, m, mats, dim, T, j, l, c, s, cc, K, 
         F, rels, u, x0, y0, z0, v1, v2, v3, w, G_BCH, B, GtoL, LtoG, normalisecf, prels, G, g;

   # L : a Lie ring
   # we get the group

   if not IsBound( LRPrivateFunctions.LAZARDTrec.G_BCH ) then
      LRPrivateFunctions.InitialiseLAZARD();
   fi;
   G_BCH:= LRPrivateFunctions.LAZARDTrec.G_BCH;

   t := Torsion( Basis( L ) );

   if t[ 1 ]  = 0 then
      return fail;
   fi;

   fc := Set( Factors( t[ 1 ] ) );

   if Length( fc ) > 1 then
      return fail;
   fi;

   p := fc[ 1 ];
   for i in [ 1 .. Length( t ) ] do
      if t[ i ] <> p^( Log( t[ i ], p ) ) then
         return fail;
      fi;
   od;

   lc := LieLowerPCentralSeries( L, p );

   if Length( Basis( ( lc[ Length( lc ) ] ) ) ) > 0 then
      return fail;
   fi;

   q := List( [ 1 .. Length( lc ) - 1 ], i -> 
                     NaturalHomomorphismByIdeal( lc[ i ], lc[ i + 1 ] ) );
   vv := Flat( List( q, f -> List( Basis( Range( f ) ), x -> 
                                 PreImagesRepresentative( f, x ) ) ) );
   torv := [ ];
   for i in [ 1 .. Length( vv ) ] do
      k := 1;
      while not IsZero( p^k * vv[ i ] ) do k := k + 1; od;
      Add( torv, p^k );
   od;

   torsmat := [ ];
   for i in [ 1 .. Length( t ) ] do
      v := List( t, x -> 0 ); v[ i ] := t[ i ];
      Add( torsmat, v );
   od;

   m := List( vv, x -> Coefficients( Basis( L ), x ) );
   mats := [ ];

   for i in [ 1 .. Length( m ) ] do
      Add( mats, Concatenation( m{[ i .. Length( m ) ]}, torsmat ) );
   od;

   dim := Length( vv );
   T := EmptySCTable( dim, 0, "antisymmetric" );

   for i in [ 1 .. dim ] do

      for j in [ i + 1 .. dim - 1 ] do
         v := vv[ i ] * vv[ j ];
         c := Coefficients( Basis( L ), v );
         s := SolutionIntMat( mats[ j + 1 ], c );
         s := s{[ 1 .. dim - j ]};
         s := Concatenation( List( [ 1 .. j ], x -> 0 ), s );
         cc := [ ];

         for l in [ 1 .. dim ] do
            if not IsZero( s[ l ] ) then
               Append( cc, [ s[ l ] mod torv[ l ], l ] );
            fi;
         od;

         SetEntrySCTable( T, i, j, cc );
      od;
   od;

   K := LieRingByStructureConstants( torv, T );

   F := FreeGroup( dim );
   rels := [ ];

   prels:= [ ];
   # for every bas elt of K, we have that p*b_i = \sum_{j=i+1}^n c_ij*b_j
   # collect these rels...

   for i in [ 1 .. dim - 1 ] do
      v := p * vv[ i ];
      c := Coefficients( Basis( L ), v );
      s := SolutionIntMat( mats[ i + 1 ], c );
      s := s{[ 1 .. dim - i ]};
      s := Concatenation( List( [ 1 .. i ], x -> 0 ), s );
      prels[i]:= s;
   od;
   Add( prels, List( [1..dim], x -> 0 ) );

   normalisecf:= function( cf )

      # here cf is the coefficients of an element of K;
      # we get all cfs in [0..p-1] by applying p rels...

      local i, k, a;

      for i in [1..dim] do
          k:= cf[i] mod p;
          a:= (cf[i]-k)/p;
          cf[i]:= k;
          cf:= cf+a*prels[i];
      od;

      return cf;

   end;

   for i in [1..dim-1] do

      u := ShallowCopy( prels[i] );
      c := [ ];

      for l in [ 1 .. dim ] do
         Add( c, u[ l ] );
         y0 := Sum( [ 1 .. dim ], t -> u[ t ] * Basis( K )[ t ] );
         x0 := - u[ l ] * Basis( K )[ l ];
         z0 := LRPrivateFunctions.evalBCH0( G_BCH, K, x0, y0, normalisecf );
         u := Coefficients( Basis( K ), z0 );
      od;

      w := Product( [ 1 .. dim ], s -> F.( s )^( c[ s ] ) );
      Add( rels, F.( i )^p/w );
   od;

   Add( rels, F.( dim )^p );

   for i in [ 1 .. dim ] do

      for j in [ i + 1 .. dim ] do
         v1 := LRPrivateFunctions.evalBCH0( G_BCH, K, Basis( K )[ j ], Basis( K )[ i ], 
                                                                             normalisecf );
         v2 := LRPrivateFunctions.evalBCH0( G_BCH, K, - Basis( K )[ j ], - Basis( K )[ i ], 
                                                                             normalisecf );
         v3 := LRPrivateFunctions.evalBCH0( G_BCH, K, v2, v1, normalisecf );
         u := ShallowCopy( Coefficients( Basis( K ), v3 ) );
         c := [ ];

         for l in [ 1 .. dim ] do
            Add( c, u[ l ] );
            y0 := Sum( [ 1 .. dim ], t -> u[ t ] * Basis( K )[ t ] );
            x0 := - u[ l ] * Basis( K )[ l ];
            z0 := LRPrivateFunctions.evalBCH0( G_BCH, K, x0, y0, normalisecf );
            u := Coefficients( Basis( K ), z0 );
         od;

         w := Product( [ 1 .. dim ], s -> F.( s )^( c[ s ] ) );
         w := F.( j ) * w;
         Add( rels, F.( j )^F.( i )/( w ) );
      od;
   od;

   G:= PcGroupFpGroupNC( F/rels );
   g:= Pcgs(G);

      GtoL:= function( g0 )

          local cf, x0, i;

          cf:= ExponentsOfPcElement( g, g0 );
          x0:= cf[1]*Basis(K)[1];
          for i in [2..Length( Basis( (K) ) )] do
              x0:= LRPrivateFunctions.evalBCH0( LRPrivateFunctions.LAZARDTrec.G_BCH, K, x0, cf[i]*Basis(K)[i], normalisecf );
          od;
          return LinearCombination( vv, Coefficients( Basis(K), x0 ) );

      end;

      LtoG:= function( x0 )

          local cf, exps, i, s;

          cf := Coefficients( Basis( L ), x0 );      
          s:= SolutionIntMat( mats[1], cf );
          s:= s{[1..dim]};
          cf:= normalisecf( s );
          x0:= LinearCombination( Basis(K), cf );
          exps:= [ ];
          for i in [1..Length( Basis( (K) ) )] do
              Add( exps, cf[i] mod RelativeOrders(g)[i] );
              x0:= LRPrivateFunctions.evalBCH0( LRPrivateFunctions.LAZARDTrec.G_BCH, K, -cf[i]*Basis(K)[i], x0, normalisecf );
              cf:= Coefficients( Basis(K), x0 );
              cf:= normalisecf( cf );     
          od;
          return PcElementByExponents( g, exps );

      end;
      return rec( pgroup:= G, liering:= L, LtoG:= LtoG, GtoL:= GtoL );

end;

InstallMethod( LieRingToPGroup,
   "for nilpotent Lie ring of order p^n",
   true, [ IsLieRing ], 0,
   function( L )

   local F, p, lc, t, fc;

   F:= LeftActingDomain(L);

   if IsField( F ) then
      p:= Characteristic(F);
      if p = 0 then Error("The Lie algebra is defined over a field of char. 0"); fi;
      lc:= LieLowerCentralSeries(L);
      if not Length( Basis( lc[Length(lc)] ) ) = 0 then
         Error("The Lie algebra is not nilpotent.");
      fi;
      if not Length(lc)-1 < p then
         Error("The nilpotency class of the Lie algebra is >= the prime.");
      fi;
      return LRPrivateFunctions.pgroupA( L );
   else
      t:= Torsion( Basis(L) );
      if 0 in t then
         Error("The Lie ring is infinite.");
      fi;
      fc:= PrimePowersInt( Product(t) );
      if Length(fc) > 2 then
         Error( "The Lie ring is not of order p^n.");
      fi; 
      lc:= LieLowerCentralSeries( L );
      if not Length( Basis( lc[Length(lc)] )) = 0 then
         Error("The Lie algebra is not nilpotent.");
      fi;      
      if not Length(lc)-1 < fc[1] then
         Error("The nilpotency class of the Lie algebra is >= the prime.");
      fi;
      return LRPrivateFunctions.pgroupR( L );
   fi;

end );       

        
