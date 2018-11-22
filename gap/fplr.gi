#####################################################################################
#
#  fplr.gi                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 


LRPrivateFunctions.leading_mns:= function( G )
     local mm, g, eg;
     mm:= [ ];
     for g in G do
         if g = [ ] then
            Add( mm, [] );
         else
            Add( mm, g[ Length( g )-1 ] );
         fi;
     od;
     return mm;

end;

LRPrivateFunctions.make_basis:= function( fam, BB )

      # produce a basis of the subspace spanned by BB

      local o, mninds, b, i, mat, cc, bas, mns, n, t, s;

      o:= fam!.ordering;
      mninds:= [ ];
      for b in BB do
          for i in [1,3..Length(b)-1] do
              if not b[i].no in mninds then Add( mninds, b[i].no ); fi;
          od;
      od;

      Sort( mninds, function( a, b ) return o[a] > o[b]; end );
      mat:= [ ];
      for b in BB do
          cc:= List( mninds, x -> 0 );
          for i in [1,3..Length(b)-1] do
             cc[ Position( mninds, b[i].no ) ]:= b[i+1];
          od;
          Add( mat, cc );
      od;

      mat:= HermiteNormalFormIntegerMat( mat );

      bas:= [ ];
      mns:= fam!.monomials;
      n:= Length( mninds );
      for cc in mat do
          if cc <> 0*cc then
             b:= [ ];
             for i in [n,n-1..1] do
                 if cc[i] <> 0 then
                    Add( b, mns[ o[mninds[i]] ] );
                    Add( b, cc[i] );
                 fi;
             od;
             Add( bas, b );
          fi;
       
      od;      

      return bas;

end;

LRPrivateFunctions.linalg_reduce:= function( fam, f, G, lmsps )

     # reduce f modulo G, in the linalg way, i.e., only reduce if a monomial 
     # in f is equal to a lm in G
     # Elements in G are assumed monic. No divisions will be done.
     # lms: leading monomials of G in ext rep.

     local ef, gs, eg, len, i, k, lf, j, g0, cf;

     if f=[] then return f; fi;
     if G = [ ] then return f; fi;

     ef:= ShallowCopy( f );
     lf:= Length( ef );
     gs:= [ ];
     i:= lf-1;

     while i >=1 do

         if IsBound( lmsps[ef[i].no] ) then
            k:= lmsps[ ef[i].no ];
            eg:= G[k];
            len:= Length( eg );
            g0:= eg{[1..len-2]};
            cf:= ef[i+1];
            for j in [2,4..len-2] do g0[j]:= -g0[j]*cf; od;
            gs:= LRPrivateFunctions.direct_sum( fam, gs, g0 );
            Unbind( ef[i] ); Unbind( ef[i+1] );
            ef:= Filtered( ef, x -> IsBound(x) );
            i:= i-2;
         else
            i:= i-2;
         fi;
     od;

     if ef=[] then 
        return gs;
     else
        return LRPrivateFunctions.direct_sum( fam, ef, gs );
     fi;
end;

LRPrivateFunctions.linalg_reduce_allbyone:= function( fam, f, G )

     # reduce all in G modulo f, in the linalg way, i.e., only reduce if a monomial 
     # in g for g in G is equal to LM(f) then reduce...
     # f is assumed monic...

     local lf, mf, f0, o, i, j, k, g, lg, cf, g0, t;

     if G = [ ] then return G; fi;

     lf:= Length( f );
     mf:= f[ lf-1 ];
     f0:= f{[1..lf-2]};

     o:= fam!.ordering;

     for i in [1..Length(G)] do
         g:= G[i]; lg:= Length(g);
         for j in [lg-1,lg-3..1] do
            if o[ mf.no ] > o[ g[j].no ] then break; fi;
            if g[j].no = mf.no then
               cf:= g[j+1];
               g0:= ShallowCopy(f0);
               for k in [2,4..lf-2] do g0[k]:= -g0[k]*cf; od;
               Unbind( g[j] ); Unbind( g[j+1] );
               g:= Filtered( g, x -> IsBound(x) );
               g:= LRPrivateFunctions.direct_sum( fam, g, g0 );
               G[i]:= g;
               break;
            fi;
         od;
     od;

     return G;

end;


LRPrivateFunctions.linalg_reduce_onemon:= function( fam, f, G, lmspos )

     # reduce f modulo G, in the linalg way, i.e., only reduce if a monomial 
     # in f is equal to a lm in G
     # Elements in G are assumed monic. No divisions will be done.
     # lms: leading monomials of G in ext rep.

     local ef, eg, len, k, j, g0, cf;

     if G = [ ] then return f; fi;
     if f=[] then return f; fi;

     cf:= f[2]; ef:= f[1];
     if IsBound( lmspos[ef.no] ) then
        k:= lmspos[ef.no];
        eg:= G[k];
        len:= Length( eg );
        g0:= eg{[1..len-2]};
        for j in [2,4..len-2] do g0[j]:= -cf*g0[j]; od;
        return g0;
     fi;
    
     return f;

end;

LRPrivateFunctions.search_factor0:= function( m, lms )

     # same as search_factor, but now lms is not assumed to be sorted!

     local b, choices, points, pos, mns, lr, c, k;
    
     b:= m; 
     choices:= [ ];
     points:= [ b ];

     while true do

        pos:= Position( lms, b.no );       
        if pos <= Length(lms) and lms[pos] = b.no then
           mns:= [ ];
           lr:= [ ];
           c:= m;
           for k in choices do
               if k = 0 then
                  Add( lr, 1 ); Add( mns, c.right ); c:= c.left;
               else
                  Add( lr, 0 ); Add( mns, c.left ); c:= c.right;
               fi;
           od;
           return [ true, pos, Reversed(mns), Reversed(lr) ];
         fi;
         if IsBound(b.var) then
            # backtrack...
            k:= Length( choices );
            while k>=1 and choices[k] = 1 do k:= k-1; od;
            if k = 0 then return [ false ]; fi;
            choices:= choices{[1..k-1]}; points:= points{[1..k]};
           
            b:= points[k].right;
            Add( choices, 1 ); Add( points, b );
      
         else
            b:= b.left;
            Add( choices, 0 ); Add( points, b );
         fi;
     od;

end;

LRPrivateFunctions.reduce0:= function( fam, f, G, lms )

     # Here we do assume G to be monic, but not that lms is sorted,
     # so a bit different from reduce.
 
     local lms0, ef, len, r, m, cf, a, g, mns, side, lg, i;

     if f=[] then return f; fi;
     if G = [ ] then return f; fi;

     lms0:= List( lms, x -> x.no );

     ef:= ShallowCopy( f );
     len:= Length(ef);

     r:= [ ];

     while len >0 do
        m:= ef[ len-1 ]; cf:= ef[len];
        ef:= ef{[1..len-2]};
        len:= len-2;
  
        # look for a factor...
        a:= LRPrivateFunctions.search_factor0( m, lms0 );
 
        if a[1] then
           g:= ShallowCopy(G[a[2]]);
           lg:= Length(g);

           mns:= a[3];
           side:= a[4];
           g:= g{[1..lg-2]};
  
           for i in [1..Length(mns)] do
               if side[i] = 0 then 
                  g:= LRPrivateFunctions.dir_mult( fam, [mns[i],1], g );
               else
                  g:= LRPrivateFunctions.dir_mult( fam, g, [mns[i],1] );
               fi;
           od;

           # compute -cf*g:
           for i in [2,4..Length(g)] do
               g[i]:= -cf*g[i];
           od;

           ef:= LRPrivateFunctions.direct_sum( fam, ef, g );            
           len:= Length( ef );
           
        else

           r:= LRPrivateFunctions.direct_sum( fam, r, [m,cf] );
# Better: add everything, then sort!
        fi;
     od;

     if r <> [ ] then
        cf:= r[Length(r)];
        if cf = -1 then
           for i in [2,4..Length(r)] do r[i]:= -r[i]; od; 
        fi;
     fi;

     return r;

end;

LRPrivateFunctions.reduce:= function( fam, f, G, lms )

     # G not assumed monic!
     # NOTE: the lms, and hence G, are assumed to be sorted by leading monomial number!
     # assumed by search_factor....

     local lms0, ef, len, r, m, cf, a, g, mns, side, lg, i, cg, rem, q;

     if f=[] then return f; fi;
     if G = [ ] then return f; fi;

     lms0:= List( lms, x -> x.no );

     ef:= ShallowCopy( f );
     len:= Length(ef);

     r:= [ ];

     while len >0 do
        m:= ef[ len-1 ]; cf:= ef[len];
        ef:= ef{[1..len-2]};
        len:= len-2;
  
        # look for a factor...
        a:= LRPrivateFunctions.search_factor( m, lms0 );
 
        if a[1] then
#           g:= ShallowCopy(G[a[2]]![1]);
           g:= ShallowCopy(G[a[2]]);
           lg:= Length(g);
           cg:= g[lg];
           rem:= cf mod cg;
           q:= (cf-rem)/cg;
           if q <> 0 then
              mns:= a[3];
              side:= a[4];
              g:= g{[1..lg-2]};
  
              for i in [1..Length(mns)] do
                  if side[i] = 0 then 
                     g:= LRPrivateFunctions.dir_mult( fam, [mns[i],1], g );
                  else
                     g:= LRPrivateFunctions.dir_mult( fam, g, [mns[i],1] );
                  fi;
              od;

              # compute -q*g:
              for i in [2,4..Length(g)] do
                  g[i]:= -q*g[i];
              od;

              ef:= LRPrivateFunctions.direct_sum( fam, ef, g );            
              len:= Length( ef );
           fi;

           if rem <> 0 then
              r:= LRPrivateFunctions.direct_sum( fam, r, [m,rem] );
           fi;
        else

           r:= LRPrivateFunctions.direct_sum( fam, r, [m,cf] );
# Better: add everything, then sort!
        fi;
     od;

     if r <> [ ] then
        cf:= r[Length(r)];
        if cf = -1 then
           for i in [2,4..Length(r)] do r[i]:= -r[i]; od; 
        fi;
     fi;

     return r;

end;

LRPrivateFunctions.addElm_RedSet:= function( fam, f, G, lms )

    local newelms, len, h, n, Gh, i, g, pos;

    newelms:= [ f ];
    len:= 1;
    while len>0 do
       h:= newelms[len];
       newelms:= newelms{[1..len-1]};
       len:= len-1;
       h:= LRPrivateFunctions.reduce( fam, h, G, lms );
       if h <> [] then
          # we add it, but first we remove all elements of which the
          # leading monomial reduces mod h from G:
          n:= [ h[ Length(h)-1 ] ];
          Gh:= [ h ];
          for i in [1..Length(G)] do
              g:= LRPrivateFunctions.reduce( fam, G[i], Gh, n );
              if g <> [] and g[Length(g)-1].no <> lms[i].no then
                 Add( newelms, g ); len:= len+1;
                 Unbind( G[i] ); Unbind( lms[i] );
              elif g=[ ] then
                 Unbind( G[i] ); Unbind( lms[i] );
              else
                 G[i]:= g;
              fi;
          od;
          G:= Filtered( G, x -> IsBound(x) );
          lms:= Filtered( lms, x -> IsBound(x) );
          pos:= PositionSorted( lms, n[1] );
          CopyListEntries(G,pos,1,G,pos+1,1,Length(G)-pos+1);
          G[pos]:= h;
          CopyListEntries(lms,pos,1,lms,pos+1,1,Length(lms)-pos+1);
          lms[pos]:= n[1];
       fi;
    od;

    return [ G, lms ];

end;

LRPrivateFunctions.interreduce:= function( fam, U )

   local G, lms, i, r, A, B, j, cf, g;

   if U = [] then return [ [], [] ]; fi;

   G:= [ U[1] ];
   lms:= [ U[1][ Length(U[1])-1 ] ];
   for i in [2..Length(U)] do
       r:= LRPrivateFunctions.addElm_RedSet( fam, U[i], G, lms );
       G:= r[1]; lms:= r[2];
   od;

   # split monic/nonmonic...
   A:= [ ]; B:= [ ];
   for g in G do
       cf:= g[ Length(g) ];
       if cf = -1 then
          for j in [2,4..Length(g)] do
              g[j]:= -g[j];
          od;
          cf:= 1;
       fi;
       if cf = 1 then
          Add( A, g );
       else
          Add( B, g );
       fi;
   od;
   return [A,B]; 
end;

LRPrivateFunctions.FpLieRingHOM:= function( A, R, bound )

     # compute A/I, where I is the ideal gen by R along with Jacobi-s

     local zero, one, Fam, o, g, B, Bk, Bd, G, BB, lms, lmspos, deg, Moninds, 
           Qs, is_nilquot, rels, f, BBdeg, Gdeg, i, lmsposr, nonleadingr, lf, r, u, v, 
           m1, m2, m3, j, f1, f2, f3, c, m, x, h, newB, mat, b, cc, ss, Qi, bas, tor, 
           NB, Tors, nocol, tors, basinds, k, T, entry, added, mninds, a1, a2, a3, a4, cf, K;



     zero:= Zero( LeftActingDomain(A) );
     one:= One( LeftActingDomain( A ) );

     Fam:= ElementsFamily( FamilyObj( A ) );
     o:= Fam!.ordering;

     g:= GeneratorsOfAlgebra( A );
     B:= [ ];
     Bk:= [ ];
     Bd:= [ ];

     NB:= [ ]; # basis in "normal form" i.e., displaying torsion etc.
     Tors:= [ ]; # the torsion corresponding to the elements of NB

     G:= [ ];
     BB:= [ ];    # G, BB will be the reduction pair...
     lms:= [ ];
     lmspos:= [];

     Moninds:= [ ]; # no-s of monomials in the basis, listed by degree
     Qs:= [ ];  # the Q-matrices for each degree (coming out of the Smith form).

     deg:= 1;

     is_nilquot:= bound <> infinity;

     while deg <= bound do

       rels:= Filtered( R, x -> Degree(x) = deg );

       for i in [1..Length(rels)] do
           f:= ShallowCopy( LRPrivateFunctions.reduce0( Fam, rels[i]![1], G, lms ) );
           rels[i]:= f;
       od;
       rels:= Filtered( rels, x -> Length(x) > 0 );
       rels:= LRPrivateFunctions.make_basis( Fam, rels );

       #split into monic/nonmonic
       BBdeg:=  [ ];

       Gdeg:= [ ];
       lmsposr:= [ ];
       nonleadingr:= [ ];
       for f in rels do
           if f <> [ ] then
              lf:= Length( f );
              if f[ lf ] = 1 then
                 Add( Gdeg, f );
                 lmsposr[ f[ lf-1 ].no ]:= Length( Gdeg );
                 for r in [1,3..lf-3] do
                     AddSet( nonleadingr, f[r].no );
                 od; 
              else
                 Add( BBdeg, f );
              fi;
           fi;
       od;

       if deg >= 3 then

          a1:= Length(g);
          a2:= Length(Bd);

          for i in [1..a1] do
              m1:= g[i]![1];
              for u in [1..a2] do
                  v:= deg-m1[1].deg-u;
                  if v > 0 and v <= a2 then
                     a3:= Length( Bd[u] );
                     a4:= Length( Bd[v] );
                     for j in [1..a3] do
                         m2:= Bd[u][j];
                         if o[m1[1].no] < o[m2[1].no] then
                            for k in [1..a4] do
                                m3:= Bd[v][k];
                                if o[m2[1].no] < o[m3[1].no] then

                                    f1:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                  LRPrivateFunctions.dir_monmult( Fam, m2, m3 ), G, lmspos );
                                    f2:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                  LRPrivateFunctions.dir_monmult( Fam, m1, m2 ), G, lmspos );
                                    f3:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                  LRPrivateFunctions.dir_monmult( Fam, m3, m1 ), G, lmspos );

                                    f:= LRPrivateFunctions.special_mult( Fam, m1, f1, m3, f2, m2, f3 );

                                    f:= LRPrivateFunctions.linalg_reduce( Fam, f, Gdeg, lmsposr );

                                    if f <> [] then
                                       lf:= Length(f); 
                                       c:= f[ lf ];
                                       if c = -1 then
                                          for r in [2,4..lf] do f[r]:= f[r]/c; od;
                                          c:= 1;
                                       fi;
                                       if c = 1 then
                                          m:= f[ lf-1 ];
                                          if m.no in nonleadingr then
                                             Gdeg:= LRPrivateFunctions.linalg_reduce_allbyone( Fam, f, Gdeg );
                                             # NOTE that this will never change a leading monomial, as
                                             # f is reduced mod Gdeg...
                                          fi;
                                          Add( Gdeg, f );
                                          for r in [1,3..lf-3] do
                                              AddSet( nonleadingr, f[r].no );
                                          od; 
                                          lmsposr[ m.no ]:= Length( Gdeg );
                                       else
                                          Add( BBdeg, f );
                                       fi;
                                    
                                    fi;
 
                                fi;
                                      
                            od;
                         fi;
                     od;
                  fi;
              od;
          od;
       fi;

       # The elts of BBdeg may not be in normal form modulo Gdeg....

       for i in [1..Length( BBdeg )] do
           BBdeg[i]:= LRPrivateFunctions.linalg_reduce( Fam, BBdeg[i], Gdeg, lmsposr );
       od;
       BBdeg:= Filtered( BBdeg, x -> x <> [] );

       # now add elements of the form (x,b) where x is a generator,
       # and b an element of BB of degree deg- degree( generator ).

       for f in BB do
           for x in g do
               if not IsBound( lmspos[x![1][1].no] ) then
                  if f[Length(f)-1].deg + Degree(x) = deg then
                     h:= LRPrivateFunctions.dir_mult( Fam, x![1], f );
                     h:= LRPrivateFunctions.linalg_reduce( Fam, h, Gdeg, lmsposr );      
                     if h <> [ ] then
                        Add( BBdeg, h );
                     fi;
                 fi;
               fi;
           od;
       od;

       BBdeg:= LRPrivateFunctions.make_basis( Fam, BBdeg ); 

       # move monic elements to G...

       i:= 1;
       while i <= Length( BBdeg ) do
           f:= BBdeg[i];
           c:= f[ Length(f) ];
           if c = -1 then   
              for k in [2,4..Length(f)] do f[k]:= f[k]*c; od;
              c:= 1;
           fi;
           if c = 1 then
              # Move it to G, but note that we have to keep G self-reduced...
              Unbind( BBdeg[i] ); BBdeg:= Filtered( BBdeg, x -> IsBound(x) );
              Gdeg:= LRPrivateFunctions.linalg_reduce_allbyone( Fam, f, Gdeg );
              Add( Gdeg, f );
              # Maybe the reduction has resulted in non-monic elements occurring in Gdeg:
              added:= false;
              for j in [1..Length(Gdeg)] do
                  f:= Gdeg[j];
                  c:= f[ Length(f) ];
                  if c = -1 then   
                     for k in [2,4..Length(f)] do f[k]:= f[k]*c; od;
                     c:= 1;
                  fi;
                  if c <> 1 then
                     Add( BBdeg, f );
                     added:= true;
                  else
                     Gdeg[j]:= f;
                  fi;
              od;
              if added then 
                 BBdeg:= LRPrivateFunctions.make_basis( Fam, BBdeg );
                 i:= 1;
              fi;
           else
              i:= i+1;
           fi;
       od;

       Append( G, Gdeg );

       lms:= LRPrivateFunctions.leading_mns( G );

       lmspos:= [ ];
       for i in [1..Length(lms)] do
           lmspos[ lms[i].no ]:= i;
       od;


       newB:= [ ];
       for f in g do
           m:= f![1];
           if m[1].deg = deg then
              if not IsBound( lmspos[m[1].no] ) then 
                 Add( newB, m );
              fi;
           fi;
       od;       

       if deg > 1 then
          
          for u in [1..Length(Bd)] do
              v:= deg-u;
              if v>=1 and v<=Length(Bd) then
                 for i in [1..Length(Bd[u])] do
                     m1:= Bd[u][i]; 
                     for k in [1..Length( Bd[v] )] do
                         m2:= Bd[v][k];
                         if o[m1[1].no] < o[m2[1].no] then
                            m:= LRPrivateFunctions.dir_monmult( Fam, m1, m2 );
                            if not IsBound( lmspos[m[1].no] ) then 
                               Add( newB, m );
                            fi;
                         fi;
                     od;
                 od;
              fi;
          od;

       fi;

       Sort( newB, function( a, b ) return o[a[1].no] < o[b[1].no]; end );

       # Note that newB is sorted small to big (follows from the above piece of code). 
       # In the next piece of
       # code elements are made with monomials in the order of newB; hence if
       # we later ObjByExtRep, then we have to have the right order...

       mninds:= List( newB, x -> x[1].no );
       Add( Moninds, mninds );

       if Length( BBdeg ) > 0 then
          mat:= [ ];
          for b in BBdeg do
              cc:= List( mninds, x -> 0 );
              for i in [1,3..Length(b)-1] do
                 cc[ Position( mninds, b[i].no ) ]:= b[i+1];
              od;
             Add( mat, cc );
          od;

          ss:= SmithNormalFormIntegerMatTransforms( mat );
          Add( Qs, ss.coltrans );
          Qi:= ss.coltrans^-1;
          mat:= ss.normal;
      
          bas:= [ ];
          tor:= [ ];
          nocol:= Length( mninds );
          for k in [1..nocol] do
              cc:= Qi[k];
              b:= [ ];
              for i in [1..nocol] do
                  if cc[i] <> 0 then
                     Add( b, newB[ i ][1] );
                     Add( b, cc[i] );
                  fi;
              od;
              Add( bas, b );
              if k <= Length(mat) then
                 Add( tor, mat[k][k] );
              else
                 Add( tor, 0 );
              fi;
          od;      

          Add( NB, bas );
          Add( Tors, tor ); 
       else
          Add( NB, newB );
          Add( Tors, List( newB, x -> 0 ) );
          Add( Qs, [ ] );
       fi;

       Append( BB, BBdeg );

       Add( Bd, newB );
       Bk:= newB;

       if Bk = [ ] and bound > 2*deg-1 then
          bound:= 2*deg-1;
          bound:= Maximum(bound,Maximum( List( R, x -> Degree(x) ) ) );
       fi;
       deg:= deg+1;      

     od;

     bas:= [ ];
     tors:= [ ];
     basinds:= [ ]; # a list of lists, e.g., if the k-th element is [0,0,6,7,8], then
                    # the "normal basis" has 5 elements of degree k, the first two 
                    # with torsion 1, the last three with positions 6, 7, 8 in the final basis.
     k:= 1;
     for i in [1..Length(NB)] do
         Add( basinds, [ ] );
         for j in [1..Length(NB[i])] do
             if Tors[i][j] <> 1 then
                Add( bas, NB[i][j] );
                Add( tors, Tors[i][j] );
                Add( basinds[i], k ); k:= k+1;
             else
                Add( basinds[i], 0 );
             fi;
         od;
     od;

     T:= EmptySCTable( Length( bas ), 0, "antisymmetric" );

     for i in [1..Length(bas)] do
         for j in [i+1..Length(bas)] do
             if not( is_nilquot and bas[i][1].deg + bas[j][1].deg > bound ) then

                b:= LRPrivateFunctions.linalg_reduce( Fam, 
                        LRPrivateFunctions.dir_mult( Fam, bas[i], bas[j] ), G, lmspos );
                if b <> [] then
                   deg:= b[1].deg;
                   entry:= [ ];
                   if Qs[deg] = [ ] then
                      for k in [1,3..Length(b)-1] do
                          Add( entry, b[k+1] );
                          Add( entry, basinds[deg][ Position( Moninds[deg], b[k].no ) ] );
                      od;
                   else
                      cc:= List( Moninds[deg], x -> 0 );
                      for k in [1,3..Length(b)-1] do
                          cc[ Position( Moninds[deg], b[k].no ) ]:= b[k+1];
                      od;  

                      cc:= cc*Qs[deg];  # this is now the list of coefficients of b wrt normbas...
                                        # in order to get normal form we "divide" by the torsion...
                      for k in [1..Length(cc)] do 
                          if Tors[deg][k] <> 0 then
                             cc[k]:= cc[k] mod Tors[deg][k]; 
                          fi;
                      od;

                      for k in [1..Length(cc)] do
                          if cc[k] <> 0 then
                             Add( entry, cc[k] );
                             Add( entry, basinds[deg][k] );
                          fi;
                      od;
                   fi;
                   SetEntrySCTable( T, i, j, entry );
                fi;
             fi;
         od;
     od;

     K:= LieRingByStructureConstants( tors, T );

     g:= [ ];
     for i in GeneratorsOfAlgebra(A) do
         b:= LRPrivateFunctions.linalg_reduce( Fam, i![1], G, lmspos );
         cf:= List( [1..Length(bas)], x -> Zero( LeftActingDomain(K) ) );
         if b <> [] then
            deg:= b[1].deg;
            
            if Qs[deg] = [ ] then
               for k in [1,3..Length(b)-1] do
                   cf[ basinds[deg][ Position( Moninds[deg], b[k].no ) ] ]:= b[k+1];
               od;
            else
               cc:= List( Moninds[deg], x -> 0 );
               for k in [1,3..Length(b)-1] do
                   cc[ Position( Moninds[deg], b[k].no ) ]:= b[k+1];
               od;  

               cc:= cc*Qs[deg];  # this is now the list of coefficients of b wrt normbas...
                                 # in order to get normal form we "divide" by the torsion...
               for k in [1..Length(cc)] do 
                   if Tors[deg][k] <> 0 then
                      cc[k]:= cc[k] mod Tors[deg][k]; 
                   fi;
               od;
               for k in [1..Length(cc)] do
	           if not IsZero( basinds[deg][k] ) then
                      cf[basinds[deg][k]]:= cc[k];
		   fi;
               od;
            fi;
         fi;
         Add( g, cf*Basis(K) );
     od;
     SetGeneratorsImages( K, g );
     return K;

end;



# some functions for working with a linear span of elements of the free algebra.

LRPrivateFunctions.extended_make_basis:= function( fam, BB )

      # same as make_basis, only that it returns vectors and monomial indices as well

      local o, mninds, b, i, mat, cc, bas, mns, n, t, s, newmat;

      o:= fam!.ordering;
      mninds:= [ ];
      for b in BB do
          for i in [1,3..Length(b)-1] do
              if not b[i].no in mninds then Add( mninds, b[i].no ); fi;
          od;
      od;

      Sort( mninds, function( a, b ) return o[a] > o[b]; end );
      mat:= [ ];
      for b in BB do
          cc:= List( mninds, x -> 0 );
          for i in [1,3..Length(b)-1] do
             cc[ Position( mninds, b[i].no ) ]:= b[i+1];
          od;
          Add( mat, cc );
      od;

      mat:= HermiteNormalFormIntegerMat( mat );
        
      bas:= [ ];
      mns:= fam!.monomials;
      n:= Length( mninds );
      newmat:= [ ];
      for cc in mat do
          if cc <> 0*cc then
             b:= [ ];
             for i in [n,n-1..1] do
                 if cc[i] <> 0 then
                    Add( b, mns[ o[mninds[i]] ] );
                    Add( b, cc[i] );
                 fi;
             od;
             Add( bas, b );
             Add( newmat, cc );
          fi;
       
      od;      

      return [ bas, newmat, mninds ];

end;

LRPrivateFunctions.is_contained:= function( Fam, B, bas, mons, f )

    # Here B is a basis of elements of the free algebra, bas is the corresponding
    # basis in vectors, mons is a list of monomial indices occurring in B, the i-th
    # vector in bas corresponds to the i-th element in B via these monomials.
    # f is a new element. If it is in the span of B we do nothing, otherwise
    # we add it, obtaining a new B, bas, mons.
    # We assume that bas is in Hermite form.

    local v, k, pos, posv, list, iscontained, i;

    if f = [] then return [true,B,bas,mons]; fi;

    v:= List( mons, x -> 0 );
    for k in [1,3..Length(f)-1] do
        pos:= Position( mons, f[k].no );
        if pos = fail then
           list:= [ false ];
           Add( B, f );
           Append( list, LRPrivateFunctions.extended_make_basis( Fam, B ) );
           return list;
        else
           v[pos]:= f[k+1];
        fi;
    od;

    # try to reduce v to zero modulo bas:
    iscontained:= true;
    for i in [1..Length(bas)] do
        pos:= PositionProperty( bas[i], x -> x <> 0 );
        posv:= PositionProperty( v, x -> x<> 0 );
        if posv < pos then
           iscontained:= false;
           break;
        elif posv = pos then
           if v[posv] mod bas[i][pos] <> 0 then
              iscontained:= false;
              break;
           else
              v:= v - (v[posv]/bas[i][pos])*bas[i];
           fi;
        fi;
    od;

    if v <> 0*v then iscontained:= false; fi;
     
    if not iscontained then
       list:= [ false ];
       Add( B, f );
       Append( list, LRPrivateFunctions.extended_make_basis( Fam, B ) );
       return list;
    else
       return [ true, B, bas, mons ];
    fi;
end;


LRPrivateFunctions.add_elm_to_G:= function( Fam, G, lms, f )

   # Here G is a GB (i.e self reduced, monic). f is a monic element,
   # assumed reduced wrt G.
   # We add f to G. Maybe some elements of G reduce modulo f, so
   # we have to take them from G, reduce them modulo f, and if they
   # remain monic, to add them to G. The others will be returned.
   # Returned will be : the new G, new lms, the non monic elements that appeared.

   local U, V, lmsU, newelms, i, g, lg, m, c, k, eq, j, lms0, G0;

   U:= [ f ];
   V:= [ ];
   while U <> [ ] do
      lmsU:= LRPrivateFunctions.leading_mns( U );
      newelms:= [ ];
      for i in [1..Length(G)] do
          g:= G[i];
          lg:= Length(g);
          m:= g[lg-1];
          g:= LRPrivateFunctions.reduce0( Fam, g, U, lmsU );
          # this reduction might make g not reduced modulo the 
          # rest of G...
          eq:= true;
          if Length(g) <> Length( G[i] ) then
             eq:= false;
          else
             for j in [1,3..Length(g)-1] do
                 if g[j].no <> G[i][j].no or g[j+1] <> G[i][j+1] then
                    eq:= false; break;
                 fi;
             od;
          fi;
          if not eq then
             lms0:= ShallowCopy( lms );
             Unbind( lms0[i] );
             if Intersection( List( [1,3..Length(g)-1], x -> g[x].no ), 
                List( lms0, x -> x.no ) ) <> [ ] then
                G0:= ShallowCopy( G );
                Unbind( G0[i] );
                G0:= Filtered( G0, x -> IsBound(x) );
                lms0:= Filtered( lms0, x -> IsBound(x) );
                g:= LRPrivateFunctions.reduce0( Fam, g, G0, lms0 );
             fi;
          fi;
             
          if g <> [ ] then
             if g[Length(g)-1] = m then
                # leave it in G
                G[i]:= g;
             else
                Add( newelms, g );
                Unbind( G[i] );
                Unbind( lms[i] );
             fi;
          else
             Unbind( G[i] );
             Unbind( lms[i] );
          fi;
      od;
      G:= Filtered( G, x -> IsBound(x) );
      lms:= Filtered( lms, x -> IsBound( x ) );
      Append( G, U );
      Append( lms, lmsU );
           
      U:= [ ];
      for g in newelms do
          lg:= Length(g);
          c:= g[lg];
          if c=-1 then for k in [2,4..lg] do g[k]:= -g[k]; od; c:= 1; fi;
          if c = 1 then
             Add( U, g );
          else
             Add( V, g );
          fi;
      od;

      U:= LRPrivateFunctions.interreduce( Fam, U );
      Append( V, U[2] );
      U:= U[1];
   od;

   return [ G, lms, V ];

end;

LRPrivateFunctions.make_basis_NH:= function( Fam, G, lms, B, gen, dg )

   # When making the basis in the non hom case, new elements of lower degree
   # may turn up; we then have to perform the idclosure procedure...

   local made_basis, B0, newelms, f, lf, idclose, new0, new1, h, x, hh, bas, bas0, elms;

   made_basis:= false;
   while not made_basis do

      B0:= LRPrivateFunctions.make_basis( Fam, B ); 
      newelms:= [ ];
      made_basis:= true;
      for f in B0 do
          lf:= Length(f);
          if f[ lf-1 ].deg < dg and not f in B then
             made_basis:= false;
             idclose:=  [ f ];
             new0:= [ f ];
             bas:= LRPrivateFunctions.make_basis( Fam, idclose );
             while new0 <> [ ] do
                new1:= [ ];
                for h in new0 do
                    if h[ Length(h)-1 ].deg < dg then
                       for x in gen do
                           hh:= LRPrivateFunctions.reduce0( Fam, 
                              LRPrivateFunctions.dir_mult( Fam, x, h ), G, lms );
                           if hh <> [ ] then
                              elms:= ShallowCopy( idclose );
                              Add( elms, hh );
                              bas0:= LRPrivateFunctions.make_basis( Fam, elms );
                              if bas0 <> bas then
                                 Add( new1, hh );
                                 bas:= bas0;
                              fi;
                             
                           fi;
                       od;
                    fi;
                od;
                Append( idclose, new0 );
                new0:= new1;
             od;
             Append( newelms, idclose{[2..Length(idclose)]} );
          fi;
      od;
      B:= B0;
      Append( B, newelms );
   od;
   return B;

end;


LRPrivateFunctions.add_elm_to_B:= function( Fam, G, lms, B, bas, mons, dg, gen, f )

   # G a GB, B a basis of a space of normal monomials, id closed of degree dg.
   # We add f to B, so if the degree is lower, then we have to add more elements...
   # gen are the elements of degree 1, so the generators...

   # We assume that B is ideally closed of degree dg.
   # The result will have the same property...

   local list, B0, bas0, mons0, B1, bas1, mons1, made_basis, h, hh, x;


   list:= LRPrivateFunctions.is_contained( Fam, B, bas, mons, f );
   if not list[1] then
      B0:= list[2]; bas0:= list[3]; mons0:= list[4];
      B1:= B0; bas1:= list[3]; mons1:= list[4]; 
      made_basis:= false;
      while not made_basis do
          made_basis:= true;
          for h in B0 do
              list:= LRPrivateFunctions.is_contained( Fam, B, bas, mons, h );
              if not list[1] then

                 if h[ Length(h)-1 ].deg < dg then
                    for x in gen do
                        hh:= LRPrivateFunctions.reduce0( Fam, 
                            LRPrivateFunctions.dir_mult( Fam, x, h ), G, lms );
                        list:= LRPrivateFunctions.is_contained( Fam, B1, bas1, mons1, hh );
                        if not list[1] then
                           B1:= list[2]; bas1:= list[3]; mons1:= list[4];
                           made_basis:= false;
                        fi;
                    od;
                 fi;
              fi;
          od;
          B:= B0; bas:= bas0; mons:= mons0;
          B0:= B1; bas0:= bas1; mons0:= mons1; 
      od;
   fi;

   return [B,bas,mons];

end;

LRPrivateFunctions.IsFactor_yn:= function( a, m )

     # same as IsFactor, without the appliance.

     local da, dm, b, choices, points, mns, lr, c, k, fla;

     if a.deg > m.deg then return false; fi;
     if a.deg = m.deg then 
        if a.no=m.no then
           return true;
        else
           return false; 
        fi;
     fi;

     b:= m; 
     choices:= [ ];
     points:= [ b ];

     while true do

         if a.no=b.no then
            return true;
         fi;
         if IsBound(b.var) then
            # backtrack...
            k:= Length( choices );
            while k>=1 and choices[k] = 1 do k:= k-1; od;
            if k = 0 then return false; fi;
            choices:= choices{[1..k-1]}; points:= points{[1..k]};
           
            b:= points[k].right;
            Add( choices, 1 ); Add( points, b );
      
         else
            b:= b.left;
            Add( choices, 0 ); Add( points, b );
         fi;
     od;
end;


LRPrivateFunctions.is_self_red:= function( Fam, G )

     local i, f, H, lms, g;

     for i in [1..Length(G)] do
         if G[i][ Length(G[i]) ] <> 1 then return false; fi;
         f:= ShallowCopy( G[i] );
         H:= ShallowCopy( G );
         Unbind( H[i] ); H:= Filtered( H, x -> IsBound(x) );
         lms:= LRPrivateFunctions.leading_mns( H );
         g:= LRPrivateFunctions.reduce0( Fam, f, H, lms );
         if g <> G[i] then return false; fi;
     od;
     return true; 

end;


LRPrivateFunctions.FpLieRingNH:= function( A, RR, bound )

     # compute A/I, where I is the ideal gen by R along with Jacobi-s

     # NONhomogeneous case

     local zero, one, Fam, o, g, gens, B, Bk, Bd, G, BB, lms, lmspos, deg, deg_1,
           is_nilquot, rels, i, j, k, u, v, m1, m2, m3, f1, f2, f3, x, h, V, c, 
           list, bas, mons, lf, newB, m, b, mninds, mat, ss, Qs, Qi, tor, nocol,
           tors, basinds, r, T, entry, nilquot, f, res, cc, pos, newrls, is_hom_elm, 
           get_rid_of_hdeg, R, d, B0, ppos, cf, K;

     is_hom_elm:= function( u )

       local e, dg, j;

       e:= u![1];
       dg:= e[1].deg;
       for j in [3,5..Length(e)-1] do
           if e[j].deg <> dg then return false; fi;
       od;
       return true;

     end;

     get_rid_of_hdeg:= function( f, dd )

       # all mons of degree > dd are zero...
       local h, i;

       h:= [ ];
       for i in [1,3..Length(f)-1] do
           if f[i].deg <= dd then
              Add( h, f[i] ); Add( h, f[i+1] );
           else
              break;
           fi;
       od;
       return h;

     end;


     R:= ShallowCopy(RR);
     zero:= Zero( LeftActingDomain(A) );
     one:= One( LeftActingDomain( A ) );
     Fam:= ElementsFamily( FamilyObj( A ) );
     o:= Fam!.ordering;

     g:= GeneratorsOfAlgebra( A );
     gens:= List( g, x -> x![1] );
     B:= [ ];
     Bk:= [ ];
     Bd:= [ ];

     G:= [ ];
     BB:= [ ];    # G, BB will be the reduction pair...
     lms:= [ ];
     lmspos:= [];

     deg:= 1;
     deg_1:= 0;

     is_nilquot:= true;
     if bound = infinity then 
        is_nilquot:= false; 
        nilquot:= bound;
     else
        nilquot:= bound;        
        bound:= 2*bound;
     fi;

     while deg <= bound do

#Print(deg,"  ",is_self_red( Fam, G ),"\n");
#Print(deg,"\n");

       # First we make a potentially large set of new relations of degree deg,
       # that are in normal form wrt G. But they may still reduce modulo each other.


       rels:= [ ];
       if is_nilquot and deg >= nilquot+1 then  
          # we have to add all monomials of degree deg to the relations
          for i in [1..Length(Bd)] do
              for j in [i..Length(Bd)] do
                  if i+j = deg then
                     for m1 in Bd[i] do
                         for m2 in Bd[j] do
                             if  o[m1[1].no] < o[m2[1].no] then
                                 f:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                       LRPrivateFunctions.dir_monmult( Fam, m1, m2 ), G, lmspos );
                                 if f <> [] then
                                    Add( rels, f );
                                 fi;
                             fi;
                         od;
                     od;
                  fi;
              od;
          od;
       fi;

       if is_nilquot and deg = nilquot+1 then

          # we add all elements in the deg-th term of the lower central series
          # of the algebra that we got so far...
        
          B:= [ ];
          for i in [1..Length(Bd)] do Append( B, Bd[i] ); od;

          d:= 1;
          while d < deg do
              B0:= [ ];
              for m in Bd[1] do
                  for f in B do
                      Add( B0, get_rid_of_hdeg( LRPrivateFunctions.reduce0( 
                           Fam, LRPrivateFunctions.dir_mult( Fam, m, f ), G, lms ), nilquot ));
                  od;
              od;
              B0:= Filtered( B0, x -> not x = [ ] );
              B:= LRPrivateFunctions.make_basis( Fam, B0 );
              d:= d+1;
          od;
         
          Append( rels, B );

       fi;

       for r in R do
           if Degree(r) = deg then
              f:= get_rid_of_hdeg( r![1], nilquot );
              f:= LRPrivateFunctions.reduce0( Fam, f, G, lms );
              Add( rels, f );
           fi;
       od;

       if deg >= 3 and deg <= nilquot then

              for i in [1..Length(Bd[1])] do
                  m1:= Bd[1][i];
                  for u in [1..Length(Bd)] do
                      v:= deg-1-u;
                      if v > 0 and v <= Length( Bd ) then
                         for j in [1..Length(Bd[u])] do
                             m2:= Bd[u][j];
                             for k in [1..Length( Bd[v] )] do                                       
                                 m3:= Bd[v][k];
                                 if  o[m1[1].no] < o[m2[1].no] and 
                                     o[m2[1].no] < o[m3[1].no] then

                                    f1:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                           LRPrivateFunctions.dir_monmult( Fam, m2, m3 ), G, lmspos );
                                    f2:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                           LRPrivateFunctions.dir_monmult( Fam, m1, m2 ), G, lmspos );
                                    f3:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                           LRPrivateFunctions.dir_monmult( Fam, m3, m1 ), G, lmspos );

                                    f:= LRPrivateFunctions.special_mult( Fam, m1, f1, m3, f2, m2, f3 );    
                                    f:= LRPrivateFunctions.linalg_reduce( Fam, f, G, lmspos );  

                                    if f <> [] then
                                       Add( rels, f );
                                    fi;
 
                                 fi;
                                      
                             od;
                         od;
                      fi;
                  od;
              od;
       fi;

       # Now we have to do the following things:
       #
       #   * For all elements b\in B od degree deg-1, add (x,b) to the new relations, where
       #     x is a generator.
       #
       #   * If the degree of an element is equal to deg, then the element
       #     can only reduce modulo the other elements of the same degree, by a linalg 
       #     type reduction. We perform this reduction, and put the element in G if
       #     it is monic, in BB if it is not. 
       #
       #   * If the degree of the element is lower than deg (or the degree of the element
       #     from the previous step is such), and it is monic, then we put it in G, but have
       #     maybe to reduce existing elements modulo the new element. We remove the elements
       #     of G that have leading monomial divisible by the new one, from G, and append them
       #     to the list of new relations (after reduction mod new element).
       #
       #   * If the degree of the element is lower than deg, and it is not monic, then 
       #     we add it to BB, and add all relations that we get by multiplying by generators,
       #     until degree deg. 

       for f in BB do
           if f[Length(f)-1].deg = deg-1 then
              for x in gens do     
                  h:= LRPrivateFunctions.dir_mult( Fam, x, f );
                  Add( rels, h );
              od;
           fi;
       od;

       V:= [ ]; # elements to be added to BB
       for f in rels do
           f:= LRPrivateFunctions.reduce0( Fam, f, G, lms );
           if f <> [ ] then
              c:= f[ Length(f) ];
              if c = -1 then
                 for k in [2,4..Length(f)] do
                     f[k]:= f[k]*c;
                 od;
                 c:= 1;
              fi;
              if c = 1 then
                 res:= LRPrivateFunctions.add_elm_to_G( Fam, G, lms, f );
                 G:= res[1];
                 lms:= res[2];
                 Append( V, res[3] );
              else
                 Add( V, f );
              fi;
           fi;
       od;

       list:= LRPrivateFunctions.extended_make_basis( Fam, BB );
       BB:= list[1]; bas:= list[2]; mons:= list[3];

       for h in V do 
           list:= LRPrivateFunctions.add_elm_to_B( Fam, G, lms, BB, bas, mons, deg, gens, h );
           BB:= list[1]; bas:= list[2]; mons:= list[3];
       od;


       # We have to reduce the elements of BB modulo G MAYBE only in case
       # some lower deg element was added, and then only modulo the new ones.

       i:= 1;
       while i <= Length(BB) do
           f:= LRPrivateFunctions.reduce0( Fam, BB[i], G, lms );
           lf:= Length(f);
           if f = [ ] or BB[i] <> f then
              Unbind( BB[i] );
              BB:= Filtered( BB, x -> IsBound(x) );
              if f <> [ ] then
                 list:= LRPrivateFunctions.add_elm_to_B( Fam, G, lms, BB, bas, mons, deg, gens, f );
                 BB:= list[1]; bas:= list[2]; mons:= list[3];
              fi;
           else
              i:= i+1;
           fi;
       od;     
 
       
       # move monic elements to G...
       V:= [ ];
       for i in [1..Length(BB)] do
           f:= BB[i];
           lf:= Length(f);
           c:= f[lf];
           if c=-1 then for k in [2,4..lf] do f[k]:= -f[k]; od; c:= 1; fi;
           if c = 1 then
              res:= LRPrivateFunctions.add_elm_to_G( Fam, G, lms, f );
              G:= res[1];
              lms:= res[2];
              Append( V, res[3] );
              Unbind( BB[i] );
           fi;
       od;
       BB:= Filtered( BB, x -> IsBound(x) );

       lmspos:= [ ];
       for i in [1..Length(lms)] do
           lmspos[ lms[i].no ]:= i;
       od;

       # now we add the elements in V to BB, keeping it ideally closed...
       for f in V do
           list:= LRPrivateFunctions.add_elm_to_B( Fam, G, lms, BB, bas, mons, deg, gens, f );
           BB:= list[1]; bas:= list[2]; mons:= list[3];
       od;
       # in NONHOM case might also have to throw away old basis elements.

       for i in [1..Length(Bd)] do
           for j in [1..Length(Bd[i])] do
               for k in [1..Length(lms)] do
                     if LRPrivateFunctions.IsFactor_yn( lms[k], Bd[i][j][1] ) then 
                        Unbind( Bd[i][j] );
                        break;
                     fi;
               od;
           od;
           Bd[i]:= Filtered( Bd[i], x -> IsBound(x) );
       od;

       newB:= [ ];
       if deg <= nilquot then
          if deg = 1 then
             newB:= List( g, x -> x![1] );
             for i in [1..Length(newB)] do
                 m:= newB[i][1];
                 for j in [1..Length(lms)] do
                     if lms[j].no = m.no then 
                        Unbind( newB[i] ); break;
                     fi;
                 od;
             od;
             newB:= Filtered( newB, x -> IsBound(x) );
             gens:= newB;
             deg_1:= Length( newB );
          else
             newB:= [ ];
             for i in [1..deg_1] do
                 for k in [1..Length( Bk )] do
                     if Bd[1][i][1].no < Bk[k][1].no then
                        m:= LRPrivateFunctions.dir_monmult( Fam, Bd[1][i], Bk[k] );
                        if not IsBound( lmspos[m[1].no] ) then 
                           Add( newB, m );
                        fi;
                     fi;
                 od;
             od;
          fi;
       fi;

       # Note that newB is sorted small to big (follows from the above piece of code). 
       # In the next piece of
       # code elements are made with monomials in the order of newB; hence if
       # we later ObjByExtRep, then we have to have the right order...

       Bk:= newB;

       Add( Bd, newB );
       ppos:= Position( Bd, [ ] );

       if not is_nilquot and ppos <> fail and bound > 2*ppos-1 then
          bound:= 2*ppos-1;
          bound:= Maximum(bound,Maximum( List( R, x -> Degree(x) ) ) );
       fi;
       deg:= deg+1;      

     od;

     #End of main loop.

     newB:= [ ];
     for b in Bd do Append( newB, b ); od;
     # Sort newB in reverse order...
     Sort( newB, function(a,b) return a[1].no > b[1].no; end );
     mninds:= List( newB, x -> x[1].no );
     mat:= [ ];
     for b in BB do
         cc:= List( mninds, x -> 0 );
         for i in [1,3..Length(b)-1] do
             cc[ Position( mninds, b[i].no ) ]:= b[i+1];
         od;
         Add( mat, cc );
     od;
     if Length(mat) = 0 then mat:= [ List( mninds, x -> 0 ) ]; fi;
     ss:= SmithNormalFormIntegerMatTransforms( mat );
     Qs:= ss.coltrans;
     Qi:= ss.coltrans^-1;
     mat:= ss.normal;
      
     bas:= [ ];
     tor:= [ ];
     nocol:= Length( mninds );
     for k in [1..nocol] do
         cc:= Qi[k];
         b:= [ ];
         for i in [nocol,nocol-1..1] do
             if cc[i] <> 0 then
                Add( b, newB[ i ][1] );
                Add( b, cc[i] );
             fi;
         od;
         Add( bas, b );
         if k <= Length(mat) then
            Add( tor, mat[k][k] );
         else
            Add( tor, 0 );
         fi;
     od;      


     tors:= [ ];
     basinds:= [ ]; # list of indices of final basis, of the form [0,0,0,1,2,3,4,5,..]
                    # this means that the first three elements of the normal basis
                    # have torsion 1, then come the elements with index 1, 2, etc.

     k:= 1;
     for i in [1..Length(tor)] do
         if tor[i] = 1 then
            Add( basinds, 0 );
         else
            Add( basinds, k );
            Add( tors, tor[i] );
            k:= k+1;
         fi;
     od;

     r:= PositionProperty( tor, x -> x<> 1 );   # the first basis element which is not zero, we
                                                # begin counting from there.

     bas:= bas{[r..Length(bas)]};
     T:= EmptySCTable( Length( bas ), 0, "antisymmetric" );
     for i in [1..Length(bas)] do
         for j in [i+1..Length(bas)] do

                b:= LRPrivateFunctions.dir_mult( Fam, bas[i], bas[j] );
                if is_nilquot then b:= get_rid_of_hdeg( b, nilquot+1 ); fi;
             
                if b <> [] then

                   b:= LRPrivateFunctions.linalg_reduce( Fam, b, G, lmspos );
                  
                   v:= List( mninds, x -> 0 );
                   for k in [1,3..Length(b)-1] do
                       pos:= Position( mninds, b[k].no );
                       v[pos]:= b[k+1];
                   od;
                
                   cc:= v*Qs;     # so now cc is the list of coefficients wrt the normal basis.

                   for k in [1..Length(cc)] do 
                       if tor[k] <> 0 then
                          cc[k]:= cc[k] mod tor[k]; 
                       fi;
                   od;
                   entry:= [ ];
                   for k in [1..Length(cc)] do
                       if cc[k] <> 0 then
                          Add( entry, cc[k] );
                          Add( entry, basinds[k] );
                       fi;
                   od;
             
                   SetEntrySCTable( T, i, j, entry );
                fi;
             
         od;
     od;

     K:= LieRingByStructureConstants( tors, T );

     g:= [ ];
     for i in GeneratorsOfAlgebra(A) do
         b:= i![1];
         if is_nilquot then b:= get_rid_of_hdeg( b, nilquot+1 ); fi;
         cf:= List( [1..Length( bas )], x -> 0 );    
         if b <> [] then

            b:= LRPrivateFunctions.linalg_reduce( Fam, b, G, lmspos );
                  
            v:= List( mninds, x -> 0 );
            for k in [1,3..Length(b)-1] do
                pos:= Position( mninds, b[k].no );
                v[pos]:= b[k+1];
            od;
                
            cc:= v*Qs;     # so now cc is the list of coefficients wrt the normal basis.
            for k in [1..Length(cc)] do 
                if tor[k] <> 0 then
                   cc[k]:= cc[k] mod tor[k]; 
                fi;
            od;
            entry:= [ ];
            for k in [1..Length(cc)] do
                if cc[k] <> 0 and basinds[k] <> 0 then
                   cf[ basinds[k] ]:= cc[k];
                fi;
            od;
         fi;
         Add( g, cf*Basis(K) );
     od;
     SetGeneratorsImages( K, g );

     return K;

end;

InstallMethod( FpLieRing,
    "for free Lie algebra and list of its elements",
    true, [ IsFreeNAAlgebra, IsList ], 0,
    function( L, R )

     local bound, is_hom, r, eg, dg, k, K, genimgs, hom;

     bound:= ValueOption( "maxdeg" );
     if bound = fail then bound:= infinity; fi;

     R:= Filtered( R, x -> not IsZero(x) );

     # determine whether the relations are homogeneous.
     is_hom:= true;
     for r in R do
         eg:= r![1];
         dg:= eg[1].deg;
         for k in [3,5..Length(eg)-1] do
             if eg[k].deg <> dg then 
                is_hom:= false; break;
             fi;
         od;
         if not is_hom then break; fi;
     od;

     if is_hom then
        K:= LRPrivateFunctions.FpLieRingHOM( L, R, bound );
     else
        # for the moment we assume that all generators have degree 1 in this case...
        if not ForAll( GeneratorsOfAlgebra(L), x -> Degree(x)=1 ) then
           Error( "With non-homogeneous relations all generators should have degree 1.");
        fi;
        K:= LRPrivateFunctions.FpLieRingNH( L, R, bound );
     fi;

     genimgs:= GeneratorsImages( K );

     hom:= function( elm )

        local eval, e, len, res, i;

        eval:= function( expr )

            local a,b;
            if IsBound(expr.var) then
               return genimgs[ expr.var ];
            else
               a:= eval( expr.left );
               b:= eval( expr.right );
               return a*b;
            fi;
        end;

        e:= elm![1];
        len:= Length( e );
        res:= Zero( K );
        for i in [ 1, 3 .. len - 1 ] do
            res:= res + e[i+1]*eval( e[i] );
        od;
        return res;

     end;

     SetCanonicalProjection( K, hom );
     return K;

end );

