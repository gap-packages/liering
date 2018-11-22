#####################################################################################
#
#  fpla.gi                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 

LRPrivateFunctions.make_basis_field:= function( fam, BB )

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

      TriangulizeMat( mat );

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

LRPrivateFunctions.reduce_field:= function( fam, f, G, lms )

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
        if not IsOne(cf) then
           for i in [2,4..Length(r)] do r[i]:= r[i]/cf; od; 
        fi;
     fi;

     return r;

end;

LRPrivateFunctions.reduce_sorted:= function( fam, f, G, lms )

     # Here we do assume G to be monic, and that lms is sorted
 
     local lms0, ef, len, r, m, cf, a, g, mns, side, lg, i;

     if f=[] then return f; fi;
     if G = [ ] then return f; fi;

     lms0:= List( lms, x -> x.no );

     ef:= ShallowCopy( f );
     len:= Length(ef);

     r:= [ ];

     while len > 0 do
        m:= ef[ len-1 ]; cf:= ef[len];
        ef:= ef{[1..len-2]};
        len:= len-2;
  
        # look for a factor...
        a:= LRPrivateFunctions.search_factor( m, lms0 );
 
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
        if not IsOne(cf) then
           for i in [2,4..Length(r)] do r[i]:= r[i]/cf; od; 
        fi;
     fi;

     return r;

end;

LRPrivateFunctions.addElm_RedSet_field:= function( fam, f, G, lms )

    local newelms, len, h, n, Gh, i, g, pos;

    newelms:= [ f ];
    len:= 1;
    while len>0 do
       h:= newelms[len];
       newelms:= newelms{[1..len-1]};
       len:= len-1;
       h:= LRPrivateFunctions.reduce_sorted( fam, h, G, lms );

       if h <> [] then
          # we add it, but first we remove all elements of which the
          # leading monomial reduces mod h from G:
          n:= [ h[ Length(h)-1 ] ];
          Gh:= [ h ];
          for i in [1..Length(G)] do

              g:= LRPrivateFunctions.reduce_sorted( fam, G[i], Gh, n );
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
          pos:= PositionSorted( List(lms,x->x.no), n[1].no );
          CopyListEntries(G,pos,1,G,pos+1,1,Length(G)-pos+1);
          G[pos]:= h;
          CopyListEntries(lms,pos,1,lms,pos+1,1,Length(lms)-pos+1);
          lms[pos]:= n[1];
       fi;
    od;

    return [ G, lms ];

end;

LRPrivateFunctions.is_interred:= function( Fam, G )

   local i, j, h;

   for i in [1..Length(G)] do
       for j in [1..Length(G)] do
           if i <> j then
              h:= LRPrivateFunctions.reduce_sorted( Fam, G[i], [ G[j] ], [ G[j][Length(G[j])-1] ] );
              if h <> G[i] then
                 Print(i,"  ",j,"\n");
                 return false;
              fi;
           fi;
      od;
  od;
  return true;


end;

LRPrivateFunctions.interreduce_field:= function( fam, U )

   local G, lms, i, r, f, k, cf, lf;

   for i in [1..Length(U)] do
       if U[i] = [ ] then
          Unbind( U[i] );
       fi;
   od;
   U:= Filtered( U, x -> IsBound(x) );

   if U = [] then return U; fi;

   Sort( U, function(u,v) return u[Length(u)-1].deg < v[Length(v)-1].deg; end );

   for i in [1..Length(U)] do
       f:= ShallowCopy(U[i]); lf:= Length(f);
       cf:= f[lf];
       if not IsOne( cf ) then 
          for k in [2,4..lf] do f[k]:= f[k]/cf; od;
          U[i]:= f;
       fi;
   od;

   G:= [ U[1] ];
   lms:= [ U[1][ Length(U[1])-1 ] ];
   for i in [2..Length(U)] do
       r:= LRPrivateFunctions.addElm_RedSet_field( fam, U[i], G, lms );
       G:= r[1]; lms:= r[2];
   od;

   return G;

end;


InstallMethod( FpLieAlgebra,
    "for free Lie algebra and list of its elements",
    true, [ IsFreeNAAlgebra, IsList ], 0,
    function( A, RR )

     # compute A/I, where I is the ideal gen by R along with Jacobi s

     local one, Fam, o, g, B, Bk, Bd, G, lms, lmspos, deg, bound, is_hom, r, eg, 
           dg, k, rels, i, f, c, j, lowdeg, lmsr, lmsposr, nonleadingr, a1, a2, a3, a4,
           m1, m2, m3, u, v, f1, f2, f3, lf, m, newB, T, cc, is_nilquot, nilquot, basinds,
           newrls, is_hom_elm, get_rid_of_hdeg, x, R, B0, d, diff_degree, K, cf, hom;

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

     R:= ShallowCopy( RR );
     R:= Filtered( R, x -> not IsZero(x) );
     one:= One( LeftActingDomain( A ) );

     Fam:= ElementsFamily( FamilyObj( A ) );
     o:= Fam!.ordering;

     g:= GeneratorsOfAlgebra( A );

     diff_degree:= Length( Set( List( g, Degree ) ) ) > 1;

# i.e., if the degrees of the generators are different, then we
# loop until the bound, and we do not care about homogeneous components
# that are zero.

     Bk:= [ ];
     Bd:= [ ];
    
     G:= [ ];
     lms:= [ ];
     lmspos:= [];

     deg:= 1;

     bound:= ValueOption( "maxdeg" );
     if bound = fail then 
        bound:= infinity; 
        is_nilquot:= false;
        nilquot:= bound;
     else
        is_nilquot:= true;
        nilquot:= bound;
     fi;

     # determine whether the relations are homogeneous.
     is_hom:= true;
     for r in RR do
         eg:= r![1];
         dg:= eg[1].deg;
         for k in [3,5..Length(eg)-1] do
             if eg[k].deg <> dg then 
                is_hom:= false; break;
             fi;
         od;
         if not is_hom and is_nilquot then bound:= 2*bound; break; fi;
     od;

     while deg <= bound do

       rels:= [ ];

       if is_nilquot and deg = nilquot+1 then  # ONLY in nonhom case!!!
          # we have to add all monomials of degree deg to the relations
          for i in [1..Length(Bd)] do
              for j in [i..Length(Bd)] do
                  if i+j = deg then
                     for m1 in Bd[i] do
                         for m2 in Bd[j] do
                             if  o[m1[1].no] < o[m2[1].no] then
                                 Add( rels, LRPrivateFunctions.dir_monmult( Fam, m1, m2 ) );
                             fi;
                         od;
                     od;
                  fi;
              od;
          od;

          # we add all monomials in the deg-th term of the lower central series
          # of the algebra that we got so far...

          B:= [ ];
          for i in [1..Length(Bd)] do Append( B, Bd[i] ); od;

          d:= 1;
          while d < deg do
              B0:= [ ];
              for m in Bd[1] do
                  for f in B do
                      Add( B0, get_rid_of_hdeg( LRPrivateFunctions.reduce_field( Fam, 
                        LRPrivateFunctions.dir_mult( Fam, m, f ), G, lms ), nilquot ));
                  od;
              od;
              B0:= Filtered( B0, x -> not x = [ ] );
              B:= LRPrivateFunctions.make_basis_field( Fam, B0 );
              d:= d+1;
          od;
         
          Append( rels, B );

       fi;

       for r in R do
           if Degree(r) = deg then
              if is_nilquot then
                 f:= get_rid_of_hdeg( r![1], nilquot );
              else
                 f:= r![1];
              fi;
              Add( rels, f );
           fi;
       od;

       rels:= LRPrivateFunctions.interreduce_field( Fam, rels );

       for i in [1..Length(rels)] do
           f:= ShallowCopy( LRPrivateFunctions.reduce_field( Fam, rels[i], G, lms ) );
           if f <> [ ] then
              c:= f[Length(f)];
              if not IsOne(c) then for j in [2,4..Length(f)] do f[j]:= f[j]/c; od; fi;
              rels[i]:= f;
           else
              Unbind( rels[i] );
           fi;
       od;

       rels:= Filtered( rels, x -> IsBound(x) );

       lowdeg:= not ForAll( rels, x -> x[ Length(x)-1 ].deg = deg );
       lmsr:= LRPrivateFunctions.leading_mns( rels );
       lmsposr:= [ ];
       for i in [1..Length(lmsr)] do
           lmsposr[ lmsr[i].no ]:= i;
           if lmsr[i].deg < deg then lowdeg:= true; fi;
       od;

       nonleadingr:= [ ];
       for r in rels do
           for k in [1,3..Length(r)-3] do
               AddSet( nonleadingr, r[k].no );
           od;
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

                                   if not is_hom then
                                      f:= LRPrivateFunctions.linalg_reduce( Fam, f, G, lmspos );
                                   fi;

                                   f:= LRPrivateFunctions.linalg_reduce( Fam, f, rels, lmsposr );

                                   if f <> [] then
                                      lf:= Length(f); 
                                      c:= f[ lf ];
                                      if not IsOne(c) then for i in [2,4..lf] do f[i]:= f[i]/c; od; fi;

                                      if f[ Length(f)-1 ].no in nonleadingr then
                                         rels:= LRPrivateFunctions.linalg_reduce_allbyone( Fam, f, rels );
                                      fi;

                                      Add( rels, f );
                                      for r in [1,3..lf-3] do
                                          AddSet( nonleadingr, f[r].no );
                                      od; 
                                      m:= f[ lf -1 ];
                                      lmsposr[ m.no ]:= Length( rels );
                                      if m.deg < deg then lowdeg:= true; fi; 
                                   fi;
                               fi;
                            od; 
                         fi; 
                     od;
                  fi;
              od;
          od;

       fi;

       if is_hom then         
          Append( G, rels );
       else 
          if lowdeg then
             SortParallel( lms, G, function( u,v) return u.no < v.no; end );
             for i in [1..Length(rels)] do
                 r:= LRPrivateFunctions.addElm_RedSet_field( Fam, rels[i], G, lms );
                 G:= r[1]; lms:= r[2];
             od;
          else
             Append( G, rels );   
          fi;
       fi;

       for i in [1..Length(G)] do
           c:= G[i][ Length( G[i] ) ];
           if not IsOne(c) then
              for j in [2,4..Length(G[i])] do G[i][j]:= G[i][j]/c; od;
           fi;
       od;

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
       Add( Bd, newB );

       # maybe throw away some old basis elements (only in non-hom case!)
       if not is_hom and lowdeg then
          for i in [1..Length(Bd)] do
              for j in [1..Length(Bd[i])] do
                  m:= Bd[i][j][1];
                  for k in [1..Length(lms)] do
                      if LRPrivateFunctions.IsFactor_yn( lms[k], m ) then
                         Unbind( Bd[i][j] ); break;
                      fi;
                  od;
              od;
              Bd[i]:= Filtered( Bd[i], x -> IsBound(x) );
          od;
       fi;

       Bk:= Bd[ Length( Bd ) ];

       if Bk = [ ] and not diff_degree then
          c:= 1; 
          while Bd[c] <> [ ] do c:= c+1; od;
          bound:= 2*c-1;
          bound:= Maximum(bound,Maximum( List( R, x -> Degree(x) ) ) );
       fi;

       if is_hom and deg = nilquot then
          # we are done...
          deg:= bound+1;
       else
          deg:= deg+1;      
       fi;

     od;

     B:= [];
     for i in [1..Length(Bd)] do Append( B, Bd[i] ); od;

     basinds:= [ ];
     for i in [1..Length(B)] do
         basinds[ B[i][1].no ]:= i;
     od;

     T:= EmptySCTable( Length(B), Zero( LeftActingDomain(A) ), "antisymmetric" );

     for i in [1..Length(B)] do
         for j in [i+1..Length(B)] do
             if not( is_nilquot and B[i][1].deg + B[j][1].deg > nilquot ) then
                eg:= LRPrivateFunctions.linalg_reduce_onemon( Fam, 
                          LRPrivateFunctions.dir_monmult( Fam, B[i], B[j] ), G, lmspos );

                cc:= [ ];
                for k in [1,3..Length(eg)-1] do
                    Add( cc, eg[k+1] );
                    Add( cc, basinds[eg[k].no] );
                od;
                SetEntrySCTable( T, i, j, cc );
             fi;
         od;
     od; 

     K:= LieAlgebraByStructureConstants( LeftActingDomain(A), T );

     g:= [ ];
     for i in GeneratorsOfAlgebra(A) do
         eg:= LRPrivateFunctions.linalg_reduce_onemon( Fam, i![1], G, lmspos );
         cf:= List( [1..Dimension(K)], x -> Zero( LeftActingDomain(K) ) );
         for k in [1,3..Length(eg)-1] do
             cf[basinds[eg[k].no]]:= eg[k+1];
         od;    
         Add( g, cf*Basis(K) );
     od;
     SetGeneratorsImages( K, g );

     hom:= function( elm )

        local eval, e, len, res, i;

        eval:= function( expr )

            local a,b;
            if IsBound(expr.var) then
               return g[ expr.var ];
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


