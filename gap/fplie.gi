#####################################################################################
#
#  fplie.gi                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 


# Functions for working with free algebras.
# first we install the record containing all 
# sorts of functions we want to write protect

InstallValue( LRPrivateFunctions, rec() );

############################################################################
##
#M  ObjByExtRep( <fam>, <list> )
#M  ExtRepOfObj( <obj> )
#
InstallMethod( ObjByExtRep,
   "for family of FAlg elements, and list",
   true, [ IsFAlgElementFamily, IsList ], 0,
   function( fam, list )

    return Objectify( fam!.defaultType,
                    [ Immutable(list) ] );
end );

InstallMethod( ExtRepOfObj,
   "for an FAlg element",
   true, [ IsFAlgElement ], 0,
   function( obj )

   return obj![1];

end );

InstallMethod( PrintObj,
    "for FAlg element",
    [ IsFAlgElement ],
    function( elm )

    local names, print, e, i, len;

    names:= FamilyObj( elm )!.names;
    print:= function( expr )

      if IsBound(expr.var) then
        Print( names[ expr.var ] );
      else
        Print( "(" );
        print( expr.left );
        Print( "," );
        print( expr.right );
        Print( ")" );
      fi;
    end;

    e:= elm![1];
    len:= Length( e );
    for i in [ 1, 3 .. len - 1 ] do
        if not IsOne( e[i+1] )  then
           Print( "(",e[i+1],")*");
        fi;
        if i < len-1 then
           print( e[i] ); Print("+");
        else
           print( e[i] );
        fi;
    od;
    if len = 0 then
      Print( "0" );
    fi;
    end );

#############################################################################
##
#M  ZeroOp( <m> ) . . . . . . . . . . . . . . .  for a Falg element
#M  \<( <m1>, <m2> ) . . . . . . . . . . . . . . for two Falg elements
#M  \=( <m1>, <m2> ) . . . . . . . . . . . . . . for two Falg elements
#M  \+( <m1>, <m2> ) . . . . . . . . . . . . . . for two Falg elements
#M  \-( <m> )     . . . . . . . . . . . . . . for a Falg element
#M  \in( <U>, <u> )  . . . . . . . . . . . . . . for Free algebra, and element
##
InstallMethod( ZeroOp,
        "for FAlg element",
        true, [ IsFAlgElement ], 0,
        function( x )

    return ObjByExtRep( FamilyObj( x ), [ ] );

end );


InstallMethod( \<,
                "for two FAlg elements",
        IsIdenticalObj, [ IsFAlgElement, IsFAlgElement ], 0,
        function( x, y )
    return x![1]< y![1];
end );

InstallMethod( \=,
                "for two FAlg elements",
        IsIdenticalObj, [ IsFAlgElement, IsFAlgElement], 0,
        function( x, y )

    local len, i;
    return x![1] = y![1];
end );


LRPrivateFunctions.direct_sum:= function( F, x, y )

    local sum,z,mons,o,ord;

    o:= F!.ordering;

    ord:= function( a, b )
       return o[a.no] < o[b.no];
    end;

    sum:= ZIPPED_SUM_LISTS( x, y, F!.zeroCoefficient, [ ord, \+ ] ); 
    return sum;

end;

InstallMethod( \+,
        "for two FAlg elements",
        true, [ IsFAlgElement, IsFAlgElement ], 0, 
        function( x, y )
    local F;
    F:= FamilyObj(x);
    return ObjByExtRep( F, LRPrivateFunctions.direct_sum( F, x![1], y![1] ) );

end );

LRPrivateFunctions.dir_monmult:= function( F, x, y )

    local T, mons, o, ord_1, a, b, c, i, j, t1, t2, s1, r, pos, num, p, s; 

    T:= F!.multTable;
    mons:= F!.monomials;
    o:= F!.ordering;

    ord_1:= function( mon1, mon2 )


         if mon1.no = mon2.no then return false; fi;
         if mon1.deg <> mon2.deg then return mon1.deg < mon2.deg; fi;
         if mon1.left.no <> mon2.left.no then return o[mon1.left.no] < o[mon2.left.no]; fi;
         return o[mon1.right.no] < o[mon2.right.no]; 

    end;

    a:= x[1]; b:= y[1];
    c:= x[2]*y[2];
    i:= a.no; j:= b.no;

    if F!.sign = -1 then

        if i = j then return [ a, 0*c ]; fi; 
        if i > j then
           t1:= j; t2:= i;
           s1:= -1;
        else
           t1:= i; t2:= j;
           s1:= 1;
        fi;
        if IsBound( T[t1] ) and IsBound( T[t1][t2] ) then
           r:= T[t1][t2];
           pos:= o[ r[1] ];
           return [ mons[pos], s1*r[2]*c ];
        fi;
        # If we arrive here then the product is not known yet.
        num:= Length( mons ) + 1; # number of new monomial...

        if o[i] < o[j] then
           # i.e., a < b
           p:= rec( no:= num, deg:= a.deg+b.deg, left:= a, right:= b );
           s:= 1;
        else   
           p:= rec( no:= num, deg:= a.deg+b.deg, left:= b, right:= a );
           c:= -c;
           s:= -1;
        fi;

        if not IsBound( T[t1] ) then T[t1]:= [ ]; fi;
        T[t1][t2]:= [ num, s*s1 ]; 
        F!.multTable:= T;

        # now we have to insert p in the sorted list of monomials...
        
        pos:= POSITION_SORTED_LIST_COMP( mons, p, ord_1 );
        for i in [pos..Length(o)] do o[ mons[i].no ]:= o[ mons[i].no ]+1; od;
        Add( o, pos );

        CopyListEntries(mons,pos,1,mons,pos+1,1,Length(mons)-pos+1);
        mons[pos]:= p;

        F!.monomials:= mons;
        F!.ordering:= o;

        return [ p, c ]; 

    else
       # The extremely free multiplication...

       if IsBound( T[i] ) and IsBound( T[i][j] ) then
          r:= T[i][j];
          pos:= o[ r ];
          return [ mons[pos], c ];
       fi;
       # If we arrive here then the product is not known yet.
       num:= Length( mons ) + 1; # number of new monomial...
       p:= rec( no:= num, deg:= a.deg+b.deg, left:= a, right:= b );

       if not IsBound( T[i] ) then T[i]:= [ ]; fi;
       T[i][j]:= num; 
       F!.multTable:= T;

       # now we have to insert p in the sorted list of monomials...
       pos:= POSITION_SORTED_LIST_COMP( mons, p, ord_1 );

       for i in [pos..Length(o)] do o[ mons[i].no ]:= o[ mons[i].no ]+1; od;
       Add( o, pos );

       CopyListEntries(mons,pos,1,mons,pos+1,1,Length(mons)-pos+1);
       mons[pos]:= p;

       F!.monomials:= mons;
       F!.ordering:= o;

       return [ p, c ]; 
       
    fi;

end;

LRPrivateFunctions.monmult:= function( x, y )

    local F;

    F:= FamilyObj(x);
    return ObjByExtRep( F, LRPrivateFunctions.dir_monmult( F, x![1], y![1] ) );
       
end;


LRPrivateFunctions.dir_mult:= function( F, x, y )

    local o, ord, mns, cfs, i, j, l, res, len;

    o:= F!.ordering;

    ord:= function( a, b )
       return o[a.no] < o[b.no];
    end;

# Keeping it sorted might make it faster!!

    mns:= []; cfs:= [];
    for i in [1,3..Length(x)-1] do
        for j in [1,3..Length(y)-1] do
            l:= LRPrivateFunctions.dir_monmult( F, [x[i],x[i+1]], [y[j],y[j+1]] );
            if not IsZero( l[2] ) then
               Add( mns, l[1] ); Add(cfs, l[2] );
            fi;
        od;
    od;

    SortParallel( mns, cfs, ord );

    res:= [];
    len:= -1;
    for i in [1..Length(mns)] do
        if len > 0 and mns[i].no = res[len].no then
           res[len+1]:= res[len+1]+cfs[i];
        else
           Add( res, mns[i] ); Add( res, cfs[i] );
           len:= len+2;
        fi;
    od; 
    for i in [2,4..Length(res)] do
        if IsZero(res[i]) then
           Unbind( res[i-1] ); Unbind( res[i] );
        fi;
    od;
    res:= Filtered( res, x -> IsBound(x) );

    return res;

end;

InstallMethod( \*,
        "for two FAlg elements",
        true, [ IsFAlgElement, IsFAlgElement ], 0, 
        function( x, y )
    local F;
    F:= FamilyObj(x);
    return ObjByExtRep( F, LRPrivateFunctions.dir_mult( F, x![1], y![1] ) ); 
end);

LRPrivateFunctions.special_mult:= function( F, x1, f1, x2, f2, x3, f3 )

    # compute x1f1 + x2f2 + x3f3, where the xi are monomials

    local T, mons, o, ord_1, mon_prod, ord, mns, cfs, i, j, l, res, len,t, e1, e2;

    T:= F!.multTable;
    mons:= F!.monomials;
    o:= F!.ordering;

    ord_1:= function( mon1, mon2 )


         if mon1.no = mon2.no then return false; fi;
         if mon1.deg <> mon2.deg then return mon1.deg < mon2.deg; fi;
         if mon1.left.no <> mon2.left.no then return o[mon1.left.no] < o[mon2.left.no]; fi;
         return o[mon1.right.no] < o[mon2.right.no]; 

    end;

    if F!.sign = -1 then

       mon_prod:= function( a, b, ca, cb )
           local c, p, i, j, r, pos, num, pi, pj, s, mmm, t1, t2, s1;
           c:= ca*cb;
           i:= a.no; j:= b.no;
           if i = j then return [ a, 0*c ]; fi; 
           if i > j then
              t1:= j; t2:= i;
              s1:= -1;
           else
              t1:= i; t2:= j;
              s1:= 1;
           fi;

           if IsBound( T[t1] ) and IsBound( T[t1][t2] ) then
              r:= T[t1][t2];
              pos:= o[ r[1] ];
              return [ mons[pos], s1*r[2]*c ];
           fi;
           # If we arrive here then the product is not known yet.
           num:= Length( mons ) + 1; # number of new monomial...

           if o[i] < o[j] then
              # i.e., a < b
              p:= rec( no:= num, deg:= a.deg+b.deg, left:= a, right:= b );
              s:= 1;
           else   
              p:= rec( no:= num, deg:= a.deg+b.deg, left:= b, right:= a );
              c:= -c;
              s:= -1;
           fi;

           if not IsBound( T[t1] ) then T[t1]:= [ ]; fi;
           T[t1][t2]:= [ num, s*s1 ]; 
           F!.multTable:= T;

           # now we have to insert p in the sorted list of monomials...
           pos:= POSITION_SORTED_LIST_COMP( mons, p, ord_1 );

           for i in [pos..Length(o)] do o[ mons[i].no ]:= o[ mons[i].no ]+1; od;
           Add( o, pos );

           CopyListEntries(mons,pos,1,mons,pos+1,1,Length(mons)-pos+1);
           mons[pos]:= p;

           F!.monomials:= mons;
           F!.ordering:= o;

           return [ p, c ]; 
       end;

    fi;

    ord:= function( a, b )
       return o[a.no] < o[b.no];
    end;

    e1:= [ ];
    for i in [1,3..Length(f1)-1] do
        l:= mon_prod( x1[1], f1[i], x1[2], f1[i+1] );
        if not IsZero( l[2] ) then
           Append( e1, l );
        fi;
    od;
    e2:= [ ];
    for i in [1,3..Length(f2)-1] do
        l:= mon_prod( x2[1], f2[i], x2[2], f2[i+1] );
        if not IsZero( l[2] ) then
           Append( e2, l );
        fi;
    od;
    res:= ZIPPED_SUM_LISTS( e1, e2, F!.zeroCoefficient, [ ord, \+ ] ); 
    e2:= [ ];
    for i in [1,3..Length(f3)-1] do
        l:= mon_prod( x3[1], f3[i], x3[2], f3[i+1] );
        if not IsZero( l[2] ) then
           Append( e2, l );
        fi;
    od;

    return ZIPPED_SUM_LISTS( res, e2, F!.zeroCoefficient, [ ord, \+ ] ); 


end;


InstallMethod( AdditiveInverseSameMutability,
        "for FAlg element",
        true, [ IsFAlgElement ], 0,
        function( x )

    local   ex,  i;

    ex:= ShallowCopy(x![1]);
    for i in [2,4..Length(ex)] do
        ex[i]:= -ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end );

InstallMethod( AdditiveInverseMutable,
        "for FAlg element",
        true, [ IsFAlgElement ], 0,
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
#M  \*( <scal>, <m> ) . . . . . . . . .for a scalar and a FAlg element
#M  \*( <m>, <scal> ) . . . . . . . . .for a scalar and a FAlg element
##
InstallMethod( \*,
        "for scalar and FAlg element",
        true, [ IsScalar, IsFAlgElement ], 0,
        function( scal, x )

    local   ex,  i;
    
    if IsZero( scal ) then return Zero(x); fi;
    ex:= ShallowCopy( x![1] );
    for i in [2,4..Length(ex)] do
        ex[i]:= scal*ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end);

InstallMethod( \*,
        "for FAlg element and scalar",
        true, [ IsFAlgElement, IsScalar ], 0,
        function( x, scal )

    local   ex,  i;
    
    if IsZero( scal ) then return Zero(x); fi;
    ex:= ShallowCopy( x![1] );
    for i in [2,4..Length(ex)] do
        ex[i]:= scal*ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end);

InstallMethod( \in,
        "for FAlg element and free algebra",
        true, [ IsFAlgElement, IsFreeNAAlgebra ], 0,
        function( u, U )
    return IsIdenticalObj( ElementsFamily( FamilyObj(U) ), FamilyObj(u) );
end );


InstallMethod( Degree, "FAlg elements", true, [ IsFAlgElement ], 0, 
   function(x) 
    x:= x![1];
    return x[ Length(x)-1 ].deg ;
end );



LRPrivateFunctions.FreeNonassociativeAlgebra:= function( arg )

    local R,          # coefficients ring
          names,      # names of the algebra generators
          F,          # family of elements
          one,        # identity of `R'
          zero,       # zero of `R'
          A, sign, g, gr, ord;          


    R:= arg[1];

    # Construct names of generators.
    if IsInt( arg[2] ) then

      names:= List( [ 1 .. arg[2] ],
                    i -> Concatenation( "x", String(i) ) );
    elif IsList( arg[2] ) then
      names:= arg[2];
    else
      Error( "The second argument to FreeNonassociativeAlgebra has to be an integer, or a list" ); 
    fi;

    if Length(arg) >= 3 then
       if arg[3] in [1,-1] then
          sign:= arg[3];
       else
          Error("The third argument to FreeNonassociativeAlgebra must be 1, or -1 ");
       fi;
    else
       sign:= 1;
    fi;

    if Length( arg ) = 4 then
       gr:= arg[4];
    else
       gr:= List( names, x -> 1 );
    fi;

    F:= NewFamily( "FreeAlgebraEltFamily", IsFAlgElement );

    if IsField(R) then
       F!.isfield_basering:= true;
    elif R=Integers then
       F!.isfield_basering:= false;
    else
       Error("The only allowed base rings are fields and the Integers");
    fi;
       

    one:= One( R );
    zero:= Zero( R );

    F!.defaultType := NewType( F, IsFAlgElement );
    F!.zeroCoefficient    := zero;
    F!.names       := names;
    F!.sign:= sign;

    A:= Objectify( NewType( CollectionsFamily( F ),
                                IsFreeNAAlgebra
                            and IsAttributeStoringRep ),
                   rec() );

    SetLeftActingDomain( A, R );
    g:= List( [1..Length(names)],
              x -> ObjByExtRep( F, [ rec( no:= x, deg:=gr[x], var:= x ), one ] ) );
    F!.monomials:= List( g, u -> ExtRepOfObj( u )[1] );
    F!.multTable:= [];
    ord:= List( [1..Length(names)], x -> x );
    SortParallel( gr, ord );
    F!.ordering:= ord; 
    SetGeneratorsOfLeftOperatorRing( A, g );

    return A;

end;

InstallAccessToGenerators( IsFreeNAAlgebra,
                           "free algebra",
                           GeneratorsOfLeftOperatorRing );

InstallMethod( FreeLieRing,
    "for a ring and list",
    true,
    [ IsRing, IsList ], 0,
    function( R, names )

    # Check the argument list.
    if not IsRing( R ) then
      Error( "first argument must be a ring" );
    fi;

    if not ForAll( names, IsString ) then
       Error("second argument must be a list of strings");
    fi;

    return LRPrivateFunctions.FreeNonassociativeAlgebra( R, names, -1 );

end );

InstallOtherMethod( FreeLieRing,
    "for a ring and list and list",
    true,
    [ IsRing, IsList, IsList ], 0,
    function( R, names, grad )

    # Check the argument list.
    if not IsRing( R ) then
      Error( "first argument must be a ring" );
    fi;

    if not ForAll( names, IsString ) then
       Error("second argument must be a list of strings");
    fi;

    return LRPrivateFunctions.FreeNonassociativeAlgebra( R, names, -1, grad );

end );

InstallOtherMethod( FreeLieRing,
    "for a ring and an integer",
    true,
    [ IsRing, IsInt ], 0,
    function( R, k )

    # Check the argument list.
    if not IsRing( R ) then
      Error( "first argument must be a ring" );
    fi;

    return LRPrivateFunctions.FreeNonassociativeAlgebra( R, k, -1 );

end );

InstallOtherMethod( FreeLieRing,
    "for a ring and an integer",
    true,
    [ IsRing, IsInt, IsList ], 0,
    function( R, k, grad )

    # Check the argument list.
    if not IsRing( R ) then
      Error( "first argument must be a ring" );
    fi;

    return LRPrivateFunctions.FreeNonassociativeAlgebra( R, k, -1, grad );

end );


InstallMethod( PrintObj,
    "for a nonassociative algebra",
    true,
    [ IsFreeNAAlgebra ], 0,
    function( A )

    local g, i; 

    Print("<Free algebra over ",LeftActingDomain(A)," generators: " );
    g:= GeneratorsOfAlgebra(A);
    for i in [1..Length(g)-1] do 
        Print( g[i], ", " ); 
    od;
    Print( g[ Length(g) ], " >" );
    

end );


InstallMethod( ViewObj,
    "for a nonassociative algebra",
    true,
    [ IsFreeNAAlgebra ], 0,
    function( A )

    local g, i; 

    Print("<Free algebra over ",LeftActingDomain(A)," generators: " );
    g:= GeneratorsOfAlgebra(A);
    for i in [1..Length(g)-1] do 
        Print( g[i], ", " ); 
    od;
    Print( g[ Length(g) ], " >" );
    

end );

InstallMethod( PrintObj,
    "for a reduced set",
    true,
    [ IsReducedSetOfFAE ], 0,
    function( G )

    Print("<Reduced set of free algebra elements>" );

end );

InstallMethod( ViewObj,
    "for a reduced set",
    true,
    [ IsReducedSetOfFAE ], 0,
    function( G )

    Print("<Reduced set of free algebra elements>" );

end );


InstallMethod( AsSSortedList,
    "for a reduced set",
    true,
    [ IsReducedSetOfFAE ], 0,
    function( G )

    return G!.elements;

end );

LRPrivateFunctions.search_factor:= function( m, lms )

     # here m is a monomial in ext rep; lms is a sorted list of monomial 
     # numbers of leading monomials. We search a leading monomial that is
     # a factor in m; if found then a list is returned with in the first
     # position the value true, in the second position, the position of the
     # factor in lms, and the third and fourth positions contain lists that
     # describe the correponding appliance (first the list of monomials, than
     # a list of 0,1; 0 means: mult on the left, 1 means mult on the right).
     # if no factor is found the list [false] is returned.

     local b, choices, points, pos, mns, lr, c, k;
    

     b:= m; 
     choices:= [ ];
     points:= [ b ];

     while true do

        pos:= PositionSorted( lms, b.no );       
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


LRPrivateFunctions.ReduceElmFreeAlg:= function( fam, f, G, lms, minus )

     local ef, len, r, a, g, lg, mns, side, i, m, cf, cg, rem, q; 

     # Here f is an elem of a free algeb in ext rep,
     # fam is its family, G is a list of elements of
     # the same free alg, but in wrapped rep, lms is a list
     # of the numbers of the leading monomials of G, 
     # minus is a boolean, if true then the result is normalised
     # i.e., multiplied by an appropriate unit.

     if f=[] then return f; fi;
     if G = [ ] then
        if minus then
           f:= ShallowCopy(f);
           cf:= f[Length(f)]; 
           if fam!.isfield_basering then
              if not IsOne(cf) then
                 for i in [2,4..Length(f)] do
                     f[i]:= f[i]/cf;
                 od;
              fi;
           else
              if cf < 0 then
                 for i in [2,4..Length(f)] do
                     f[i]:= -f[i];
                 od;
              fi;
           fi;
        fi;
        return f; 
     fi;

     ef:= ShallowCopy( f );
     len:= Length(ef);

     r:= [ ];

     if fam!.isfield_basering then
        while len >0 do
           m:= ef[ len-1 ]; cf:= ef[len];
           ef:= ef{[1..len-2]};
           len:= len-2;
  
           # look for a factor...
           a:= LRPrivateFunctions.search_factor( m, lms );
 
           if a[1] then
              g:= ShallowCopy(G[a[2]]![1]);
              mns:= a[3];
              side:= a[4];
              lg:= Length(g);
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

        if r <> [ ] and minus then
           cf:= r[Length(r)];
           if not IsOne(cf) then
              for i in [2,4..Length(r)] do r[i]:= r[i]/cf; od; 
           fi;
        fi;

     else
        # so the base ring is the integers...
        while len >0 do
           m:= ef[ len-1 ]; cf:= ef[len];
           ef:= ef{[1..len-2]};
           len:= len-2;
  
           # look for a factor...
           a:= LRPrivateFunctions.search_factor( m, lms );
 
           if a[1] then
              g:= ShallowCopy(G[a[2]]![1]);
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

        if r <> [ ] and minus then
           cf:= r[Length(r)];
           if cf < 0 then
              for i in [2,4..Length(r)] do r[i]:= -r[i]; od;
           fi;
        fi;

     fi;

     return r;

end;

LRPrivateFunctions.AddElmRedSet:= function( fam, f, G, lms )

    local newelms, len, h, n, Gh, i, g, pos;

    newelms:= [ f ];
    len:= 1;
    while len>0 do
       h:= newelms[len];
       newelms:= newelms{[1..len-1]};
       len:= len-1;
       h:= LRPrivateFunctions.ReduceElmFreeAlg( fam, h, G, lms, true );
       if h <> [] then
          # we add it, but first we remove all elements of which the
          # leading monomial reduces mod h from G:
          n:= [ h[ Length(h)-1 ].no ];
          h:= ObjByExtRep( fam, h );
          Gh:= [ h ];
          for i in [1..Length(G)] do
              g:= LRPrivateFunctions.ReduceElmFreeAlg( fam, G[i]![1], Gh, n, true );
              if g <> [] and g[Length(g)-1].no <> lms[i] then
                 Add( newelms, g ); len:= len+1;
                 Unbind( G[i] ); Unbind( lms[i] );
              elif g=[ ] then
                 Unbind( G[i] ); Unbind( lms[i] );
              else
                 G[i]:= ObjByExtRep( fam, g );
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

InstallMethod( ReducedSet, 
    "for a set of free alg elms",
    true,
    [ IsList ], 0,
    function( elms )

    local RS, G, lms, fam, g, a;

    RS:= Objectify( NewType( NewFamily( "ReducedSetFam", IsReducedSetOfFAE ), IsReducedSetOfFAE ), 
                    rec() );

    if elms = [ ] then
       RS!.elements:= [ ];
       RS!.leading_mns:= [ ];
       return RS;
    fi;

    G:= [ ]; lms:= [ ];
    fam:= FamilyObj( elms[1] );
    for g in elms do
        a:= LRPrivateFunctions.AddElmRedSet( fam, g![1], G, lms );
        G:= a[1]; lms:= a[2];
    od;
    RS!.elements:= G;
    RS!.leading_mns:= lms;
    return RS;

end );



InstallMethod( AddToReducedSet, 
    "for a reduced set of free alg elms, and a free alg elm",
    true,
    [ IsReducedSetOfFAE, IsFAlgElement ], 0,
    function( G, f )

    local elms, lms, ef, a;

    elms:= G!.elements;
    lms:= G!.leading_mns;
    ef:= f![1];
    if elms = [ ] and ef <> [ ] then
       G!.elements:= [ f ];
       G!.leading_mns:= [ ef[ Length(ef)-1 ].no ];
    elif elms <> [ ] then
       a:= LRPrivateFunctions.AddElmRedSet( FamilyObj( f ), ef, elms, lms );
       G!.elements:= a[1];
       G!.leading_mns:= a[2];
    fi;

end );

InstallMethod( NormalForm, 
    "for a reduced set of free alg elms, and a free alg elm",
    true,
    [ IsReducedSetOfFAE, IsFAlgElement ], 0,
    function( G, f )

     local h;

     h:= LRPrivateFunctions.ReduceElmFreeAlg( 
                            FamilyObj(f), f![1], G!.elements, G!.leading_mns, false );
     return ObjByExtRep( FamilyObj(f), h );

end );

