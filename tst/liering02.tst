# LieRing, chapter 2
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been autogenerated with GAP. It contains examples
# extracted from the documentation. Each example is preceded by the
# comment which points to the location of its source.
#
gap> START_TEST( "liering02.tst");

# doc/manual.xml:174-182
gap> L:= FreeLieRing( Integers, ["a","b"] );
<Free algebra over Integers generators: a, b >
gap> a:= L.1; b:= L.2;
a
b
gap> (a*b)*b+2*a*b;       
(2)*(a,b)+(-1)*(b,(a,b))

# doc/manual.xml:193-200
gap> L:= FreeLieRing( Integers, ["a","b"] );;
gap> a:= L.1;; b:= L.2;;
gap> f:=(a*b)*b+2*a*b;
(2)*(a,b)+(-1)*(b,(a,b))
gap> Degree(f);
3

# doc/manual.xml:239-244
gap> T:= EmptySCTable( 3, 0, "antisymmetric" );;
gap> SetEntrySCTable( T, 1, 2, [1,3] );
gap> LieRingByStructureConstants( [3,6,3], T );
<Lie ring with 3 generators>

# doc/manual.xml:269-284
gap> L:= FreeLieRing( Integers, ["x","y"], [1,2] );                   
<Free algebra over Integers generators: x, y >
gap> x:= L.1;; y:= L.2;;
gap> R:= [((y*x)*x)*x-6*(y*x)*y, 3*((((y*x)*x)*x)*x)*x-20*(((y*x)*x)*x)*y ];
[ (-1)*(x,(x,(x,y)))+(-6)*(y,(x,y)), 
  (-3)*(x,(x,(x,(x,(x,y)))))+(-20)*(y,(x,(x,(x,y)))) ]
gap> K:= FpLieRing( L, R : maxdeg:= 15 );
<Lie ring with 75 generators>
gap> f:=CanonicalProjection(K);
function( elm ) ... end
gap> f(R[1]);
0
gap> f(x);
v_1

# doc/manual.xml:314-323
gap> T:= EmptySCTable( 3, 0, "antisymmetric" );;
gap> SetEntrySCTable( T, 1, 2, [1,3] );
gap> K:= LieRingByStructureConstants( [3,6,3], T );
<Lie ring with 3 generators>
gap> Basis(K); 
Basis( <Lie ring with 3 generators>, [ v_1, v_2, v_3 ] )
gap> BasisVectors( Basis(K) );
[ v_1, v_2, v_3 ]

# doc/manual.xml:332-341
gap> T:= EmptySCTable( 3, 0, "antisymmetric" );;
gap> SetEntrySCTable( T, 1, 2, [1,3] );
gap> K:= LieRingByStructureConstants( [3,6,3], T );
<Lie ring with 3 generators>
gap> StructureConstantsTable( Basis(K) );
[ [ [ [  ], [  ] ], [ [ 3 ], [ 1 ] ], [ [  ], [  ] ] ], 
  [ [ [ 3 ], [ -1 ] ], [ [  ], [  ] ], [ [  ], [  ] ] ], 
  [ [ [  ], [  ] ], [ [  ], [  ] ], [ [  ], [  ] ] ], -1, 0 ]

# doc/manual.xml:350-357
gap> T:= EmptySCTable( 3, 0, "antisymmetric" );;
gap> SetEntrySCTable( T, 1, 2, [1,3] );
gap> K:= LieRingByStructureConstants( [3,6,3], T );
<Lie ring with 3 generators>
gap> Torsion( Basis(K) );
[ 3, 6, 3 ]

# doc/manual.xml:367-377
gap> L:= FreeLieRing( Integers, ["x","y"] );; x:= L.1;; y:= L.2;;
gap> rr:=[((y*x)*x)*x-6*(y*x)*y, 3*((((y*x)*x)*x)*x)*x-20*(((y*x)*x)*x)*y ];;
gap> K:= FpLieRing( L, rr : maxdeg:= 6 );;
gap> C:=LieCentre(K);
<Lie ring with 9 generators>
gap> Coefficients( Basis(K), Basis(C)[6] );
[ 5, 5, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]
gap> Coefficients( Basis(C), Basis(C)[6] );
[ 0, 0, 0, 0, 0, 1, 0, 0, 0 ]

# doc/manual.xml:391-405
gap> L:= FreeLieRing( Integers, ["x","y"] );;                         
gap> x:= L.1;; y:= L.2;;
gap> rr:=[((y*x)*x)*x-6*(y*x)*y, 3*((((y*x)*x)*x)*x)*x-20*(((y*x)*x)*x)*y ];; 
gap> K:= FpLieRing( L, rr : maxdeg:= 8 );
<Lie ring with 41 generators>
gap> b:= Basis(K);;
gap> M:= SubLieRing( K, [ b[30], b[40] ] );
<Lie ring with 6 generators>
gap> Torsion(Basis(M));
[ 3, 6, 6, 12, 360, 0 ]
gap> Basis(M)[2];
3*v_2+2*v_3+2*v_10+4*v_12+4*v_13+5*v_14+v_15+3*v_17+3*v_18+6*v_20+10*v_22+6*v_
24+6*v_25+10*v_26+4*v_27+18*v_28+30*v_29+60*v_30+360*v_31+5040*v_32

# doc/manual.xml:429-448
gap> L:= FreeLieRing( Integers, ["x","y"] );;                         
gap> x:= L.1;; y:= L.2;;
gap> rr:=[((y*x)*x)*x-6*(y*x)*y, 3*((((y*x)*x)*x)*x)*x-20*(((y*x)*x)*x)*y ];; 
gap> K:= FpLieRing( L, rr : maxdeg:= 8 );;
gap> b:= Basis(K);;
gap> I:= LieRingIdeal( K, [ b[29] ] );
<Lie ring with 23 generators>
gap> f:= NaturalHomomorphismByIdeal( K, I );;
gap> M:= Range(f);
<Lie ring with 27 generators>
gap> Torsion(Basis(M));
[ 2, 2, 2, 2, 2, 2, 2, 2, 2, 6, 6, 6, 12, 12, 12, 120, 720, 10080, 0, 0, 0, 
  0, 0, 0, 0, 0, 0 ]
gap> Image( f, b[30] );
v_16+716*v_17
gap> PreImagesRepresentative( f, Basis(M)[10] );
4*v_2+4*v_3+4*v_4+4*v_5+5*v_6+v_7+5*v_8+v_9+5*v_10+v_11+5*v_12+v_13+5*v_14+v_
24+v_25+11*v_26+v_29+10*v_30+100*v_31

# doc/manual.xml:459-468
gap> L:= FreeLieRing( Integers, ["x","y"] );; x:= L.1;; y:= L.2;;
gap> rr:=[((y*x)*x)*x-6*(y*x)*y, 3*((((y*x)*x)*x)*x)*x-20*(((y*x)*x)*x)*y ];;
gap> K:= FpLieRing( L, rr : maxdeg:= 7 );;
gap> LieLowerCentralSeries(K);
[ <Lie ring with 26 generators>, <Lie ring with 24 generators>, 
  <Lie ring with 23 generators>, <Lie ring with 22 generators>, 
  <Lie ring with 21 generators>, <Lie ring with 19 generators>, 
  <Lie ring with 16 generators>, <Lie ring with 0 generators> ]

# doc/manual.xml:483-492
gap> L:= FreeLieRing( Integers, ["x","y"] );; x:= L.1;; y:= L.2;;
gap> rr:=[((y*x)*x)*x-7*(y*x)*y, 7*((((y*x)*x)*x)*x)*x-49*(((y*x)*x)*x)*y, 
> 7*x, 49*y ];;
gap> K:= FpLieRing( L, rr : maxdeg:= 5 );;
gap> LieLowerPCentralSeries(K,7);
[ <Lie ring with 11 generators>, <Lie ring with 10 generators>, 
  <Lie ring with 8 generators>, <Lie ring with 6 generators>, 
  <Lie ring with 4 generators>, <Lie ring with 0 generators> ]

# doc/manual.xml:502-511
gap> L:= FreeLieRing( Integers, ["x","y"] );; x:= L.1;; y:= L.2;;
gap> rr:=[((y*x)*x)*x-6*(y*x)*y, 3*((((y*x)*x)*x)*x)*x-20*(((y*x)*x)*x)*y ];;
gap> K:= FpLieRing( L, rr : maxdeg:= 7 );;
gap> LieCentre(K);
<Lie ring with 16 generators>
gap> Torsion( Basis(K) );
[ 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 12, 12, 12, 12, 360, 5040, 0, 0, 0, 0, 
  0, 0, 0, 0 ]

# doc/manual.xml:521-531
gap> T:= EmptySCTable( 3, 0, "antisymmetric" );;
gap> SetEntrySCTable( T, 1, 2, [1,3] );
gap> K:= LieRingByStructureConstants( [3,6,3], T );;
gap> TensorWithField( K, GF(3) );
<Lie algebra of dimension 3 over GF(3)>
gap> TensorWithField( K, GF(2) );
<Lie algebra of dimension 1 over GF(2)>
gap> Dimension( TensorWithField( K, GF(5) ) );
0

# doc/manual.xml:561-586
gap> F := FreeGroup(IsSyllableWordsFamily,"a","b","c","d", "e", "f", "g");;
gap> a := F.1;; b := F.2;; c := F.3;; d := F.4;; e := F.5;; f := F.6;; g:=F.7;;
gap> rels := [ a^13, b^13/g, c^13, d^13, e^13, f^13, g^13,  
> Comm(b,a)/c, Comm(c,a)/d, Comm(d,a)/e, Comm(e,a)/f, Comm(f,a), Comm(g,a),
> Comm(c,b)/(g^11), Comm(d,b)/g, Comm(e,b)/g, Comm(g,b), Comm(d,c)/(g^12),
> Comm(e,c), Comm(f,c), Comm(g,c), Comm(e,d), Comm(f,d), Comm(g,d), Comm(f,e), 
> Comm(g,e), Comm(g,f)];;
gap> G := PcGroupFpGroup( F/rels );
<pc group of size 62748517 with 7 generators>
gap> r:= PGroupToLieRing(G);
rec( GtoL := function( g0 ) ... end, LtoG := function( x0 ) ... end, 
  liering := <Lie ring with 6 generators>, 
  pgroup := <pc group of size 62748517 with 7 generators> )
gap> f:= r.GtoL; h:= r.LtoG;
function( g0 ) ... end
function( x0 ) ... end
gap> L:= r.liering;
<Lie ring with 6 generators>
gap> b:= Basis(L);
Basis( <Lie ring with 6 generators>, [ v_1, v_2, v_3, v_4, v_5, v_6 ] )
gap> h(b[1]);
a^12*c*d^5*e^3*f^8*g^7
gap> f(h(b[1]));
v_1

# doc/manual.xml:603-621
gap> L:= FreeLieRing( Integers, ["a","b","c"] );; 
gap> a:= L.1;; b:= L.2;; c:= L.3;;
gap> rels:= [ (b*a)*b, c*a, c*b-(b*a)*a, 7^2*a, 7*b-((b*a)*a)*a, 
> 7*c-((b*a)*a)*a];;
gap> K:= FpLieRing( L, rels );
<Lie ring with 5 generators>
gap> r:= LieRingToPGroup(K);
rec( GtoL := function( g0 ) ... end, LtoG := function( x0 ) ... end, 
  liering := <Lie ring with 5 generators>, 
  pgroup := <pc group of size 823543 with 7 generators> )
gap> G:= r.pgroup;; f:= r.LtoG;; h:= r.GtoL;;
gap> u:= 5*Basis(K)[2]+9*Basis(K)[5];
5*v_2+9*v_5
gap> f(u);
f3^2*f4^2*f5^6*f7^3
gap> h(f(u));
5*v_2+9*v_5

# doc/manual.xml:646-658
gap> L:= SmallNEngelLieRing( 4, 3 );
<Lie ring with 133 generators>
gap> x:= 10*Basis(L)[1]+7*Basis(L)[10]+19*Basis(L)[89];
7*v_10+19*v_89
gap> ForAll( Basis(L), y -> IsZero( x*(x*(x*(x*y))) ) );
true
gap> K:= TensorWithField( L, GF(3) );
<Lie algebra of dimension 83 over GF(3)>
gap> x:= Random(K);;
gap> ForAll( Basis(K), y -> IsZero( x*(x*(x*(x*y))) ) );
true
gap> STOP_TEST("liering02.tst", 1 );
