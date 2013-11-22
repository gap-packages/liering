#####################################################################################
#
#  fplie.gd                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 


#############################################################################
##
#G  LRPrivateFunctions
##
## 
DeclareGlobalVariable( "LRPrivateFunctions", 
       "Private functions for LieRing package" );



##############################################################################
##
#C  IsFAlgElement( <obj> )
#C  IsFAlgElementCollection( <obj> )
#C  IsFAlgElementFamily( <fam> )
##
##  This is the category of elements of a free algebra.
##  
DeclareCategory( "IsFAlgElement", IsVector and IsRingElement and
                     IsMultiplicativeElement );
DeclareCategoryCollections( "IsFAlgElement" );
DeclareCategoryFamily( "IsFAlgElement" );




#############################################################################
##
#C   IsFreeNAAlgebra( <A> )
##
##   Category of the free non-associative algebras.
##
DeclareCategory( "IsFreeNAAlgebra", IsAlgebra );

###############################################################################
##
#O   FreeLieRing( <R>, <names> )
##
##   Produce the free Lie ring with generator names in names.
##
DeclareOperation( "FreeLieRing", [ IsRing, IsList ] );


##############################################################################
##
#C   IsReducedSetOfFAE( <G> )
##
##   Category of reduced sets of free algebra elements.
##
DeclareCategory( "IsReducedSetOfFAE", IsList );

###############################################################################
##
#O   AddToReducedSet( <G>, <f> )
##
##   to add an element to a reduced set.
##
DeclareOperation( "AddToReducedSet", [ IsReducedSetOfFAE, IsFAlgElement ] );

###############################################################################
##
#O   ReducedSet( <G> )
##
##   Produce a reduced set generating the same ideal as G.
##
DeclareOperation( "ReducedSet", [ IsList ] );


###############################################################################
##
#O   NormalForm( <G>, <f> )
##
##   The normal form of <f> modulo <G>.
##
DeclareOperation( "NormalForm", [ IsReducedSetOfFAE, IsFAlgElement ] );

###############################################################################
##
#O   FpLieRing( <L>, <R> )
##
##   Finitely-presented Lie ring.
##
DeclareOperation( "FpLieRing", [ IsFreeNAAlgebra, IsList ] );

###############################################################################
##
#O   FpLieAlgebra( <L>, <R> )
##
##   Finitely-presented Lie algebra.
##
DeclareOperation( "FpLieAlgebra", [ IsFreeNAAlgebra, IsList ] );

DeclareAttribute( "GeneratorsImages", IsAlgebra );
DeclareAttribute( "CanonicalProjection", IsAlgebra );