#####################################################################################
#
#  liering.gd                                      Serena Cicalo' and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 



##############################################################################
##
#C  IsLRElement( <obj> )
#C  IsLRElementCollection( <obj> )
#C  IsLRElementFamily( <fam> )
##
##  This is the category of elements of a Lie ring.
##  
DeclareCategory( "IsLRElement", IsVector and IsRingElement and
                     IsMultiplicativeElement );
DeclareCategoryCollections( "IsLRElement" );
DeclareCategoryFamily( "IsLRElement" );

#############################################################################
##
#C   IsLieRing( <L> )
##
##   The category of Lie rings.
##
#DeclareCategory( "IsLieRing", IsAlgebra and IsLieAlgebra );
DeclareCategory( "IsLieRing", IsLeftOperatorRing and IsLeftModule 
                                   and IsJacobianRing and IsZeroSquaredRing );

#DeclareOperation( "NaturalHomomorphismByIdeal",
#    [ IsLieRing, IsLieRing ] );

DeclareAttribute( "LieLowerCentralSeries", IsLieRing );
DeclareAttribute( "LieCentre", IsLieRing );

##############################################################################
##
#O  LieRingByStructureConstants( <tors>, <T> )
##
##  Here T is a multiplication table (following the usual GAP conventions),
##  and tors is a torsion list, so the dimension of the corresponding Lie
##  ring is the length of that list. 
##
DeclareOperation( "LieRingByStructureConstants", [ IsList, IsList ] );

##############################################################################
##
#C  IsBasisOfLieRing( <B> )
##
##  Category of bases of Lie rings. This has two attributes: 
##  StructureConstantsTable, and Torsion.
##
DeclareCategory( "IsBasisOfLieRing", IsBasis );


##############################################################################
##
#P  IsStandardBasisOfLieRing( <B> )
##
##  Lie rings are always given by structure constants; a basis of
##  such a Lie ring is the standard basis if it is the basis the
##  Lie ring comes with at birth.
##
DeclareProperty( "IsStandardBasisOfLieRing", IsBasis );

###############################################################################
##
#A   Torsion( <B> )
##
##
DeclareAttribute( "Torsion", IsBasisOfLieRing );

#############################################################################
##
#O  SubLieRing( <L>, <gens> )
#O  SubLieRing( <L>, <gens>, "basis" )
##
DeclareOperation( "SubLieRing", [ IsLieRing, IsList ] );

#############################################################################
##
#O  LieRingIdeal( <L>, <gens> )
#O  LieRingIdeal( <L>, <gens>, "basis" )
##
DeclareOperation( "LieRingIdeal", [ IsLieRing, IsList ] );


#############################################################################
##
#O  TensorWithField( <L>, <F> )
##
DeclareOperation( "TensorWithField", [ IsLieRing, IsField ] );

#############################################################################
##
#O  SmallNEngelLieRing( <n>, <k> )
##
DeclareOperation( "SmallNEngelLieRing", [ IsInt, IsInt ] );
