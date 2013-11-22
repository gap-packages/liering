#####################################################################################
#
#  PackageInfo.g                                      Serena Cicalo and Willem de Graaf
#
#
# The package LieRing is free software; you can redistribute it and/or modify it under the 
# terms of the GNU General Public License as published by the Free Software Foundation; 
# either version 2 of the License, or (at your option) any later version. 


SetPackageInfo( rec(
PackageName := "LieRing",
Subtitle := "finitely presented Lie rings",        
Version := "2.1",
Date := "22/12/2011",
ArchiveURL := Concatenation("http://www.science.unitn.it/~degraaf/liering/liering-",
                            ~.Version),
ArchiveFormats := ".tar.gz",
Persons := [
    rec( 
      LastName      := "Cicalo'",
      FirstNames    := "Serena",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "cicalo@science.unitn.it",
      PostalAddress := Concatenation( [
                     "Serena Cicalo'\n",
                         "Dipartimento di Matematica e Informatica\n",
                         "Via Ospedale 72\n",
                         "Italy" ]),
      Place         := "Cagliari",
      Institution   := "Universita' di Cagliari"

             ),

  rec(
  LastName := "de Graaf",
  FirstNames := "Willem Adriaan",
  IsAuthor := true,
  IsMaintainer := true,
  Email := "degraaf@science.unitn.it",
  WWWHome := "http://www.science.unitn.it/~degraaf",
  Place := "Trento",
  Institution := "Dipartimento di Matematica"
  )
],
Status := "other",
#CommunicatedBy := ,
#AcceptDate := ,
PackageDoc := rec(
  BookName  := "LieRing",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Computing with Lie rings",
  Autoload  := true
),
README_URL := 
  "http://www.science.unitn.it/~degraaf/liering/README.liering",
PackageInfoURL := 
  "http://www.science.unitn.it/~degraaf/liering/PackageInfo.g",
AbstractHTML := "The package <span class=\"pkgname\">LieRing</span> contains \
                 functionality for working with finitely presented Lie rings and the \
Lazard correspondence.",
PackageWWWHome := "http://www.science.unitn.it/~degraaf/liering.html",
Dependencies := rec(
  GAP := ">=4.4",
  NeededOtherPackages:= [ ],                 
  SuggestedOtherPackages := [ ["GAPDoc", ">= 1.0"] ],
  ExternalConditions := []
),
AvailabilityTest := ReturnTrue,
Autoload := false,

# the banner
BannerString := "LieRing\n a package for working with Lie rings \n by Serena Cicalo' and Willem de Graaf\n",
Keywords := ["Lie rings","Lazard correspondence"]
));


