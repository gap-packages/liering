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
Subtitle := "Computing with finitely presented Lie rings",
Version := "2.4.2",
Date := "10/02/2022", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
    rec(
      LastName      := "Cicalò",
      FirstNames    := "Serena",
      IsAuthor      := true,
      IsMaintainer  := true,
      Email         := "cicalo@science.unitn.it",
      PostalAddress := Concatenation( [
                     "Serena Cicalò\n",
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
  ),
  rec(
    LastName      := "GAP Team",
    FirstNames    := "The",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "support@gap-system.org",
  ),
],
Status := "accepted",
CommunicatedBy := "Max Neunhoeffer (Cologne)",
AcceptDate := "12/2013",

PackageWWWHome  := "https://gap-packages.github.io/liering/",
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/gap-packages/liering",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/liering-", ~.Version ),
ArchiveFormats := ".tar.gz",


PackageDoc := rec(
  BookName  := "LieRing",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Computing with finitely presented Lie rings",
  Autoload  := true
),

AbstractHTML := "The package <span class=\"pkgname\">LieRing</span> contains \
                 functionality for working with finitely presented Lie rings and the \
Lazard correspondence.",

Dependencies := rec(
  GAP := ">=4.8",
  NeededOtherPackages:= [ ],
  SuggestedOtherPackages := [ ],
  ExternalConditions := []
),
AvailabilityTest := ReturnTrue,

# the banner
BannerString := "LieRing\n a package for working with Lie rings \n by Serena Cicalò and Willem de Graaf\n",
TestFile := "tst/testall.g",
Keywords := ["Lie rings","Lazard correspondence"],

AutoDoc := rec(
    TitlePage := rec(
        Version := Concatenation( "Version ", ~.Version ),
        Abstract := """
            This package provides functions for constructing and working with Lie
            rings. There are functions for dealing with finitely-presented Lie
            rings, and for performing the Lazard correspondence. The package also
            contains a small database of finitely-generated Lie rings satisfying
            an Engel condition.
            """,
        Copyright := "&copyright; 2016 Serena Cicalò and Willem de Graaf",
    ),
),

));


