############################################################################
##
##  PackageInfo.g
##  Copyright (C) 2011-21                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

##  <#GAPDoc Label="PKGVERSIONDATA">
##  <!ENTITY VERSION "3.4.2">
##  <!ENTITY GAPVERS "4.10.0">
##  <!ENTITY ARCHIVENAME "semigroups-3.4.2">
##  <!ENTITY COPYRIGHTYEARS "2011-21">
##  <!ENTITY DATASTRUCTURESVERS "0.2.5">
##  <!ENTITY DIGRAPHSVERS "1.2.0">
##  <!ENTITY GENSSVERS "1.6.5">
##  <!ENTITY IMAGESVERS "1.3.0">
##  <!ENTITY IOVERS "4.5.1">
##  <!ENTITY ORBVERS "4.8.2">
##  <#/GAPDoc>

BindGlobal("_RecogsFunnyNameFormatterFunction",
function(st)
  if Length(st) = 0 then
    return st;
  else
    return Concatenation(" (", st, ")");
  fi;
end);

BindGlobal("_RecogsFunnyWWWURLFunction",
function(re)
  if IsBound(re.WWWHome) then
    return re.WWWHome;
  else
    return "";
  fi;
end);

_STANDREWS := Concatenation(["Mathematical Institute, ",
                             "North Haugh, ",
                             "St Andrews, ",
                             "Fife, ",
                             "KY16 9SS, ",
                             "Scotland"]);

SetPackageInfo(rec(
PackageName := "Semigroups",
Subtitle := "A package for semigroups and monoids",
Version := "3.4.2",
Date := "07/02/2021",  # dd/mm/yyyy format
License := "GPL-3.0-or-later",

ArchiveFormats := ".tar.gz",

SourceRepository := rec(
    Type := "git",
    URL := Concatenation("https://github.com/semigroups/", ~.PackageName),
),

IssueTrackerURL := Concatenation(~.SourceRepository.URL, "/issues"),
PackageWWWHome  := Concatenation("https://semigroups.github.io/",
                                 ~.PackageName),
README_URL      := Concatenation(~.PackageWWWHome, "/README.md"),
PackageInfoURL  := Concatenation(~.PackageWWWHome, "/PackageInfo.g"),
ArchiveURL      := Concatenation(~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", "semigroups-", ~.Version),

Persons := [
  rec(
    LastName      := "Mitchell",
    FirstNames    := "James",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email         := "jdm3@st-andrews.ac.uk",
    WWWHome       := "https://jdbm.me",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName     := "Burrell",
    FirstNames    := "Stuart",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "sb235@st-andrews.ac.uk ",
    WWWHome       := "https://stuartburrell.github.io",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Delgado",
    FirstNames    := "Manuel",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "mdelgado@fc.up.pt",
    WWWHome       := "https://cmup.fc.up.pt/cmup/mdelgado/",
    Place         := "Porto",
    Institution   := "Universidade do Porto"),

  rec(
    LastName      := "East",
    FirstNames    := "James",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "j.east@uws.edu.au",
    WWWHome       := "https://goo.gl/MuiJu5",
    Place         := "Sydney",
    Institution   := "Western Sydney University"),

  rec(
    LastName      := "Egri-Nagy",
    FirstNames    := "Attila",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "attila@egri-nagy.hu",
    WWWHome       := "http://www.egri-nagy.hu",
    Place         := "Akita, Japan",
    Institution   := "Akita International University"),

  rec(
    LastName      := "Elliott",
    FirstNames    := "Luke",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "le27@st-andrews.ac.uk",
    WWWHome       := "https://le27.github.io/Luke-Elliott/",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Ham",
    FirstNames    := "Nicholas",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "nicholas.charles.ham@gmail.com",
    WWWHome       := "https://n-ham.github.io",
    Place         := "Hobart, Tasmania",
    Institution   := "University of Tasmania"),

  rec(
    LastName      := "Horn",
    FirstNames    := "Max",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "horn@mathematik.uni-kl.de",
    WWWHome       := "https://www.quendi.de/math",
    PostalAddress := Concatenation(
                       "Fachbereich Mathematik, ",
                       "TU Kaiserslautern, ",
                       "Gottlieb-Daimler-Straße 48, ",
                       "67663 Kaiserslautern, ",
                       "Germany"),
    Place         := "Kaiserslautern, Germany",
    Institution   := "TU Kaiserslautern"),

  rec(
    LastName      := "Jefferson",
    FirstNames    := "Christopher",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "caj21@st-andrews.ac.uk",
    WWWHome       := "https://caj.host.cs.st-andrews.ac.uk/",
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Jonusas",
    FirstNames    := "Julius",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "julius.jonusas@tuwien.ac.at",
    WWWHome       := "http://julius.jonusas.work",
    PostalAddress := Concatenation([
                       "Institut für Diskrete Mathematik und Geometrie, ",
                       "Wiedner Hauptstrasse 8-10, 1040 Wien, Austria"]),
    Place         := "Wien, Austria",
    Institution   := "TU Wien"),

  rec(
    LastName      := "Pasechnik",
    FirstNames    := "Dima V.",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "dmitrii.pasechnik@cs.ox.ac.uk",
    WWWHome       := "http://users.ox.ac.uk/~coml0531/",
    PostalAddress := Concatenation(["Pembroke College, ",
                                    "St. Aldates, ",
                                    "Oxford OX1 1DW, ",
                                    "England"]),
    Place         := "Oxford",
    Institution   := "University of Oxford"),

   rec(
    LastName      := "Pfeiffer",
    FirstNames    := "Markus",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "markus.pfeiffer@morphism.de",
    WWWHome       := "https://www.morphism.de/~markusp/",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Russell",
    FirstNames    := "Christopher",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "cr66@st-andrews.ac.uk",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Steinberg",
    FirstNames    := "Benjamin",
    IsAuthor      := false,
    IsMaintainer  := false,
    WWWHome       := "https://bsteinberg.ccny.cuny.edu/Webpage/"),

  rec(
    LastName      := "Smith",
    FirstNames    := "Finn",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "fls3@st-andrews.ac.uk",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Smith",
    FirstNames    := "Jhevon",
    IsAuthor      := false,
    IsMaintainer  := false,
    WWWHome       := "https://math.sci.ccny.cuny.edu/person/jhevon-smith/"),

  rec(
    LastName      := "Torpey",
    FirstNames    := "Michael",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "mct25@st-and.ac.uk",
    WWWHome       := "https://mtorpey.github.io",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Whyte",
    FirstNames    := "Murray",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "mw231@st-andrews.ac.uk",
    PostalAddress := _STANDREWS,
    Place         := "St Andrews",
    Institution   := "University of St Andrews"),

  rec(
    LastName      := "Wilson",
    FirstNames    := "Wilf A.",
    IsAuthor      := false,
    IsMaintainer  := false,
    Email         := "gap@wilf-wilson.net",
    WWWHome       := "https://wilf.me")],

Status := "deposited",

AbstractHTML := Concatenation(
  "<p>The Semigroups package is a GAP package containing ",
  "methods for semigroups, monoids, and inverse semigroups.  There are ",
  "particularly efficient methods for semigroups or ideals consisting of ",
  "transformations, partial permutations, bipartitions, partitioned binary ",
  "relations, subsemigroups of regular Rees 0-matrix semigroups, and matrices ",
  "of various semirings including boolean matrices, matrices over finite ",
  "fields, and certain tropical matrices.</p><p>",
  "Semigroups contains efficient methods for creating semigroups, ",
  "monoids, and inverse semigroup, calculating their Green's structure, ",
  "ideals, size, elements, group of units, small generating sets, testing ",
  "membership, finding the inverses of a regular element, factorizing ",
  "elements over the generators, and so on. It is possible to test if a ",
  "semigroup satisfies a particular property, such as if it is regular, ",
  "simple, inverse, completely regular, and a variety of further ",
  "properties.</p><p>",
  "There are methods for finding presentations for a semigroup, the ",
  "congruences of a semigroup, the normalizer of a semigroup in a permutation ",
  "group, the maximal subsemigroups of a finite semigroup, smaller degree ",
  "partial permutation representations, and the character tables of inverse ",
  "semigroups. There are functions for producing pictures of the Green's ",
  "structure of a semigroup, and for drawing graphical representations of ",
  "certain types of elements.</p>"),

PackageDoc := rec(
  BookName  := "Semigroups",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Semigroups",
  Autoload  := true
),

Dependencies := rec(
  GAP := ">=4.10.0",
  NeededOtherPackages := [["orb", ">=4.8.2"],
                          ["io", ">=4.5.1"],
                          ["datastructures", ">=0.2.5"],
                          ["digraphs", ">=1.2.0"],
                          ["genss", ">=1.6.5"],
                          ["images", ">=1.3.0"]],
  SuggestedOtherPackages := [["gapdoc", ">=1.5.1"]],

  ExternalConditions := []),

BannerString := Concatenation(
  "----------------------------------------------------------------------",
  "-------\n",
  "Loading  Semigroups ", ~.Version, "\n",
  "by ", ~.Persons[1].FirstNames, " ", ~.Persons[1].LastName,
        " (", ~.Persons[1].WWWHome, ")\n",
  "with contributions by:\n",
  Concatenation(Concatenation(List(~.Persons{[2 .. Length(~.Persons) - 1]},
       p -> ["     ", p.FirstNames, " ", p.LastName,
       _RecogsFunnyNameFormatterFunction(
         _RecogsFunnyWWWURLFunction(p)), ",\n"]))),
  " and ", ~.Persons[Length(~.Persons)].FirstNames, " ",
  ~.Persons[Length(~.Persons)].LastName,
  _RecogsFunnyNameFormatterFunction(
    _RecogsFunnyWWWURLFunction(~.Persons[Length(~.Persons)])), ".\n",
  "-----------------------------------------------------------------------",
  "------\n"),

AvailabilityTest := function()
  local semigroups_so;
  semigroups_so := Filename(DirectoriesPackagePrograms("semigroups"),
                            "semigroups.so");
  if (not "semigroups" in SHOW_STAT()) and semigroups_so = fail then
    LogPackageLoadingMessage(PACKAGE_WARNING,
                             "the kernel module is not compiled, ",
                             "the package cannot be loaded.");
    return fail;
  fi;
  return true;
end,

Autoload := false,
TestFile := "tst/teststandard.g",
Keywords := ["transformation semigroups", "partial permutations",
             "inverse semigroups", "Green's relations",
             "free inverse semigroup", "partition monoid", "bipartitions",
             "Rees matrix semigroups"]
));

MakeReadWriteGlobal("_RecogsFunnyWWWURLFunction");
MakeReadWriteGlobal("_RecogsFunnyNameFormatterFunction");
Unbind(_RecogsFunnyWWWURLFunction);
Unbind(_RecogsFunnyNameFormatterFunction);
Unbind(_STANDREWS);
