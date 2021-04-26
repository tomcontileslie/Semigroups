#############################################################################
##
#W  standard/tietze.tst
#Y  Copyright (C) 2021                                      Tom Conti-Leslie
#Y                                                          Ben Spiers
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
gap> START_TEST("Semigroups package: standard/tietze.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SEMIGROUPS.StartTest();

# Test StzPresentation and basic attributes
gap> f := FreeSemigroup(["a", "b", "c"]);;
gap> r := [[(f.1 ^ 2 * f.2) ^ 2, f.1 ^ 2 * f.2], [f.3, f.1 ^ 2 * f.2]];
[ [ (a^2*b)^2, a^2*b ], [ c, a^2*b ] ]
gap> s := f / r;
<fp semigroup on the generators [ a, b, c ]>
gap> f := FreeSemigroup(["a", "b", "c"]);
<free semigroup on the generators [ a, b, c ]>
gap> r := [[(f.1 ^ 2 * f.2) ^ 2, f.1 ^ 2 * f.2], [f.3, f.1 ^ 2 * f.2]];
[ [ (a^2*b)^2, a^2*b ], [ c, a^2*b ] ]
gap> s := f / r;
<fp semigroup on the generators [ a, b, c ]>
gap> stz := StzPresentation(s);
<fp semigroup presentation with 3 generators and 2 relations with length 16>
gap> GeneratorsOfStzPresentation(stz);
[ "a", "b", "c" ]
gap> RelationsOfStzPresentation(stz);
[ [ [ 1, 1, 2, 1, 1, 2 ], [ 1, 1, 2 ] ], [ [ 3 ], [ 1, 1, 2 ] ] ]
gap> s = UnreducedSemigroupOfStzPresentation(stz);
true
