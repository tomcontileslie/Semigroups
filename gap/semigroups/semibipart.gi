#############################################################################
##
#W  semibipart.gi
#Y  Copyright (C) 2013-15                                 James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# this file contains methods for every operation/attribute/property that is
# specific to bipartition semigroups.

InstallMethod(SemigroupViewStringPrefix, "for a bipartition semigroup",
[IsBipartitionSemigroup], S -> "\>bipartition\< ");

InstallMethod(SemigroupViewStringSuffix, "for a bipartition semigroup",
[IsBipartitionSemigroup],
function(S)
  return Concatenation("\>degree \>",
                       ViewString(DegreeOfBipartitionSemigroup(S)),
                       "\<\< ");
end);

# same method for ideals

InstallMethod(GroupOfUnits, "for an acting bipartition semigroup",
[IsBipartitionSemigroup and IsActingSemigroup],
function(S)
  local R, G, deg, U;

  if MultiplicativeNeutralElement(S) = fail then
    return fail;
  fi;

  R := GreensRClassOfElementNC(S, MultiplicativeNeutralElement(S));
  G := SchutzenbergerGroup(R);
  deg := DegreeOfBipartitionSemigroup(S);

  U := Semigroup(List(GeneratorsOfGroup(G), x -> AsBipartition(x, deg)));

  SetIsomorphismPermGroup(U, MappingByFunction(U, G, AsPermutation,
                                               x -> AsBipartition(x, deg)));

  SetIsGroupAsSemigroup(U, true);
  UseIsomorphismRelation(U, G);

  return U;
end);

#

InstallMethod(AsBlockBijectionSemigroup, "for a semigroup", [IsSemigroup],
S -> Range(IsomorphismBlockBijectionSemigroup(S)));

#

InstallImmediateMethod(IsBlockBijectionSemigroup, IsSemigroup and
HasGeneratorsOfSemigroup, 0,
function(S)
  return IsBipartitionSemigroup(S)
         and ForAll(GeneratorsOfSemigroup(S), IsBlockBijection);
end);

#

InstallImmediateMethod(IsPartialPermBipartitionSemigroup, IsSemigroup and
HasGeneratorsOfSemigroup, 0,
function(S)
  return IsBipartitionSemigroup(S)
         and ForAll(GeneratorsOfSemigroup(S), IsPartialPermBipartition);
end);

#

InstallImmediateMethod(IsPermBipartitionGroup, IsSemigroup and
HasGeneratorsOfSemigroup, 0,
function(S)
  return IsBipartitionSemigroup(S)
         and ForAll(GeneratorsOfSemigroup(S), IsPermBipartition);
end);

#

InstallMethod(IsBlockBijectionSemigroup, "for a semigroup ideal",
[IsSemigroupIdeal],
function(S)
  if IsBlockBijectionSemigroup(SupersemigroupOfIdeal(S)) then
    return true;
  fi;
  return IsBipartitionSemigroup(S)
         and ForAll(GeneratorsOfSemigroup(S), IsBlockBijection);
end);

#

InstallMethod(IsPartialPermBipartitionSemigroup, "for a semigroup ideal",
[IsSemigroupIdeal],
function(S)
  if IsPartialPermBipartitionSemigroup(SupersemigroupOfIdeal(S)) then
    return true;
  fi;
  return IsBipartitionSemigroup(S)
         and ForAll(GeneratorsOfSemigroup(S), IsPartialPermBipartition);
end);

#

InstallMethod(IsPermBipartitionGroup, "for a semigroup ideal",
[IsSemigroupIdeal],
function(S)
  if IsPermBipartitionGroup(SupersemigroupOfIdeal(S)) then
    return true;
  fi;
  return IsBipartitionSemigroup(S)
         and ForAll(GeneratorsOfSemigroup(S), IsPermBipartition);
end);

#

InstallMethod(NaturalLeqInverseSemigroup, "for a bipartition semigroup",
[IsBipartitionSemigroup],
function(S)
  if IsInverseSemigroup(S) then
    if IsBlockBijectionSemigroup(S) then
      return NaturalLeqBlockBijection;
    elif IsPartialPermBipartitionSemigroup(S) then
      return NaturalLeqPartialPermBipartition;
    fi;
    TryNextMethod(); # this should be the default method for a non-inverse op
                     # semigroup
  fi;
  ErrorMayQuit("Semigroups: NaturalLeqInverseSemigroup: usage,\n",
               "the argument is not an inverse semigroup,");
end);

#

InstallMethod(NaturalPartialOrder,
"for an inverse block bijection semigroup",
[IsBlockBijectionSemigroup and IsInverseSemigroup],
function(S)
  local elts, n, out, i, j;

  elts := Elements(S);
  n := Length(elts);
  out := List([1 .. n], x -> []);

  for i in [n, n - 1 .. 2] do
    for j in [i - 1, i - 2 .. 1] do
      if NaturalLeqBlockBijection(elts[j], elts[i]) then
        AddSet(out[i], j);
      fi;
    od;
  od;

  return out;
end);

#

InstallMethod(NaturalPartialOrder,
"for an inverse partial perm bipartition semigroup",
[IsPartialPermBipartitionSemigroup and IsInverseSemigroup],
function(S)
  local elts, p, n, out, i, j;

  elts := ShallowCopy(Elements(S));
  n := Length(elts);
  out := List([1 .. n], x -> []);
  p := Sortex(elts, PartialPermLeqBipartition) ^ -1;

  for i in [n, n - 1 .. 2] do
    for j in [i - 1, i - 2 .. 1] do
      if NaturalLeqPartialPermBipartition(elts[j], elts[i]) then
        AddSet(out[i ^ p], j ^ p);
      fi;
    od;
  od;

  Perform(out, ShrinkAllocationPlist);
  return out;
end);

InstallMethod(AsBipartitionSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  return Range(IsomorphismBipartitionSemigroup(S));
end);

# this is just a composition of IsomorphismTransformationSemigroup and the
# method below for IsomorphismBipartitionSemigroup...

InstallMethod(IsomorphismBipartitionSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  local en, act, gens;

  en := EnumeratorSorted(S);

  act := function(i, x)
    if i <= Length(en) then
      return Position(en, en[i] * x);
    fi;
    return Position(en, x);
  end;

  gens := List(en,
               x -> AsBipartition(TransformationOp(x,
                                                   [1 .. Length(en) + 1],
                                                   act),
                                  Length(en) + 1));
  # gaplint: ignore 4
  return MagmaIsomorphismByFunctionsNC(S, Semigroup(gens),
   x -> AsBipartition(TransformationOp(x, [1 .. Length(en) + 1], act),
                      Length(en) + 1),
   x -> en[(Length(en) + 1) ^ AsTransformation(x)]);
end);

#

InstallMethod(IsomorphismBipartitionSemigroup,
"for a transformation semigroup with generators",
[IsTransformationSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, source, range, i;

  n := Maximum(1, DegreeOfTransformationSemigroup(S));
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsBipartition(source[i], n);
  od;
  # gaplint: ignore 2
  return MagmaIsomorphismByFunctionsNC(S, Semigroup(range),
           x -> AsBipartition(x, n), AsTransformation);
end);

# the converse of the previous method

InstallMethod(IsomorphismTransformationSemigroup,
"for a bipartition semigroup with generators",
[IsBipartitionSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, source, range, i;

  if not ForAll(GeneratorsOfSemigroup(S), IsTransBipartition) then
    TryNextMethod();
  fi;

  n := DegreeOfBipartitionSemigroup(S);
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsTransformation(source[i]);
  od;

  # gaplint: ignore 2
  return MagmaIsomorphismByFunctionsNC(S, Semigroup(range),
           AsTransformation, x -> AsBipartition(x, n));
end);

#

InstallMethod(IsomorphismBipartitionSemigroup,
"for a partial perm semigroup with generators",
[IsPartialPermSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, source, range, i;

  n := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S));
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsBipartition(source[i], n);
  od;

  # gaplint: ignore 2
  return MagmaIsomorphismByFunctionsNC(S, Semigroup(range),
   x -> AsBipartition(x, n), AsPartialPerm);
end);

# the converse of the previous method

InstallMethod(IsomorphismPartialPermSemigroup,
"for a bipartition semigroup with generators",
[IsBipartitionSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, source, range, i;

  if not ForAll(GeneratorsOfSemigroup(S), IsPartialPermBipartition) then
    TryNextMethod();
  fi;

  n := DegreeOfBipartitionSemigroup(S);
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsPartialPerm(source[i]);
  od;

  # gaplint: ignore 2
  return MagmaIsomorphismByFunctionsNC(S, Semigroup(range),
           AsPartialPerm, x -> AsBipartition(x, n));
end);

#

InstallMethod(IsomorphismBipartitionSemigroup,
"for a partial perm inverse semigroup with generators",
[IsPartialPermSemigroup and IsInverseSemigroup and
 HasGeneratorsOfInverseSemigroup],
function(S)
  local n, source, range, i;

  n := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S));
  source := GeneratorsOfInverseSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsBipartition(source[i], n);
  od;

  return MagmaIsomorphismByFunctionsNC(S,
                                       InverseSemigroup(range),
                                       x -> AsBipartition(x, n),
                                       AsPartialPerm);
end);

# the converse of the last method

InstallMethod(IsomorphismPartialPermSemigroup,
"for a bipartition inverse semigroup with generators",
[IsBipartitionSemigroup and IsInverseSemigroup and
 HasGeneratorsOfInverseSemigroup],
function(S)
  local n, source, range, i;

  if not ForAll(GeneratorsOfInverseSemigroup(S), IsPartialPermBipartition) then
    TryNextMethod();
  fi;

  n := DegreeOfBipartitionSemigroup(S);
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsPartialPerm(source[i]);
  od;

  return MagmaIsomorphismByFunctionsNC(S,
                                       InverseSemigroup(range),
                                       AsPartialPerm,
                                       x -> AsBipartition(x, n));
end);

#

InstallMethod(IsomorphismBipartitionSemigroup,
"for a perm group with generators",
[IsPermGroup and HasGeneratorsOfGroup],
function(S)
  local n, source, range, i;

  n := LargestMovedPoint(S);
  source := GeneratorsOfGroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsBipartition(source[i], n);
  od;

  return MagmaIsomorphismByFunctionsNC(S,
                                       Semigroup(range),
                                       x -> AsBipartition(x, n),
                                       AsPermutation);
end);

# the converse of the previous method

InstallMethod(IsomorphismPermGroup,
"for a perm bipartition group with generators",
[IsPermBipartitionGroup and HasGeneratorsOfSemigroup],
1, # to beat the method for IsBlockBijectionSemigroup
function(S)
  local n, source, range, i;

  n := DegreeOfBipartitionSemigroup(S);
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsPermutation(source[i]);
  od;

  return MagmaIsomorphismByFunctionsNC(S,
                                       Semigroup(range),
                                       AsPermutation,
                                       x -> AsBipartition(x, n));
end);

InstallMethod(IsomorphismPermGroup,
"for a block bijection semigroup with generators",
[IsBlockBijectionSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local iso, inv;

  if not IsGroupAsSemigroup(S) then
    return fail;
  fi;

  iso := IsomorphismPermGroup(GroupHClass(DClass(S, Representative(S))));
  inv := InverseGeneralMapping(iso);

  return MagmaIsomorphismByFunctionsNC(S,
                                       Range(iso),
                                       x -> x ^ iso,
                                       x -> x ^ inv);
end);

# this is one way, i.e. no converse method

InstallMethod(IsomorphismBlockBijectionSemigroup,
"for an inverse partial perm semigroup with generators",
[IsPartialPermSemigroup and IsInverseSemigroup and
 HasGeneratorsOfInverseSemigroup],
function(S)
  local n, source, range, i, inv;

  n := DegreeOfPartialPermSemigroup(S) + 1;
  source := GeneratorsOfInverseSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsBlockBijection(source[i], n);
  od;

  # AsPartialPerm for a block bijection created using AsBlockBijection with
  # argument a partial perm
  inv := function(x)
    local blocks, n, bigblock, lookup, out, i;

    blocks := x!.blocks;
    n := DegreeOfBipartition(x);
    bigblock := blocks[n];

    # find the images of [1..n]
    lookup := EmptyPlist(n - 1);
    for i in [1 .. n - 1] do
      lookup[blocks[i + n]] := i;
    od;

    # put it together
    out := [1 .. n - 1] * 0;
    for i in [1 .. n - 1] do
      if blocks[i] <> bigblock then
        out[i] := lookup[blocks[i]];
      fi;
    od;

    return PartialPerm(out);
  end;

  return MagmaIsomorphismByFunctionsNC(S,
                                       InverseSemigroup(range), x ->
                                       AsBlockBijection(x, n),
                                       inv);
end);

# this is one way, i.e. no converse method

InstallMethod(IsomorphismBlockBijectionSemigroup,
"for a partial perm semigroup with generators",
[IsPartialPermSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local n, source, range, i, inv;

  n := Maximum(DegreeOfPartialPermSemigroup(S),
               CodegreeOfPartialPermSemigroup(S)) + 1;
  source := GeneratorsOfSemigroup(S);
  range := EmptyPlist(Length(source));

  for i in [1 .. Length(source)] do
    range[i] := AsBlockBijection(source[i], n);
  od;

  # AsPartialPerm for a block bijection created using AsBlockBijection with
  # argument a partial perm
  inv := function(x)
    local blocks, n, bigblock, lookup, out, i;

    blocks := x!.blocks;
    n := DegreeOfBipartition(x);
    bigblock := blocks[n];

    # find the images of [1..n]
    lookup := EmptyPlist(n - 1);
    for i in [1 .. n - 1] do
      lookup[blocks[i + n]] := i;
    od;

    # put it together
    out := [1 .. n - 1] * 0;
    for i in [1 .. n - 1] do
      if blocks[i] <> bigblock then
        out[i] := lookup[blocks[i]];
      fi;
    od;

    return PartialPerm(out);
  end;

  return MagmaIsomorphismByFunctionsNC(S,
                                       Semigroup(range),
                                       x -> AsBlockBijection(x, n),
                                       inv);
end);

# JDM could have a method for IsomorphismBlockBijectionSemigroup for
# IsPartialPermBipartitions too..  or just for general inverse semigroups, via
# composing IsomorphismPartialPermSemigroup and IsomorphismBlockBijection

InstallMethod(IsGeneratorsOfInverseSemigroup, "for a bipartition collection",
[IsBipartitionCollection],
function(coll)
  if IsSemigroup(coll) and HasGeneratorsOfSemigroup(coll) then
    TryNextMethod(); # FIXME why is this necessary?
  fi;

  return ForAll(coll, IsBlockBijection)
   or ForAll(coll, IsPartialPermBipartition);
end);

#

InstallMethod(GeneratorsOfInverseSemigroup,
"for an inverse bipartition semigroup with generators",
[IsBipartitionSemigroup and IsInverseSemigroup and HasGeneratorsOfSemigroup],
function(S)
  local gens, pos, x;

  gens := ShallowCopy(GeneratorsOfSemigroup(S));
  for x in gens do
    pos := Position(gens, x ^ -1);
    if pos <> fail and x <> x ^ -1 then
      Remove(gens, pos);
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

#

InstallMethod(GeneratorsOfInverseMonoid,
"for an inverse bipartition monoid with generators",
[IsBipartitionSemigroup and IsInverseMonoid and HasGeneratorsOfMonoid],
function(s)
  local gens, one, pos, f;

  gens := ShallowCopy(GeneratorsOfMonoid(s));
  one := One(s);
  for f in gens do
    pos := Position(gens, f ^ -1);
    if pos <> fail and (f <> f ^ -1 or f = one) then
      Remove(gens, pos);
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

#

InstallImmediateMethod(GeneratorsOfSemigroup,
IsBipartitionSemigroup and HasGeneratorsOfInverseSemigroup, 0,
function(s)
  local gens, f;

  gens := ShallowCopy(GeneratorsOfInverseSemigroup(s));
  for f in gens do
    if not IsPermBipartition(f) then
      f := f ^ -1;
      if not f in gens then
        Add(gens, f);
      fi;
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

#

InstallImmediateMethod(GeneratorsOfMonoid,
IsBipartitionMonoid and HasGeneratorsOfInverseMonoid, 0,
function(s)
  local gens, f;

  gens := ShallowCopy(GeneratorsOfInverseMonoid(s));
  for f in gens do
    if not IsPermBipartition(f) then
      f := f ^ -1;
      if not f in gens then
        Add(gens, f);
      fi;
    fi;
  od;
  MakeImmutable(gens);
  return gens;
end);

#

InstallMethod(IsBipartitionSemigroupGreensClass, "for a Green's class",
[IsGreensClass], x -> IsBipartitionSemigroup(Parent(x)));

#

InstallMethod(DegreeOfBipartitionSemigroup, "for a bipartition semigroup",
[IsBipartitionSemigroup], s -> DegreeOfBipartition(Representative(s)));
