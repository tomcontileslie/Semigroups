#############################################################################
##
##  isomorph.gi
##  Copyright (C) 2014-20                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains methods for finding isomorphisms between semigroups and
# some related methods.
#
# Isomorphism.* methods for transformation, partial perm, bipartition and Rees
# 0-matrix semigroups can be found in the files semitrans.gi, semipperm.gi,
# semibipart.gi , and reesmat.gi.

InstallMethod(OnMultiplicationTable, "for a multiplication table, and perm",
[IsRectangularTable, IsPerm],
function(table, p)
  local out;
  out := Permuted(table, p);
  Apply(out, x -> OnTuples(x, p));
  Apply(out, x -> Permuted(x, p));
  return out;
end);

InstallMethod(CanonicalMultiplicationTablePerm, "for a semigroup",
[IsSemigroup],
function(S)
  local D, p;
  D := SEMIGROUPS.CanonicalDigraph(S);
  p := BlissCanonicalLabelling(D[1], D[2]);
  return RestrictedPerm(p, [1 .. Size(S)]);
end);

InstallMethod(CanonicalMultiplicationTable, "for a semigroup",
[IsSemigroup],
function(S)
  return OnMultiplicationTable(MultiplicationTable(S),
                               CanonicalMultiplicationTablePerm(S));
end);

# Returns the lex-least multiplication table of the semigroup <S>
InstallMethod(SmallestMultiplicationTable, "for a semigroup",
[IsSemigroup],
function(S)
  local LitNum, NumLit, DiagonalToLits, TableToLits, LitsToTable, OnLiterals,
  n, phi, lits, p, stab, table;

  LitNum := function(ln, n)
    return [QuoInt(ln - 1, n ^ 2) + 1,
            QuoInt((ln - 1) mod n ^ 2, n) + 1,
            (ln - 1) mod n + 1];
  end;

  NumLit := function(lit, n)
    # lit = [ row, col, val ]
    return (lit[1] - 1) * n ^ 2 + (lit[2] - 1) * n + lit[3];
  end;

  DiagonalToLits := function(diag, n)
    return List([1 .. n], i -> NumLit([i, i, diag[i]], n));
  end;

  TableToLits := function(table, n)
    local literals, val, i, j;
    literals := [];
    for i in [1 .. n] do
      for j in [1 .. n] do
        val := table[i][j];
        Add(literals, NumLit([i, j, val], n));
      od;
    od;
    return literals;
  end;

  LitsToTable := function(lits, n)
    local table, i, j;
    table := [];
    for i in [0 .. n - 1] do
      table[i + 1] := [];
      for j in [1 .. n] do
        table[i + 1][j] := LitNum(lits[i * n + j], n)[3];
      od;
    od;
    return table;
  end;

  OnLiterals := n -> function(ln, pi)
    return NumLit(OnTuples(LitNum(ln, n), pi), n);
  end;

  # for not too big semigroups...
  n   := Size(S);
  phi := ActionHomomorphism(SymmetricGroup(n), [1 .. n ^ 3], OnLiterals(n));

  # get minimal representative of diagonal
  lits := DiagonalToLits(DiagonalOfMat(MultiplicationTable(S)), n);
  p    := MinimalImagePerm(Image(phi), lits, OnSets);
  lits := OnSets(lits, p);

  # work with stabiliser of new diagonal on changed table
  stab  := Stabilizer(Image(phi), lits, OnSets);
  table := OnSets(TableToLits(MultiplicationTable(S), n), p);

  return LitsToTable(MinimalImage(stab, table, OnSets), n);
end);

InstallMethod(IsIsomorphicSemigroup, "for semigroups",
[IsSemigroup, IsSemigroup],
function(S, T)
  return IsomorphismSemigroups(S, T) <> fail;
end);

InstallMethod(IsomorphismSemigroups, "for finite simple semigroups",
[IsSimpleSemigroup and IsFinite, IsSimpleSemigroup and IsFinite],
function(S, T)
  local isoS, rmsS, invT, rmsT, iso;

  # Take an isomorphism of S to an RMS if appropriate
  if not (IsReesMatrixSemigroup(S) and IsWholeFamily(S)
      and IsPermGroup(UnderlyingSemigroup(S))) then
    isoS := IsomorphismReesMatrixSemigroupOverPermGroup(S);
    rmsS := Range(isoS);
  else
    rmsS := S;
  fi;
  # Take an isomorphism of T to an RMS if appropriate
  if not (IsReesMatrixSemigroup(T) and IsWholeFamily(T)
      and IsPermGroup(UnderlyingSemigroup(T))) then
    invT := IsomorphismReesMatrixSemigroupOverPermGroup(T);
    invT := InverseGeneralMapping(invT);
    rmsT := Source(invT);
  else
    rmsT := T;
  fi;

  # Uses more specific method to find isomorphism between RMS/RZMS
  iso := IsomorphismSemigroups(rmsS, rmsT);
  if iso = fail then
    return fail;
  elif IsBound(isoS) and IsBound(invT) then
    return CompositionMapping(invT, iso, isoS);
  elif IsBound(isoS) then
    return CompositionMapping(iso, isoS);
  elif IsBound(invT) then
    return CompositionMapping(invT, iso);
  fi;
  # If this method was selected, at least one of isoS and invT is bound
end);

InstallMethod(IsomorphismSemigroups, "for finite 0-simple semigroups",
[IsZeroSimpleSemigroup and IsFinite, IsZeroSimpleSemigroup and IsFinite],
function(S, T)
  local isoS, rmsS, invT, rmsT, iso;

  # Take an isomorphism of S to an RZMS if appropriate
  if not (IsReesZeroMatrixSemigroup(S) and IsWholeFamily(S)
      and IsPermGroup(UnderlyingSemigroup(S))) then
    isoS := IsomorphismReesZeroMatrixSemigroupOverPermGroup(S);
    rmsS := Range(isoS);
  else
    rmsS := S;
  fi;
  # Take an isomorphism of T to an RZMS if appropriate
  if not (IsReesZeroMatrixSemigroup(T) and IsWholeFamily(T)
      and IsPermGroup(UnderlyingSemigroup(T))) then
    invT := IsomorphismReesZeroMatrixSemigroupOverPermGroup(T);
    invT := InverseGeneralMapping(invT);
    rmsT := Source(invT);
  else
    rmsT := T;
  fi;

  # Uses more specific method to find isomorphism between RMS/RZMS
  iso := IsomorphismSemigroups(rmsS, rmsT);
  if iso = fail then
    return fail;
  elif IsBound(isoS) and IsBound(invT) then
    return CompositionMapping(invT, iso, isoS);
  elif IsBound(isoS) then
    return CompositionMapping(iso, isoS);
  elif IsBound(invT) then
    return CompositionMapping(invT, iso);
  fi;
  # If this method was selected, at least one of isoS and invT is bound
end);

InstallMethod(IsomorphismSemigroups, "for finite monogenic semigroups",
[IsMonogenicSemigroup and IsFinite, IsMonogenicSemigroup and IsFinite],
function(S, T)
  local s, t, SS, TT, map, inv;

  if IsSimpleSemigroup(S) then
    if IsSimpleSemigroup(T) then
      return IsomorphismSemigroups(S, T);
    else
      return fail;
    fi;
  elif Size(S) <> Size(T) or NrDClasses(S) <> NrDClasses(T) then
    return fail;
  fi;

  # Monogenic semigroups are of the same size, are not groups, and have the
  # same number of D-classes by this point, and so they are isomorphic
  s := Representative(MaximalDClasses(S)[1]);
  t := Representative(MaximalDClasses(T)[1]);
  SS := Semigroup(s);
  TT := Semigroup(t);
  map := x -> t ^ Length(Factorization(SS, x));
  inv := x -> s ^ Length(Factorization(TT, x));
  return MagmaIsomorphismByFunctionsNC(S, T, map, inv);
end);

# TODO when/if Digraphs has vertex coloured digraphs, make this a user facing
# function
SEMIGROUPS.CanonicalDigraph := function(S)
  local M, n, Color1Node, Color2Node, Widget, out, colors, x, y, z;

  M := MultiplicationTable(S);
  n := Size(S);

  # The original nodes
  Color1Node := IdFunc;

  # i = 1 .. n, j = 1 .. n
  Color2Node := function(i, j)
    Assert(1, 1 <= i and i <= n);
    Assert(1, 1 <= j and j <= n);
    return i * n + j;
  end;

  Widget := function(i)
    Assert(1, 1 <= i and i <= n);
    return n ^ 2 + n + i;
  end;

  out := List([1 .. n ^ 2 + 2 * n], x -> []);
  colors := ListWithIdenticalEntries(n, 1);
  Append(colors, ListWithIdenticalEntries(n ^ 2, 2));
  Append(colors, ListWithIdenticalEntries(n, 3));

  for x in [1 .. n] do
    Add(out[Color2Node(x, x)], Widget(x));
    for y in [1 .. n] do
      Add(out[Color1Node(x)], Color2Node(x, y));
      Add(out[Color2Node(x, y)], Color1Node(M[x][y]));
      for z in [1 .. n] do
        if z <> x then
          Add(out[Color2Node(x, y)], Color2Node(z, y));
        fi;
      od;
    od;
  od;
  return [Digraph(out), colors];
end;

InstallMethod(IsomorphismSemigroups, "for semigroups",
[IsSemigroup, IsSemigroup],
function(S, T)
  local invariants, map, DS, DT, p, inv;

  # TODO more invariants
  invariants := [IsFinite, IsSimpleSemigroup, IsZeroSimpleSemigroup, Size,
                 NrLClasses, NrDClasses, NrRClasses, NrHClasses, NrIdempotents];
  if S = T then
    return MagmaIsomorphismByFunctionsNC(S, T, IdFunc, IdFunc);
  elif IsFinite(S) <> IsFinite(T) then
    return fail;
  elif not IsFinite(S) then
    TryNextMethod();
  elif IsTransformationSemigroup(T)
      and HasIsomorphismTransformationSemigroup(S) then
    map := IsomorphismTransformationSemigroup(S);
    if T = Range(map) then
      return map;
    fi;
  elif (IsSimpleSemigroup(S) and IsSimpleSemigroup(T))
      or (IsZeroSimpleSemigroup(S) and IsZeroSimpleSemigroup(T))
      or (IsMonogenicSemigroup(S) and IsMonogenicSemigroup(T)) then
    return IsomorphismSemigroups(S, T);
  elif not ForAll(invariants,
                  func -> func(S) = func(T)) then
    return fail;
  fi;

  DS := SEMIGROUPS.CanonicalDigraph(S);
  DT := SEMIGROUPS.CanonicalDigraph(T);
  p := IsomorphismDigraphs(DS[1], DT[1], DS[2], DT[2]);
  if p = fail then
    return fail;
  fi;
  p := RestrictedPerm(p, [1 .. Size(S)]);
  map := x -> AsSSortedList(T)[PositionSorted(S, x) ^ p];
  inv := x -> AsSSortedList(S)[PositionSorted(T, x) ^ (p ^ -1)];
  return MagmaIsomorphismByFunctionsNC(S, T, map, inv);
end);

InstallMethod(AutomorphismGroup, "for a semigroup",
[IsSemigroup],
function(S)
  local D, G, X, map, Y, H;
  # JDM: I'm not sure I trust the AutomorphismGroup methods for Rees 0-matrix
  # semigroups, and so this method doesn't try to use them in the case that S
  # is 0-simple, or simple. Note that the first test in tst/standard/isorms.tst
  # is much much faster using the R(Z)MS specific method.

  # TODO use the R(Z)MS specific method if we have a (0-)simple semigroup.

  if not IsFinite(S) then
    TryNextMethod();
  fi;
  D := SEMIGROUPS.CanonicalDigraph(S);
  G := AutomorphismGroup(D[1], D[2]);
  X := List(GeneratorsOfGroup(G), x -> RestrictedPerm(x, [1 .. Size(S)]));
  G := Group(X);
  map := p -> (x -> AsSSortedList(S)[PositionSorted(S, x) ^ p]);
  Y := List(GeneratorsOfGroup(G),
            p -> MagmaIsomorphismByFunctionsNC(S,
                                               S,
                                               map(p),
                                               map(p ^ -1)));
  H := Group(Y);
  SetNiceMonomorphism(H, GroupHomomorphismByImagesNC(H, G, Y, X));
  SetIsHandledByNiceMonomorphism(H, true);
  UseIsomorphismRelation(H, G);
  return H;
end);

InstallMethod(IsomorphismSemigroup,
"for IsStrongSemilatticeOfSemigroups and a Clifford semigroup",
[IsStrongSemilatticeOfSemigroups, IsSemigroup and IsFinite],
function(filt, S)
  local A, idemps, n, D, N, L, idemp, H, map, i, j;
  # decomposes a finite Clifford semigroup S into a strong semilattice of
  # groups and returns an SSS object.
  if not (IsCliffordSemigroup(S) and IsFinite(S)) then
    TryNextMethod();
  fi;
  # There should be one idempotent per D-class, i.e. per semilattice element
  # since the semilattice decomposition is by J-classes, and J = D here
  A      := Semigroup(Idempotents(S));
  idemps := Elements(A);
  n      := Size(idemps);

  # create semilattice
  D := DigraphReflexiveTransitiveReduction(Digraph(NaturalPartialOrder(A)));
  # currently wrong way round
  D := DigraphReverse(D);
  N := OutNeighbours(D);

  # populate list of semigroups in semilattice
  L := [];
  for i in [1 .. n] do
    idemp := idemps[i];  # the idempotent of this D-class
    Add(L, Semigroup(DClass(S, idemp)));
  od;

  # populate list of homomorphisms
  H := [];
  for i in [1 .. n] do
    idemp := idemps[i];
    Add(H, []);
    for j in N[i] do
      map := function(elm)
        return idemp * elm;
      end;
      Add(H[i], MappingByFunction(L[j], L[i], map));
    od;
  od;

  return StrongSemilatticeOfSemigroups(D, L, H);
  # TODO make this output the isom rather than the range
end);
