SEMIGROUPS.StzReplaceSubword := function(rels, subword, newWord)
  local newRels, rel1, rel2, i;
  # Using format of LetterRepAssocWord, can change
  # Global variable eg STZ_GENS := 1, STZ_RELS := 2?

  newRels := List([1 .. Length(rels)], x -> []);
  for i in [1 .. Length(rels)] do
    rel1       := SEMIGROUPS.StzReplaceSubwordRel(rels[i][1], subword, newWord);
    rel2       := SEMIGROUPS.StzReplaceSubwordRel(rels[i][2], subword, newWord);
    newRels[i] := [rel1, rel2];
  od;
  return newRels;
end;

# Searches a single LetterRepAssocWord list and replace instances of subword
# with newWord
SEMIGROUPS.StzReplaceSubwordRel := function(letterRep, subword, newWord)
    local out, pos;
    out := [];
    pos := PositionSublist(letterRep, subword);
    if pos <> fail then
        for i in [1 .. pos - 1] do
            Append(out, [letterRep[i]]);
        od;
        for i in [1 .. Length(newWord)] do
            Append(out, [newWord[i]]);
        od;
        for i in [pos + Length(subword) .. Length(letterRep)] do
            Append(out, [letterRep[i]]);
        od;
        pos := PositionSublist(out, subword);
        if pos <> fail then
            return SEMIGROUPS.StzReplaceSubwordRel(out, subword, newWord);
        else
            return out;
        fi;
    else
        return letterRep;
    fi;
end;

SEMIGROUPS.NewGeneratorName := function(names)
  local alph, Alph, na, nA, names_prefx, names_suffx, int_positions, prefixes,
        prefixes_collected, p, ints, i, name;

  # useful helper variables
  alph := "abcdefghijklmnopqrstuvwxyz";
  Alph := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";

  # SPECIAL CASE 0: empty list
  if Length(names) = 0 then
    return "a";
  fi;

  # SPECIAL CASE 1: only one generator
  if Length(names) = 1 then
    if Length(names[1]) = 1 then
      if names[1][1] in Alph then
        return [First(Alph, x -> not [x] in names)];
      elif names[1][1] in alph then
        return [First(alph, x -> not [x] in names)];
      else
        return "a";
      fi;
    else
      return "a";
    fi;
  fi;

  # SPECIAL CASE 2: single letter names are present. Add an unused letter
  # with the most common capitalisation
  na := Length(Filtered(names, x -> Length(x) = 1 and x[1] in alph));
  nA := Length(Filtered(names, x -> Length(x) = 1 and x[1] in Alph));
  if 2 <= na and na < 26 then
    if na <= nA and nA < 26 then
      return [First(Alph, x -> not [x] in names)];
    else
      return [First(alph, x -> not [x] in names)];
    fi;
  elif 2 <= nA and nA < 26 then
    return [First(Alph, x -> not [x] in names)];
  fi;

  # SPECIAL CASE 3: there are names like s1, s3, s23, etc or x12, etc
  names_prefx := StructuralCopy(names);
  names_suffx := StructuralCopy(names);
  Apply(names_prefx, x -> [x[1]]);
  for name in names_suffx do
    Remove(name, 1);
  od;
  int_positions := PositionsProperty(names_suffx, x -> Int(x) <> fail
                                              and x <> ""
                                              and x[1] <> '-');
  if Length(int_positions) >= 2 then
    prefixes           := names_prefx{int_positions};
    prefixes_collected := Collected(prefixes);
    # look for highest frequency in collected list
    p := prefixes_collected[PositionMaximum(prefixes_collected, x -> x[2])][1];
    # find maximum suffix int, even amongst those with prefix not p
    ints := List(names_suffx{int_positions}, Int);
    i    := Maximum(ints) + 1;
    return Concatenation(p, String(i));
  fi;

  # if none of the special cases are covered, just try s1, s2,... until good
  for i in [1 .. Length(names) + 1] do
    if not Concatenation("s", String(i)) in names then
      return Concatenation("s", String(i));
    fi;
  od;
end;

InstallMethod(StzPresentation, "for a finitely presented semigroup",
[IsFpSemigroup],
function(S)
  local out, rels, type;

  type := NewType(NewFamily("StzFamily", IsStzPresentation),
                  IsStzPresentation and IsComponentObjectRep);

  rels := List(RelationsOfFpSemigroup(S),
              x -> [LetterRepAssocWord(x[1]), LetterRepAssocWord(x[2])]);

  out := rec(gens               := List(GeneratorsOfSemigroup(S),
                                        x -> ViewString(x)),
             rels               := rels,
             unreducedSemigroup := S,
             tietzeForwardMap   := List([1 .. Length(GeneratorsOfSemigroup(S))],
                                        x -> [x]),
             tietzeBackwardMap  := List([1 .. Length(GeneratorsOfSemigroup(S))],
                                        x -> [x]));

  return ObjectifyWithAttributes(out, type,
                                  RelationsOfStzPresentation,
                                  out!.rels,
                                  GeneratorsOfStzPresentation,
                                  out!.gens,
                                  UnreducedSemigroupOfStzPresentation,
                                  out!.unreducedSemigroup,
                                  TietzeForwardMap,
                                  out!.tietzeForwardMap,
                                  TietzeBackwardMap,
                                  out!.tietzeBackwardMap);
end);

# TODO Add checks cause this can break everything
InstallMethod(SetRelationsOfStzPresentation,
[IsStzPresentation, IsList],
function(stz, arg)
  if not ForAll(arg, IsList) or
      not ForAll(arg, x -> ForAll(x, IsList)) or
      not ForAll(arg, x -> ForAll(x, y -> ForAll(y, IsPosInt))) then
        ErrorNoReturn("parameter <arg> must be a list of pairs of words in\n",
                     "LetterRep format,");
  fi;
  stz!.rels := arg;
end);

InstallMethod(RelationsOfStzPresentation,
[IsStzPresentation],
function(stz)
    return stz!.rels;
end);

InstallMethod(UnreducedSemigroupOfStzPresentation,
[IsStzPresentation],
function(stz)
    return stz!.unreducedSemigroup;
end);

InstallMethod(TietzeForwardMap,
[IsStzPresentation],
function(stz)
    return stz!.tietzeForwardMap;
end);

InstallMethod(TietzeBackwardMap,
[IsStzPresentation],
function(stz)
    return stz!.tietzeBackwardMap;
end);

InstallMethod(GeneratorsOfStzPresentation,
[IsStzPresentation],
function(stz)
    return stz!.gens;
end);

InstallMethod(SetGeneratorsOfStzPresentation,
[IsStzPresentation, IsList],
function(stz, newGens)
    stz!.gens := newGens;
end);

# # Storing as attribute kinda breaks it since
# InstallMethod(LetterRepRelationsOfStzPresentation,
# [IsStzPresentation],
# function(stz)
#   local out, rels, rel, relSide, i, exp, letter, newRels, newRelSide, newRel,
#         w;
#   rels := RelationsOfStzPresentation(stz);
#   out := [];

#   # There's something here, I'm fairly sure
#   # w := ObjByExtRep(FamilyObj(stz!.gens[1]), stz!.rels);

#   for rel in [1..Length(rels)] do
#     newRel :=[];
#     for relSide in [1,2] do
#       newRelSide := [];
#       for i in [1 .. Length(rels[rel][relSide])/2]*2 do
#         letter:=rels[rel][relSide][i-1];
#         exp:=rels[rel][relSide][i];
#         newRelSide:=Concatenation(newRelSide,List([1..exp], x-> letter));
#       od;
#       Append(newRel, [newRelSide]);
#     od;
#     Append(out, [newRel]);
#   od;

#   return out;
# end);

InstallMethod(SemigroupOfStzPresentation,
[IsStzPresentation],
function(stz)
    local out, F, rels, gens;
    F := FreeSemigroup(stz!.gens);
    rels := RelationsOfStzPresentation(stz);
    gens := GeneratorsOfSemigroup(F);
    out := F / List(rels, x -> List(x, y -> Product(List(y, z -> gens[z]))));
    SetUnreducedFpSemigroupOfFpSemigroup(out,
                                    UnreducedSemigroupOfStzPresentation(stz));
    # May well break now but this MUST exist so its okay at the moment
    # TCL: this may be useless (we can just define an operation on stz which
    # will return an actual mapping object, rather than storing it as an
    # attribute of the output semigroup)
    SetTietzeForwardMap(out,
                            TietzeForwardMap(stz));
    return out;
end);

InstallMethod(SetTietzeForwardMap,
[IsStzPresentation, IsPosInt, IsList],
function(stz, index, newMap)
    stz!.tietzeForwardMap[index] := newMap;
end);

InstallMethod(SetTietzeBackwardMap,
[IsStzPresentation, IsPosInt, IsList],
function(stz, index, newMap)
    stz!.tietzeBackwardMap[index] := newMap;
end);

InstallMethod(SetTietzeForwardMap,
[IsStzPresentation, IsList],
function(stz, newMaps)
    if not ForAll(newMaps, x -> IsList(x) and ForAll(x, IsPosInt)) then
        ErrorNoReturn("argument <newMaps> must be a list of positive integers,");
    fi;
    stz!.tietzeForwardMap := newMaps;
end);

InstallMethod(SetTietzeBackwardMap,
[IsStzPresentation, IsList],
function(stz, newMaps)
    if not ForAll(newMaps, x -> IsList(x) and ForAll(x, IsPosInt)) then
        ErrorNoReturn("argument <newMaps> must be a list of positive integers,");
    fi;
    stz!.tietzeBackwardMap := newMaps;
end);

InstallMethod(TietzeForwardMapReplaceSubword,
[IsStzPresentation, IsList, IsList],
function(stz, subWord, newSubWord)
    local newMaps;
    newMaps := List(stz!.tietzeForwardMap,
                    x -> SEMIGROUPS.StzReplaceSubwordRel(x,
                                                         subWord,
                                                         newSubWord));
    stz!.tietzeForwardMap := newMaps;
end);

InstallMethod(TietzeBackwardMapReplaceSubword,
[IsStzPresentation, IsList, IsList],
function(stz, subWord, newSubWord)
    local newMaps;
    newMaps := List(stz!.tietzeBackwardMap,
                    x -> SEMIGROUPS.StzReplaceSubwordRel(x,
                                                         subWord,
                                                         newSubWord));
    stz!.tietzeBackwardMap := newMaps;
end);

InstallMethod(Length,
[IsStzPresentation],
function(stz)
    local out, rels, rel;
    out := Length(stz!.gens);
    rels := RelationsOfStzPresentation(stz);
    for rel in rels do
        out := out + Length(rel[1]) + Length(rel[2]);
    od;
    return out;
end);

InstallMethod(ViewString,
[IsStzPresentation],
function(stz)
    local str;
    str := "<fp semigroup presentation with ";
    Append(str, String(Length(stz!.gens)));
    Append(str, " generator");
    if Length(stz!.gens) > 1 then
        Append(str, "s");
    fi;
    Append(str, " and ");
    Append(str, String(Length(stz!.rels)));
    Append(str, " relation");
    if Length(stz!.rels) > 1 then
        Append(str, "s");
    fi;
    Append(str, " with length ");
    Append(str, String(Length(stz)));
    Append(str, ">");
    return PRINT_STRINGIFY(str);
end);

InstallMethod(\<,
[IsStzPresentation, IsStzPresentation],
function(stz1, stz2)
    return Length(stz1) < Length(stz2);
end);

# Unnecessary? Probably
InstallMethod(Size,
[IsStzPresentation],
function(stz)
    return Length(stz);
end);

# TIETZE TRANSFORMATION 1: ADD REDUNDANT RELATION
SEMIGROUPS.TietzeTransformation1 := function(stz, pair)
  local f, free_fam, r, s, fp_fam, w1, w2, p1, p2, rels_copy;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <pair> should be a pair of LetterRep words.
  # TODO there might be a better input format for second argument.
  #
  # Returns:
  # - nothing, and modifies <stz> in place with <pair> added, if <pair> follows
  #   from the relations already present in <stz>.
  # - ErrorNoReturn if the pair cannot be deduced from current relations.

  # TODO argument checks

  # first check that the pair can be deduced from the other relations, by
  # creating fp semigroup with current relations.
  f        := FreeSemigroup(stz!.gens);  # base free semigroup
  free_fam := FamilyObj(f.1);            # marrow for creating free semigp words
  r        := List(stz!.rels,
                   x -> List(x, y -> AssocWordByLetterRep(free_fam, y)));
  s        := f / r;                    # fp semigroup
  fp_fam   := FamilyObj(s.1);           # marrow for creating fp words
  # words first in free semigroup, then map to fp semigroup:
  w1       := AssocWordByLetterRep(free_fam, pair[1]);
  w2       := AssocWordByLetterRep(free_fam, pair[2]);
  p1       := ElementOfFpSemigroup(fp_fam, w1);
  p2       := ElementOfFpSemigroup(fp_fam, w2);
  # check if words are equal in the fp semigroup
  # WARNING: may run forever if undecidable
  if p1 = p2 then
    rels_copy := ShallowCopy(stz!.rels);
    Add(rels_copy, pair);
    stz!.rels := rels_copy;
    return;
  else
    ErrorNoReturn("Argument <pair> must be equal in the presentation <stz>");
  fi;
end;

# TIETZE TRANSFORMATION 2: REMOVE REDUNDANT RELATION
# TODO will this work on stz = rec(gens:=[a], rels:=[[a,a]])?
SEMIGROUPS.TietzeTransformation2 := function(stz, index)
  local rels, pair, new_f, new_gens, new_s, free_fam, w1, w2, fp_fam, p1, p2;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <index> should be the index of the relation needing removing in the
  # overall list of relations.
  #
  # Returns:
  # - nothing, and modifies <stz> in place with <index>^th pair removed, if that
  #   pair follows from the relations already present in <stz>.
  # - ErrorNoReturn if the pair to be removed cannot be deduced from the other
  #   relations.
  rels := ShallowCopy(stz!.rels);
  if index > Length(rels) then
    ErrorNoReturn("Second argument <index> must be less than or equal to \n",
                  "the number of relations of the first argument <stz>");
  fi;

  # create hypothetical fp semigroup that would be the result of removing
  # the requested pair
  pair := rels[index];
  Remove(rels, index);
  new_f    := FreeSemigroup(stz!.gens);
  new_gens := GeneratorsOfSemigroup(new_f);
  new_s    := new_f / List(rels,
                           x -> List(x,
                                     y -> Product(List(y,
                                                       z -> new_gens[z]))));

  # create two associative words
  free_fam := FamilyObj(new_f.1);
  w1       := AssocWordByLetterRep(free_fam, pair[1]);
  w2       := AssocWordByLetterRep(free_fam, pair[2]);

  # map these words to hypothetical fp semigroup words and check equality
  fp_fam := FamilyObj(new_s.1);
  p1     := ElementOfFpSemigroup(fp_fam, w1);
  p2     := ElementOfFpSemigroup(fp_fam, w2);
  # WARNING: may run forever if undecidable
  if p1 = p2 then
    stz!.rels := rels;
    return;
  else
    ErrorNoReturn("Second argument <index> must point to a relation that is \n",
                  "redundant in the presentation <stz>");
  fi;
end;

# TIETZE TRANSFORMATION 3: ADD NEW GENERATOR
SEMIGROUPS.TietzeTransformation3 := function(stz, word)
  local new_gens, new_rels;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <word> should be a LetterRep word
  #
  # Returns:
  # - nothing, and modifies <stz> in place by adding the relation gen=word,
  #   if the input is reasonable.
  # - ErrorNoReturn if the generator number already exists in stz.

  # TODO could be custom specification of what generator string should be
  # TODO argument checks

  # Add new generator string to the list of gens in similar format
  new_gens := ShallowCopy(stz!.gens);
  new_rels := ShallowCopy(stz!.rels);
  Add(new_gens, SEMIGROUPS.NewGeneratorName(stz!.gens));
  Add(new_rels, [word, [Length(stz!.gens) + 1]]);
  SetGeneratorsOfStzPresentation(stz, new_gens);
  SetRelationsOfStzPresentation(stz, new_rels);
end;

# TIETZE TRANSFORMATION 4: REMOVE GENERATOR
SEMIGROUPS.TietzeTransformation4 := function(stz, gen)
  local found_expr, expr, index, i, decrement, tempRels, tempGens;
  # Arguments:
  # - <stz> should be a Semigroup Tietze object.
  # - <gen> should be a pos int (number of generator to be removed)
  #
  # Returns:
  # - nothing, and modifies <stz> in place by removing generator number <gen>,
  #   if this function can find an expression for that generator as a product
  #   of some combination of other generators.
  # - ErrorNoReturn if this is impossible.

  # TODO probably very reasonable to have a NC version where where you specify
  # generator number and word to replace it with, and it just does it without
  # asking.

  # TODO also an intermediate implementation is to have a method for this
  # function which takes in three arguments stz, gen, word and subs word for gen
  # IF it can verify that [gen] = word in stz.

  # argument checks
  if Length(stz!.gens) = 1 then
    ErrorNoReturn("cannot remove only remaining generator",
                  ViewString(stz!.gens[1]));
  fi;
  if gen > Length(stz!.gens) then
    ErrorNoReturn("second argument must be no greater than the total\n",
                  "number of generators");
  fi;

  # find expression for gen
  # TODO this can be less lazy than just looking for an explicit relation
  # NOTE: on the above todo, in fairness we could implement only lazy checking
  # and get the user to add a reduandant relation using Tietze 1, then apply
  # Tietze 4.
  found_expr := false;
  for i in [1 .. Length(stz!.rels)] do
    if stz!.rels[i][1] = [gen] and not gen in stz!.rels[i][2] then
      found_expr := true;
      expr       := ShallowCopy(stz!.rels[i][2]);  # TODO necessary?
      index      := i;
      break;
    elif stz!.rels[i][2] = [gen] and not gen in stz!.rels[i][1] then
      found_expr := true;
      expr       := ShallowCopy(stz!.rels[i][1]);  # TODO necessary?
      index      := i;
      break;
    fi;
  od;

  # check we found one
  if not found_expr then
    ErrorNoReturn("no explicit relation expressing second argument as a\n",
                  "combination of other generators");
  fi;

  # Define decrement function to bump down generator numbers past the one
  # we're going to remove
  decrement := function(z)
    if z <= gen then  # shouldn't be equal but just in case
      return z;
    else
      return z - 1;
    fi;
  end;

  # update mapping component
  TietzeForwardMapReplaceSubword(stz, [gen], expr);
  tempMaps := ShallowCopy(TietzeForwardMap(stz));
  Apply(tempMaps, x -> List(x, decrement));
  SetTietzeForwardMap(stz, tempMaps);

  # otherwise, sub in expression we found and remove relation we used for gen
  # TODO stop the middle man ext rep conversion
  tempRels := ShallowCopy(RelationsOfStzPresentation(stz));
  Remove(tempRels, index);
  tempRels := SEMIGROUPS.StzReplaceSubword(tempRels, [gen], expr);
  SetRelationsOfStzPresentation(stz, tempRels);
  Apply(stz!.rels, x -> List(x, y -> List(y, decrement)));

  # remove generator.
  tempGens := ShallowCopy(GeneratorsOfStzPresentation(stz));
  Remove(tempGens, gen);
  SetGeneratorsOfStzPresentation(stz, tempGens);
end;
