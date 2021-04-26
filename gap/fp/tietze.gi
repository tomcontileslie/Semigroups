SEMIGROUPS.StzReplaceSubword := function(rels, subword, newWord)
  local newRels, rel1, rel2, i;

  newRels := List([1 .. Length(rels)], x -> []);
  for i in [1 .. Length(rels)] do
    rel1 := SEMIGROUPS.StzReplaceSubwordRel(rels[i][1], subword, newWord);
    rel2 := SEMIGROUPS.StzReplaceSubwordRel(rels[i][2], subword, newWord);
    newRels[i] := [rel1, rel2];
  od;
  return newRels;
end;

SEMIGROUPS.StzReplaceSubwordRel := function(word, subword, newWord)
  local out, k, l, i;
  # Searches a single LetterRepAssocWord list and replaces instances of
  # subword with newWord.

  # build word up as we read through the old word.
  out := [];
  k   := Length(subword);
  l   := Length(word);
  i   := 1;  # current index that we are looking at when trying to see subword
  while i <= l do
    if word{[i .. Minimum(i + k - 1, l)]} = subword then
      # in this, case the word starting at i needs to be substituted out.
      # (the minimum is there to make sure we don't fall off the end of word)
      Append(out, newWord);
      # jump to end of occurrence
      i := i + k;
    else
      # move over by one and append the original letter, since the word is not
      # seen here.
      Add(out, word[i]);
      i := i + 1;
    fi;
  od;
  return out;
end;

# takes in a letterrep word and replaces every letter with its expression in
# dict.
# NOTE: does not check arguments. Assumes in good faith that every integer
# in word has an entry in the list <dict>.
SEMIGROUPS.StzExpandWord := function(word, dict)
  local out, letter;
  out := [];
  for letter in word do
    Append(out, dict[letter]);
  od;
  return out;
end;

SEMIGROUPS.NewGeneratorName := function(names_immut)
  local alph, Alph, na, nA, names_prefx, names_suffx, int_positions, prefixes,
  prefixes_collected, p, ints, i, name, names;
  names := [];
  for name in names_immut do
    Add(names, ShallowCopy(name));
  od;

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
  names_prefx := ShallowCopy(names);
  names_suffx := ShallowCopy(names);
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

#####
##### TODO: consider removing
#####
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

InstallMethod(TietzeIsomorphism,
[IsStzPresentation],
function(stz)
  local source, range, forward_dict, forward_map, backward_dict, backward_map;
  source := UnreducedSemigroupOfStzPresentation(stz);
  range := SemigroupOfStzPresentation(stz);

  # build forward map
  forward_dict := TietzeForwardMap(stz);
  forward_map  := function(word)
    local new_word;
    new_word := SEMIGROUPS.StzExpandWord(
                LetterRepAssocWord(UnderlyingElement(word)), forward_dict);
    return Product(new_word, x -> GeneratorsOfSemigroup(range)[x]);
  end;

  # build backward map
  backward_dict := TietzeBackwardMap(stz);
  backward_map  := function(word)
    local new_word;
    new_word := SEMIGROUPS.StzExpandWord(
                LetterRepAssocWord(UnderlyingElement(word)), backward_dict);
    return Product(new_word, x -> GeneratorsOfSemigroup(source)[x]);
  end;

  # TODO: are we okay to assume this is necessarily an isomorphism?
  return MagmaIsomorphismByFunctionsNC(source,
                                       range,
                                       forward_map,
                                       backward_map);

end);

InstallMethod(SetTietzeForwardMap,
[IsStzPresentation, IsPosInt, IsList],
function(stz, index, newMap)
    stz!.tietzeForwardMap[index] := newMap;
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
    if Length(stz!.rels) <> 1 then
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

InstallMethod(StzSimplifyPresentation,
[IsStzPresentation],
function(stz)
  local len, newLen, transformApplied;
  len := Length(stz);
  transformApplied := true;
  Info(InfoWarning, 1, ViewString(stz));
  while transformApplied do
    transformApplied := StzSimplifyOnce(stz);
    Info(InfoWarning, 1, ViewString(stz));
  od;
end);

InstallMethod(SimplifiedFpPresentation,
[IsFpSemigroup],
function(S)
  local T, map;
  map := SimplifyFpPresentation(S);
  T := Range(map);
  SetUnreducedFpSemigroupOfFpSemigroup(T, S);
  SetFpTietzeIsomorphism(T, map);
  return T;
end);

InstallMethod(SimplifyFpPresentation,
[IsFpSemigroup],
function(S)
  local stz;
  stz := StzPresentation(S);
  StzSimplifyPresentation(stz);
  return TietzeIsomorphism(stz);
end);

# TIETZE TRANSFORMATION 1: INTERNAL: ADD REDUNDANT RELATION - NO CHECK
SEMIGROUPS.TietzeTransformation1 := function(stz, pair)
  local rels_copy;
  rels_copy := ShallowCopy(stz!.rels);
  Add(rels_copy, pair);
  stz!.rels := rels_copy;
  return;
end;

# TIETZE TRANSFORMATION 2: INTERNAL: REMOVE REDUNDANT RELATION - NO CHECK
# TODO will this work on stz = rec(gens:=[a], rels:=[[a,a]])?
SEMIGROUPS.TietzeTransformation2 := function(stz, index)
  local rels;
  rels := ShallowCopy(RelationsOfStzPresentation(stz));
  Remove(rels, index);
  stz!.rels := rels;
end;

# TIETZE TRANSFORMATION 3: ADD NEW GENERATOR
SEMIGROUPS.TietzeTransformation3 := function(stz, word)
  local new_gens, new_rels, back_word, new_maps, letter;
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

  # Now we need to update the backwards maps to express the new generator in
  # terms of the original generators.
  back_word := [];
  new_maps  := ShallowCopy(TietzeBackwardMap(stz));
  for letter in word do
    Append(back_word, new_maps[letter]);
  od;
  Add(new_maps, back_word);
  SetTietzeBackwardMap(stz, new_maps);
end;

# TIETZE TRANSFORMATION 4: REMOVE GENERATOR
SEMIGROUPS.TietzeTransformation4 := function(stz, gen)
  local found_expr, expr, index, decrement, tempMaps, tempRels, tempGens, i;
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

  # update forward mapping component
  TietzeForwardMapReplaceSubword(stz, [gen], expr);
  tempMaps := ShallowCopy(TietzeForwardMap(stz));
  Apply(tempMaps, x -> List(x, decrement));
  SetTietzeForwardMap(stz, tempMaps);

  # remove generator from backward mapping component
  tempMaps := ShallowCopy(TietzeBackwardMap(stz));
  Remove(tempMaps, gen);
  SetTietzeBackwardMap(stz, tempMaps);

  # sub in expression we found and remove relation we used for gen
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

InstallMethod(StzPrintRelation, "for an stz presentation,",
[IsStzPresentation, IsPosInt],
function(stz, i)
  local str, rels, f, gens, w1, w2, out;
  rels := RelationsOfStzPresentation(stz);
  if i > Length(rels) then
    return fail;
  else
    f    := FreeSemigroup(GeneratorsOfStzPresentation(stz));
    gens := GeneratorsOfSemigroup(f);
    w1  := Product(rels[i][1], x -> gens[x]);
    w2  := Product(rels[i][2], x -> gens[x]);
    out := Concatenation(PrintString(i),
                        ". ",
                        PrintString(w1),
                        " = ",
                        PrintString(w2));
    return out;
  fi;
end);

InstallMethod(StzPrintRelations, "For an stz presentation",
[IsStzPresentation],
function(stz)
  local rels, f, gens, w1, w2, out, i;
  # This function displays the current relations in terms of the current
  # generators for a semigroup Tietze presentation.
  # We'd like patterns to be grouped, i.e. abab=(ab)^2 when displayed. To
  # do this we sneakily piggyback off display methods for the free semigroup.
  if RelationsOfStzPresentation(stz) = [] then
    Info(InfoWarning, 1, "There are no relations in the presentation <stz>");
  fi;

  rels := RelationsOfStzPresentation(stz);
  f    := FreeSemigroup(GeneratorsOfStzPresentation(stz));
  gens := GeneratorsOfSemigroup(f);

  for i in [1 .. Length(rels)] do
    w1  := Product(rels[i][1], x -> gens[x]);
    w2  := Product(rels[i][2], x -> gens[x]);
    out := Concatenation(PrintString(i),
                         ". ",
                         PrintString(w1),
                         " = ",
                         PrintString(w2));
    Info(InfoWarning, 1, out);
  od;
end);

InstallMethod(StzPrintGenerators, "For an stz presentation",
[IsStzPresentation],
function(stz)
  local flat, gens, out, rel, i;
  # This function displays a list of generators and number of occurences
  # of each

  # warn if there are no generators in the list (not sure this could happen)
  if GeneratorsOfStzPresentation(stz) = [] then
    Info(InfoWarning, 1, "There are no generators in the presentation <stz>");
  fi;

  # create flat flat list of relations to count occurrences
  flat := [];
  for rel in RelationsOfStzPresentation(stz) do
    Append(flat, rel[1]);
    Append(flat, rel[2]);
  od;

  # enumerate and count generators
  gens := GeneratorsOfStzPresentation(stz);
  for i in [1 .. Length(gens)] do
    out := Concatenation(PrintString(i),
                         ".  ",
                         gens[i],
                         "  ",
                         PrintString(Number(flat, x -> x = i)),
                         " occurrences");
    Info(InfoWarning, 1, out);
  od;
end);

###### USER-FRIENDLY TIETZE TRANSFORMATIONS

### TIETZE 1
InstallMethod(StzAddRelation, "For an stz presentation and a pair of words",
[IsStzPresentation, IsList],
function(stz, pair)
  local n, f, free_fam, r, s, fp_fam, w1, w2, p1, p2, word, letter;
  # <pair> should be a pair of LetterRep words.

  # argument checks:
  if Length(pair) <> 2 then
    ErrorNoReturn("Second argument <pair> should be a list of length 2");
  fi;
  n := Length(stz!.gens);
  for word in pair do
    if not IsList(word) then
      TryNextMethod();  # pass this on to the case where the list may be a pair
                        # of words in OG semigroup
    elif Length(word) = 0 then
      ErrorNoReturn("Words in second argument <pair> should be non-empty");
    else
      for letter in word do
        if not (IsPosInt(letter) and letter <= n) then
          ErrorNoReturn("Words in second argument <pair> should be lists of\n",
                        "pos ints no greater than the number of generators\n",
                        "of first argument <stz>");
        fi;
      od;
    fi;
  od;

  # check that the pair can be deduced from the other relations, by
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
    SEMIGROUPS.TietzeTransformation1(stz, pair);
    return;
  else
    ErrorNoReturn("Argument <pair> must be equal in the presentation <stz>");
  fi;
end);

InstallMethod(StzAddRelation,
"For an stz presentation and a pair of semigroup elements",
[IsStzPresentation, IsList],
function(stz, pair)
  local s, pairwords, word;
  # argument checks
  if Length(pair) <> 2 then
    ErrorNoReturn("Second argument <pair> should be a list of length 2");
  fi;

  # retrieve original semigroup
  s := UnreducedSemigroupOfStzPresentation(stz);
  for word in pair do
    if not word in s then
      TryNextMethod();
    fi;
  od;

  # convert into words in original semigroup
  pairwords := List(pair, UnderlyingElement);
  Apply(pairwords, LetterRepAssocWord);
  # map to words in new semigroup
  Apply(pairwords, x -> SEMIGROUPS.StzExpandWord(x, TietzeForwardMap(stz)));

  # apply tietze1, with argument checks
  StzAddRelation(stz, pairwords);
  return;
end);

### TIETZE 1: NO CHECK
InstallMethod(StzAddRelationNC, "For an stz presentation and a pair of words",
[IsStzPresentation, IsList],
function(stz, pair)
  local n, word, letter;
  # <pair> should be a pair of LetterRep words.

  # argument checks:
  if Length(pair) <> 2 then
    ErrorNoReturn("Second argument <pair> should be a list of length 2");
  fi;
  n := Length(stz!.gens);
  for word in pair do
    if not IsList(word) then
      TryNextMethod();  # pass this on to the case where the list may be a pair
                        # of words in OG semigroup
    elif Length(word) = 0 then
      ErrorNoReturn("Words in second argument <pair> should be non-empty");
    else
      for letter in word do
        if not (IsPosInt(letter) and letter <= n) then
          ErrorNoReturn("Words in second argument <pair> should be lists of\n",
                        "pos ints no greater than the number of generators\n",
                        "of first argument <stz>");
        fi;
      od;
    fi;
  od;

  # WARNING: no checks are run to verify that the pair is redundant. This
  # may result in an output semigroup which is non-isomorphic to the
  # starting semigroup.
  SEMIGROUPS.TietzeTransformation1(stz, pair);
  return;
end);

InstallMethod(StzAddRelationNC,
"For an stz presentation and a pair of semigroup elements",
[IsStzPresentation, IsList],
function(stz, pair)
  local s, pairwords, word;
  # argument checks
  if Length(pair) <> 2 then
    ErrorNoReturn("Second argument <pair> should be a list of length 2");
  fi;

  # retrieve original semigroup
  s := UnreducedSemigroupOfStzPresentation(stz);
  for word in pair do
    if not word in s then
      TryNextMethod();
    fi;
  od;

  # convert into words in original semigroup
  pairwords := List(pair, UnderlyingElement);
  Apply(pairwords, LetterRepAssocWord);
  # map to words in new semigroup
  Apply(pairwords, x -> SEMIGROUPS.StzExpandWord(x, TietzeForwardMap(stz)));

  # apply tietze1, without argument checks
  # WARNING: no checks are run to verify that the pair is redundant. This
  # may result in an output semigroup which is non-isomorphic to the
  # starting semigroup.
  SEMIGROUPS.TietzeTransformation1(stz, pairwords);
  return;
end);

### TIETZE 2
InstallMethod(StzRemoveRelation,
"For an stz presentation and a pos int",
[IsStzPresentation, IsPosInt],
function(stz, index)
  local rels, pair, new_f, new_gens, new_s, free_fam, w1, w2, fp_fam, p1, p2;
  # <index> should be the index of the relation needing removing in the
  # overall list of relations.

  # argument check: valid index
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
    SEMIGROUPS.TietzeTransformation2(stz, index);
    return;
  else
    ErrorNoReturn("Second argument <index> must point to a relation that is \n",
                  "redundant in the presentation <stz>");
  fi;
end);

### TIETZE 2: NO CHECK
InstallMethod(StzRemoveRelationNC,
"For an stz presentation and a pos int",
[IsStzPresentation, IsPosInt],
function(stz, index)
  if index > Length(RelationsOfStzPresentation(stz)) then
    ErrorNoReturn("Second argument <index> must be less than or equal to \n",
                  "the number of relations of the first argument <stz>");
  fi;

  # WARNING: no checks are run to verify that the pair is redundant. This
  # may result in an output semigroup which is non-isomorphic to the
  # starting semigroup.
  SEMIGROUPS.TietzeTransformation2(stz, index);
  return;
end);

SEMIGROUPS.StzCountRelationSubwords := function(stz, subWord)
  local count, relSide, rel, rels, pos, len, relSideCopy;
  rels := RelationsOfStzPresentation(stz);
  len := Length(subWord);
  count := 0;
  for rel in rels do
    for relSide in rel do
      pos := PositionSublist(relSide, subWord);
      relSideCopy := ShallowCopy(relSide);
      while pos <> fail do
        count := count + 1;
        relSideCopy := List([(pos + len) .. Length(relSideCopy)],
                            x -> relSideCopy[x]);
        pos := PositionSublist(relSideCopy, subWord);
      od;
    od;
  od;
  return count;
end;

SEMIGROUPS.StzFrequentSubwordCheck := function(stz)
  local best_gain, best_word, flat, count_occurrences, n, c, gain, word,
        pair, i, j;
  # SUPER INEFFICIENT (~n^3), do something about this eventually (@Reinis?)
  # Look at every subword, count how many times it appears, and see whether
  # introducing a new generator equal to a given subword would make the
  # whole presentation shorter
  best_gain := 0;   # best reduction seen so far
  best_word := [];  # word currently holding record

  # flat list of words (don't care about which one is related to which)
  flat := [];
  for pair in stz!.rels do
    Append(flat, ShallowCopy(pair));  # TODO might not need shallow copy
  od;

  # function to count occurrences of subword in list of lists
  count_occurrences := function(list, subword)
    local count, k, l, i, word;
    count := 0;
    k     := Length(subword);
    for word in list do
      l := Length(word);
      i := 1;  # index at which to start counting
      while i <= l - k + 1 do
        if word{[i .. i + k - 1]} = subword then
          count := count + 1;
          # jump to end of occurrence
          i := i + k;
        else
          # move over by one
          i := i + 1;
        fi;
      od;
    od;
    return count;
  end;

  # now check for every subword, how many times it appears
  for word in flat do
    # N.B. ASSUMES WORDS NON-EMPTY
    n := Length(word);
    for i in [1 .. n - 1] do
      for j in [i + 1 .. n] do
        c := count_occurrences(flat, word{[i .. j]});
        # now calculate what a gain that would be:
        # subbing out every instance of word{[i .. j]} for a word of length 1
        # makes us gain j - i characters per substitution
        # BUT, we also have a new generator cost of 1
        # AND a new relation cost of 3 + j - i
        gain := (c - 1) * (j - i) - 3;
        if gain > best_gain then
          best_gain := gain;
          best_word := word{[i .. j]};
        fi;
      od;
    od;
  od;
  return rec(reduction := Length(stz) - best_gain,
             word := best_word);
end;

SEMIGROUPS.StzFrequentSubwordApply := function(stz, metadata)
  local word, rels, n, gens, k, shortened_rels, new_rel, i, str, f, aWord;

  # have received instruction to sub out metadata.word for something shorter.
  word := metadata.word;
  rels := ShallowCopy(RelationsOfStzPresentation(stz));
  n    := Length(rels);
  gens := ShallowCopy(GeneratorsOfStzPresentation(stz));
  k    := Length(gens);

  # Build message
  str := "<Creating new generator to replace instances of word: ";
  f := FreeSemigroup(gens);
  aWord := AssocWordByLetterRep(FamilyObj(f.1), metadata.word);
  Append(str, PrintString(aWord));
  Append(str, ">");
  Info(InfoWarning, 1, PRINT_STRINGIFY(str));

  # first, add new generator.
  SEMIGROUPS.TietzeTransformation3(stz, word);

  # then, go through and add loads of relations which are the old ones but
  # with the old word subbed out.
  shortened_rels := SEMIGROUPS.StzReplaceSubword(rels, word, [k + 1]);
  for new_rel in shortened_rels do
    SEMIGROUPS.TietzeTransformation1(stz, new_rel);
  od;

  # finally, remove the original relations.
  for i in [1 .. n] do
    SEMIGROUPS.TietzeTransformation2(stz, 1);
  od;
  return;
end;

SEMIGROUPS.StzRelsSubCheck := function(stz)
  local len, newLen, numInstances, rel, relLenDiff, out, tempRel, rels;
  rels := RelationsOfStzPresentation(stz);
  out := [];
  for rel in rels do
    tempRel := ShallowCopy(rel);
    SortBy(tempRel, Length);
    len := Length(stz);
    relLenDiff := Length(tempRel[2]) - Length(tempRel[1]);
    numInstances := SEMIGROUPS.StzCountRelationSubwords(stz, tempRel[2]) - 1;
    newLen := len - numInstances * relLenDiff;
    Append(out, [newLen]);
  od;
  return rec(reduction := Minimum(out),
              argument := Position(out, Minimum(out)));
end;

SEMIGROUPS.StzSubstituteInstancesOfRelation := function(stz, relIndex)
  local rels, rel, containsRel, subword, tempRelSide1, tempRelSide2, i, j,
        replaceWord;
  rels := RelationsOfStzPresentation(stz);
  rel := ShallowCopy(rels[relIndex]);
  SortBy(rel, Length);
  subword := rel[2];
  replaceWord := rel[1];
  containsRel := PositionsProperty(rels,
            x -> Position(rels, x) <> relIndex and
              ((PositionSublist(x[1], subword) <> fail)
              or (PositionSublist(x[2], subword) <> fail)));
  for i in containsRel do
    tempRelSide1 := ShallowCopy(rels[i][1]);
    tempRelSide2 := ShallowCopy(rels[i][2]);
    # Ugly as sin make better
    if PositionSublist(tempRelSide1, subword) <> fail then
      tempRelSide1 := SEMIGROUPS.StzReplaceSubwordRel(tempRelSide1, subword,
                                                      replaceWord);
    elif PositionSublist(tempRelSide2, subword) <> fail then
      tempRelSide2 := SEMIGROUPS.StzReplaceSubwordRel(tempRelSide2, subword,
                                                      replaceWord);
    fi;
    SEMIGROUPS.TietzeTransformation1(stz, [tempRelSide1, tempRelSide2]);
  od;
  for j in [1 .. Length(containsRel)] do
    SEMIGROUPS.TietzeTransformation2(stz, containsRel[j]);
    containsRel := containsRel - 1;
  od;
end;

#####
## TODO
##
#####
# Rewrite for 3 different paths
SEMIGROUPS.StzRedundantGeneratorCheck := function(stz)
  local rel, rels, numInstances, relPos, tempPositions, r, out, redLen,
        genToRemove, wordToReplace, foundRedundant, currentMin, currentGen;
  rels := RelationsOfStzPresentation(stz);
  out := [];
  currentMin := Length(stz);
  currentGen := 0;
  for rel in rels do
    foundRedundant := false;
    if Length(rel[1]) = 1 and Length(rel[2]) = 1 and rel[1] <> rel[2] then
      genToRemove := rel[1][1];
      wordToReplace := rel[2];
      Append(out, [Length(stz) - 3]);
      if Length(stz) - 3 < currentMin then
        currentMin := Length(stz) - 3;
        currentGen := genToRemove;
      fi;
      continue;
    elif Length(rel[1]) = 1 and Length(rel[2]) > 1 and
          (not (rel[1][1] in rel[2])) then
      genToRemove := rel[1][1];
      wordToReplace := rel[2];
      foundRedundant := true;
    elif Length(rel[2]) = 1 and Length(rel[1]) > 1 and
          (not (rel[2][1] in rel[1])) then
      genToRemove := rel[2][1];
      wordToReplace := rel[1];
      foundRedundant := true;
    fi;
    if foundRedundant then
      relPos := Position(rels, rel);
      numInstances := 0;
      for r in Concatenation([1 .. relPos - 1], [relPos + 1 .. Length(rels)]) do
        tempPositions := Length(Positions(Concatenation(rels[r][1],rels[r][2]),
                                          genToRemove));
        numInstances := numInstances + tempPositions;
      od;
      redLen := Length(stz) + (numInstances * (Length(wordToReplace) - 1))
                - 2 - Length(wordToReplace);
      if redLen < currentMin then
        currentMin := redLen;
        currentGen := genToRemove;
      fi;
    fi;
  od;
  return rec(reduction := currentMin,
              argument := currentGen);
end;

# Simple check to see if any relation is literally the same - verbatim - as
# another
SEMIGROUPS.StzDuplicateRelsCheck := function(stz)
  local rel, rels, i, tempRel, out, j;
  rels := RelationsOfStzPresentation(stz);
  out := [];
  if Length(rels) < 2 then
    return rec(reduction := Length(stz),
                argument := 1);
  else
    for j in [1 .. Length(rels)] do
      rel := rels[j];
      for i in Concatenation([1 .. j - 1],
                              [j + 1 .. Length(rels)]) do
        tempRel := rels[i];
        if (tempRel[1] = rel[1] and tempRel[2] = rel[2]) or
            (tempRel[1] = rel[2] and tempRel[2] = rel[1]) then
          Append(out, [Length(stz) - Length(rel[1]) - Length(rel[2])]);
        else
          Append(out, [Length(stz)]);
        fi;
      od;
    od;
    return rec(reduction := Minimum(out),
                argument := Position(out, Minimum(out)));
  fi;
end;

SEMIGROUPS.StzTrivialRelationCheck := function(stz)
  local rels, out, len, i;
  rels := RelationsOfStzPresentation(stz);
  len := Length(stz);
  out := [];
  for i in [1 .. Length(rels)] do
    if rels[i][1] = rels[i][2] then
      Append(out, [len - Length(rels[i][1]) * 2]);
    else
      Append(out, [len]);
    fi;
  od;
  return rec(reduction := Minimum(out),
              argument := Position(out, Minimum(out)));
end;

SEMIGROUPS.StzTrivialRelationApply := function(stz, args)
  local str;
  str := "<Removing trivial relation: ";
  Append(str, StzPrintRelation(stz, args.argument));
  Append(str, ">");
  Info(InfoWarning, 1, PRINT_STRINGIFY(str));
  SEMIGROUPS.TietzeTransformation2(stz, args.argument);
end;

SEMIGROUPS.StzDuplicateRelsApply := function(stz, args)
  local str;
  str := "<Removing duplicate relation: ";
  Append(str, StzPrintRelation(stz, args.argument));
  Append(str, ">");
  Info(InfoWarning, 1, PRINT_STRINGIFY(str));
  SEMIGROUPS.TietzeTransformation2(stz, args.argument);
end;

SEMIGROUPS.StzGensRedundantApply := function(stz, args)
  local str;
  str := "<Removing redundant generator: ";
  Append(str, GeneratorsOfStzPresentation(stz)[args.argument]);
  Append(str,">");
  Info(InfoWarning, 1, PRINT_STRINGIFY(str));
  SEMIGROUPS.TietzeTransformation4(stz, args.argument);
end;

SEMIGROUPS.StzRelsSubApply := function(stz, args)
  local str;
  str := "<Replacing all instances in other relations of relation: ";
  Append(str, StzPrintRelation(stz, args.argument));
  Append(str, ">");
  Info(InfoWarning, 1, PRINT_STRINGIFY(str));
  SEMIGROUPS.StzSubstituteInstancesOfRelation(stz, args.argument);
end;

## Format to add a new reduction check:
## StzCheck: function that takes an stz presentation as input and checks all
##           possible instances of the desired reduction, and outputs as a
##           record the least length of the possible reductions together with
##           the arguments required to achieve that length
## StzApply: function that takes an stz presentationa and the above record as
##           input and applies the arguments from the record to achieve the
##           desired reduction
## Add the above two functions to the list results below as the pair
## [StzApply, StzCheck(stz)]

InstallMethod(StzSimplifyOnce,
[IsStzPresentation],
function(stz)
  local rels, gens, results, mins, len, func, args, result;
  rels := RelationsOfStzPresentation(stz);
  if Length(rels) = 0 then
    return false;
  else
    results := [[SEMIGROUPS.StzGensRedundantApply,
                  SEMIGROUPS.StzRedundantGeneratorCheck(stz)],
                [SEMIGROUPS.StzDuplicateRelsApply,
                  SEMIGROUPS.StzDuplicateRelsCheck(stz)],
                [SEMIGROUPS.StzRelsSubApply,
                  SEMIGROUPS.StzRelsSubCheck(stz)],
                [SEMIGROUPS.StzFrequentSubwordApply,
                  SEMIGROUPS.StzFrequentSubwordCheck(stz)],
                [SEMIGROUPS.StzTrivialRelationApply,
                  SEMIGROUPS.StzTrivialRelationCheck(stz)]];
    len := Length(stz);
    mins := List(results, x -> x[2].reduction);
    if Minimum(mins) < len then
      result := results[Position(mins, Minimum(mins))];
      func := result[1];
      args := result[2];
      func(stz, args);
      return true;
    fi;
    return false;
  fi;
end);

#### TODO
# For testing purposes, remove before merge (also possibly a duplicate of an
# existing function)
SEMIGROUPS.RandomFpSemigroup := function(maxgen, maxrel, maxwordlen)
  local S, rels, gens, ngens, nrels, F, i, lside, rside, nwordlen;
  ngens := Random([1..maxgen]);
  nrels := Random([1..maxrel]);
  F := FreeSemigroup(ngens);
  gens := GeneratorsOfSemigroup(F);
  rels := [];
  for i in [1..nrels] do
    nwordlen := Random([1..maxwordlen]);
    lside := Product(List([1..nwordlen], x -> gens[Random([1..ngens])]));
    rside := Product(List([1..nwordlen], x -> gens[Random([1..ngens])]));
    Append(rels, [[lside, rside]]);
  od;
  return F/rels;
end;