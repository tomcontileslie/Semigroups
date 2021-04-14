################################################################################
# The Stz Object (name pending)
# Idea is to have a single object containing generators and relations that can
# have the relations be presented in a number of different computation-friendly
# or user-friendly formats (LetterRepAssocWord, ExtRepOfObj, user-readable
# strings). Ideally never seen by the user, but used internally to - among other
# things - reduce the relations of an FP semigroup/monoid to a simple form
#
# I argue: no need for IsMutable/IsImmutable/etc, since StzPresentation likely
# is never seen by the user, so as long as it is contained to the stz reduction
# (as it likely will be) there will be no issues.
################################################################################

# DeclareOperation("StzPresentation", [IsList, IsList]);
DeclareOperation("StzPresentation", [IsFpSemigroup]);
DeclareCategory("IsStzPresentation", IsList);
#DeclareRepresentation("IsStzPresentationRep", IsStzPresentation and IsPositionalObjectRep,
#                        3);


# Can add extra representations as attributes?
# Maybe use 'representation' instead

# Current relations in the process of being reduced
DeclareAttribute("RelationsOfStzPresentation", IsStzPresentation);

# Letter representation of the current relations
DeclareOperation("LetterRepRelationsOfStzPresentation", [IsStzPresentation]);

# Setter for relations, checks that list is in ext rep form
DeclareOperation("SetRelationsOfStzPresentation", [IsStzPresentation, IsList]);

DeclareAttribute("GeneratorsOfStzPresentation", IsStzPresentation);

DeclareOperation("SetGeneratorsOfStzPresentation", [IsStzPresentation, IsList]);

# Constructs new fp semigroup out of current relations and generators
DeclareOperation("SemigroupOfStzPresentation", [IsStzPresentation]);

# Stores original semigroup before reductions
DeclareAttribute("UnreducedSemigroupOfStzPresentation", IsStzPresentation);

# Stores a map between the words of each semigroup (how?)
# Change as relations change
# Otherwise must keep track of all tietze transforms i suppose
DeclareAttribute("MapToUnreducedFpSemigroup", IsStzPresentation);

DeclareOperation("SetMapToUnreducedFpSemigroup", [IsStzPresentation, IsPosInt, IsList]); # no longer needed?
DeclareOperation("SetMapToUnreducedFpSemigroup", [IsStzPresentation, IsList]);

DeclareOperation("MapToUnreducedFpSemigroupReplaceSubword", [IsStzPresentation, IsList, IsList]);

# FP semigroup attributes
DeclareAttribute("UnreducedFpSemigroupOfFpSemigroup", IsFpSemigroup);
DeclareAttribute("MapToUnreducedFpSemigroup", IsFpSemigroup);

