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

DeclareOperation("StzPresentation", [IsFpSemigroup]);
DeclareCategory("IsStzPresentation", IsList);

# Current relations in the process of being reduced
DeclareAttribute("RelationsOfStzPresentation", IsStzPresentation);

DeclareAttribute("GeneratorsOfStzPresentation", IsStzPresentation);

# Stores original semigroup before reductions
DeclareAttribute("UnreducedSemigroupOfStzPresentation", IsStzPresentation);

# Stores a map between the words of each semigroup (how?)
# Change as relations change
# Otherwise must keep track of all tietze transforms i suppose
DeclareAttribute("TietzeForwardMap", IsStzPresentation);
DeclareAttribute("TietzeBackwardMap", IsStzPresentation);

DeclareOperation("TietzeForwardMapReplaceSubword",
[IsStzPresentation, IsList, IsList]);

DeclareOperation("StzSimplifyOnce", [IsStzPresentation]);
DeclareOperation("StzSimplifyPresentation", [IsStzPresentation]);

DeclareOperation("SimplifiedFpSemigroup", [IsFpSemigroup]);
DeclareOperation("SimplifyFpSemigroup", [IsFpSemigroup]);

# FP semigroup attributes
DeclareAttribute("UnreducedFpSemigroupOfFpSemigroup", IsFpSemigroup);
DeclareAttribute("FpTietzeIsomorphism", IsFpSemigroup);

DeclareOperation("TietzeIsomorphism", [IsStzPresentation]);

## Tietze Transformations - various implementations
# Tietze 1 (add relation)
DeclareOperation("StzAddRelation", [IsStzPresentation, IsList]);
DeclareOperation("StzAddRelationNC", [IsStzPresentation, IsList]);
# Tietze 2 (remove relation)
DeclareOperation("StzRemoveRelation", [IsStzPresentation, IsPosInt]);
DeclareOperation("StzRemoveRelationNC", [IsStzPresentation, IsPosInt]);
# Tietze 3 (add generator)
DeclareOperation("StzAddGenerator", [IsStzPresentation, IsList]);
DeclareOperation("StzAddGenerator", [IsStzPresentation,
                                     IsElementOfFpSemigroup]);
DeclareOperation("StzAddGenerator", [IsStzPresentation, IsList, IsString]);
DeclareOperation("StzAddGenerator", [IsStzPresentation,
                                     IsElementOfFpSemigroup,
                                     IsString]);
# Tietze 4 (remove generator)
DeclareOperation("StzRemoveGenerator", [IsStzPresentation, IsPosInt]);
DeclareOperation("StzRemoveGenerator", [IsStzPresentation, IsString]);

DeclareOperation("StzPrintRelations", [IsStzPresentation]);
DeclareOperation("StzPrintRelations", [IsStzPresentation, IsList]);
DeclareOperation("StzPrintRelation", [IsStzPresentation, IsPosInt]);
DeclareOperation("StzPrintGenerators", [IsStzPresentation]);
DeclareOperation("StzPrintGenerators", [IsStzPresentation, IsList]);
DeclareOperation("StzPrintPresentation", [IsStzPresentation]);
