/*
 * Semigroups GAP package
 *
 * This file contains some methods for bipartitions
 *
 */

#include "src/bipart.h"
#include "src/semigroups++/elements.h"
#include <vector>

// Create a bipartition
// This is just a wrapper for the C++ objects.
//
// @return a GAP Obj..

Obj BIPART_NC (Obj self, Obj gap_blocks) {

  assert(IS_LIST(gap_blocks));
  assert(LEN_LIST(gap_blocks) > 0);

  std::vector<u_int32_t>* blocks = new std::vector<u_int32_t>();

  size_t degree         = 0;
  size_t nr_left_blocks = 0;
  size_t nr_blocks      = 0;
  bool   by_ext_rep;

  if (IS_LIST(ELM_LIST(gap_blocks, 1))) { // gap_blocks is a list of lists
    by_ext_rep = true;
    nr_blocks = LEN_LIST(gap_blocks);
    for (size_t i = 1; i <= nr_blocks; i++) {
      assert(IS_LIST(ELM_LIST(gap_blocks, i)));
      degree += LEN_LIST(ELM_LIST(gap_blocks, i));
    }
    blocks->resize(degree);

    degree /= 2;

    for (size_t i = 1; i <= nr_blocks; i++) {
      Obj block = ELM_LIST(gap_blocks, i);
      for (size_t j = 1; j <= (size_t) LEN_LIST(block); j++) {
        assert(IS_INTOBJ(ELM_LIST(block, j)));
        int jj = INT_INTOBJ(ELM_LIST(block, j));
        if (jj < 0) {
          (*blocks)[- jj + degree - 1] = i - 1;
        } else {
          nr_left_blocks = i;
          (*blocks)[jj - 1] = i - 1;
        }
      }
    }
  } else { // gap_blocks is the internal rep of a bipartition
    by_ext_rep = false;
    blocks->reserve(LEN_LIST(gap_blocks));
    for (size_t i = 1; i <= (size_t) LEN_LIST(gap_blocks) / 2; i++) {
      assert(IS_INTOBJ(ELM_LIST(gap_blocks, i)) &&
             INT_INTOBJ(ELM_LIST(gap_blocks, i)) > 0);
      size_t index = INT_INTOBJ(ELM_LIST(gap_blocks, i)) - 1;
      blocks->push_back(index);
      nr_blocks = (index > nr_blocks ? index : nr_blocks);
    }
    nr_left_blocks = nr_blocks;
    for (size_t i = ((size_t) LEN_LIST(gap_blocks) / 2) + 1;
         i <= (size_t) LEN_LIST(gap_blocks); i++) {
      assert(IS_INTOBJ(ELM_LIST(gap_blocks, i)) &&
             INT_INTOBJ(ELM_LIST(gap_blocks, i)) > 0);
      size_t index = INT_INTOBJ(ELM_LIST(gap_blocks, i)) - 1;
      blocks->push_back(index);
      nr_blocks = (index > nr_blocks ? index : nr_blocks);
    }
  }

  // construct C++ object
  Bipartition* x = new Bipartition(blocks);
  x->set_nr_left_blocks(nr_left_blocks + 1);
  x->set_nr_blocks(nr_blocks + 1);

  // construct GAP wrapper for C++ object
  Obj wrapper = NewSemigroupsBag(x, GAP_BIPART, 4);
  if (by_ext_rep) {
    ADDR_OBJ(wrapper)[2] = gap_blocks; //copy blocks here? FIXME
  } else {
    ADDR_OBJ(wrapper)[3] = gap_blocks; //copy blocks here? FIXME
  }
  CHANGED_BAG(wrapper);

  // put the GAP wrapper in a list and Objectify
  // FIXME this should be unnecessary
  Obj out = NEW_PLIST(T_PLIST, 1);
  SET_LEN_PLIST(out, 1);
  SET_ELM_PLIST(out, 1, wrapper);
  TYPE_POSOBJ(out) = BipartitionType;
  RetypeBag(out, T_POSOBJ);
  CHANGED_BAG(out);

  return out;
}

Obj BIPART_EXT_REP (Obj self, Obj bipart) {

  Obj x = ELM_PLIST(bipart, 1);

  if (ADDR_OBJ(x)[2] == NULL) {
    Bipartition* xx = CLASS_OBJ<Bipartition>(x); // get C++ bipartition
    size_t n = xx->degree();

    Obj ext_rep = NEW_PLIST(T_PLIST_HOM, xx->nr_blocks());
    SET_LEN_PLIST(ext_rep, (Int) xx->nr_blocks());

    for (size_t i = 0; i < 2 * n; i++) {
      Obj block;
      Obj entry = INTOBJ_INT((i < n ? i + 1 : -(i - n) - 1));
      if (ELM_PLIST(ext_rep, xx->block(i) + 1) == 0) {
        block = NEW_PLIST(T_PLIST_CYC, 1);
        SET_LEN_PLIST(block, 1);
        SET_ELM_PLIST(block, 1, entry);
        SET_ELM_PLIST(ext_rep, xx->block(i) + 1, block);
        CHANGED_BAG(ext_rep);
      } else {
        block = ELM_PLIST(ext_rep, xx->block(i) + 1);
        AssPlist(block, LEN_PLIST(block) + 1, entry);
      }
    }
    ADDR_OBJ(x)[2] = ext_rep;
    CHANGED_BAG(x);
  }

  return ADDR_OBJ(x)[2];
}

Obj BIPART_INT_REP (Obj self, Obj bipart) {

  Obj x = ELM_PLIST(bipart, 1);

  if (ADDR_OBJ(x)[3] == NULL) {
    Bipartition* xx = CLASS_OBJ<Bipartition>(x); // get C++ bipartition
    size_t n = xx->degree();

    Obj int_rep = NEW_PLIST(T_PLIST_CYC, 2 * xx->degree());
    SET_LEN_PLIST(int_rep, (Int) 2 * xx->nr_blocks());

    for (size_t i = 0; i < 2 * n; i++) {
      SET_ELM_PLIST(int_rep, i + 1, INTOBJ_INT(xx->block(i) + 1));
    }
    ADDR_OBJ(x)[3] = int_rep;
    CHANGED_BAG(x);
  }

  return ADDR_OBJ(x)[3];
}

Obj BIPART_DEGREE (Obj self, Obj bipart) {
  Bipartition* x = CLASS_OBJ<Bipartition>(ELM_PLIST(bipart, 1));
  return INTOBJ_INT(x->degree());
}
