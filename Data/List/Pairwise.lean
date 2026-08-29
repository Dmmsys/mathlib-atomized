/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.List.Pairwise
public import Mathlib.Logic.Pairwise
public import Mathlib.Logic.Relation
public import Batteries.Data.List.Lemmas

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise R [a 0, ..., a (n - 1)]` means `∀ i j, i < j → R (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter R l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise R l'`.

## Tags

sorted, nodup
-/

public section


open Nat Function

namespace List

variable {α β : Type*} {R : α -> α -> Prop} {l : List α} {a : α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff


/--
theorem `pairwise_iff_forall_infix` / 定理 `pairwise_iff_forall_infix`

English:
theorem pairwise_iff_forall_infix
  given: {α : Type*} {l : List α} {R : α -> α -> Prop}
  proof: by
  refine l.pairwise_iff_getElem.trans ⟨fun h l' hne ⟨l₁, l₂, hl⟩ => ?_, fun h i j hi hj hij => ?_⟩
  · grind [getElem_append_left', getElem_append_right']
  · grind [h _ _ <| List.drop_suffix i _ |>.isInfix.trans <| l.take_prefix (j + 1) |>.isInfix]

中文:
定理 pairwise_iff_forall_infix
  条件: {α : 类型} {l : List α} {R : α -> α -> 命题}
  证明: by
  refine l.pairwise_iff_getElem.trans ⟨fun h l' hne ⟨l₁, l₂, hl⟩ => ?_, fun h i j hi hj hij => ?_⟩
  · grind [getElem_append_left', getElem_append_right']
  · grind [h _ _ <| List.drop_suffix i _ |>.isInfix.trans <| l.take_prefix (j + 1) |>.isInfix]

Depends on / 依赖: List.drop_suffix, drop_suffix, getElem_append_left, getElem_append_right, isInfix, isInfix.trans, l.pairwise_iff_getElem.trans, l.take_prefix, pairwise_iff_getElem, take_prefix
-/
theorem pairwise_iff_forall_infix {α : Type*} {l : List α} {R : α -> α -> Prop} :
    l.Pairwise R ↔
      forall l', (h : 1 < l'.length) -> l' <:+: l -> R (l'.head <| by grind) (l'.getLast <| by grind) := by
  refine l.pairwise_iff_getElem.trans ⟨fun h l' hne ⟨l₁, l₂, hl⟩ => ?_, fun h i j hi hj hij => ?_⟩
  · grind [getElem_append_left', getElem_append_right']
  · grind [h _ _ <| List.drop_suffix i _ |>.isInfix.trans <| l.take_prefix (j + 1) |>.isInfix]

/--
theorem `Pairwise.forall_of_forall` / 定理 `Pairwise.forall_of_forall`

English:
theorem Pairwise.forall_of_forall
  given: [Std.Symm R] (H₁ : forall x in l, R x x) (H₂ : l.Pairwise R)
  proof: H₂.forall_of_forall_of_flip H₁ by rwa [Std.Symm.flip_eq]

中文:
定理 Pairwise.forall_of_forall
  条件: [Std.Symm R] (H₁ : 对任意 x in l, R x x) (H₂ : l.Pairwise R)
  证明: H₂.forall_of_forall_of_flip H₁ by rwa [Std.Symm.flip_eq]

Depends on / 依赖: Std.Symm.flip_eq, flip_eq, forall_of_forall_of_flip
-/
theorem Pairwise.forall_of_forall [Std.Symm R] (H₁ : forall x in l, R x x) (H₂ : l.Pairwise R) :
    forall ⦃x⦄, x in l -> forall ⦃y⦄, y in l -> R x y :=
H₂.forall_of_forall_of_flip H₁ by rwa [Std.Symm.flip_eq]

/--
theorem `Pairwise.forall` / 定理 `Pairwise.forall`

English:
theorem Pairwise.forall
  given: [Std.Symm R] (hl : l.Pairwise R)
  proof: by
  have : Std.Symm fun x y => x != y -> R x y := { symm a b h hne := symm <| h hne.symm }
  apply Pairwise.forall_of_forall
  · exact fun _ _ => absurd rfl
  · exact hl.imp @fun a b h _ => by exact h

中文:
定理 Pairwise.forall
  条件: [Std.Symm R] (hl : l.Pairwise R)
  证明: by
  have : Std.Symm fun x y => x != y -> R x y := { symm a b h hne := symm <| h hne.symm }
  apply Pairwise.forall_of_forall
  · exact fun _ _ => absurd rfl
  · exact hl.imp @fun a b h _ => by exact h

Depends on / 依赖: Pairwise, Pairwise.forall_of_forall, Std.Symm, absurd, forall_of_forall, hl.imp, hne.symm
-/
theorem Pairwise.forall [Std.Symm R] (hl : l.Pairwise R) :
    forall ⦃a⦄, a in l -> forall ⦃b⦄, b in l -> a != b -> R a b := by
  have : Std.Symm fun x y => x != y -> R x y := { symm a b h hne := symm <| h hne.symm }
  apply Pairwise.forall_of_forall
  · exact fun _ _ => absurd rfl
  · exact hl.imp @fun a b h _ => by exact h

/--
theorem `Pairwise.set_pairwise` / 定理 `Pairwise.set_pairwise`

English:
theorem Pairwise.set_pairwise
  given: (hl : Pairwise R l) [Std.Symm R]
  statement: { x | x in l }.Pairwise R
  proof: hl.forall

中文:
定理 Pairwise.set_pairwise
  条件: (hl : Pairwise R l) [Std.Symm R]
  结论: { x | x in l }.Pairwise R
  证明: hl.forall

Depends on / 依赖: hl.forall
-/
theorem Pairwise.set_pairwise (hl : Pairwise R l) [Std.Symm R] : { x | x in l }.Pairwise R :=
  hl.forall

/--
theorem `pairwise_of_reflexive_of_forall_ne` / 定理 `pairwise_of_reflexive_of_forall_ne`

English:
theorem pairwise_of_reflexive_of_forall_ne
  given: [Std.Refl R] (h : forall a in l, forall b in l, a != b -> R a b)
  proof: by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply refl
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

中文:
定理 pairwise_of_reflexive_of_forall_ne
  条件: [Std.Refl R] (h : 对任意 a in l, 对任意 b in l, a != b -> R a b)
  证明: by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply refl
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

Depends on / 依赖: hab.subset, pairwise_iff_forall_sublist, subset
-/
theorem pairwise_of_reflexive_of_forall_ne [Std.Refl R] (h : forall a in l, forall b in l, a != b -> R a b) :
    l.Pairwise R := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply refl
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

/--
theorem `Pairwise.rel_head_tail` / 定理 `Pairwise.rel_head_tail`

English:
theorem Pairwise.rel_head_tail
  given: (h₁ : l.Pairwise R) (ha : a in l.tail)
  proof: by
  grind +splitIndPred

中文:
定理 Pairwise.rel_head_tail
  条件: (h₁ : l.Pairwise R) (ha : a in l.tail)
  证明: by
  grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
theorem Pairwise.rel_head_tail (h₁ : l.Pairwise R) (ha : a in l.tail) :
    R (l.head <| ne_nil_of_mem <| mem_of_mem_tail ha) a := by
  grind +splitIndPred

/--
theorem `Pairwise.rel_head_of_rel_head_head` / 定理 `Pairwise.rel_head_of_rel_head_head`

English:
theorem Pairwise.rel_head_of_rel_head_head
  statement: (h₁ : l.Pairwise R) (ha : a in l)
  proof: by
  grind +splitIndPred

中文:
定理 Pairwise.rel_head_of_rel_head_head
  结论: (h₁ : l.Pairwise R) (ha : a in l)
  证明: by
  grind +splitIndPred

Depends on / 依赖: splitIndPred
-/
theorem Pairwise.rel_head_of_rel_head_head (h₁ : l.Pairwise R) (ha : a in l)
    (hhead : R (l.head <| ne_nil_of_mem ha) (l.head <| ne_nil_of_mem ha)) :
    R (l.head <| ne_nil_of_mem ha) a := by
  grind +splitIndPred

/--
theorem `Pairwise.rel_head` / 定理 `Pairwise.rel_head`

English:
theorem Pairwise.rel_head
  given: [Std.Refl R] (h₁ : l.Pairwise R) (ha : a in l)
  proof: h₁.rel_head_of_rel_head_head ha (refl_of ..)

中文:
定理 Pairwise.rel_head
  条件: [Std.Refl R] (h₁ : l.Pairwise R) (ha : a in l)
  证明: h₁.rel_head_of_rel_head_head ha (refl_of ..)

Depends on / 依赖: refl_of, rel_head_of_rel_head_head
-/
theorem Pairwise.rel_head [Std.Refl R] (h₁ : l.Pairwise R) (ha : a in l) :
    R (l.head <| ne_nil_of_mem ha) a :=
  h₁.rel_head_of_rel_head_head ha (refl_of ..)

/--
theorem `Pairwise.rel_dropLast_getLast` / 定理 `Pairwise.rel_dropLast_getLast`

English:
theorem Pairwise.rel_dropLast_getLast
  given: (h : l.Pairwise R) (ha : a in l.dropLast)
  proof: by
  rw [← pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])

中文:
定理 Pairwise.rel_dropLast_getLast
  条件: (h : l.Pairwise R) (ha : a in l.dropLast)
  证明: by
  rw [← pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])

Depends on / 依赖: getLast_eq_head_reverse, h.rel_head_tail, mem_reverse, pairwise_reverse, rel_head_tail, tail_reverse
-/
theorem Pairwise.rel_dropLast_getLast (h : l.Pairwise R) (ha : a in l.dropLast) :
    R a (l.getLast <| ne_nil_of_mem <| dropLast_subset _ ha) := by
  rw [← pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])

/--
theorem `Pairwise.rel_getLast_of_rel_getLast_getLast` / 定理 `Pairwise.rel_getLast_of_rel_getLast_getLast`

English:
theorem Pairwise.rel_getLast_of_rel_getLast_getLast
  statement: (h₁ : l.Pairwise R) (ha : a in l)
  proof: by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha)]; rw [mem_append]; rw [List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)

中文:
定理 Pairwise.rel_getLast_of_rel_getLast_getLast
  结论: (h₁ : l.Pairwise R) (ha : a in l)
  证明: by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha)]; rw [mem_append]; rw [List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)

Depends on / 依赖: List.mem_singleton, dropLast_concat_getLast, ha.elim, mem_append, mem_singleton, ne_nil_of_mem, rel_dropLast_getLast
-/
theorem Pairwise.rel_getLast_of_rel_getLast_getLast (h₁ : l.Pairwise R) (ha : a in l)
    (hlast : R (l.getLast <| ne_nil_of_mem ha) (l.getLast <| ne_nil_of_mem ha)) :
    R a (l.getLast <| ne_nil_of_mem ha) := by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha)]; rw [mem_append]; rw [List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)

/--
theorem `Pairwise.rel_getLast` / 定理 `Pairwise.rel_getLast`

English:
theorem Pairwise.rel_getLast
  given: [Std.Refl R] (h₁ : l.Pairwise R) (ha : a in l)
  proof: h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse

中文:
定理 Pairwise.rel_getLast
  条件: [Std.Refl R] (h₁ : l.Pairwise R) (ha : a in l)
  证明: h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse

Depends on / 依赖: refl_of, rel_getLast_of_rel_getLast_getLast
-/
theorem Pairwise.rel_getLast [Std.Refl R] (h₁ : l.Pairwise R) (ha : a in l) :
    R a (l.getLast <| ne_nil_of_mem ha) :=
  h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse

/--
theorem `Pairwise.head!_le` / 定理 `Pairwise.head!_le`

English:
theorem Pairwise.head!_le
  statement: [Inhabited α] [Std.Refl R] (h : l.Pairwise R)
  proof: by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)

中文:
定理 Pairwise.head!_le
  结论: [Inhabited α] [Std.Refl R] (h : l.Pairwise R)
  证明: by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)

Depends on / 依赖: refl_of, rel_of_pairwise_cons
-/
theorem Pairwise.head!_le [Inhabited α] [Std.Refl R] (h : l.Pairwise R)
    (ha : a in l) : R l.head! a := by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)

/--
theorem `pairwise_replicate_of_refl` / 定理 `pairwise_replicate_of_refl`

English:
theorem pairwise_replicate_of_refl
  given: {n} [Std.Refl R]
  statement: (replicate n a).Pairwise R
  proof: pairwise_replicate.mpr (Or.inr <| refl_of ..)

中文:
定理 pairwise_replicate_of_refl
  条件: {n} [Std.Refl R]
  结论: (replicate n a).Pairwise R
  证明: pairwise_replicate.mpr (Or.inr <| refl_of ..)

Depends on / 依赖: Or.inr, pairwise_replicate, pairwise_replicate.mpr, refl_of
-/
theorem pairwise_replicate_of_refl {n} [Std.Refl R] : (replicate n a).Pairwise R :=
  pairwise_replicate.mpr (Or.inr <| refl_of ..)

/-! ### Pairwise filtering -/

protected alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self

/--
theorem `pairwise_cons_cons_iff_of_trans` / 定理 `pairwise_cons_cons_iff_of_trans`

English:
theorem pairwise_cons_cons_iff_of_trans
  given: [IsTrans α R] {l : List α} {a b : α}
  proof: by
  simp_rw [← isChain_iff_pairwise, isChain_cons_cons]

中文:
定理 pairwise_cons_cons_iff_of_trans
  条件: [IsTrans α R] {l : List α} {a b : α}
  证明: by
  simp_rw [← isChain_iff_pairwise, isChain_cons_cons]

Depends on / 依赖: isChain_cons_cons, isChain_iff_pairwise, simp_rw
-/
theorem pairwise_cons_cons_iff_of_trans [IsTrans α R] {l : List α} {a b : α} :
    Pairwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (b :: l) := by
  simp_rw [← isChain_iff_pairwise, isChain_cons_cons]

/--
theorem `Pairwise.cons_cons_of_trans` / 定理 `Pairwise.cons_cons_of_trans`

English:
theorem Pairwise.cons_cons_of_trans
  given: [IsTrans α R] {l : List α} {a b : α}
  proof: by
  simp_rw [pairwise_cons_cons_iff_of_trans]
  exact And.intro

中文:
定理 Pairwise.cons_cons_of_trans
  条件: [IsTrans α R] {l : List α} {a b : α}
  证明: by
  simp_rw [pairwise_cons_cons_iff_of_trans]
  exact And.intro

Depends on / 依赖: And.intro, pairwise_cons_cons_iff_of_trans, simp_rw
-/
theorem Pairwise.cons_cons_of_trans [IsTrans α R] {l : List α} {a b : α} :
    R a b -> Pairwise R (b :: l) -> Pairwise R (a :: b :: l) := by
  simp_rw [pairwise_cons_cons_iff_of_trans]
  exact And.intro

/--
theorem `Pairwise.rel_get_of_lt` / 定理 `Pairwise.rel_get_of_lt`

English:
theorem Pairwise.rel_get_of_lt
  given: {l : List α} (h : l.Pairwise R) {a b : Fin l.length} (hab : a < b)
  proof: List.pairwise_iff_get.1 h _ _ hab

中文:
定理 Pairwise.rel_get_of_lt
  条件: {l : List α} (h : l.Pairwise R) {a b : Fin l.length} (hab : a < b)
  证明: List.pairwise_iff_get.1 h _ _ hab

Depends on / 依赖: List.pairwise_iff_get, pairwise_iff_get
-/
theorem Pairwise.rel_get_of_lt {l : List α} (h : l.Pairwise R) {a b : Fin l.length} (hab : a < b) :
    R (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab

/--
theorem `Pairwise.rel_get_of_le` / 定理 `Pairwise.rel_get_of_le`

English:
theorem Pairwise.rel_get_of_le
  statement: [Std.Refl R] {l : List α} (h : l.Pairwise R) {a b : Fin l.length}
  proof: by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, (pairwise_iff_get.1 h) _ _ hlt]

中文:
定理 Pairwise.rel_get_of_le
  结论: [Std.Refl R] {l : List α} (h : l.Pairwise R) {a b : Fin l.length}
  证明: by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, (pairwise_iff_get.1 h) _ _ hlt]

Depends on / 依赖: Fin.eq_or_lt_of_le, eq_or_lt_of_le, exacts, pairwise_iff_get
-/
theorem Pairwise.rel_get_of_le [Std.Refl R] {l : List α} (h : l.Pairwise R) {a b : Fin l.length}
    (hab : a <= b) : R (l.get a) (l.get b) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, (pairwise_iff_get.1 h) _ _ hlt]

/--
theorem `Pairwise.decide` / 定理 `Pairwise.decide`

English:
theorem Pairwise.decide
  given: [DecidableRel R] (l : List α) (h : Pairwise R l)
  proof: by
  refine h.imp fun {a b} h => by simpa using h

中文:
定理 Pairwise.decide
  条件: [DecidableRel R] (l : List α) (h : Pairwise R l)
  证明: by
  refine h.imp fun {a b} h => by simpa using h

Depends on / 依赖: h.imp
-/
theorem Pairwise.decide [DecidableRel R] (l : List α) (h : Pairwise R l) :
    Pairwise (fun a b => decide (R a b) = true) l := by
  refine h.imp fun {a b} h => by simpa using h

end List
