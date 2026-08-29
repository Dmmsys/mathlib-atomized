/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sigma.Lex
public import Mathlib.Order.RelIso.Set
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Tactic.TFAE

/-!
# Well-founded sets

This file introduces versions of `WellFounded` and `WellQuasiOrdered` for sets.

## Main Definitions

* `Set.WellFoundedOn s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
* `Set.IsWF s` indicates that `<` is well-founded when restricted to `s`.
* `Set.PartiallyWellOrderedOn s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
* `Set.IsPWO s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results

* Higman's Lemma, `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`,
  shows that if `r` is partially well-ordered on `s`, then `List.SublistForall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
* `Set.wellFoundedOn_iff` relates `well_founded_on` to the well-foundedness of a relation on the
  original type, to avoid dealing with subtypes.
* `Set.IsWF.mono` shows that a subset of a well-founded subset is well-founded.
* `Set.IsWF.union` shows that the union of two well-founded subsets is well-founded.
* `Finset.isWF` shows that all `Finset`s are well-founded.

## TODO

* Prove that `s` is partially well-ordered iff it has no infinite descending chain or antichain.
* Rename `Set.PartiallyWellOrderedOn` to `Set.WellQuasiOrderedOn` and `Set.IsPWO` to `Set.IsWQO`.

## References
* [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
* [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/

@[expose] public section

assert_not_exists IsOrderedRing

open scoped Function -- required for scoped `on` notation

variable {ι α β γ : Type*} {π : ι -> Type*}

namespace Set

/-! ### Relations well-founded on sets -/

/--
Definition of `WellFoundedOn` / `WellFoundedOn` 的定义

English:
definition WellFoundedOn
  signature: (s : Set α) (r : α -> α -> Prop)
  body: WellFounded (Subrel r (· in s))

@[simp]

中文:
定义 WellFoundedOn
  签名: (s : Set α) (r : α -> α -> 命题)
  定义体: WellFounded (Subrel r (· in s))

@[simp]

Depends on / 依赖: Subrel, WellFounded
-/
def WellFoundedOn (s : Set α) (r : α -> α -> Prop) : Prop :=
  WellFounded (Subrel r (· in s))

@[simp]
/--
theorem `wellFoundedOn_empty` / 定理 `wellFoundedOn_empty`

English:
theorem wellFoundedOn_empty
  given: (r : α -> α -> Prop)
  statement: WellFoundedOn ∅ r
  proof: wellFounded_of_isEmpty _

中文:
定理 wellFoundedOn_empty
  条件: (r : α -> α -> 命题)
  结论: WellFoundedOn ∅ r
  证明: wellFounded_of_isEmpty _

Depends on / 依赖: wellFounded_of_isEmpty
-/
theorem wellFoundedOn_empty (r : α -> α -> Prop) : WellFoundedOn ∅ r :=
  wellFounded_of_isEmpty _

section WellFoundedOn

variable {r r' : α -> α -> Prop}

section AnyRel

variable {f : β -> α} {s t : Set α} {x y : α}

/--
theorem `wellFoundedOn_iff` / 定理 `wellFoundedOn_iff`

English:
theorem wellFoundedOn_iff
  proof: by
  have f : RelEmbedding (Subrel r (· in s)) fun a b : α => r a b ∧ a in s ∧ b in s :=
    ⟨⟨(↑), Subtype.coe_injective⟩, by simp⟩
  refine ⟨fun h => ?_, f.wellFounded⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hst : (s inter t).Nonempty
  · rw [← Subtype.preimage_coe_none

中文:
定理 wellFoundedOn_iff
  证明: by
  have f : RelEmbedding (Subrel r (· in s)) fun a b : α => r a b ∧ a in s ∧ b in s :=
    ⟨⟨(↑), Subtype.coe_injective⟩, by simp⟩
  refine ⟨fun h => ?_, f.wellFounded⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hst : (s inter t).Nonempty
  · rw [← Subtype.preimage_coe_none

Depends on / 依赖: Nonempty, RelEmbedding, Subrel, Subtype, Subtype.coe_injective, Subtype.preimage_coe_nonempty, Subtype.val, WellFounded, WellFounded.wellFounded_iff_has_min, coe_injective, f.wellFounded, h.has_min, has_min, preimage_coe_nonempty, wellFounded, wellFounded_iff_has_min
-/
theorem wellFoundedOn_iff :
    s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧ a in s ∧ b in s := by
  have f : RelEmbedding (Subrel r (· in s)) fun a b : α => r a b ∧ a in s ∧ b in s :=
    ⟨⟨(↑), Subtype.coe_injective⟩, by simp⟩
  refine ⟨fun h => ?_, f.wellFounded⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hst : (s inter t).Nonempty
  · rw [← Subtype.preimage_coe_nonempty] at hst
    rcases h.has_min (Subtype.val ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, _⟩ => hm ⟨x, xs⟩ xt xm⟩
  · rcases ht with ⟨m, mt⟩
    exact ⟨m, mt, fun x _ ⟨_, _, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩

@[simp]
/--
theorem `wellFoundedOn_univ` / 定理 `wellFoundedOn_univ`

English:
theorem wellFoundedOn_univ
  statement: (univ : Set α).WellFoundedOn r ↔ WellFounded r
  proof: by
  simp [wellFoundedOn_iff]

中文:
定理 wellFoundedOn_univ
  结论: (univ : Set α).WellFoundedOn r ↔ WellFounded r
  证明: by
  simp [wellFoundedOn_iff]

Depends on / 依赖: wellFoundedOn_iff
-/
theorem wellFoundedOn_univ : (univ : Set α).WellFoundedOn r ↔ WellFounded r := by
  simp [wellFoundedOn_iff]

/--
theorem `_root_.WellFounded.wellFoundedOn` / 定理 `_root_.WellFounded.wellFoundedOn`

English:
theorem _root_.WellFounded.wellFoundedOn
  statement: WellFounded r -> s.WellFoundedOn r
  proof: InvImage.wf _

@[simp]

中文:
定理 _root_.WellFounded.wellFoundedOn
  结论: WellFounded r -> s.WellFoundedOn r
  证明: InvImage.wf _

@[simp]

Depends on / 依赖: InvImage, InvImage.wf
-/
theorem _root_.WellFounded.wellFoundedOn : WellFounded r -> s.WellFoundedOn r :=
  InvImage.wf _

@[simp]
/--
theorem `wellFoundedOn_range` / 定理 `wellFoundedOn_range`

English:
theorem wellFoundedOn_range
  statement: (range f).WellFoundedOn r ↔ WellFounded (r on f)
  proof: by
  let f' : β -> range f := fun c => ⟨f c, c, rfl⟩
  refine ⟨fun h => (InvImage.wf f' h).mono fun c c' => id, fun h => ⟨?_⟩⟩
  rintro ⟨_, c, rfl⟩
  refine Acc.of_downward_closed f' ?_ _ ?_
  · rintro _ ⟨_, c', rfl⟩ -
    exact ⟨c', rfl⟩
  · exact h.apply _

@[simp]

中文:
定理 wellFoundedOn_range
  结论: (range f).WellFoundedOn r ↔ WellFounded (r on f)
  证明: by
  let f' : β -> range f := fun c => ⟨f c, c, rfl⟩
  refine ⟨fun h => (InvImage.wf f' h).mono fun c c' => id, fun h => ⟨?_⟩⟩
  rintro ⟨_, c, rfl⟩
  refine Acc.of_downward_closed f' ?_ _ ?_
  · rintro _ ⟨_, c', rfl⟩ -
    exact ⟨c', rfl⟩
  · exact h.apply _

@[simp]

Depends on / 依赖: Acc.of_downward_closed, InvImage, InvImage.wf, h.apply, of_downward_closed
-/
theorem wellFoundedOn_range : (range f).WellFoundedOn r ↔ WellFounded (r on f) := by
  let f' : β -> range f := fun c => ⟨f c, c, rfl⟩
  refine ⟨fun h => (InvImage.wf f' h).mono fun c c' => id, fun h => ⟨?_⟩⟩
  rintro ⟨_, c, rfl⟩
  refine Acc.of_downward_closed f' ?_ _ ?_
  · rintro _ ⟨_, c', rfl⟩ -
    exact ⟨c', rfl⟩
  · exact h.apply _

@[simp]
/--
theorem `wellFoundedOn_image` / 定理 `wellFoundedOn_image`

English:
theorem wellFoundedOn_image
  given: {s : Set β}
  statement: (f '' s).WellFoundedOn r ↔ s.WellFoundedOn (r on f)
  proof: by
  rw [image_eq_range]; exact wellFoundedOn_range

中文:
定理 wellFoundedOn_image
  条件: {s : Set β}
  结论: (f '' s).WellFoundedOn r ↔ s.WellFoundedOn (r on f)
  证明: by
  rw [image_eq_range]; exact wellFoundedOn_range

Depends on / 依赖: image_eq_range, wellFoundedOn_range
-/
theorem wellFoundedOn_image {s : Set β} : (f '' s).WellFoundedOn r ↔ s.WellFoundedOn (r on f) := by
  rw [image_eq_range]; exact wellFoundedOn_range

namespace WellFoundedOn

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: (hs : s.WellFoundedOn r) (hx : x in s) {P : α -> Prop}
  proof: by
  let Q : s -> Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine WellFounded.induction hs ⟨x, hx⟩ ?_
  simpa only [Subtype.forall]

中文:
定理 induction
  结论: (hs : s.WellFoundedOn r) (hx : x in s) {P : α -> 命题}
  证明: by
  let Q : s -> Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine WellFounded.induction hs ⟨x, hx⟩ ?_
  simpa only [Subtype.forall]
-/
protected theorem induction (hs : s.WellFoundedOn r) (hx : x in s) {P : α -> Prop}
    (hP : forall y in s, (forall z in s, r z y -> P z) -> P y) : P x := by
  let Q : s -> Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine WellFounded.induction hs ⟨x, hx⟩ ?_
  simpa only [Subtype.forall]

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : t.WellFoundedOn r') (hle : r <= r') (hst : s subseteq t)
  proof: by
  rw [wellFoundedOn_iff] at *
  exact Subrelation.wf (fun xy => ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩) h

中文:
定理 mono
  条件: (h : t.WellFoundedOn r') (hle : r <= r') (hst : s subseteq t)
  证明: by
  rw [wellFoundedOn_iff] at *
  exact Subrelation.wf (fun xy => ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩) h
-/
protected theorem mono (h : t.WellFoundedOn r') (hle : r <= r') (hst : s subseteq t) :
    s.WellFoundedOn r := by
  rw [wellFoundedOn_iff] at *
  exact Subrelation.wf (fun xy => ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩) h

/--
theorem `mono'` / 定理 `mono'`

English:
theorem mono'
  given: (h : forall (a) (_ : a in s) (b) (_ : b in s), r' a b -> r a b)
  proof: Subrelation.wf @fun a b => h _ a.2 _ b.2

中文:
定理 mono'
  条件: (h : 对任意 (a) (_ : a in s) (b) (_ : b in s), r' a b -> r a b)
  证明: Subrelation.wf @fun a b => h _ a.2 _ b.2

Depends on / 依赖: Subrelation, Subrelation.wf
-/
theorem mono' (h : forall (a) (_ : a in s) (b) (_ : b in s), r' a b -> r a b) :
    s.WellFoundedOn r -> s.WellFoundedOn r' :=
  Subrelation.wf @fun a b => h _ a.2 _ b.2

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (h : t.WellFoundedOn r) (hst : s subseteq t)
  statement: s.WellFoundedOn r
  proof: h.mono le_rfl hst

中文:
定理 subset
  条件: (h : t.WellFoundedOn r) (hst : s subseteq t)
  结论: s.WellFoundedOn r
  证明: h.mono le_rfl hst

Depends on / 依赖: h.mono, le_rfl
-/
theorem subset (h : t.WellFoundedOn r) (hst : s subseteq t) : s.WellFoundedOn r :=
  h.mono le_rfl hst

open Relation

open List in
/--
theorem `acc_iff_wellFoundedOn` / 定理 `acc_iff_wellFoundedOn`

English:
theorem acc_iff_wellFoundedOn
  given: {α} {r : α -> α -> Prop} {a : α}
  proof: by
  tfae_have 1 -> 2 := by
    refine fun h => ⟨fun b => InvImage.accessible Subtype.val ?_⟩
    rw [← acc_transGen_iff] at h ⊢
    obtain h' | h' := reflTransGen_iff_eq_or_transGen.1 b.2
    · rwa [h'] at h
    · exact h.inv h'
  tfae_have 2 -> 3 := fun h => h.subset fun _ => TransGen.to_reflTrans

中文:
定理 acc_iff_wellFoundedOn
  条件: {α} {r : α -> α -> 命题} {a : α}
  证明: by
  tfae_have 1 -> 2 := by
    refine fun h => ⟨fun b => InvImage.accessible Subtype.val ?_⟩
    rw [← acc_transGen_iff] at h ⊢
    obtain h' | h' := reflTransGen_iff_eq_or_transGen.1 b.2
    · rwa [h'] at h
    · exact h.inv h'
  tfae_have 2 -> 3 := fun h => h.subset fun _ => TransGen.to_reflTrans

Depends on / 依赖: Acc.intro, InvImage, InvImage.accessible, Subtype, Subtype.val, TransGen, TransGen.to_reflTransGen, acc_transGen_iff, accessible, h.apply, h.inv, h.subset, of_fibration, reflTransGen_iff_eq_or_transGen, single, subset, tfae_finish, tfae_have, to_reflTransGen
-/
theorem acc_iff_wellFoundedOn {α} {r : α -> α -> Prop} {a : α} :
    TFAE [Acc r a,
      WellFoundedOn { b | ReflTransGen r b a } r,
      WellFoundedOn { b | TransGen r b a } r] := by
  tfae_have 1 -> 2 := by
    refine fun h => ⟨fun b => InvImage.accessible Subtype.val ?_⟩
    rw [← acc_transGen_iff] at h ⊢
    obtain h' | h' := reflTransGen_iff_eq_or_transGen.1 b.2
    · rwa [h'] at h
    · exact h.inv h'
  tfae_have 2 -> 3 := fun h => h.subset fun _ => TransGen.to_reflTransGen
  tfae_have 3 -> 1 := by
    refine fun h => Acc.intro _ (fun b hb => (h.apply ⟨b, .single hb⟩).of_fibration Subtype.val ?_)
    exact fun ⟨c, hc⟩ d h => ⟨⟨d, .head h hc⟩, h, rfl⟩
  tfae_finish

end WellFoundedOn

end AnyRel

section IsStrictOrder

variable [IsStrictOrder α r] {s t : Set α}

/--
Instance `IsStrictOrder.subset` / 实例 `IsStrictOrder.subset`

English:
instance IsStrictOrder.subset
  signature: : IsStrictOrder α fun a b : α => r a b ∧ a in s ∧ b in s where
  body: ⟨fun a con => irrefl_of r a con.1⟩
  toIsTrans := ⟨fun _ _ _ ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩

中文:
实例 IsStrictOrder.subset
  签名: : IsStrictOrder α fun a b : α => r a b ∧ a in s ∧ b in s where
  定义体: ⟨fun a con => irrefl_of r a con.1⟩
  toIsTrans := ⟨fun _ _ _ ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩

Depends on / 依赖: irrefl_of
-/
instance IsStrictOrder.subset : IsStrictOrder α fun a b : α => r a b ∧ a in s ∧ b in s where
  toIrrefl := ⟨fun a con => irrefl_of r a con.1⟩
  toIsTrans := ⟨fun _ _ _ ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩

/--
theorem `wellFoundedOn_iff_no_descending_seq` / 定理 `wellFoundedOn_iff_no_descending_seq`

English:
theorem wellFoundedOn_iff_no_descending_seq
  proof: by
  simp only [wellFoundedOn_iff, RelEmbedding.wellFounded_iff_isEmpty, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : forall n, f n in s := fun n => (hf.2 n.lt_succ_self).2.2
    refine ⟨⟨f, ?_⟩, H⟩
    simpa only [H, and_true] using @hf
  · rint

中文:
定理 wellFoundedOn_iff_no_descending_seq
  证明: by
  simp only [wellFoundedOn_iff, RelEmbedding.wellFounded_iff_isEmpty, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : forall n, f n in s := fun n => (hf.2 n.lt_succ_self).2.2
    refine ⟨⟨f, ?_⟩, H⟩
    simpa only [H, and_true] using @hf
  · rint

Depends on / 依赖: RelEmbedding, RelEmbedding.wellFounded_iff_isEmpty, and_true, lt_succ_self, n.lt_succ_self, not_exists, not_iff_not, not_nonempty_iff, wellFoundedOn_iff, wellFounded_iff_isEmpty
-/
theorem wellFoundedOn_iff_no_descending_seq :
    s.WellFoundedOn r ↔ forall f : ((· > ·) : Nat -> Nat -> Prop) ↪r r, ¬forall n, f n in s := by
  simp only [wellFoundedOn_iff, RelEmbedding.wellFounded_iff_isEmpty, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : forall n, f n in s := fun n => (hf.2 n.lt_succ_self).2.2
    refine ⟨⟨f, ?_⟩, H⟩
    simpa only [H, and_true] using @hf
  · rintro ⟨⟨f, hf⟩, hfs : forall n, f n in s⟩
    refine ⟨⟨f, ?_⟩⟩
    simpa only [hfs, and_true] using @hf

/--
theorem `WellFoundedOn.union` / 定理 `WellFoundedOn.union`

English:
theorem WellFoundedOn.union
  given: (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r)
  proof: by
  rw [wellFoundedOn_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts [hs (g.dual.ltEmbedding.trans f) hg, ht (g.dual.ltEmbedding.trans f) hg]

@[simp]

中文:
定理 WellFoundedOn.union
  条件: (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r)
  证明: by
  rw [wellFoundedOn_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts [hs (g.dual.ltEmbedding.trans f) hg, ht (g.dual.ltEmbedding.trans f) hg]

@[simp]

Depends on / 依赖: Nat.exists_subseq_of_forall_mem_union, exacts, exists_subseq_of_forall_mem_union, g.dual.ltEmbedding.trans, ltEmbedding, wellFoundedOn_iff_no_descending_seq
-/
theorem WellFoundedOn.union (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r) :
    (s union t).WellFoundedOn r := by
  rw [wellFoundedOn_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts [hs (g.dual.ltEmbedding.trans f) hg, ht (g.dual.ltEmbedding.trans f) hg]

@[simp]
/--
theorem `wellFoundedOn_union` / 定理 `wellFoundedOn_union`

English:
theorem wellFoundedOn_union
  statement: (s union t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r
  proof: ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun h =>
    h.1.union h.2⟩

中文:
定理 wellFoundedOn_union
  结论: (s union t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r
  证明: ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun h =>
    h.1.union h.2⟩

Depends on / 依赖: h.subset, subset, subset_union_left, subset_union_right
-/
theorem wellFoundedOn_union : (s union t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r :=
  ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun h =>
    h.1.union h.2⟩

end IsStrictOrder

end WellFoundedOn

/-! ### Sets well-founded w.r.t. the strict inequality -/

section LT

variable [LT α] {s t : Set α}

/--
Definition of `IsWF` / `IsWF` 的定义

English:
definition IsWF
  signature: (s : Set α)
  body: WellFoundedOn s (· < ·)

@[simp]

中文:
定义 IsWF
  签名: (s : Set α)
  定义体: WellFoundedOn s (· < ·)

@[simp]

Depends on / 依赖: WellFoundedOn
-/
def IsWF (s : Set α) : Prop :=
  WellFoundedOn s (· < ·)

@[simp]
/--
theorem `isWF_empty` / 定理 `isWF_empty`

English:
theorem isWF_empty
  statement: IsWF (∅ : Set α)
  proof: wellFounded_of_isEmpty _

中文:
定理 isWF_empty
  结论: IsWF (∅ : Set α)
  证明: wellFounded_of_isEmpty _

Depends on / 依赖: wellFounded_of_isEmpty
-/
theorem isWF_empty : IsWF (∅ : Set α) :=
  wellFounded_of_isEmpty _

/--
theorem `IsWF.mono` / 定理 `IsWF.mono`

English:
theorem IsWF.mono
  given: (h : IsWF t) (st : s subseteq t)
  statement: IsWF s
  proof: h.subset st

中文:
定理 IsWF.mono
  条件: (h : IsWF t) (st : s subseteq t)
  结论: IsWF s
  证明: h.subset st

Depends on / 依赖: h.subset, subset
-/
theorem IsWF.mono (h : IsWF t) (st : s subseteq t) : IsWF s := h.subset st

/--
theorem `isWF_univ_iff` / 定理 `isWF_univ_iff`

English:
theorem isWF_univ_iff
  statement: IsWF (univ : Set α) ↔ WellFoundedLT α
  proof: by
  simp [IsWF, wellFoundedOn_iff, isWellFounded_iff]

中文:
定理 isWF_univ_iff
  结论: IsWF (univ : Set α) ↔ WellFoundedLT α
  证明: by
  simp [IsWF, wellFoundedOn_iff, isWellFounded_iff]

Depends on / 依赖: isWellFounded_iff, wellFoundedOn_iff
-/
theorem isWF_univ_iff : IsWF (univ : Set α) ↔ WellFoundedLT α := by
  simp [IsWF, wellFoundedOn_iff, isWellFounded_iff]

/--
theorem `IsWF.of_wellFoundedLT` / 定理 `IsWF.of_wellFoundedLT`

English:
theorem IsWF.of_wellFoundedLT
  given: [h : WellFoundedLT α] (s : Set α)
  statement: s.IsWF
  proof: (Set.isWF_univ_iff.2 h).mono s.subset_univ

中文:
定理 IsWF.of_wellFoundedLT
  条件: [h : WellFoundedLT α] (s : Set α)
  结论: s.IsWF
  证明: (Set.isWF_univ_iff.2 h).mono s.subset_univ

Depends on / 依赖: Set.isWF_univ_iff, isWF_univ_iff, s.subset_univ, subset_univ
-/
theorem IsWF.of_wellFoundedLT [h : WellFoundedLT α] (s : Set α) : s.IsWF :=
  (Set.isWF_univ_iff.2 h).mono s.subset_univ

end LT

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

protected nonrec theorem IsWF.union (hs : IsWF s) (ht : IsWF t) : IsWF (s union t) := hs.union ht

/--
theorem `isWF_union` / 定理 `isWF_union`

English:
theorem isWF_union
  statement: IsWF (s union t) ↔ IsWF s ∧ IsWF t
  proof: wellFoundedOn_union

中文:
定理 isWF_union
  结论: IsWF (s union t) ↔ IsWF s ∧ IsWF t
  证明: wellFoundedOn_union
-/
@[simp] theorem isWF_union : IsWF (s union t) ↔ IsWF s ∧ IsWF t := wellFoundedOn_union

end Preorder

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

/--
theorem `isWF_iff_no_descending_seq` / 定理 `isWF_iff_no_descending_seq`

English:
theorem isWF_iff_no_descending_seq
  proof: wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.injective⟩, hf.lt_iff_gt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩

中文:
定理 isWF_iff_no_descending_seq
  证明: wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.injective⟩, hf.lt_iff_gt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩

Depends on / 依赖: f.map_rel_iff, hf.injective, hf.lt_iff_gt, injective, lt_iff_gt, map_rel_iff, wellFoundedOn_iff_no_descending_seq, wellFoundedOn_iff_no_descending_seq.trans
-/
theorem isWF_iff_no_descending_seq :
    IsWF s ↔ forall f : Nat -> α, StrictAnti f -> ¬forall n, f n in s :=
  wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.injective⟩, hf.lt_iff_gt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩

end Preorder

/-! ### Partially well-ordered sets -/

/--
Definition of `PartiallyWellOrderedOn` / `PartiallyWellOrderedOn` 的定义

English:
definition PartiallyWellOrderedOn
  signature: (s : Set α) (r : α -> α -> Prop)
  body: WellQuasiOrdered (Subrel r (· in s))

中文:
定义 PartiallyWellOrderedOn
  签名: (s : Set α) (r : α -> α -> 命题)
  定义体: WellQuasiOrdered (Subrel r (· in s))

Depends on / 依赖: Subrel, WellQuasiOrdered
-/
def PartiallyWellOrderedOn (s : Set α) (r : α -> α -> Prop) : Prop :=
  WellQuasiOrdered (Subrel r (· in s))

section PartiallyWellOrderedOn

variable {r : α -> α -> Prop} {r' : β -> β -> Prop} {f : α -> β} {s : Set α} {t : Set α} {a : α}

/--
theorem `PartiallyWellOrderedOn.exists_lt` / 定理 `PartiallyWellOrderedOn.exists_lt`

English:
theorem PartiallyWellOrderedOn.exists_lt
  statement: (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α}
  proof: hs fun n => ⟨_, hf n⟩

中文:
定理 PartiallyWellOrderedOn.exists_lt
  结论: (hs : s.PartiallyWellOrderedOn r) {f : 自然数 -> α}
  证明: hs fun n => ⟨_, hf n⟩
-/
theorem PartiallyWellOrderedOn.exists_lt (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α}
    (hf : forall n, f n in s) : exists m n, m < n ∧ r (f m) (f n) :=
  hs fun n => ⟨_, hf n⟩

/--
theorem `partiallyWellOrderedOn_iff_exists_lt` / 定理 `partiallyWellOrderedOn_iff_exists_lt`

English:
theorem partiallyWellOrderedOn_iff_exists_lt
  statement: s.PartiallyWellOrderedOn r ↔
  proof: ⟨PartiallyWellOrderedOn.exists_lt, fun hf f => hf _ fun n => (f n).2⟩

中文:
定理 partiallyWellOrderedOn_iff_exists_lt
  结论: s.PartiallyWellOrderedOn r ↔
  证明: ⟨PartiallyWellOrderedOn.exists_lt, fun hf f => hf _ fun n => (f n).2⟩

Depends on / 依赖: PartiallyWellOrderedOn, PartiallyWellOrderedOn.exists_lt, exists_lt
-/
theorem partiallyWellOrderedOn_iff_exists_lt : s.PartiallyWellOrderedOn r ↔
    forall f : Nat -> α, (forall n, f n in s) -> exists m n, m < n ∧ r (f m) (f n) :=
  ⟨PartiallyWellOrderedOn.exists_lt, fun hf f => hf _ fun n => (f n).2⟩

/--
theorem `partiallyWellOrderedOn_univ_iff` / 定理 `partiallyWellOrderedOn_univ_iff`

English:
theorem partiallyWellOrderedOn_univ_iff
  statement: univ.PartiallyWellOrderedOn r ↔ WellQuasiOrdered r
  proof: (RelIso.subrelUnivIso (by simp)).wellQuasiOrdered_iff

中文:
定理 partiallyWellOrderedOn_univ_iff
  结论: univ.PartiallyWellOrderedOn r ↔ WellQuasiOrdered r
  证明: (RelIso.subrelUnivIso (by simp)).wellQuasiOrdered_iff

Depends on / 依赖: RelIso, RelIso.subrelUnivIso, subrelUnivIso, wellQuasiOrdered_iff
-/
theorem partiallyWellOrderedOn_univ_iff : univ.PartiallyWellOrderedOn r ↔ WellQuasiOrdered r :=
  (RelIso.subrelUnivIso (by simp)).wellQuasiOrdered_iff

/--
theorem `PartiallyWellOrderedOn.mono` / 定理 `PartiallyWellOrderedOn.mono`

English:
theorem PartiallyWellOrderedOn.mono
  given: (ht : t.PartiallyWellOrderedOn r) (h : s subseteq t)
  proof: fun f => ht (Set.inclusion h ∘ f)

中文:
定理 PartiallyWellOrderedOn.mono
  条件: (ht : t.PartiallyWellOrderedOn r) (h : s subseteq t)
  证明: fun f => ht (Set.inclusion h ∘ f)

Depends on / 依赖: Set.inclusion, inclusion
-/
theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s subseteq t) :
    s.PartiallyWellOrderedOn r :=
  fun f => ht (Set.inclusion h ∘ f)

/--
theorem `partiallyWellOrderedOn_of_wellQuasiOrdered` / 定理 `partiallyWellOrderedOn_of_wellQuasiOrdered`

English:
theorem partiallyWellOrderedOn_of_wellQuasiOrdered
  given: (h : WellQuasiOrdered r) (s : Set α)
  proof: (partiallyWellOrderedOn_univ_iff.mpr h).mono s.subset_univ

@[simp]

中文:
定理 partiallyWellOrderedOn_of_wellQuasiOrdered
  条件: (h : WellQuasiOrdered r) (s : Set α)
  证明: (partiallyWellOrderedOn_univ_iff.mpr h).mono s.subset_univ

@[simp]

Depends on / 依赖: partiallyWellOrderedOn_univ_iff, partiallyWellOrderedOn_univ_iff.mpr, s.subset_univ, subset_univ
-/
theorem partiallyWellOrderedOn_of_wellQuasiOrdered (h : WellQuasiOrdered r) (s : Set α) :
    s.PartiallyWellOrderedOn r :=
  (partiallyWellOrderedOn_univ_iff.mpr h).mono s.subset_univ

@[simp]
/--
theorem `partiallyWellOrderedOn_empty` / 定理 `partiallyWellOrderedOn_empty`

English:
theorem partiallyWellOrderedOn_empty
  given: (r : α -> α -> Prop)
  statement: PartiallyWellOrderedOn ∅ r
  proof: wellQuasiOrdered_of_isEmpty _

中文:
定理 partiallyWellOrderedOn_empty
  条件: (r : α -> α -> 命题)
  结论: PartiallyWellOrderedOn ∅ r
  证明: wellQuasiOrdered_of_isEmpty _

Depends on / 依赖: wellQuasiOrdered_of_isEmpty
-/
theorem partiallyWellOrderedOn_empty (r : α -> α -> Prop) : PartiallyWellOrderedOn ∅ r :=
  wellQuasiOrdered_of_isEmpty _

/--
theorem `PartiallyWellOrderedOn.union` / 定理 `PartiallyWellOrderedOn.union`

English:
theorem PartiallyWellOrderedOn.union
  statement: (hs : s.PartiallyWellOrderedOn r)
  proof: by
  intro f
  obtain ⟨g, hgs | hgt⟩ := Nat.exists_subseq_of_forall_mem_union _ fun x => (f x).2
  · rcases hs.exists_lt hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
  · rcases ht.exists_lt hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩

@[simp]

中文:
定理 PartiallyWellOrderedOn.union
  结论: (hs : s.PartiallyWellOrderedOn r)
  证明: by
  intro f
  obtain ⟨g, hgs | hgt⟩ := Nat.exists_subseq_of_forall_mem_union _ fun x => (f x).2
  · rcases hs.exists_lt hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
  · rcases ht.exists_lt hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩

@[simp]

Depends on / 依赖: Nat.exists_subseq_of_forall_mem_union, exists_lt, exists_subseq_of_forall_mem_union, g.strictMono, hs.exists_lt, ht.exists_lt, strictMono
-/
theorem PartiallyWellOrderedOn.union (hs : s.PartiallyWellOrderedOn r)
    (ht : t.PartiallyWellOrderedOn r) : (s union t).PartiallyWellOrderedOn r := by
  intro f
  obtain ⟨g, hgs | hgt⟩ := Nat.exists_subseq_of_forall_mem_union _ fun x => (f x).2
  · rcases hs.exists_lt hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩
  · rcases ht.exists_lt hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strictMono hlt, hr⟩

@[simp]
/--
theorem `partiallyWellOrderedOn_union` / 定理 `partiallyWellOrderedOn_union`

English:
theorem partiallyWellOrderedOn_union
  proof: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h => h.1.union h.2⟩

中文:
定理 partiallyWellOrderedOn_union
  证明: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h => h.1.union h.2⟩

Depends on / 依赖: h.mono, subset_union_left, subset_union_right
-/
theorem partiallyWellOrderedOn_union :
    (s union t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h => h.1.union h.2⟩

/--
theorem `PartiallyWellOrderedOn.image_of_monotone_on` / 定理 `PartiallyWellOrderedOn.image_of_monotone_on`

English:
theorem PartiallyWellOrderedOn.image_of_monotone_on
  statement: (hs : s.PartiallyWellOrderedOn r)
  proof: by
  rw [partiallyWellOrderedOn_iff_exists_lt] at *
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g' := funext heq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩

中文:
定理 PartiallyWellOrderedOn.image_of_monotone_on
  结论: (hs : s.PartiallyWellOrderedOn r)
  证明: by
  rw [partiallyWellOrderedOn_iff_exists_lt] at *
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g' := funext heq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩

Depends on / 依赖: partiallyWellOrderedOn_iff_exists_lt
-/
theorem PartiallyWellOrderedOn.image_of_monotone_on (hs : s.PartiallyWellOrderedOn r)
    (hf : forall a₁ in s, forall a₂ in s, r a₁ a₂ -> r' (f a₁) (f a₂)) : (f '' s).PartiallyWellOrderedOn r' := by
  rw [partiallyWellOrderedOn_iff_exists_lt] at *
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g' := funext heq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩

-- TODO: prove this in terms of `IsAntichain.finite_of_wellQuasiOrdered`
/--
theorem `_root_.IsAntichain.finite_of_partiallyWellOrderedOn` / 定理 `_root_.IsAntichain.finite_of_partiallyWellOrderedOn`

English:
theorem _root_.IsAntichain.finite_of_partiallyWellOrderedOn
  statement: (ha : IsAntichain r s)
  proof: by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hp (hi.natEmbedding _)
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    ha.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

中文:
定理 _root_.IsAntichain.finite_of_partiallyWellOrderedOn
  结论: (ha : IsAntichain r s)
  证明: by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hp (hi.natEmbedding _)
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    ha.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

Depends on / 依赖: Subtype, Subtype.val_injective, ha.eq, hi.natEmbedding, hmn.ne, injective, natEmbedding, val_injective
-/
theorem _root_.IsAntichain.finite_of_partiallyWellOrderedOn (ha : IsAntichain r s)
    (hp : s.PartiallyWellOrderedOn r) : s.Finite := by
  by_contra! hi
  obtain ⟨m, n, hmn, h⟩ := hp (hi.natEmbedding _)
  exact hmn.ne ((hi.natEmbedding _).injective <| Subtype.val_injective <|
    ha.eq (hi.natEmbedding _ m).2 (hi.natEmbedding _ n).2 h)

section Refl
variable [Std.Refl r]

/--
theorem `Finite.partiallyWellOrderedOn` / 定理 `Finite.partiallyWellOrderedOn`

English:
theorem Finite.partiallyWellOrderedOn
  given: (hs : s.Finite)
  statement: s.PartiallyWellOrderedOn r
  proof: hs.to_subtype.wellQuasiOrdered _

中文:
定理 Finite.partiallyWellOrderedOn
  条件: (hs : s.Finite)
  结论: s.PartiallyWellOrderedOn r
  证明: hs.to_subtype.wellQuasiOrdered _
-/
protected theorem Finite.partiallyWellOrderedOn (hs : s.Finite) : s.PartiallyWellOrderedOn r :=
  hs.to_subtype.wellQuasiOrdered _

/--
theorem `_root_.IsAntichain.partiallyWellOrderedOn_iff` / 定理 `_root_.IsAntichain.partiallyWellOrderedOn_iff`

English:
theorem _root_.IsAntichain.partiallyWellOrderedOn_iff
  given: (hs : IsAntichain r s)
  proof: ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩

@[simp]

中文:
定理 _root_.IsAntichain.partiallyWellOrderedOn_iff
  条件: (hs : IsAntichain r s)
  证明: ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩

@[simp]

Depends on / 依赖: Finite, Finite.partiallyWellOrderedOn, finite_of_partiallyWellOrderedOn, hs.finite_of_partiallyWellOrderedOn, partiallyWellOrderedOn
-/
theorem _root_.IsAntichain.partiallyWellOrderedOn_iff (hs : IsAntichain r s) :
    s.PartiallyWellOrderedOn r ↔ s.Finite :=
  ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩

@[simp]
/--
theorem `partiallyWellOrderedOn_singleton` / 定理 `partiallyWellOrderedOn_singleton`

English:
theorem partiallyWellOrderedOn_singleton
  given: (a : α)
  statement: PartiallyWellOrderedOn {a} r
  proof: (finite_singleton a).partiallyWellOrderedOn

@[nontriviality]

中文:
定理 partiallyWellOrderedOn_singleton
  条件: (a : α)
  结论: PartiallyWellOrderedOn {a} r
  证明: (finite_singleton a).partiallyWellOrderedOn

@[nontriviality]

Depends on / 依赖: finite_singleton, partiallyWellOrderedOn
-/
theorem partiallyWellOrderedOn_singleton (a : α) : PartiallyWellOrderedOn {a} r :=
  (finite_singleton a).partiallyWellOrderedOn

@[nontriviality]
/--
theorem `Subsingleton.partiallyWellOrderedOn` / 定理 `Subsingleton.partiallyWellOrderedOn`

English:
theorem Subsingleton.partiallyWellOrderedOn
  given: (hs : s.Subsingleton)
  statement: PartiallyWellOrderedOn s r
  proof: hs.finite.partiallyWellOrderedOn

@[simp]

中文:
定理 Subsingleton.partiallyWellOrderedOn
  条件: (hs : s.Subsingleton)
  结论: PartiallyWellOrderedOn s r
  证明: hs.finite.partiallyWellOrderedOn

@[simp]

Depends on / 依赖: finite, hs.finite.partiallyWellOrderedOn, partiallyWellOrderedOn
-/
theorem Subsingleton.partiallyWellOrderedOn (hs : s.Subsingleton) : PartiallyWellOrderedOn s r :=
  hs.finite.partiallyWellOrderedOn

@[simp]
/--
theorem `partiallyWellOrderedOn_insert` / 定理 `partiallyWellOrderedOn_insert`

English:
theorem partiallyWellOrderedOn_insert
  proof: by
  simp only [← singleton_union, partiallyWellOrderedOn_union,
    partiallyWellOrderedOn_singleton, true_and]

中文:
定理 partiallyWellOrderedOn_insert
  证明: by
  simp only [← singleton_union, partiallyWellOrderedOn_union,
    partiallyWellOrderedOn_singleton, true_and]

Depends on / 依赖: partiallyWellOrderedOn_singleton, partiallyWellOrderedOn_union, singleton_union, true_and
-/
theorem partiallyWellOrderedOn_insert :
    PartiallyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r := by
  simp only [← singleton_union, partiallyWellOrderedOn_union,
    partiallyWellOrderedOn_singleton, true_and]

/--
theorem `PartiallyWellOrderedOn.insert` / 定理 `PartiallyWellOrderedOn.insert`

English:
theorem PartiallyWellOrderedOn.insert
  given: (h : PartiallyWellOrderedOn s r) (a : α)
  proof: partiallyWellOrderedOn_insert.2 h

中文:
定理 PartiallyWellOrderedOn.insert
  条件: (h : PartiallyWellOrderedOn s r) (a : α)
  证明: partiallyWellOrderedOn_insert.2 h
-/
protected theorem PartiallyWellOrderedOn.insert (h : PartiallyWellOrderedOn s r) (a : α) :
    PartiallyWellOrderedOn (insert a s) r :=
  partiallyWellOrderedOn_insert.2 h

/--
theorem `partiallyWellOrderedOn_iff_finite_antichains` / 定理 `partiallyWellOrderedOn_iff_finite_antichains`

English:
theorem partiallyWellOrderedOn_iff_finite_antichains
  given: [Std.Symm r]
  proof: by
  refine ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), ?_⟩
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro hs f hf
  by_contra! H
  refine infinite_range_of_injective (fun m n hmn => ?_) (hs _ (range_subset_iff.2 hf) ?_)
  · obtain h | h | h := lt_trichotomy m n
    · r

中文:
定理 partiallyWellOrderedOn_iff_finite_antichains
  条件: [Std.Symm r]
  证明: by
  refine ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), ?_⟩
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro hs f hf
  by_contra! H
  refine infinite_range_of_injective (fun m n hmn => ?_) (hs _ (range_subset_iff.2 hf) ?_)
  · obtain h | h | h := lt_trichotomy m n
    · r

Depends on / 依赖: finite_of_partiallyWellOrderedOn, h.mono, hrt.finite_of_partiallyWellOrderedOn, infinite_range_of_injective, lt_or_gt, lt_trichotomy, ne_of_apply_ne, partiallyWellOrderedOn_iff_exists_lt, range_subset_iff
-/
theorem partiallyWellOrderedOn_iff_finite_antichains [Std.Symm r] :
    s.PartiallyWellOrderedOn r ↔ forall t, t subseteq s -> IsAntichain r t -> t.Finite := by
  refine ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), ?_⟩
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro hs f hf
  by_contra! H
  refine infinite_range_of_injective (fun m n hmn => ?_) (hs _ (range_subset_iff.2 hf) ?_)
  · obtain h | h | h := lt_trichotomy m n
    · refine (H _ _ h ?_).elim
      rw [hmn]
      exact refl _
    · exact h
    · refine (H _ _ h ?_).elim
      rw [hmn]
      exact refl _
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn
  obtain h | h := (ne_of_apply_ne _ hmn).lt_or_gt
  · exact H _ _ h
  · exact mt symm (H _ _ h)

end Refl

section IsPreorder
variable [IsPreorder α r]

/--
theorem `PartiallyWellOrderedOn.exists_monotone_subseq` / 定理 `PartiallyWellOrderedOn.exists_monotone_subseq`

English:
theorem PartiallyWellOrderedOn.exists_monotone_subseq
  statement: (h : s.PartiallyWellOrderedOn r) {f : Nat -> α}
  proof: WellQuasiOrdered.exists_monotone_subseq h fun n => ⟨_, hf n⟩

中文:
定理 PartiallyWellOrderedOn.exists_monotone_subseq
  结论: (h : s.PartiallyWellOrderedOn r) {f : 自然数 -> α}
  证明: WellQuasiOrdered.exists_monotone_subseq h fun n => ⟨_, hf n⟩

Depends on / 依赖: WellQuasiOrdered, WellQuasiOrdered.exists_monotone_subseq, exists_monotone_subseq
-/
theorem PartiallyWellOrderedOn.exists_monotone_subseq (h : s.PartiallyWellOrderedOn r) {f : Nat -> α}
    (hf : forall n, f n in s) : exists g : Nat ↪o Nat, forall m n : Nat, m <= n -> r (f (g m)) (f (g n)) :=
  WellQuasiOrdered.exists_monotone_subseq h fun n => ⟨_, hf n⟩

/--
theorem `partiallyWellOrderedOn_iff_exists_monotone_subseq` / 定理 `partiallyWellOrderedOn_iff_exists_monotone_subseq`

English:
theorem partiallyWellOrderedOn_iff_exists_monotone_subseq
  proof: by
  use PartiallyWellOrderedOn.exists_monotone_subseq
  rw [PartiallyWellOrderedOn]; rw [wellQuasiOrdered_iff_exists_monotone_subseq]
  exact fun H f => H _ fun n => (f n).2

中文:
定理 partiallyWellOrderedOn_iff_exists_monotone_subseq
  证明: by
  use PartiallyWellOrderedOn.exists_monotone_subseq
  rw [PartiallyWellOrderedOn]; rw [wellQuasiOrdered_iff_exists_monotone_subseq]
  exact fun H f => H _ fun n => (f n).2

Depends on / 依赖: PartiallyWellOrderedOn, PartiallyWellOrderedOn.exists_monotone_subseq, exists_monotone_subseq, wellQuasiOrdered_iff_exists_monotone_subseq
-/
theorem partiallyWellOrderedOn_iff_exists_monotone_subseq :
    s.PartiallyWellOrderedOn r ↔
      forall f : Nat -> α, (forall n, f n in s) -> exists g : Nat ↪o Nat, forall m n : Nat, m <= n -> r (f (g m)) (f (g n)) := by
  use PartiallyWellOrderedOn.exists_monotone_subseq
  rw [PartiallyWellOrderedOn]; rw [wellQuasiOrdered_iff_exists_monotone_subseq]
  exact fun H f => H _ fun n => (f n).2

/--
theorem `PartiallyWellOrderedOn.prod` / 定理 `PartiallyWellOrderedOn.prod`

English:
theorem PartiallyWellOrderedOn.prod
  statement: {t : Set β} (hs : PartiallyWellOrderedOn s r)
  proof: by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht.exists_lt fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strictMono hlt, h₁ _ _ hlt.le, hle⟩

中文:
定理 PartiallyWellOrderedOn.prod
  结论: {t : Set β} (hs : PartiallyWellOrderedOn s r)
  证明: by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht.exists_lt fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strictMono hlt, h₁ _ _ hlt.le, hle⟩
-/
protected theorem PartiallyWellOrderedOn.prod {t : Set β} (hs : PartiallyWellOrderedOn s r)
    (ht : PartiallyWellOrderedOn t r') :
    PartiallyWellOrderedOn (s ×ˢ t) fun x y : α × β => r x.1 y.1 ∧ r' x.2 y.2 := by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht.exists_lt fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strictMono hlt, h₁ _ _ hlt.le, hle⟩

/--
theorem `PartiallyWellOrderedOn.pi` / 定理 `PartiallyWellOrderedOn.pi`

English:
theorem PartiallyWellOrderedOn.pi
  statement: {α : ι -> Type*} [Finite ι] {r : forall i, α i -> α i -> Prop}
  proof: by
  have := Fintype.ofFinite ι
  have : IsPreorder (forall i, α i) (fun a b : forall i, α i => forall i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices forall (t : Finset ι), forall (f : Nat -> forall i, α i), (forall n i, f

中文:
定理 PartiallyWellOrderedOn.pi
  结论: {α : ι -> 类型} [Finite ι] {r : 对任意 i, α i -> α i -> 命题}
  证明: by
  have := Fintype.ofFinite ι
  have : IsPreorder (forall i, α i) (fun a b : forall i, α i => forall i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices forall (t : Finset ι), forall (f : Nat -> forall i, α i), (forall n i, f
-/
protected theorem PartiallyWellOrderedOn.pi {α : ι -> Type*} [Finite ι] {r : forall i, α i -> α i -> Prop}
    [forall i, IsPreorder (α i) (r i)] {s : forall i, Set (α i)}
    (hs : forall i, PartiallyWellOrderedOn (s i) (r i)) :
    PartiallyWellOrderedOn (Set.univ.pi s) fun a b : forall i, α i => forall i, r i (a i) (b i) := by
  have := Fintype.ofFinite ι
  have : IsPreorder (forall i, α i) (fun a b : forall i, α i => forall i, r i (a i) (b i)) :=
    { refl a i := refl (a i)
      trans a b c hab hbc i := _root_.trans (hab i) (hbc i) }
  suffices forall (t : Finset ι), forall (f : Nat -> forall i, α i), (forall n i, f n i in s i) ->
    exists g : Nat ↪o Nat, forall ⦃a b : Nat⦄, a <= b -> forall i, i in t -> r i ((f ∘ g) a i) ((f ∘ g) b i) by
    rw [partiallyWellOrderedOn_iff_exists_monotone_subseq]
    intro f hf
    simp only [mem_pi, mem_univ, forall_const] at hf
    simpa only [Finset.mem_univ, true_imp_iff] using! this Finset.univ f hf
  refine Finset.cons_induction ?_ ?_
  · intro f hf
    exists RelEmbedding.refl (· <= ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, Finset.notMem_empty]
  · intro i t hi ih f hf
    obtain ⟨g, hg⟩ := (hs i).exists_monotone_subseq (hf · i)
    obtain ⟨g', hg'⟩ := ih (f ∘ g) (hf <| g ·)
    refine ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 ?_⟩
    exact ⟨hg _ _ (OrderHomClass.mono g' hab), hg' hab⟩

/--
theorem `PartiallyWellOrderedOn.wellFoundedOn` / 定理 `PartiallyWellOrderedOn.wellFoundedOn`

English:
theorem PartiallyWellOrderedOn.wellFoundedOn
  given: (h : s.PartiallyWellOrderedOn r)
  proof: h.wellFounded

中文:
定理 PartiallyWellOrderedOn.wellFoundedOn
  条件: (h : s.PartiallyWellOrderedOn r)
  证明: h.wellFounded

Depends on / 依赖: h.wellFounded, wellFounded
-/
theorem PartiallyWellOrderedOn.wellFoundedOn (h : s.PartiallyWellOrderedOn r) :
    s.WellFoundedOn fun a b => r a b ∧ ¬ r b a :=
  h.wellFounded

end IsPreorder

end PartiallyWellOrderedOn

section IsPWO

variable [Preorder α] [Preorder β] {s t : Set α}

/--
Definition of `IsPWO` / `IsPWO` 的定义

English:
definition IsPWO
  signature: (s : Set α)
  body: PartiallyWellOrderedOn s (· <= ·)

nonrec theorem IsPWO.mono (ht : t.IsPWO) : s subseteq t -> s.IsPWO := ht.mono

nonrec theorem IsPWO.exists_monotone_subseq (h : s.IsPWO) {f : Nat -> α} (hf : forall n, f n in s) :
    exists g : Nat ↪o Nat, Monotone (f ∘ g) :=
  h.exists_monotone_subseq hf

中文:
定义 IsPWO
  签名: (s : Set α)
  定义体: PartiallyWellOrderedOn s (· <= ·)

nonrec theorem IsPWO.mono (ht : t.IsPWO) : s subseteq t -> s.IsPWO := ht.mono

nonrec theorem IsPWO.exists_monotone_subseq (h : s.IsPWO) {f : Nat -> α} (hf : forall n, f n in s) :
    exists g : Nat ↪o Nat, Monotone (f ∘ g) :=
  h.exists_monotone_subseq hf

Depends on / 依赖: PartiallyWellOrderedOn
-/
def IsPWO (s : Set α) : Prop :=
  PartiallyWellOrderedOn s (· <= ·)

nonrec theorem IsPWO.mono (ht : t.IsPWO) : s subseteq t -> s.IsPWO := ht.mono

nonrec theorem IsPWO.exists_monotone_subseq (h : s.IsPWO) {f : Nat -> α} (hf : forall n, f n in s) :
    exists g : Nat ↪o Nat, Monotone (f ∘ g) :=
  h.exists_monotone_subseq hf

/--
theorem `isPWO_univ_iff` / 定理 `isPWO_univ_iff`

English:
theorem isPWO_univ_iff
  statement: (univ : Set α).IsPWO ↔ WellQuasiOrderedLE α
  proof: partiallyWellOrderedOn_univ_iff.trans (wellQuasiOrderedLE_def _).symm

中文:
定理 isPWO_univ_iff
  结论: (univ : Set α).IsPWO ↔ WellQuasiOrderedLE α
  证明: partiallyWellOrderedOn_univ_iff.trans (wellQuasiOrderedLE_def _).symm

Depends on / 依赖: partiallyWellOrderedOn_univ_iff, partiallyWellOrderedOn_univ_iff.trans, wellQuasiOrderedLE_def
-/
theorem isPWO_univ_iff : (univ : Set α).IsPWO ↔ WellQuasiOrderedLE α :=
  partiallyWellOrderedOn_univ_iff.trans (wellQuasiOrderedLE_def _).symm

/--
theorem `isPWO_of_wellQuasiOrderedLE` / 定理 `isPWO_of_wellQuasiOrderedLE`

English:
theorem isPWO_of_wellQuasiOrderedLE
  given: [h : WellQuasiOrderedLE α] (s : Set α)
  statement: s.IsPWO
  proof: partiallyWellOrderedOn_of_wellQuasiOrdered h.wqo s

中文:
定理 isPWO_of_wellQuasiOrderedLE
  条件: [h : WellQuasiOrderedLE α] (s : Set α)
  结论: s.IsPWO
  证明: partiallyWellOrderedOn_of_wellQuasiOrdered h.wqo s

Depends on / 依赖: h.wqo, partiallyWellOrderedOn_of_wellQuasiOrdered
-/
theorem isPWO_of_wellQuasiOrderedLE [h : WellQuasiOrderedLE α] (s : Set α) : s.IsPWO :=
  partiallyWellOrderedOn_of_wellQuasiOrdered h.wqo s

/--
theorem `isPWO_iff_exists_monotone_subseq` / 定理 `isPWO_iff_exists_monotone_subseq`

English:
theorem isPWO_iff_exists_monotone_subseq
  proof: partiallyWellOrderedOn_iff_exists_monotone_subseq

中文:
定理 isPWO_iff_exists_monotone_subseq
  证明: partiallyWellOrderedOn_iff_exists_monotone_subseq

Depends on / 依赖: partiallyWellOrderedOn_iff_exists_monotone_subseq
-/
theorem isPWO_iff_exists_monotone_subseq :
    s.IsPWO ↔ forall f : Nat -> α, (forall n, f n in s) -> exists g : Nat ↪o Nat, Monotone (f ∘ g) :=
  partiallyWellOrderedOn_iff_exists_monotone_subseq

/--
theorem `IsPWO.isWF` / 定理 `IsPWO.isWF`

English:
theorem IsPWO.isWF
  given: (h : s.IsPWO)
  statement: s.IsWF
  proof: by
  simpa only [← lt_iff_le_not_ge] using! h.wellFoundedOn

nonrec theorem IsPWO.prod {t : Set β} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s ×ˢ t) :=
  hs.prod ht

中文:
定理 IsPWO.isWF
  条件: (h : s.IsPWO)
  结论: s.IsWF
  证明: by
  simpa only [← lt_iff_le_not_ge] using! h.wellFoundedOn

nonrec theorem IsPWO.prod {t : Set β} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s ×ˢ t) :=
  hs.prod ht
-/
protected theorem IsPWO.isWF (h : s.IsPWO) : s.IsWF := by
  simpa only [← lt_iff_le_not_ge] using! h.wellFoundedOn

nonrec theorem IsPWO.prod {t : Set β} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s ×ˢ t) :=
  hs.prod ht

/--
theorem `IsPWO.pi` / 定理 `IsPWO.pi`

English:
theorem IsPWO.pi
  statement: {α : ι -> Type*} [Finite ι] [forall i, Preorder (α i)] {s : forall i, Set (α i)}
  proof: PartiallyWellOrderedOn.pi hs

中文:
定理 IsPWO.pi
  结论: {α : ι -> 类型} [Finite ι] [对任意 i, Preorder (α i)] {s : 对任意 i, Set (α i)}
  证明: PartiallyWellOrderedOn.pi hs

Depends on / 依赖: PartiallyWellOrderedOn, PartiallyWellOrderedOn.pi
-/
theorem IsPWO.pi {α : ι -> Type*} [Finite ι] [forall i, Preorder (α i)] {s : forall i, Set (α i)}
    (hs : forall i, (s i).IsPWO) : (Set.univ.pi s).IsPWO :=
  PartiallyWellOrderedOn.pi hs

/--
theorem `IsPWO.image_of_monotoneOn` / 定理 `IsPWO.image_of_monotoneOn`

English:
theorem IsPWO.image_of_monotoneOn
  given: (hs : s.IsPWO) {f : α -> β} (hf : MonotoneOn f s)
  proof: hs.image_of_monotone_on hf

中文:
定理 IsPWO.image_of_monotoneOn
  条件: (hs : s.IsPWO) {f : α -> β} (hf : MonotoneOn f s)
  证明: hs.image_of_monotone_on hf

Depends on / 依赖: hs.image_of_monotone_on, image_of_monotone_on
-/
theorem IsPWO.image_of_monotoneOn (hs : s.IsPWO) {f : α -> β} (hf : MonotoneOn f s) :
    IsPWO (f '' s) :=
  hs.image_of_monotone_on hf

/--
theorem `IsPWO.image_of_monotone` / 定理 `IsPWO.image_of_monotone`

English:
theorem IsPWO.image_of_monotone
  given: (hs : s.IsPWO) {f : α -> β} (hf : Monotone f)
  statement: IsPWO (f '' s)
  proof: hs.image_of_monotone_on (hf.monotoneOn _)

protected nonrec theorem IsPWO.union (hs : IsPWO s) (ht : IsPWO t) : IsPWO (s union t) :=
  hs.union ht

@[simp]

中文:
定理 IsPWO.image_of_monotone
  条件: (hs : s.IsPWO) {f : α -> β} (hf : Monotone f)
  结论: IsPWO (f '' s)
  证明: hs.image_of_monotone_on (hf.monotoneOn _)

protected nonrec theorem IsPWO.union (hs : IsPWO s) (ht : IsPWO t) : IsPWO (s union t) :=
  hs.union ht

@[simp]

Depends on / 依赖: hf.monotoneOn, hs.image_of_monotone_on, image_of_monotone_on, monotoneOn
-/
theorem IsPWO.image_of_monotone (hs : s.IsPWO) {f : α -> β} (hf : Monotone f) : IsPWO (f '' s) :=
  hs.image_of_monotone_on (hf.monotoneOn _)

protected nonrec theorem IsPWO.union (hs : IsPWO s) (ht : IsPWO t) : IsPWO (s union t) :=
  hs.union ht

@[simp]
/--
theorem `isPWO_union` / 定理 `isPWO_union`

English:
theorem isPWO_union
  statement: IsPWO (s union t) ↔ IsPWO s ∧ IsPWO t
  proof: partiallyWellOrderedOn_union

中文:
定理 isPWO_union
  结论: IsPWO (s union t) ↔ IsPWO s ∧ IsPWO t
  证明: partiallyWellOrderedOn_union

Depends on / 依赖: partiallyWellOrderedOn_union
-/
theorem isPWO_union : IsPWO (s union t) ↔ IsPWO s ∧ IsPWO t :=
  partiallyWellOrderedOn_union

/--
theorem `Finite.isPWO` / 定理 `Finite.isPWO`

English:
theorem Finite.isPWO
  given: (hs : s.Finite)
  statement: IsPWO s
  proof: hs.partiallyWellOrderedOn

中文:
定理 Finite.isPWO
  条件: (hs : s.Finite)
  结论: IsPWO s
  证明: hs.partiallyWellOrderedOn
-/
protected theorem Finite.isPWO (hs : s.Finite) : IsPWO s := hs.partiallyWellOrderedOn

/--
theorem `isPWO_of_finite` / 定理 `isPWO_of_finite`

English:
theorem isPWO_of_finite
  given: [Finite α]
  statement: s.IsPWO
  proof: s.toFinite.isPWO

中文:
定理 isPWO_of_finite
  条件: [Finite α]
  结论: s.IsPWO
  证明: s.toFinite.isPWO
-/
@[simp] theorem isPWO_of_finite [Finite α] : s.IsPWO := s.toFinite.isPWO

/--
theorem `isPWO_singleton` / 定理 `isPWO_singleton`

English:
theorem isPWO_singleton
  given: (a : α)
  statement: IsPWO ({a} : Set α)
  proof: (finite_singleton a).isPWO

中文:
定理 isPWO_singleton
  条件: (a : α)
  结论: IsPWO ({a} : Set α)
  证明: (finite_singleton a).isPWO
-/
@[simp] theorem isPWO_singleton (a : α) : IsPWO ({a} : Set α) := (finite_singleton a).isPWO

/--
theorem `isPWO_empty` / 定理 `isPWO_empty`

English:
theorem isPWO_empty
  statement: IsPWO (∅ : Set α)
  proof: finite_empty.isPWO

中文:
定理 isPWO_empty
  结论: IsPWO (∅ : Set α)
  证明: finite_empty.isPWO
-/
@[simp] theorem isPWO_empty : IsPWO (∅ : Set α) := finite_empty.isPWO

/--
theorem `Subsingleton.isPWO` / 定理 `Subsingleton.isPWO`

English:
theorem Subsingleton.isPWO
  given: (hs : s.Subsingleton)
  statement: IsPWO s
  proof: hs.finite.isPWO

@[simp]

中文:
定理 Subsingleton.isPWO
  条件: (hs : s.Subsingleton)
  结论: IsPWO s
  证明: hs.finite.isPWO

@[simp]
-/
protected theorem Subsingleton.isPWO (hs : s.Subsingleton) : IsPWO s := hs.finite.isPWO

@[simp]
/--
theorem `isPWO_insert` / 定理 `isPWO_insert`

English:
theorem isPWO_insert
  given: {a}
  statement: IsPWO (insert a s) ↔ IsPWO s
  proof: by
  simp only [← singleton_union, isPWO_union, isPWO_singleton, true_and]

中文:
定理 isPWO_insert
  条件: {a}
  结论: IsPWO (insert a s) ↔ IsPWO s
  证明: by
  simp only [← singleton_union, isPWO_union, isPWO_singleton, true_and]

Depends on / 依赖: isPWO_singleton, isPWO_union, singleton_union, true_and
-/
theorem isPWO_insert {a} : IsPWO (insert a s) ↔ IsPWO s := by
  simp only [← singleton_union, isPWO_union, isPWO_singleton, true_and]

/--
theorem `IsPWO.insert` / 定理 `IsPWO.insert`

English:
theorem IsPWO.insert
  given: (h : IsPWO s) (a : α)
  statement: IsPWO (insert a s)
  proof: isPWO_insert.2 h

中文:
定理 IsPWO.insert
  条件: (h : IsPWO s) (a : α)
  结论: IsPWO (insert a s)
  证明: isPWO_insert.2 h
-/
protected theorem IsPWO.insert (h : IsPWO s) (a : α) : IsPWO (insert a s) :=
  isPWO_insert.2 h

/--
theorem `Finite.isWF` / 定理 `Finite.isWF`

English:
theorem Finite.isWF
  given: (hs : s.Finite)
  statement: IsWF s
  proof: hs.isPWO.isWF

中文:
定理 Finite.isWF
  条件: (hs : s.Finite)
  结论: IsWF s
  证明: hs.isPWO.isWF
-/
protected theorem Finite.isWF (hs : s.Finite) : IsWF s := hs.isPWO.isWF

/--
theorem `isWF_singleton` / 定理 `isWF_singleton`

English:
theorem isWF_singleton
  given: {a : α}
  statement: IsWF ({a} : Set α)
  proof: (finite_singleton a).isWF

中文:
定理 isWF_singleton
  条件: {a : α}
  结论: IsWF ({a} : Set α)
  证明: (finite_singleton a).isWF
-/
@[simp] theorem isWF_singleton {a : α} : IsWF ({a} : Set α) := (finite_singleton a).isWF

/--
theorem `Subsingleton.isWF` / 定理 `Subsingleton.isWF`

English:
theorem Subsingleton.isWF
  given: (hs : s.Subsingleton)
  statement: IsWF s
  proof: hs.isPWO.isWF

@[simp]

中文:
定理 Subsingleton.isWF
  条件: (hs : s.Subsingleton)
  结论: IsWF s
  证明: hs.isPWO.isWF

@[simp]
-/
protected theorem Subsingleton.isWF (hs : s.Subsingleton) : IsWF s := hs.isPWO.isWF

@[simp]
/--
theorem `isWF_insert` / 定理 `isWF_insert`

English:
theorem isWF_insert
  given: {a}
  statement: IsWF (insert a s) ↔ IsWF s
  proof: by
  simp only [← singleton_union, isWF_union, isWF_singleton, true_and]

中文:
定理 isWF_insert
  条件: {a}
  结论: IsWF (insert a s) ↔ IsWF s
  证明: by
  simp only [← singleton_union, isWF_union, isWF_singleton, true_and]

Depends on / 依赖: isWF_singleton, isWF_union, singleton_union, true_and
-/
theorem isWF_insert {a} : IsWF (insert a s) ↔ IsWF s := by
  simp only [← singleton_union, isWF_union, isWF_singleton, true_and]

/--
theorem `IsWF.insert` / 定理 `IsWF.insert`

English:
theorem IsWF.insert
  given: (h : IsWF s) (a : α)
  statement: IsWF (insert a s)
  proof: isWF_insert.2 h

中文:
定理 IsWF.insert
  条件: (h : IsWF s) (a : α)
  结论: IsWF (insert a s)
  证明: isWF_insert.2 h
-/
protected theorem IsWF.insert (h : IsWF s) (a : α) : IsWF (insert a s) :=
  isWF_insert.2 h

/--
theorem `IsPWO.exists_le_minimal` / 定理 `IsPWO.exists_le_minimal`

English:
theorem IsPWO.exists_le_minimal
  given: {a} (hs : s.IsPWO) (ha : a in s)
  proof: by
  let t : Set s := {x | x <= a}
  let h : t.Nonempty := ⟨⟨a, ha⟩, le_rfl⟩
  refine ⟨hs.wellFounded.min t h, hs.wellFounded.min_mem t h,
    (hs.wellFounded.min t h).2, fun y hy hle => ?_⟩
  by_contra hnle
  exact hs.wellFounded.not_lt_min t (x := ⟨y, hy⟩) (hle.trans (hs.wellFounded.min_mem t h))


中文:
定理 IsPWO.exists_le_minimal
  条件: {a} (hs : s.IsPWO) (ha : a in s)
  证明: by
  let t : Set s := {x | x <= a}
  let h : t.Nonempty := ⟨⟨a, ha⟩, le_rfl⟩
  refine ⟨hs.wellFounded.min t h, hs.wellFounded.min_mem t h,
    (hs.wellFounded.min t h).2, fun y hy hle => ?_⟩
  by_contra hnle
  exact hs.wellFounded.not_lt_min t (x := ⟨y, hy⟩) (hle.trans (hs.wellFounded.min_mem t h))


Depends on / 依赖: Nonempty, hle.trans, hs.wellFounded.min, hs.wellFounded.min_mem, hs.wellFounded.not_lt_min, le_rfl, min_mem, not_lt_min, t.Nonempty, wellFounded
-/
theorem IsPWO.exists_le_minimal {a} (hs : s.IsPWO) (ha : a in s) :
    exists b <= a, Minimal (· in s) b := by
  let t : Set s := {x | x <= a}
  let h : t.Nonempty := ⟨⟨a, ha⟩, le_rfl⟩
  refine ⟨hs.wellFounded.min t h, hs.wellFounded.min_mem t h,
    (hs.wellFounded.min t h).2, fun y hy hle => ?_⟩
  by_contra hnle
  exact hs.wellFounded.not_lt_min t (x := ⟨y, hy⟩) (hle.trans (hs.wellFounded.min_mem t h))
    ⟨hle, hnle⟩

/--
theorem `IsPWO.exists_minimal` / 定理 `IsPWO.exists_minimal`

English:
theorem IsPWO.exists_minimal
  given: (h : s.IsPWO) (hs : s.Nonempty)
  proof: by
  rcases hs with ⟨a, ha⟩
  obtain ⟨b, _, hb⟩ := h.exists_le_minimal ha
  exact ⟨b, hb⟩

中文:
定理 IsPWO.exists_minimal
  条件: (h : s.IsPWO) (hs : s.Nonempty)
  证明: by
  rcases hs with ⟨a, ha⟩
  obtain ⟨b, _, hb⟩ := h.exists_le_minimal ha
  exact ⟨b, hb⟩

Depends on / 依赖: exists_le_minimal, h.exists_le_minimal
-/
theorem IsPWO.exists_minimal (h : s.IsPWO) (hs : s.Nonempty) :
    exists a, Minimal (· in s) a := by
  rcases hs with ⟨a, ha⟩
  obtain ⟨b, _, hb⟩ := h.exists_le_minimal ha
  exact ⟨b, hb⟩

/--
theorem `IsPWO.exists_minimalFor` / 定理 `IsPWO.exists_minimalFor`

English:
theorem IsPWO.exists_minimalFor
  given: (f : ι -> α) (s : Set ι) (h : (f '' s).IsPWO) (hs : s.Nonempty)
  proof: by
  obtain ⟨_, h⟩ := h.exists_minimal (hs.image _)
  obtain ⟨a, ha, rfl⟩ := h.1
  exact ⟨a, ha, fun b hb => h.2 (mem_image_of_mem _ hb)⟩

中文:
定理 IsPWO.exists_minimalFor
  条件: (f : ι -> α) (s : Set ι) (h : (f '' s).IsPWO) (hs : s.Nonempty)
  证明: by
  obtain ⟨_, h⟩ := h.exists_minimal (hs.image _)
  obtain ⟨a, ha, rfl⟩ := h.1
  exact ⟨a, ha, fun b hb => h.2 (mem_image_of_mem _ hb)⟩

Depends on / 依赖: exists_minimal, h.exists_minimal, hs.image, mem_image_of_mem
-/
theorem IsPWO.exists_minimalFor (f : ι -> α) (s : Set ι) (h : (f '' s).IsPWO) (hs : s.Nonempty) :
    exists i, MinimalFor (· in s) f i := by
  obtain ⟨_, h⟩ := h.exists_minimal (hs.image _)
  obtain ⟨a, ha, rfl⟩ := h.1
  exact ⟨a, ha, fun b hb => h.2 (mem_image_of_mem _ hb)⟩

end IsPWO

section WellFoundedOn

variable {r : α -> α -> Prop} [IsStrictOrder α r] {s : Set α} {a : α}

/--
theorem `Finite.wellFoundedOn` / 定理 `Finite.wellFoundedOn`

English:
theorem Finite.wellFoundedOn
  given: (hs : s.Finite)
  statement: s.WellFoundedOn r
  proof: letI := partialOrderOfSO r
  hs.isWF

@[simp]

中文:
定理 Finite.wellFoundedOn
  条件: (hs : s.Finite)
  结论: s.WellFoundedOn r
  证明: letI := partialOrderOfSO r
  hs.isWF

@[simp]
-/
protected theorem Finite.wellFoundedOn (hs : s.Finite) : s.WellFoundedOn r :=
  letI := partialOrderOfSO r
  hs.isWF

@[simp]
/--
theorem `wellFoundedOn_singleton` / 定理 `wellFoundedOn_singleton`

English:
theorem wellFoundedOn_singleton
  statement: WellFoundedOn ({a} : Set α) r
  proof: (finite_singleton a).wellFoundedOn

中文:
定理 wellFoundedOn_singleton
  结论: WellFoundedOn ({a} : Set α) r
  证明: (finite_singleton a).wellFoundedOn

Depends on / 依赖: finite_singleton, wellFoundedOn
-/
theorem wellFoundedOn_singleton : WellFoundedOn ({a} : Set α) r :=
  (finite_singleton a).wellFoundedOn

/--
theorem `Subsingleton.wellFoundedOn` / 定理 `Subsingleton.wellFoundedOn`

English:
theorem Subsingleton.wellFoundedOn
  given: (hs : s.Subsingleton)
  statement: s.WellFoundedOn r
  proof: hs.finite.wellFoundedOn

@[simp]

中文:
定理 Subsingleton.wellFoundedOn
  条件: (hs : s.Subsingleton)
  结论: s.WellFoundedOn r
  证明: hs.finite.wellFoundedOn

@[simp]
-/
protected theorem Subsingleton.wellFoundedOn (hs : s.Subsingleton) : s.WellFoundedOn r :=
  hs.finite.wellFoundedOn

@[simp]
/--
theorem `wellFoundedOn_insert` / 定理 `wellFoundedOn_insert`

English:
theorem wellFoundedOn_insert
  statement: WellFoundedOn (insert a s) r ↔ WellFoundedOn s r
  proof: by
  simp only [← singleton_union, wellFoundedOn_union, wellFoundedOn_singleton, true_and]

@[simp]

中文:
定理 wellFoundedOn_insert
  结论: WellFoundedOn (insert a s) r ↔ WellFoundedOn s r
  证明: by
  simp only [← singleton_union, wellFoundedOn_union, wellFoundedOn_singleton, true_and]

@[simp]

Depends on / 依赖: singleton_union, true_and, wellFoundedOn_singleton, wellFoundedOn_union
-/
theorem wellFoundedOn_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r := by
  simp only [← singleton_union, wellFoundedOn_union, wellFoundedOn_singleton, true_and]

@[simp]
/--
theorem `wellFoundedOn_sdiff_singleton` / 定理 `wellFoundedOn_sdiff_singleton`

English:
theorem wellFoundedOn_sdiff_singleton
  statement: WellFoundedOn (s \ {a}) r ↔ WellFoundedOn s r
  proof: by
  simp only [← wellFoundedOn_insert (a := a), insert_sdiff_singleton, mem_insert_iff, true_or,
    insert_eq_of_mem]

中文:
定理 wellFoundedOn_sdiff_singleton
  结论: WellFoundedOn (s \ {a}) r ↔ WellFoundedOn s r
  证明: by
  simp only [← wellFoundedOn_insert (a := a), insert_sdiff_singleton, mem_insert_iff, true_or,
    insert_eq_of_mem]

Depends on / 依赖: insert_eq_of_mem, insert_sdiff_singleton, mem_insert_iff, true_or, wellFoundedOn_insert
-/
theorem wellFoundedOn_sdiff_singleton : WellFoundedOn (s \ {a}) r ↔ WellFoundedOn s r := by
  simp only [← wellFoundedOn_insert (a := a), insert_sdiff_singleton, mem_insert_iff, true_or,
    insert_eq_of_mem]

/--
theorem `WellFoundedOn.insert` / 定理 `WellFoundedOn.insert`

English:
theorem WellFoundedOn.insert
  given: (h : WellFoundedOn s r) (a : α)
  proof: wellFoundedOn_insert.2 h

中文:
定理 WellFoundedOn.insert
  条件: (h : WellFoundedOn s r) (a : α)
  证明: wellFoundedOn_insert.2 h
-/
protected theorem WellFoundedOn.insert (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (insert a s) r :=
  wellFoundedOn_insert.2 h

/--
theorem `WellFoundedOn.sdiff_singleton` / 定理 `WellFoundedOn.sdiff_singleton`

English:
theorem WellFoundedOn.sdiff_singleton
  given: (h : WellFoundedOn s r) (a : α)
  proof: wellFoundedOn_sdiff_singleton.2 h

中文:
定理 WellFoundedOn.sdiff_singleton
  条件: (h : WellFoundedOn s r) (a : α)
  证明: wellFoundedOn_sdiff_singleton.2 h

Depends on / 依赖: truncFinset
-/
protected theorem WellFoundedOn.sdiff_singleton (h : WellFoundedOn s r) (a : α) :
    WellFoundedOn (s \ {a}) r :=
  wellFoundedOn_sdiff_singleton.2 h

/--
lemma `WellFoundedOn.mapsTo` / 引理 `WellFoundedOn.mapsTo`

English:
lemma WellFoundedOn.mapsTo
  statement: {α β : Type*} {r : α -> α -> Prop} (f : β -> α)
  proof: by
  exact InvImage.wf (fun x : t => ⟨f x, h x.prop⟩) hw

@[to_dual]

中文:
引理 WellFoundedOn.mapsTo
  结论: {α β : 类型} {r : α -> α -> 命题} (f : β -> α)
  证明: by
  exact InvImage.wf (fun x : t => ⟨f x, h x.prop⟩) hw

@[to_dual]

Depends on / 依赖: InvImage, InvImage.wf, x.prop
-/
lemma WellFoundedOn.mapsTo {α β : Type*} {r : α -> α -> Prop} (f : β -> α)
    {s : Set α} {t : Set β} (h : MapsTo f t s) (hw : s.WellFoundedOn r) :
    t.WellFoundedOn (r on f) := by
  exact InvImage.wf (fun x : t => ⟨f x, h x.prop⟩) hw

@[to_dual]
/--
theorem `WellFoundedOn.exists_minimal` / 定理 `WellFoundedOn.exists_minimal`

English:
theorem WellFoundedOn.exists_minimal
  statement: {α : Type*} [Preorder α] {s : Set α}
  proof: have ⟨m, hm⟩ := WellFoundedLT.exists_minimal ⟨h⟩ univ nonempty.elim (⟨⟨·, ·⟩, trivial⟩)
  ⟨m, m.property, fun y hy => hm.right (y := ⟨y, hy⟩) trivial⟩

中文:
定理 WellFoundedOn.exists_minimal
  结论: {α : 类型} [Preorder α] {s : Set α}
  证明: have ⟨m, hm⟩ := WellFoundedLT.exists_minimal ⟨h⟩ univ nonempty.elim (⟨⟨·, ·⟩, trivial⟩)
  ⟨m, m.property, fun y hy => hm.right (y := ⟨y, hy⟩) trivial⟩

Depends on / 依赖: Iic_subset_Iic, Iic_subset_Iic.mpr, WellFoundedLT, WellFoundedLT.exists_minimal, exists_minimal, hm.right, m.property, nonempty, nonempty.elim, property, truncFinset_truncFinset
-/
theorem WellFoundedOn.exists_minimal {α : Type*} [Preorder α] {s : Set α}
    (h : s.WellFoundedOn (· < ·)) (nonempty : s.Nonempty) : exists a, Minimal (· in s) a :=
have ⟨m, hm⟩ := WellFoundedLT.exists_minimal ⟨h⟩ univ nonempty.elim (⟨⟨·, ·⟩, trivial⟩)
  ⟨m, m.property, fun y hy => hm.right (y := ⟨y, hy⟩) trivial⟩

end WellFoundedOn

section LinearOrder

variable [LinearOrder α] {s : Set α}

/--
theorem `isPWO_iff_isWF` / 定理 `isPWO_iff_isWF`

English:
theorem isPWO_iff_isWF
  statement: s.IsPWO ↔ s.IsWF
  proof: by
  change WellQuasiOrdered (· <= ·) ↔ WellFounded (· < ·)
  rw [← wellQuasiOrderedLE_def]; rw [← isWellFounded_iff]; rw [wellQuasiOrderedLE_iff_wellFoundedLT]

alias ⟨_, IsWF.isPWO⟩ := isPWO_iff_isWF

中文:
定理 isPWO_iff_isWF
  结论: s.IsPWO ↔ s.IsWF
  证明: by
  change WellQuasiOrdered (· <= ·) ↔ WellFounded (· < ·)
  rw [← wellQuasiOrderedLE_def]; rw [← isWellFounded_iff]; rw [wellQuasiOrderedLE_iff_wellFoundedLT]

alias ⟨_, IsWF.isPWO⟩ := isPWO_iff_isWF

Depends on / 依赖: WellFounded, WellQuasiOrdered, isWellFounded_iff, truncFinset_one, wellQuasiOrderedLE_def, wellQuasiOrderedLE_iff_wellFoundedLT
-/
theorem isPWO_iff_isWF : s.IsPWO ↔ s.IsWF := by
  change WellQuasiOrdered (· <= ·) ↔ WellFounded (· < ·)
  rw [← wellQuasiOrderedLE_def]; rw [← isWellFounded_iff]; rw [wellQuasiOrderedLE_iff_wellFoundedLT]

alias ⟨_, IsWF.isPWO⟩ := isPWO_iff_isWF

/--
lemma `IsPWO.of_linearOrder` / 引理 `IsPWO.of_linearOrder`

English:
lemma IsPWO.of_linearOrder
  given: [WellFoundedLT α] (s : Set α)
  statement: s.IsPWO
  proof: (IsWF.of_wellFoundedLT s).isPWO

中文:
引理 IsPWO.of_linearOrder
  条件: [WellFoundedLT α] (s : Set α)
  结论: s.IsPWO
  证明: (IsWF.of_wellFoundedLT s).isPWO

Depends on / 依赖: IsWF.of_wellFoundedLT, of_wellFoundedLT, truncFinset_C
-/
lemma IsPWO.of_linearOrder [WellFoundedLT α] (s : Set α) : s.IsPWO :=
  (IsWF.of_wellFoundedLT s).isPWO

end LinearOrder

end Set

namespace Finset

variable {r : α -> α -> Prop}

@[simp]
/--
theorem `partiallyWellOrderedOn` / 定理 `partiallyWellOrderedOn`

English:
theorem partiallyWellOrderedOn
  given: [Std.Refl r] (s : Finset α)
  proof: s.finite_toSet.partiallyWellOrderedOn

@[simp]

中文:
定理 partiallyWellOrderedOn
  条件: [Std.Refl r] (s : Finset α)
  证明: s.finite_toSet.partiallyWellOrderedOn

@[simp]

Depends on / 依赖: IsLowerSet
-/
protected theorem partiallyWellOrderedOn [Std.Refl r] (s : Finset α) :
    (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_toSet.partiallyWellOrderedOn

@[simp]
/--
theorem `isPWO` / 定理 `isPWO`

English:
theorem isPWO
  given: [Preorder α] (s : Finset α)
  statement: Set.IsPWO (↑s : Set α)
  proof: s.partiallyWellOrderedOn

@[simp]

中文:
定理 isPWO
  条件: [Preorder α] (s : Finset α)
  结论: Set.IsPWO (↑s : Set α)
  证明: s.partiallyWellOrderedOn

@[simp]

Depends on / 依赖: _mul_trunc, coeff_trunc
-/
protected theorem isPWO [Preorder α] (s : Finset α) : Set.IsPWO (↑s : Set α) :=
  s.partiallyWellOrderedOn

@[simp]
/--
theorem `isWF` / 定理 `isWF`

English:
theorem isWF
  given: [Preorder α] (s : Finset α)
  statement: Set.IsWF (↑s : Set α)
  proof: s.finite_toSet.isWF

@[simp]

中文:
定理 isWF
  条件: [Preorder α] (s : Finset α)
  结论: Set.IsWF (↑s : Set α)
  证明: s.finite_toSet.isWF

@[simp]
-/
protected theorem isWF [Preorder α] (s : Finset α) : Set.IsWF (↑s : Set α) :=
  s.finite_toSet.isWF

@[simp]
/--
theorem `wellFoundedOn` / 定理 `wellFoundedOn`

English:
theorem wellFoundedOn
  given: [IsStrictOrder α r] (s : Finset α)
  proof: letI := partialOrderOfSO r
  s.isWF

中文:
定理 wellFoundedOn
  条件: [IsStrictOrder α r] (s : Finset α)
  证明: letI := partialOrderOfSO r
  s.isWF

Depends on / 依赖: truncFinset_truncFinset_pow
-/
protected theorem wellFoundedOn [IsStrictOrder α r] (s : Finset α) :
    Set.WellFoundedOn (↑s : Set α) r :=
  letI := partialOrderOfSO r
  s.isWF

/--
theorem `wellFoundedOn_sup` / 定理 `wellFoundedOn_sup`

English:
theorem wellFoundedOn_sup
  given: [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α}
  proof: Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

中文:
定理 wellFoundedOn_sup
  条件: [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α}
  证明: Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

Depends on / 依赖: Finset, Finset.cons_induction_on, coeff_trunc, cons_induction_on, sup_set_eq_biUnion
-/
theorem wellFoundedOn_sup [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α} :
    (s.sup f).WellFoundedOn r ↔ forall i in s, (f i).WellFoundedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

/--
theorem `partiallyWellOrderedOn_sup` / 定理 `partiallyWellOrderedOn_sup`

English:
theorem partiallyWellOrderedOn_sup
  given: (s : Finset ι) {f : ι -> Set α}
  proof: Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

中文:
定理 partiallyWellOrderedOn_sup
  条件: (s : Finset ι) {f : ι -> Set α}
  证明: Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

Depends on / 依赖: Finset, Finset.cons_induction_on, cons_induction_on, sup_set_eq_biUnion, truncFinset_map
-/
theorem partiallyWellOrderedOn_sup (s : Finset ι) {f : ι -> Set α} :
    (s.sup f).PartiallyWellOrderedOn r ↔ forall i in s, (f i).PartiallyWellOrderedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_biUnion, hs]

/--
theorem `isWF_sup` / 定理 `isWF_sup`

English:
theorem isWF_sup
  given: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  proof: s.wellFoundedOn_sup

中文:
定理 isWF_sup
  条件: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  证明: s.wellFoundedOn_sup

Depends on / 依赖: s.wellFoundedOn_sup, wellFoundedOn_sup
-/
theorem isWF_sup [Preorder α] (s : Finset ι) {f : ι -> Set α} :
    (s.sup f).IsWF ↔ forall i in s, (f i).IsWF :=
  s.wellFoundedOn_sup

/--
theorem `isPWO_sup` / 定理 `isPWO_sup`

English:
theorem isPWO_sup
  given: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  proof: s.partiallyWellOrderedOn_sup

@[simp]

中文:
定理 isPWO_sup
  条件: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  证明: s.partiallyWellOrderedOn_sup

@[simp]

Depends on / 依赖: partiallyWellOrderedOn_sup, s.partiallyWellOrderedOn_sup
-/
theorem isPWO_sup [Preorder α] (s : Finset ι) {f : ι -> Set α} :
    (s.sup f).IsPWO ↔ forall i in s, (f i).IsPWO :=
  s.partiallyWellOrderedOn_sup

@[simp]
/--
theorem `wellFoundedOn_bUnion` / 定理 `wellFoundedOn_bUnion`

English:
theorem wellFoundedOn_bUnion
  given: [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α}
  proof: by
  simpa only [Finset.sup_eq_iSup] using! s.wellFoundedOn_sup

@[simp]

中文:
定理 wellFoundedOn_bUnion
  条件: [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α}
  证明: by
  simpa only [Finset.sup_eq_iSup] using! s.wellFoundedOn_sup

@[simp]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, s.wellFoundedOn_sup, sup_eq_iSup, wellFoundedOn_sup
-/
theorem wellFoundedOn_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι -> Set α} :
    (⋃ i in s, f i).WellFoundedOn r ↔ forall i in s, (f i).WellFoundedOn r := by
  simpa only [Finset.sup_eq_iSup] using! s.wellFoundedOn_sup

@[simp]
/--
theorem `partiallyWellOrderedOn_bUnion` / 定理 `partiallyWellOrderedOn_bUnion`

English:
theorem partiallyWellOrderedOn_bUnion
  given: (s : Finset ι) {f : ι -> Set α}
  proof: by
  simpa only [Finset.sup_eq_iSup] using! s.partiallyWellOrderedOn_sup

@[simp]

中文:
定理 partiallyWellOrderedOn_bUnion
  条件: (s : Finset ι) {f : ι -> Set α}
  证明: by
  simpa only [Finset.sup_eq_iSup] using! s.partiallyWellOrderedOn_sup

@[simp]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, partiallyWellOrderedOn_sup, s.partiallyWellOrderedOn_sup, sup_eq_iSup
-/
theorem partiallyWellOrderedOn_bUnion (s : Finset ι) {f : ι -> Set α} :
    (⋃ i in s, f i).PartiallyWellOrderedOn r ↔ forall i in s, (f i).PartiallyWellOrderedOn r := by
  simpa only [Finset.sup_eq_iSup] using! s.partiallyWellOrderedOn_sup

@[simp]
/--
theorem `isWF_bUnion` / 定理 `isWF_bUnion`

English:
theorem isWF_bUnion
  given: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  proof: s.wellFoundedOn_bUnion

@[simp]

中文:
定理 isWF_bUnion
  条件: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  证明: s.wellFoundedOn_bUnion

@[simp]

Depends on / 依赖: s.wellFoundedOn_bUnion, wellFoundedOn_bUnion
-/
theorem isWF_bUnion [Preorder α] (s : Finset ι) {f : ι -> Set α} :
    (⋃ i in s, f i).IsWF ↔ forall i in s, (f i).IsWF :=
  s.wellFoundedOn_bUnion

@[simp]
/--
theorem `isPWO_bUnion` / 定理 `isPWO_bUnion`

English:
theorem isPWO_bUnion
  given: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  proof: s.partiallyWellOrderedOn_bUnion

中文:
定理 isPWO_bUnion
  条件: [Preorder α] (s : Finset ι) {f : ι -> Set α}
  证明: s.partiallyWellOrderedOn_bUnion

Depends on / 依赖: partiallyWellOrderedOn_bUnion, s.partiallyWellOrderedOn_bUnion
-/
theorem isPWO_bUnion [Preorder α] (s : Finset ι) {f : ι -> Set α} :
    (⋃ i in s, f i).IsPWO ↔ forall i in s, (f i).IsPWO :=
  s.partiallyWellOrderedOn_bUnion

end Finset

namespace Set

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

/-- `Set.IsWF.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable nonrec def IsWF.min (hs : IsWF s) (hn : s.Nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

/--
theorem `IsWF.min_mem` / 定理 `IsWF.min_mem`

English:
theorem IsWF.min_mem
  given: (hs : IsWF s) (hn : s.Nonempty)
  statement: hs.min hn in s
  proof: (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

nonrec theorem IsWF.not_lt_min (hs : IsWF s) (hn : s.Nonempty) (ha : a in s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (mem_univ (⟨a, ha⟩ : s))

中文:
定理 IsWF.min_mem
  条件: (hs : IsWF s) (hn : s.Nonempty)
  结论: hs.min hn in s
  证明: (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

nonrec theorem IsWF.not_lt_min (hs : IsWF s) (hn : s.Nonempty) (ha : a in s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (mem_univ (⟨a, ha⟩ : s))

Depends on / 依赖: WellFounded, WellFounded.min, hn.to_subtype, nonempty_iff_univ_nonempty, to_subtype
-/
theorem IsWF.min_mem (hs : IsWF s) (hn : s.Nonempty) : hs.min hn in s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

nonrec theorem IsWF.not_lt_min (hs : IsWF s) (hn : s.Nonempty) (ha : a in s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (mem_univ (⟨a, ha⟩ : s))

/--
theorem `IsWF.min_of_subset_not_lt_min` / 定理 `IsWF.min_of_subset_not_lt_min`

English:
theorem IsWF.min_of_subset_not_lt_min
  statement: {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF}
  proof: ht.not_lt_min htn (hst (min_mem hs hsn))

@[simp]

中文:
定理 IsWF.min_of_subset_not_lt_min
  结论: {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF}
  证明: ht.not_lt_min htn (hst (min_mem hs hsn))

@[simp]

Depends on / 依赖: ht.not_lt_min, min_mem, not_lt_min
-/
theorem IsWF.min_of_subset_not_lt_min {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF}
    {htn : t.Nonempty} (hst : s subseteq t) : ¬hs.min hsn < ht.min htn :=
  ht.not_lt_min htn (hst (min_mem hs hsn))

@[simp]
/--
theorem `isWF_min_singleton` / 定理 `isWF_min_singleton`

English:
theorem isWF_min_singleton
  given: (a) {hs : IsWF ({a} : Set α)} {hn : ({a} : Set α).Nonempty}
  proof: eq_of_mem_singleton (IsWF.min_mem hs hn)

中文:
定理 isWF_min_singleton
  条件: (a) {hs : IsWF ({a} : Set α)} {hn : ({a} : Set α).Nonempty}
  证明: eq_of_mem_singleton (IsWF.min_mem hs hn)

Depends on / 依赖: IsWF.min_mem, eq_of_mem_singleton, min_mem
-/
theorem isWF_min_singleton (a) {hs : IsWF ({a} : Set α)} {hn : ({a} : Set α).Nonempty} :
    hs.min hn = a :=
  eq_of_mem_singleton (IsWF.min_mem hs hn)

/--
theorem `IsWF.min_eq_of_lt` / 定理 `IsWF.min_eq_of_lt`

English:
theorem IsWF.min_eq_of_lt
  given: (hs : s.IsWF) (ha : a in s) (hlt : forall b in s, b != a -> a < b)
  proof: by
  by_contra h
  exact (hs.not_lt_min (nonempty_of_mem ha) ha) (hlt (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha)) h)

中文:
定理 IsWF.min_eq_of_lt
  条件: (hs : s.IsWF) (ha : a in s) (hlt : 对任意 b in s, b != a -> a < b)
  证明: by
  by_contra h
  exact (hs.not_lt_min (nonempty_of_mem ha) ha) (hlt (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha)) h)

Depends on / 依赖: hs.min, hs.min_mem, hs.not_lt_min, min_mem, nonempty_of_mem, not_lt_min
-/
theorem IsWF.min_eq_of_lt (hs : s.IsWF) (ha : a in s) (hlt : forall b in s, b != a -> a < b) :
    hs.min (nonempty_of_mem ha) = a := by
  by_contra h
  exact (hs.not_lt_min (nonempty_of_mem ha) ha) (hlt (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha)) h)

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a : α}

/--
theorem `IsWF.min_eq_of_le` / 定理 `IsWF.min_eq_of_le`

English:
theorem IsWF.min_eq_of_le
  given: (hs : s.IsWF) (ha : a in s) (hle : forall b in s, a <= b)
  proof: (eq_of_le_of_not_lt (hle (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha))) (hs.not_lt_min (nonempty_of_mem ha) ha)).symm

中文:
定理 IsWF.min_eq_of_le
  条件: (hs : s.IsWF) (ha : a in s) (hle : 对任意 b in s, a <= b)
  证明: (eq_of_le_of_not_lt (hle (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha))) (hs.not_lt_min (nonempty_of_mem ha) ha)).symm

Depends on / 依赖: eq_of_le_of_not_lt, hs.min, hs.min_mem, hs.not_lt_min, min_mem, nonempty_of_mem, not_lt_min
-/
theorem IsWF.min_eq_of_le (hs : s.IsWF) (ha : a in s) (hle : forall b in s, a <= b) :
    hs.min (nonempty_of_mem ha) = a :=
  (eq_of_le_of_not_lt (hle (hs.min (nonempty_of_mem ha))
    (hs.min_mem (nonempty_of_mem ha))) (hs.not_lt_min (nonempty_of_mem ha) ha)).symm

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α} {a : α}

/--
theorem `IsWF.min_le` / 定理 `IsWF.min_le`

English:
theorem IsWF.min_le
  given: (hs : s.IsWF) (hn : s.Nonempty) (ha : a in s)
  statement: hs.min hn <= a
  proof: le_of_not_gt (hs.not_lt_min hn ha)

中文:
定理 IsWF.min_le
  条件: (hs : s.IsWF) (hn : s.Nonempty) (ha : a in s)
  结论: hs.min hn <= a
  证明: le_of_not_gt (hs.not_lt_min hn ha)

Depends on / 依赖: hs.not_lt_min, le_of_not_gt, not_lt_min
-/
theorem IsWF.min_le (hs : s.IsWF) (hn : s.Nonempty) (ha : a in s) : hs.min hn <= a :=
  le_of_not_gt (hs.not_lt_min hn ha)

/--
theorem `IsWF.le_min_iff` / 定理 `IsWF.le_min_iff`

English:
theorem IsWF.le_min_iff
  given: (hs : s.IsWF) (hn : s.Nonempty)
  statement: a <= hs.min hn ↔ forall b, b in s -> a <= b
  proof: ⟨fun ha _b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

中文:
定理 IsWF.le_min_iff
  条件: (hs : s.IsWF) (hn : s.Nonempty)
  结论: a <= hs.min hn ↔ 对任意 b, b in s -> a <= b
  证明: ⟨fun ha _b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

Depends on / 依赖: hs.min_le, hs.min_mem, le_trans, min_le, min_mem
-/
theorem IsWF.le_min_iff (hs : s.IsWF) (hn : s.Nonempty) : a <= hs.min hn ↔ forall b, b in s -> a <= b :=
  ⟨fun ha _b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

/--
theorem `IsWF.min_le_min_of_subset` / 定理 `IsWF.min_le_min_of_subset`

English:
theorem IsWF.min_le_min_of_subset
  statement: {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}
  proof: (IsWF.le_min_iff _ _).2 fun _b hb => ht.min_le htn (hst hb)

中文:
定理 IsWF.min_le_min_of_subset
  结论: {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}
  证明: (IsWF.le_min_iff _ _).2 fun _b hb => ht.min_le htn (hst hb)

Depends on / 依赖: IsWF.le_min_iff, ht.min_le, le_min_iff, min_le
-/
theorem IsWF.min_le_min_of_subset {hs : s.IsWF} {hsn : s.Nonempty} {ht : t.IsWF} {htn : t.Nonempty}
    (hst : s subseteq t) : ht.min htn <= hs.min hsn :=
  (IsWF.le_min_iff _ _).2 fun _b hb => ht.min_le htn (hst hb)

/--
theorem `IsWF.min_union` / 定理 `IsWF.min_union`

English:
theorem IsWF.min_union
  given: (hs : s.IsWF) (hsn : s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty)
  proof: by
  refine le_antisymm (le_min (IsWF.min_le_min_of_subset subset_union_left)
    (IsWF.min_le_min_of_subset subset_union_right)) ?_
  rw [min_le_iff]
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (.inl hsn)))).imp
    (hs.min_le _) (ht.min_le _)

中文:
定理 IsWF.min_union
  条件: (hs : s.IsWF) (hsn : s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty)
  证明: by
  refine le_antisymm (le_min (IsWF.min_le_min_of_subset subset_union_left)
    (IsWF.min_le_min_of_subset subset_union_right)) ?_
  rw [min_le_iff]
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (.inl hsn)))).imp
    (hs.min_le _) (ht.min_le _)

Depends on / 依赖: IsWF.min_le_min_of_subset, hs.min_le, hs.union, ht.min_le, le_antisymm, le_min, mem_union, min_le, min_le_iff, min_le_min_of_subset, min_mem, subset_union_left, subset_union_right, union_nonempty
-/
theorem IsWF.min_union (hs : s.IsWF) (hsn : s.Nonempty) (ht : t.IsWF) (htn : t.Nonempty) :
    (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) =
      Min.min (hs.min hsn) (ht.min htn) := by
  refine le_antisymm (le_min (IsWF.min_le_min_of_subset subset_union_left)
    (IsWF.min_le_min_of_subset subset_union_right)) ?_
  rw [min_le_iff]
  exact ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (.inl hsn)))).imp
    (hs.min_le _) (ht.min_le _)

end LinearOrder

end Set

open Set

section LocallyFiniteOrder

variable {s : Set α} [Preorder α] [LocallyFiniteOrder α]

/--
theorem `BddBelow.wellFoundedOn_lt` / 定理 `BddBelow.wellFoundedOn_lt`

English:
theorem BddBelow.wellFoundedOn_lt
  statement: BddBelow s -> s.WellFoundedOn (· < ·)
  proof: by
  rw [wellFoundedOn_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf
  refine infinite_range_of_injective f.injective ?_
exact (finite_Icc a <| f 0).subset range_subset_iff.2 fun n =>
⟨ha hf _,
antitone_iff_forall_lt.2 (fun a b hab => (f.map_rel_iff.2 hab).le) Nat.zero_le _⟩

中文:
定理 BddBelow.wellFoundedOn_lt
  结论: BddBelow s -> s.WellFoundedOn (· < ·)
  证明: by
  rw [wellFoundedOn_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf
  refine infinite_range_of_injective f.injective ?_
exact (finite_Icc a <| f 0).subset range_subset_iff.2 fun n =>
⟨ha hf _,
antitone_iff_forall_lt.2 (fun a b hab => (f.map_rel_iff.2 hab).le) Nat.zero_le _⟩

Depends on / 依赖: Nat.zero_le, antitone_iff_forall_lt, f.injective, f.map_rel_iff, finite_Icc, infinite_range_of_injective, injective, map_rel_iff, range_subset_iff, subset, wellFoundedOn_iff_no_descending_seq, zero_le
-/
theorem BddBelow.wellFoundedOn_lt : BddBelow s -> s.WellFoundedOn (· < ·) := by
  rw [wellFoundedOn_iff_no_descending_seq]
  rintro ⟨a, ha⟩ f hf
  refine infinite_range_of_injective f.injective ?_
exact (finite_Icc a <| f 0).subset range_subset_iff.2 fun n =>
⟨ha hf _,
antitone_iff_forall_lt.2 (fun a b hab => (f.map_rel_iff.2 hab).le) Nat.zero_le _⟩

/--
theorem `BddAbove.wellFoundedOn_gt` / 定理 `BddAbove.wellFoundedOn_gt`

English:
theorem BddAbove.wellFoundedOn_gt
  statement: BddAbove s -> s.WellFoundedOn (· > ·)
  proof: fun h => h.dual.wellFoundedOn_lt

中文:
定理 BddAbove.wellFoundedOn_gt
  结论: BddAbove s -> s.WellFoundedOn (· > ·)
  证明: fun h => h.dual.wellFoundedOn_lt

Depends on / 依赖: h.dual.wellFoundedOn_lt, wellFoundedOn_lt
-/
theorem BddAbove.wellFoundedOn_gt : BddAbove s -> s.WellFoundedOn (· > ·) :=
  fun h => h.dual.wellFoundedOn_lt

/--
theorem `BddBelow.isWF` / 定理 `BddBelow.isWF`

English:
theorem BddBelow.isWF
  statement: BddBelow s -> IsWF s
  proof: BddBelow.wellFoundedOn_lt

中文:
定理 BddBelow.isWF
  结论: BddBelow s -> IsWF s
  证明: BddBelow.wellFoundedOn_lt

Depends on / 依赖: BddBelow, BddBelow.wellFoundedOn_lt, wellFoundedOn_lt
-/
theorem BddBelow.isWF : BddBelow s -> IsWF s :=
  BddBelow.wellFoundedOn_lt

end LocallyFiniteOrder

namespace Set.PartiallyWellOrderedOn

variable {r : α -> α -> Prop}

/--
theorem `bddAbove_preimage` / 定理 `bddAbove_preimage`

English:
theorem bddAbove_preimage
  statement: {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α}
  proof: by
  contrapose! hf
  rw [not_bddAbove_iff] at hf
  obtain ⟨φ, hφm, hφs⟩ := Nat.exists_strictMono_subsequence
    fun n => (hf n).casesOn fun m h => h.casesOn fun hs hmn => Exists.intro m ⟨hmn, hs⟩
  rw [partiallyWellOrderedOn_iff_exists_lt] at hs
  obtain ⟨m, n, hmn, hr⟩ := hs (fun n => f (φ n)) hφ

中文:
定理 bddAbove_preimage
  结论: {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : 自然数 -> α}
  证明: by
  contrapose! hf
  rw [not_bddAbove_iff] at hf
  obtain ⟨φ, hφm, hφs⟩ := Nat.exists_strictMono_subsequence
    fun n => (hf n).casesOn fun m h => h.casesOn fun hs hmn => Exists.intro m ⟨hmn, hs⟩
  rw [partiallyWellOrderedOn_iff_exists_lt] at hs
  obtain ⟨m, n, hmn, hr⟩ := hs (fun n => f (φ n)) hφ

Depends on / 依赖: Exists, Exists.intro, Nat.exists_strictMono_subsequence, casesOn, contrapose, exists_strictMono_subsequence, h.casesOn, not_bddAbove_iff, partiallyWellOrderedOn_iff_exists_lt
-/
theorem bddAbove_preimage {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α}
    (hf : forall m n : Nat, m < n -> ¬ r (f m) (f n)) :
    BddAbove (s.preimage f) := by
  contrapose! hf
  rw [not_bddAbove_iff] at hf
  obtain ⟨φ, hφm, hφs⟩ := Nat.exists_strictMono_subsequence
    fun n => (hf n).casesOn fun m h => h.casesOn fun hs hmn => Exists.intro m ⟨hmn, hs⟩
  rw [partiallyWellOrderedOn_iff_exists_lt] at hs
  obtain ⟨m, n, hmn, hr⟩ := hs (fun n => f (φ n)) hφs
  use (φ m), (φ n)
  exact ⟨hφm hmn, hr⟩

/--
theorem `exists_notMem_of_gt` / 定理 `exists_notMem_of_gt`

English:
theorem exists_notMem_of_gt
  statement: {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α}
  proof: by
  have := hs.bddAbove_preimage hf
  contrapose! this
  simpa [not_bddAbove_iff, and_comm]

中文:
定理 exists_notMem_of_gt
  结论: {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : 自然数 -> α}
  证明: by
  have := hs.bddAbove_preimage hf
  contrapose! this
  simpa [not_bddAbove_iff, and_comm]

Depends on / 依赖: and_comm, bddAbove_preimage, contrapose, hs.bddAbove_preimage, not_bddAbove_iff
-/
theorem exists_notMem_of_gt {s : Set α} (hs : s.PartiallyWellOrderedOn r) {f : Nat -> α}
    (hf : forall m n : Nat, m < n -> ¬ r (f m) (f n)) :
    exists k : Nat, forall m, k < m -> f m ∉ s := by
  have := hs.bddAbove_preimage hf
  contrapose! this
  simpa [not_bddAbove_iff, and_comm]

-- TODO: move this material to the main file on WQOs.

/--
Definition of `IsBadSeq` / `IsBadSeq` 的定义

English:
definition IsBadSeq
  signature: (r : α -> α -> Prop) (s : Set α) (f : Nat -> α)
  body: (forall n, f n in s) ∧ forall m n : Nat, m < n -> ¬r (f m) (f n)

中文:
定义 IsBadSeq
  签名: (r : α -> α -> 命题) (s : Set α) (f : 自然数 -> α)
  定义体: (forall n, f n in s) ∧ forall m n : Nat, m < n -> ¬r (f m) (f n)
-/
def IsBadSeq (r : α -> α -> Prop) (s : Set α) (f : Nat -> α) : Prop :=
  (forall n, f n in s) ∧ forall m n : Nat, m < n -> ¬r (f m) (f n)

/--
theorem `iff_forall_not_isBadSeq` / 定理 `iff_forall_not_isBadSeq`

English:
theorem iff_forall_not_isBadSeq
  given: (r : α -> α -> Prop) (s : Set α)
  proof: by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  exact forall_congr' fun f => by simp [IsBadSeq]

中文:
定理 iff_forall_not_isBadSeq
  条件: (r : α -> α -> 命题) (s : Set α)
  证明: by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  exact forall_congr' fun f => by simp [IsBadSeq]

Depends on / 依赖: IsBadSeq, forall_congr, partiallyWellOrderedOn_iff_exists_lt
-/
theorem iff_forall_not_isBadSeq (r : α -> α -> Prop) (s : Set α) :
    s.PartiallyWellOrderedOn r ↔ forall f, ¬IsBadSeq r s f := by
  rw [partiallyWellOrderedOn_iff_exists_lt]
  exact forall_congr' fun f => by simp [IsBadSeq]

/--
Definition of `IsMinBadSeq` / `IsMinBadSeq` 的定义

English:
definition IsMinBadSeq
  signature: (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) (n : Nat) (f : Nat -> α)
  body: forall g : Nat -> α, (forall m : Nat, m < n -> f m = g m) -> rk (g n) < rk (f n) -> ¬IsBadSeq r s g

中文:
定义 IsMinBadSeq
  签名: (r : α -> α -> 命题) (rk : α -> 自然数) (s : Set α) (n : 自然数) (f : 自然数 -> α)
  定义体: forall g : Nat -> α, (forall m : Nat, m < n -> f m = g m) -> rk (g n) < rk (f n) -> ¬IsBadSeq r s g

Depends on / 依赖: IsBadSeq
-/
def IsMinBadSeq (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) (n : Nat) (f : Nat -> α) : Prop :=
  forall g : Nat -> α, (forall m : Nat, m < n -> f m = g m) -> rk (g n) < rk (f n) -> ¬IsBadSeq r s g

/--
Definition of `minBadSeqOfBadSeq` / `minBadSeqOfBadSeq` 的定义

English:
definition minBadSeqOfBadSeq
  signature: (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) (n : Nat) (f : Nat -> α)
  body: by
  classical
    have h : exists (k : Nat) (g : Nat -> α), (forall m, m < n -> f m = g m) ∧ IsBadSeq r s g ∧ rk (g n) = k :=
      ⟨_, f, fun _ _ => rfl, hf, rfl⟩
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Nat.find_spec h)
    refine ⟨Classical.choose (Nat.find_spec h), h1, by convert! h2, 

中文:
定义 minBadSeqOfBadSeq
  签名: (r : α -> α -> 命题) (rk : α -> 自然数) (s : Set α) (n : 自然数) (f : 自然数 -> α)
  定义体: by
  classical
    have h : exists (k : Nat) (g : Nat -> α), (forall m, m < n -> f m = g m) ∧ IsBadSeq r s g ∧ rk (g n) = k :=
      ⟨_, f, fun _ _ => rfl, hf, rfl⟩
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Nat.find_spec h)
    refine ⟨Classical.choose (Nat.find_spec h), h1, by convert! h2, 

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, IsBadSeq, Nat.find_min, Nat.find_spec, choose_spec, classical, convert, find_min, find_spec
-/
noncomputable def minBadSeqOfBadSeq (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) (n : Nat) (f : Nat -> α)
    (hf : IsBadSeq r s f) :
    { g : Nat -> α // (forall m : Nat, m < n -> f m = g m) ∧ IsBadSeq r s g ∧ IsMinBadSeq r rk s n g } := by
  classical
    have h : exists (k : Nat) (g : Nat -> α), (forall m, m < n -> f m = g m) ∧ IsBadSeq r s g ∧ rk (g n) = k :=
      ⟨_, f, fun _ _ => rfl, hf, rfl⟩
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Nat.find_spec h)
    refine ⟨Classical.choose (Nat.find_spec h), h1, by convert! h2, fun g hg1 hg2 con => ?_⟩
    refine Nat.find_min h ?_ ⟨g, fun m mn => (h1 m mn).trans (hg1 m mn), con, rfl⟩
    rwa [← h3]

/--
theorem `exists_min_bad_of_exists_bad` / 定理 `exists_min_bad_of_exists_bad`

English:
theorem exists_min_bad_of_exists_bad
  given: (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α)
  proof: by
  rintro ⟨f0, hf0 : IsBadSeq r s f0⟩
  let fs : forall n : Nat, { f : Nat -> α // IsBadSeq r s f ∧ IsMinBadSeq r rk s n f } := by
    refine Nat.rec ?_ fun n fn => ?_
    · exact ⟨(minBadSeqOfBadSeq r rk s 0 f0 hf0).1, (minBadSeqOfBadSeq r rk s 0 f0 hf0).2.2⟩
    · exact ⟨(minBadSeqOfBadSeq r rk 

中文:
定理 exists_min_bad_of_exists_bad
  条件: (r : α -> α -> 命题) (rk : α -> 自然数) (s : Set α)
  证明: by
  rintro ⟨f0, hf0 : IsBadSeq r s f0⟩
  let fs : forall n : Nat, { f : Nat -> α // IsBadSeq r s f ∧ IsMinBadSeq r rk s n f } := by
    refine Nat.rec ?_ fun n fn => ?_
    · exact ⟨(minBadSeqOfBadSeq r rk s 0 f0 hf0).1, (minBadSeqOfBadSeq r rk s 0 f0 hf0).2.2⟩
    · exact ⟨(minBadSeqOfBadSeq r rk 

Depends on / 依赖: IsBadSeq, IsMinBadSeq, Nat.exists_eq_add_of_le, Nat.rec, exists_eq_add_of_le, inducti, minBadSeqOfBadSeq
-/
theorem exists_min_bad_of_exists_bad (r : α -> α -> Prop) (rk : α -> Nat) (s : Set α) :
    (exists f, IsBadSeq r s f) -> exists f, IsBadSeq r s f ∧ forall n, IsMinBadSeq r rk s n f := by
  rintro ⟨f0, hf0 : IsBadSeq r s f0⟩
  let fs : forall n : Nat, { f : Nat -> α // IsBadSeq r s f ∧ IsMinBadSeq r rk s n f } := by
    refine Nat.rec ?_ fun n fn => ?_
    · exact ⟨(minBadSeqOfBadSeq r rk s 0 f0 hf0).1, (minBadSeqOfBadSeq r rk s 0 f0 hf0).2.2⟩
    · exact ⟨(minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).1,
        (minBadSeqOfBadSeq r rk s (n + 1) fn.1 fn.2.1).2.2⟩
  have h : forall m n, m <= n -> (fs m).1 m = (fs n).1 m := fun m n mn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le mn; clear mn
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [ih]; rw [(minBadSeqOfBadSeq r rk s (m + k + 1) (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (Nat.lt_succ_iff.2 (Nat.add_le_add_left k.zero_le m))]
      rfl
  refine ⟨fun n => (fs n).1 n, ⟨fun n => (fs n).2.1.1 n, fun m n mn => ?_⟩, fun n g hg1 hg2 => ?_⟩
  · dsimp
    rw [h m n mn.le]
    exact (fs n).2.1.2 m n mn
  · refine (fs n).2.2 g (fun m mn => ?_) hg2
    rw [← h m n mn.le]; rw [← hg1 m mn]

/--
theorem `iff_not_exists_isMinBadSeq` / 定理 `iff_not_exists_isMinBadSeq`

English:
theorem iff_not_exists_isMinBadSeq
  given: (rk : α -> Nat) {s : Set α}
  proof: by
  rw [iff_forall_not_isBadSeq]; rw [← not_exists]; rw [not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
  · rintro ⟨f, hf1, -⟩
    exact ⟨f, hf1⟩

中文:
定理 iff_not_exists_isMinBadSeq
  条件: (rk : α -> 自然数) {s : Set α}
  证明: by
  rw [iff_forall_not_isBadSeq]; rw [← not_exists]; rw [not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
  · rintro ⟨f, hf1, -⟩
    exact ⟨f, hf1⟩

Depends on / 依赖: exists_min_bad_of_exists_bad, iff_forall_not_isBadSeq, not_congr, not_exists
-/
theorem iff_not_exists_isMinBadSeq (rk : α -> Nat) {s : Set α} :
    s.PartiallyWellOrderedOn r ↔ ¬exists f, IsBadSeq r s f ∧ forall n, IsMinBadSeq r rk s n f := by
  rw [iff_forall_not_isBadSeq]; rw [← not_exists]; rw [not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
  · rintro ⟨f, hf1, -⟩
    exact ⟨f, hf1⟩

/--
theorem `partiallyWellOrderedOn_sublistForall₂` / 定理 `partiallyWellOrderedOn_sublistForall₂`

English:
theorem partiallyWellOrderedOn_sublistForall₂
  statement: (r : α -> α -> Prop) [IsPreorder α r]
  proof: by
  rcases isEmpty_or_nonempty α
  · exact subsingleton_of_subsingleton.partiallyWellOrderedOn
  inhabit α
  rw [iff_not_exists_isMinBadSeq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : forall n, f n != List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.n

中文:
定理 partiallyWellOrderedOn_sublistForall₂
  结论: (r : α -> α -> 命题) [IsPreorder α r]
  证明: by
  rcases isEmpty_or_nonempty α
  · exact subsingleton_of_subsingleton.partiallyWellOrderedOn
  inhabit α
  rw [iff_not_exists_isMinBadSeq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : forall n, f n != List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.n

Depends on / 依赖: List.SublistForall, List.head, List.length, List.nil, List.tail, _mem_self, con.symm, exists_monotone_subseq, h.exists_monotone_subseq, if_pos, iff_not_exists_isMinBadSeq, inhabit, isEmpty_or_nonempty, length, lt_succ_self, n.lt_succ_self, n.succ, partiallyWellOrderedOn, subsingleton_of_subsingleton, subsingleton_of_subsingleton.partiallyWellOrderedOn
-/
theorem partiallyWellOrderedOn_sublistForall₂ (r : α -> α -> Prop) [IsPreorder α r]
    {s : Set α} (h : s.PartiallyWellOrderedOn r) :
    { l : List α | forall x, x in l -> x in s }.PartiallyWellOrderedOn (List.SublistForall₂ r) := by
  rcases isEmpty_or_nonempty α
  · exact subsingleton_of_subsingleton.partiallyWellOrderedOn
  inhabit α
  rw [iff_not_exists_isMinBadSeq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : forall n, f n != List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.nil)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq fun n => hf1.1 n _ (List.head!_mem_self (hnil n))
  have hf' :=
    hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0))))
      (fun m hm => (if_pos hm).symm) ?_
  swap
  · simp only [if_neg (lt_irrefl (g 0)), Nat.sub_self]
    rw [List.length_tail]; rw [← Nat.pred_eq_sub_one]
    exact Nat.pred_lt fun con => hnil _ (List.length_eq_zero_iff.1 con)
  rw [IsBadSeq] at hf'
  push Not at hf'
  obtain ⟨m, n, mn, hmn⟩ := hf' fun n x hx => by
    split_ifs at hx with hn
    exacts [hf1.1 _ _ hx, hf1.1 _ _ (List.tail_subset _ hx)]
  by_cases hn : n < g 0
  · apply hf1.2 m n mn
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
    rw [if_neg hn]; rw [add_comm (g 0) n']; rw [Nat.add_sub_cancel_right] at hmn
    split_ifs at hmn with hm
    · apply hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le))
      exact _root_.trans hmn (List.tail_sublistForall₂_self _)
    · rw [← Nat.sub_lt_iff_lt_add' (le_of_not_gt hm)] at mn
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      rw [← List.cons_head!_tail (hnil (g (m - g 0)))]; rw [← List.cons_head!_tail (hnil (g n'))]
      exact List.SublistForall₂.cons (hg _ _ (le_of_lt mn)) hmn

/--
theorem `subsetProdLex` / 定理 `subsetProdLex`

English:
theorem subsetProdLex
  statement: [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
  proof: by
  rw [IsPWO]; rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  rw [isPWO_iff_exists_monotone_subseq] at hα
  obtain ⟨g, hg⟩ : exists (g : (Nat ↪o Nat)), Monotone fun n => (ofLex f (g n)).1 :=
    hα (fun n => (ofLex f n).1) (fun k => mem_image_of_mem (fun x => (ofLex x).1) (hf k))
  have 

中文:
定理 subsetProdLex
  结论: [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
  证明: by
  rw [IsPWO]; rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  rw [isPWO_iff_exists_monotone_subseq] at hα
  obtain ⟨g, hg⟩ : exists (g : (Nat ↪o Nat)), Monotone fun n => (ofLex f (g n)).1 :=
    hα (fun n => (ofLex f n).1) (fun k => mem_image_of_mem (fun x => (ofLex x).1) (hf k))
  have 

Depends on / 依赖: Monotone, isPWO_iff_exists_monotone_subseq, mem_image_of_mem, n.zero_le, partiallyWellOrderedOn_iff_exists_lt, zero_le
-/
theorem subsetProdLex [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hα : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO)
    (hβ : forall a, {y | toLex (a, y) in s}.IsPWO) : s.IsPWO := by
  rw [IsPWO]; rw [partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  rw [isPWO_iff_exists_monotone_subseq] at hα
  obtain ⟨g, hg⟩ : exists (g : (Nat ↪o Nat)), Monotone fun n => (ofLex f (g n)).1 :=
    hα (fun n => (ofLex f n).1) (fun k => mem_image_of_mem (fun x => (ofLex x).1) (hf k))
  have hhg : forall n, (ofLex f (g 0)).1 <= (ofLex f (g n)).1 := fun n => hg n.zero_le
  by_cases! hc : exists n, (ofLex f (g 0)).1 < (ofLex f (g n)).1
  · obtain ⟨n, hn⟩ := hc
    use (g 0), (g n)
    constructor
    · by_contra hx
      simp_all
· exact Prod.Lex.toLex_le_toLex.mpr .inl hn
  · have hhc : forall n, (ofLex f (g 0)).1 = (ofLex f (g n)).1 := by
      intro n
      exact (hhg n).eq_of_not_lt (hc n)
    obtain ⟨g', hg'⟩ : exists g' : Nat ↪o Nat, Monotone ((fun n => (ofLex f (g (g' n))).2)) := by
      simp_rw [isPWO_iff_exists_monotone_subseq] at hβ
      apply hβ (ofLex f (g 0)).1 fun n => (ofLex f (g n)).2
      intro n
      rw [hhc n]
      simpa using! hf _
    use (g (g' 0)), (g (g' 1))
    suffices (f (g (g' 0))) <= (f (g (g' 1))) by simpa
· refine Prod.Lex.toLex_le_toLex.mpr .inr ⟨?_, ?_⟩
      · exact (hhc (g' 0)).symm.trans (hhc (g' 1))
      · exact hg' (Nat.zero_le 1)

/--
theorem `imageProdLex` / 定理 `imageProdLex`

English:
theorem imageProdLex
  statement: [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
  proof: IsPWO.image_of_monotone hαβ Prod.Lex.monotone_fst

中文:
定理 imageProdLex
  结论: [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
  证明: IsPWO.image_of_monotone hαβ Prod.Lex.monotone_fst

Depends on / 依赖: IsPWO.image_of_monotone, Prod.Lex.monotone_fst, image_of_monotone, monotone_fst
-/
theorem imageProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hαβ : s.IsPWO) : ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO :=
  IsPWO.image_of_monotone hαβ Prod.Lex.monotone_fst

/--
theorem `fiberProdLex` / 定理 `fiberProdLex`

English:
theorem fiberProdLex
  statement: [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
  proof: by
  let f : α ×ₗ β -> β := fun x => (ofLex x).2
  have h : {y | toLex (a, y) in s} = f '' (s inter (fun x => (ofLex x).1) ⁻¹' {a}) := by
    ext x
    simp [f]
  rw [h]
  apply IsPWO.image_of_monotoneOn (hαβ.mono inter_subset_left)
  rintro b ⟨-, hb⟩ c ⟨-, hc⟩ hbc
  simp only [mem_preimage, mem_sin

中文:
定理 fiberProdLex
  结论: [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
  证明: by
  let f : α ×ₗ β -> β := fun x => (ofLex x).2
  have h : {y | toLex (a, y) in s} = f '' (s inter (fun x => (ofLex x).1) ⁻¹' {a}) := by
    ext x
    simp [f]
  rw [h]
  apply IsPWO.image_of_monotoneOn (hαβ.mono inter_subset_left)
  rintro b ⟨-, hb⟩ c ⟨-, hc⟩ hbc
  simp only [mem_preimage, mem_sin

Depends on / 依赖: IsPWO.image_of_monotoneOn, Prod.Lex.toLex_le_toLex.mp, Prod.ext_iff, ext_iff, false_or, image_of_monotoneOn, inter_subset_left, lt_self_iff_false, mem_preimage, mem_singleton_iff, toLex_le_toLex, true_and
-/
theorem fiberProdLex [Preorder α] [Preorder β] {s : Set (α ×ₗ β)}
    (hαβ : s.IsPWO) (a : α) : {y | toLex (a, y) in s}.IsPWO := by
  let f : α ×ₗ β -> β := fun x => (ofLex x).2
  have h : {y | toLex (a, y) in s} = f '' (s inter (fun x => (ofLex x).1) ⁻¹' {a}) := by
    ext x
    simp [f]
  rw [h]
  apply IsPWO.image_of_monotoneOn (hαβ.mono inter_subset_left)
  rintro b ⟨-, hb⟩ c ⟨-, hc⟩ hbc
  simp only [mem_preimage, mem_singleton_iff] at hb hc
  have : (ofLex b).1 < (ofLex c).1 ∨ (ofLex b).1 = (ofLex c).1 ∧ f b <= f c :=
    Prod.Lex.toLex_le_toLex.mp hbc
  simp_all only [lt_self_iff_false, true_and, false_or]

/--
theorem `ProdLex_iff` / 定理 `ProdLex_iff`

English:
theorem ProdLex_iff
  given: [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
  proof: ⟨fun h => ⟨imageProdLex h, fiberProdLex h⟩, fun h => subsetProdLex h.1 h.2⟩

中文:
定理 ProdLex_iff
  条件: [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)}
  证明: ⟨fun h => ⟨imageProdLex h, fiberProdLex h⟩, fun h => subsetProdLex h.1 h.2⟩

Depends on / 依赖: fiberProdLex, imageProdLex, subsetProdLex
-/
theorem ProdLex_iff [PartialOrder α] [Preorder β] {s : Set (α ×ₗ β)} :
    s.IsPWO ↔
      ((fun (x : α ×ₗ β) => (ofLex x).1) '' s).IsPWO ∧ forall a, {y | toLex (a, y) in s}.IsPWO :=
  ⟨fun h => ⟨imageProdLex h, fiberProdLex h⟩, fun h => subsetProdLex h.1 h.2⟩

end Set.PartiallyWellOrderedOn

section ProdLex
variable {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {f : γ -> α} {g : γ -> β} {s : Set γ}

/--
theorem `WellFounded.prod_lex_of_wellFoundedOn_fiber` / 定理 `WellFounded.prod_lex_of_wellFoundedOn_fiber`

English:
theorem WellFounded.prod_lex_of_wellFoundedOn_fiber
  statement: (hα : WellFounded (rα on f))
  proof: by
  refine ((psigma_lex (wellFoundedOn_range.2 hα) fun a => hβ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | h' := Prod.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', rfl⟩ : ra

中文:
定理 WellFounded.prod_lex_of_wellFoundedOn_fiber
  结论: (hα : WellFounded (rα on f))
  证明: by
  refine ((psigma_lex (wellFoundedOn_range.2 hα) fun a => hβ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | h' := Prod.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', rfl⟩ : ra

Depends on / 依赖: InvImage, PSigma, PSigma.Lex.left, PSigma.Lex.right, PSigma.subtype_ext, Prod.lex_iff, Subtype, Subtype.ext, convert, exacts, lex_iff, psigma_lex, subtype_ext, wellFoundedOn_range
-/
theorem WellFounded.prod_lex_of_wellFoundedOn_fiber (hα : WellFounded (rα on f))
    (hβ : forall a, (f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    WellFounded (Prod.Lex rα rβ on fun c => (f c, g c)) := by
  refine ((psigma_lex (wellFoundedOn_range.2 hα) fun a => hβ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | h' := Prod.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    exacts [⟨c, h'.1⟩, PSigma.subtype_ext (Subtype.ext h'.1) rfl, h'.2]

/--
theorem `Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber` / 定理 `Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber`

English:
theorem Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber
  statement: (hα : s.WellFoundedOn (rα on f))
  proof: WellFounded.prod_lex_of_wellFoundedOn_fiber hα
    fun a => ((hβ a).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun _ _ h => ‹_›)

中文:
定理 Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber
  结论: (hα : s.WellFoundedOn (rα on f))
  证明: WellFounded.prod_lex_of_wellFoundedOn_fiber hα
    fun a => ((hβ a).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun _ _ h => ‹_›)

Depends on / 依赖: WellFounded, WellFounded.prod_lex_of_wellFoundedOn_fiber, prod_lex_of_wellFoundedOn_fiber
-/
theorem Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber (hα : s.WellFoundedOn (rα on f))
    (hβ : forall a, (s inter f ⁻¹' {a}).WellFoundedOn (rβ on g)) :
    s.WellFoundedOn (Prod.Lex rα rβ on fun c => (f c, g c)) :=
  WellFounded.prod_lex_of_wellFoundedOn_fiber hα
    fun a => ((hβ a).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun _ _ h => ‹_›)

end ProdLex

section SigmaLex

variable {rι : ι -> ι -> Prop} {rπ : forall i, π i -> π i -> Prop} {f : γ -> ι} {g : forall i, γ -> π i} {s : Set γ}

/--
theorem `WellFounded.sigma_lex_of_wellFoundedOn_fiber` / 定理 `WellFounded.sigma_lex_of_wellFoundedOn_fiber`

English:
theorem WellFounded.sigma_lex_of_wellFoundedOn_fiber
  statement: (hι : WellFounded (rι on f))
  proof: by
  refine ((psigma_lex (wellFoundedOn_range.2 hι) fun a => hπ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | ⟨h', h''⟩ := Sigma.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', r

中文:
定理 WellFounded.sigma_lex_of_wellFoundedOn_fiber
  结论: (hι : WellFounded (rι on f))
  证明: by
  refine ((psigma_lex (wellFoundedOn_range.2 hι) fun a => hπ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | ⟨h', h''⟩ := Sigma.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', r

Depends on / 依赖: InvImage, Order.Preimage, PSigma, PSigma.Lex.left, PSigma.Lex.right, PSigma.subtype_ext, Preimage, Sigma.lex_iff, Subrel, Subtype, Subtype.coe_mk, Subtype.ext, coe_mk, convert, lex_iff, psigma_lex, subtype_ext, wellFoundedOn_range
-/
theorem WellFounded.sigma_lex_of_wellFoundedOn_fiber (hι : WellFounded (rι on f))
    (hπ : forall i, (f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    WellFounded (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  refine ((psigma_lex (wellFoundedOn_range.2 hι) fun a => hπ a).onFun
    (f := fun c => ⟨⟨_, c, rfl⟩, c, rfl⟩)).mono fun c c' h => ?_
  obtain h' | ⟨h', h''⟩ := Sigma.lex_iff.1 h
  · exact PSigma.Lex.left _ _ h'
  · dsimp only [InvImage, (· on ·)] at h' ⊢
    convert! PSigma.Lex.right (⟨_, c', rfl⟩ : range f) _ using 1; swap
    · exact ⟨c, h'⟩
    · exact PSigma.subtype_ext (Subtype.ext h') rfl
    · dsimp only [Subtype.coe_mk, Subrel, Order.Preimage] at *
      grind

/--
theorem `Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber` / 定理 `Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber`

English:
theorem Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber
  statement: (hι : s.WellFoundedOn (rι on f))
  proof: by
  change WellFounded (Sigma.Lex rι rπ on fun c : s => ⟨f c, g (f c) c⟩)
  exact
    @WellFounded.sigma_lex_of_wellFoundedOn_fiber _ s _ _ rπ (fun c => f c) (fun i c => g _ c) hι
      fun i => ((hπ i).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun b c h => ‹_›)

中文:
定理 Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber
  结论: (hι : s.WellFoundedOn (rι on f))
  证明: by
  change WellFounded (Sigma.Lex rι rπ on fun c : s => ⟨f c, g (f c) c⟩)
  exact
    @WellFounded.sigma_lex_of_wellFoundedOn_fiber _ s _ _ rπ (fun c => f c) (fun i c => g _ c) hι
      fun i => ((hπ i).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun b c h => ‹_›)

Depends on / 依赖: Sigma.Lex, WellFounded, WellFounded.sigma_lex_of_wellFoundedOn_fiber, sigma_lex_of_wellFoundedOn_fiber
-/
theorem Set.WellFoundedOn.sigma_lex_of_wellFoundedOn_fiber (hι : s.WellFoundedOn (rι on f))
    (hπ : forall i, (s inter f ⁻¹' {i}).WellFoundedOn (rπ i on g i)) :
    s.WellFoundedOn (Sigma.Lex rι rπ on fun c => ⟨f c, g (f c) c⟩) := by
  change WellFounded (Sigma.Lex rι rπ on fun c : s => ⟨f c, g (f c) c⟩)
  exact
    @WellFounded.sigma_lex_of_wellFoundedOn_fiber _ s _ _ rπ (fun c => f c) (fun i c => g _ c) hι
      fun i => ((hπ i).onFun (f := fun x => ⟨x, x.1.2, x.2⟩)).mono (fun b c h => ‹_›)

end SigmaLex
