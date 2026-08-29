/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies, David Loeffler
-/
module

public import Mathlib.Order.PartialSups
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.LinearLocallyFinite
public import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Making a sequence disjoint

This file defines the way to make a sequence of sets - or, more generally, a map from a partially
ordered type `ι` into a (generalized) Boolean algebra `α` - into a *pairwise disjoint* sequence with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1) ⋯`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The map sending `i` to `f i \ (⨆ j < i, f j)`. We require the index type to be a
  `LocallyFiniteOrderBot` to ensure that the supremum is well defined.
* `partialSups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `Fintype.sup_disjointed` (for finite `ι`) or `iSup_disjointed` (for complete `α`):
  `disjointed f` has the same supremum as `f`. Limiting case of `partialSups_disjointed`.
* `Fintype.exists_disjointed_le`: for any finite family `f : ι → α`, there exists a pairwise
  disjoint family `g : ι → α` which is bounded above by `f` and has the same supremum. This is
  an analogue of `disjointed` for arbitrary finite index types (but without any uniqueness).

We also provide set notation variants of some lemmas.
-/

@[expose] public section

assert_not_exists SuccAddOrder

open Finset Order

variable {α ι : Type*}

open scoped Function -- required for scoped `on` notation

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

section Preorder -- the *index type* is a preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

/--
Definition of `disjointed` / `disjointed` 的定义

English:
definition disjointed
  signature: (f : ι -> α) (i : ι)
  body: f i \ (Iio i).sup f

中文:
定义 disjointed
  签名: (f : ι -> α) (i : ι)
  定义体: f i \ (Iio i).sup f
-/
def disjointed (f : ι -> α) (i : ι) : α := f i \ (Iio i).sup f

/--
lemma `disjointed_apply` / 引理 `disjointed_apply`

English:
lemma disjointed_apply
  given: (f : ι -> α) (i : ι)
  statement: disjointed f i = f i \ (Iio i).sup f
  proof: rfl

中文:
引理 disjointed_apply
  条件: (f : ι -> α) (i : ι)
  结论: disjointed f i = f i \ (Iio i).sup f
  证明: rfl
-/
lemma disjointed_apply (f : ι -> α) (i : ι) : disjointed f i = f i \ (Iio i).sup f := rfl

/--
lemma `disjointed_of_isMin` / 引理 `disjointed_of_isMin`

English:
lemma disjointed_of_isMin
  given: (f : ι -> α) {i : ι} (hn : IsMin i)
  proof: by
  have : Iio i = ∅ := by rwa [← Finset.coe_eq_empty, coe_Iio, Set.Iio_eq_empty_iff]
  simp only [disjointed_apply, this, sup_empty, sdiff_bot]

中文:
引理 disjointed_of_isMin
  条件: (f : ι -> α) {i : ι} (hn : IsMin i)
  证明: by
  have : Iio i = ∅ := by rwa [← Finset.coe_eq_empty, coe_Iio, Set.Iio_eq_empty_iff]
  simp only [disjointed_apply, this, sup_empty, sdiff_bot]

Depends on / 依赖: Finset, Finset.coe_eq_empty, Iio_eq_empty_iff, Set.Iio_eq_empty_iff, coe_Iio, coe_eq_empty, disjointed_apply, sdiff_bot, sup_empty
-/
lemma disjointed_of_isMin (f : ι -> α) {i : ι} (hn : IsMin i) :
    disjointed f i = f i := by
  have : Iio i = ∅ := by rwa [← Finset.coe_eq_empty, coe_Iio, Set.Iio_eq_empty_iff]
  simp only [disjointed_apply, this, sup_empty, sdiff_bot]

/--
lemma `disjointed_bot` / 引理 `disjointed_bot`

English:
lemma disjointed_bot
  given: [OrderBot ι] (f : ι -> α)
  statement: disjointed f ⊥ = f ⊥
  proof: disjointed_of_isMin _ isMin_bot

中文:
引理 disjointed_bot
  条件: [OrderBot ι] (f : ι -> α)
  结论: disjointed f ⊥ = f ⊥
  证明: disjointed_of_isMin _ isMin_bot
-/
@[simp] lemma disjointed_bot [OrderBot ι] (f : ι -> α) : disjointed f ⊥ = f ⊥ :=
  disjointed_of_isMin _ isMin_bot

/--
theorem `disjointed_le_id` / 定理 `disjointed_le_id`

English:
theorem disjointed_le_id
  statement: disjointed <= (id : (ι -> α) -> ι -> α)
  proof: fun _ _ => sdiff_le

中文:
定理 disjointed_le_id
  结论: disjointed <= (id : (ι -> α) -> ι -> α)
  证明: fun _ _ => sdiff_le

Depends on / 依赖: sdiff_le
-/
theorem disjointed_le_id : disjointed <= (id : (ι -> α) -> ι -> α) :=
  fun _ _ => sdiff_le

/--
theorem `disjointed_le` / 定理 `disjointed_le`

English:
theorem disjointed_le
  given: (f : ι -> α)
  statement: disjointed f <= f
  proof: disjointed_le_id f

中文:
定理 disjointed_le
  条件: (f : ι -> α)
  结论: disjointed f <= f
  证明: disjointed_le_id f

Depends on / 依赖: disjointed_le_id
-/
theorem disjointed_le (f : ι -> α) : disjointed f <= f :=
  disjointed_le_id f

/--
theorem `disjoint_disjointed_of_lt` / 定理 `disjoint_disjointed_of_lt`

English:
theorem disjoint_disjointed_of_lt
  given: (f : ι -> α) {i j : ι} (h : i < j)
  proof: (disjoint_sdiff_self_right.mono_left <| le_sup (mem_Iio.mpr h)).mono_left (disjointed_le f i)

中文:
定理 disjoint_disjointed_of_lt
  条件: (f : ι -> α) {i j : ι} (h : i < j)
  证明: (disjoint_sdiff_self_right.mono_left <| le_sup (mem_Iio.mpr h)).mono_left (disjointed_le f i)

Depends on / 依赖: disjoint_sdiff_self_right, disjoint_sdiff_self_right.mono_left, disjointed_le, le_sup, mem_Iio, mem_Iio.mpr, mono_left
-/
theorem disjoint_disjointed_of_lt (f : ι -> α) {i j : ι} (h : i < j) :
    Disjoint (disjointed f i) (disjointed f j) :=
  (disjoint_sdiff_self_right.mono_left <| le_sup (mem_Iio.mpr h)).mono_left (disjointed_le f i)

/--
lemma `disjointed_eq_self` / 引理 `disjointed_eq_self`

English:
lemma disjointed_eq_self
  given: {f : ι -> α} {i : ι} (hf : forall j < i, Disjoint (f j) (f i))
  proof: by
  rw [disjointed_apply]; rw [sdiff_eq_left]; rw [disjoint_iff]; rw [sup_inf_distrib_left]; rw [sup_congr rfl fun j hj => disjoint_iff.mp (hf _ (mem_Iio.mp hj)).symm]
  exact sup_bot _

中文:
引理 disjointed_eq_self
  条件: {f : ι -> α} {i : ι} (hf : 对任意 j < i, Disjoint (f j) (f i))
  证明: by
  rw [disjointed_apply]; rw [sdiff_eq_left]; rw [disjoint_iff]; rw [sup_inf_distrib_left]; rw [sup_congr rfl fun j hj => disjoint_iff.mp (hf _ (mem_Iio.mp hj)).symm]
  exact sup_bot _

Depends on / 依赖: disjoint_iff, disjoint_iff.mp, disjointed_apply, mem_Iio, mem_Iio.mp, sdiff_eq_left, sup_bot, sup_congr, sup_inf_distrib_left
-/
lemma disjointed_eq_self {f : ι -> α} {i : ι} (hf : forall j < i, Disjoint (f j) (f i)) :
    disjointed f i = f i := by
  rw [disjointed_apply]; rw [sdiff_eq_left]; rw [disjoint_iff]; rw [sup_inf_distrib_left]; rw [sup_congr rfl fun j hj => disjoint_iff.mp (hf _ (mem_Iio.mp hj)).symm]
  exact sup_bot _

/- NB: The original statement for `ι = ℕ` was a `def` and worked for `p : α → Sort*`. I couldn't
prove the `Sort*` version for general `ι`, but all instances of `disjointedRec` in the library are
for Prop anyway. -/
/--
lemma `disjointedRec` / 引理 `disjointedRec`

English:
lemma disjointedRec
  given: {f : ι -> α} {p : α -> Prop} (hdiff : forall ⦃t i⦄, p t -> p (t \ f i))
  proof: by
  classical
  intro i hpi
  rw [disjointed]
  suffices forall (s : Finset ι), p (f i \ s.sup f) from this _
  intro s
  induction s using Finset.induction with
  | empty => simpa only [sup_empty, sdiff_bot] using hpi
  | insert _ _ ht IH =>
    rw [sup_insert]; rw [sup_comm]; rw [← sdiff_sdiff]
 

中文:
引理 disjointedRec
  条件: {f : ι -> α} {p : α -> 命题} (hdiff : 对任意 ⦃t i⦄, p t -> p (t \ f i))
  证明: by
  classical
  intro i hpi
  rw [disjointed]
  suffices forall (s : Finset ι), p (f i \ s.sup f) from this _
  intro s
  induction s using Finset.induction with
  | empty => simpa only [sup_empty, sdiff_bot] using hpi
  | insert _ _ ht IH =>
    rw [sup_insert]; rw [sup_comm]; rw [← sdiff_sdiff]
 

Depends on / 依赖: Finset, Finset.induction, classical, disjointed, insert, s.sup, sdiff_bot, sdiff_sdiff, sup_comm, sup_empty, sup_insert
-/
lemma disjointedRec {f : ι -> α} {p : α -> Prop} (hdiff : forall ⦃t i⦄, p t -> p (t \ f i)) :
    forall ⦃i⦄, p (f i) -> p (disjointed f i) := by
  classical
  intro i hpi
  rw [disjointed]
  suffices forall (s : Finset ι), p (f i \ s.sup f) from this _
  intro s
  induction s using Finset.induction with
  | empty => simpa only [sup_empty, sdiff_bot] using hpi
  | insert _ _ ht IH =>
    rw [sup_insert]; rw [sup_comm]; rw [← sdiff_sdiff]
    exact hdiff IH

end Preorder

section PartialOrder -- the index type is a partial order

variable [PartialOrder ι] [LocallyFiniteOrderBot ι]

@[simp]
/--
theorem `partialSups_disjointed` / 定理 `partialSups_disjointed`

English:
theorem partialSups_disjointed
  given: (f : ι -> α)
  proof: by
  -- This seems to be much more awkward than the case of linear orders, because the supremum
  -- in the definition of `disjointed` can involve multiple "paths" through the poset.
  classical
  -- We argue by induction on the size of `Iio i`.
  suffices forall r i (hi : #(Iio i) <= r), partialSup

中文:
定理 partialSups_disjointed
  条件: (f : ι -> α)
  证明: by
  -- This seems to be much more awkward than the case of linear orders, because the supremum
  -- in the definition of `disjointed` can involve multiple "paths" through the poset.
  classical
  -- We argue by induction on the size of `Iio i`.
  suffices forall r i (hi : #(Iio i) <= r), partialSup
-/
theorem partialSups_disjointed (f : ι -> α) :
    partialSups (disjointed f) = partialSups f := by
  -- This seems to be much more awkward than the case of linear orders, because the supremum
  -- in the definition of `disjointed` can involve multiple "paths" through the poset.
  classical
  -- We argue by induction on the size of `Iio i`.
  suffices forall r i (hi : #(Iio i) <= r), partialSups (disjointed f) i = partialSups f i from
    OrderHom.ext _ _ (funext fun i => this _ i le_rfl)
  intro r i hi
  induction r generalizing i with
  | zero =>
    -- Base case: `n` is minimal, so `partialSups f i = partialSups (disjointed f) n = f i`.
    simp only [Nat.le_zero, card_eq_zero] at hi
    simp only [partialSups_apply, Iic_eq_cons_Iio, hi, disjointed_apply, sup'_eq_sup, sup_cons,
      sup_empty, sdiff_bot]
  | succ n ih =>
    -- Induction step: first WLOG arrange that `#(Iio i) = r + 1`
    rcases lt_or_eq_of_le hi with hn | hn
· exact ih _ Nat.le_of_lt_succ hn
    simp only [partialSups_apply (disjointed f), Iic_eq_cons_Iio, sup'_eq_sup, sup_cons]
    -- Key claim: we can write `Iio i` as a union of (finitely many) `Iic` intervals.
    have hun : (Iio i).biUnion Iic = Iio i := by
      ext r; simpa using ⟨fun ⟨a, ha⟩ => ha.2.trans_lt ha.1, fun hr => ⟨r, hr, le_rfl⟩⟩
    -- Use claim and `sup_biUnion` to rewrite the supremum in the definition of `disjointed f`
    -- in terms of suprema over `Iic`'s. Then the RHS is a `sup` over `partialSups`, which we
    -- can rewrite via the induction hypothesis.
    rw [← hun]; rw [sup_biUnion]; rw [sup_congr rfl (g := partialSups f)]
    · simp only [funext (partialSups_apply f), sup'_eq_sup, ← sup_biUnion, hun]
      simp only [disjointed, sdiff_sup_self, Iic_eq_cons_Iio, sup_cons]
    · simp only [partialSups, sup'_eq_sup, OrderHom.coe_mk] at ih ⊢
      refine fun x hx => ih x ?_
      -- Remains to show `∀ x in Iio i, #(Iio x) ≤ r`.
      rw [← Nat.lt_add_one_iff]; rw [← hn]
      apply lt_of_lt_of_le (b := #(Iic x))
      · simpa only [Iic_eq_cons_Iio, card_cons] using Nat.lt_succ_self _
      · refine card_le_card (fun r hr => ?_)
        simp only [mem_Iic, mem_Iio] at hx hr ⊢
        exact hr.trans_lt hx

/--
lemma `Fintype.sup_disjointed` / 引理 `Fintype.sup_disjointed`

English:
lemma Fintype.sup_disjointed
  given: [Fintype ι] (f : ι -> α)
  proof: by
  classical
  have hun : univ.biUnion Iic = (univ : Finset ι) := by
    ext r; simpa only [mem_biUnion, mem_univ, mem_Iic, true_and, iff_true] using ⟨r, le_rfl⟩
  rw [← hun]; rw [sup_biUnion]; rw [sup_biUnion]; rw [sup_congr rfl (fun i _ => ?_)]
  rw [← sup'_eq_sup nonempty_Iic]; rw [← sup'_eq_su

中文:
引理 Fintype.sup_disjointed
  条件: [Fintype ι] (f : ι -> α)
  证明: by
  classical
  have hun : univ.biUnion Iic = (univ : Finset ι) := by
    ext r; simpa only [mem_biUnion, mem_univ, mem_Iic, true_and, iff_true] using ⟨r, le_rfl⟩
  rw [← hun]; rw [sup_biUnion]; rw [sup_biUnion]; rw [sup_congr rfl (fun i _ => ?_)]
  rw [← sup'_eq_sup nonempty_Iic]; rw [← sup'_eq_su

Depends on / 依赖: Finset, _eq_sup, biUnion, classical, iff_true, le_rfl, mem_Iic, mem_biUnion, mem_univ, nonempty_Iic, partialSups_apply, partialSups_disjointed, sup_biUnion, sup_congr, true_and, univ.biUnion
-/
lemma Fintype.sup_disjointed [Fintype ι] (f : ι -> α) :
    univ.sup (disjointed f) = univ.sup f := by
  classical
  have hun : univ.biUnion Iic = (univ : Finset ι) := by
    ext r; simpa only [mem_biUnion, mem_univ, mem_Iic, true_and, iff_true] using ⟨r, le_rfl⟩
  rw [← hun]; rw [sup_biUnion]; rw [sup_biUnion]; rw [sup_congr rfl (fun i _ => ?_)]
  rw [← sup'_eq_sup nonempty_Iic]; rw [← sup'_eq_sup nonempty_Iic]; rw [← partialSups_apply]; rw [← partialSups_apply]; rw [partialSups_disjointed]

/--
lemma `disjointed_partialSups` / 引理 `disjointed_partialSups`

English:
lemma disjointed_partialSups
  given: (f : ι -> α)
  proof: by
  classical
  ext i
  have step1 : f i \ (Iio i).sup f = partialSups f i \ (Iio i).sup f := by
    rw [sdiff_eq_symm (sdiff_le.trans (le_partialSups f i))]
    simp only [funext (partialSups_apply f), sup'_eq_sup]
    rw [sdiff_sdiff_eq_sdiff_sup (sup_mono Iio_subset_Iic_self)]; rw [sup_eq_right]

中文:
引理 disjointed_partialSups
  条件: (f : ι -> α)
  证明: by
  classical
  ext i
  have step1 : f i \ (Iio i).sup f = partialSups f i \ (Iio i).sup f := by
    rw [sdiff_eq_symm (sdiff_le.trans (le_partialSups f i))]
    simp only [funext (partialSups_apply f), sup'_eq_sup]
    rw [sdiff_sdiff_eq_sdiff_sup (sup_mono Iio_subset_Iic_self)]; rw [sup_eq_right]

Depends on / 依赖: Iic_eq_cons_Iio, Iio_subset_Iic_self, _eq_sup, classical, disjointed_apply, le_partialSups, le_sup_right, mem_biUni, partialSups, partialSups_apply, sdiff_eq_symm, sdiff_le, sdiff_le.trans, sdiff_le_iff, sdiff_sdiff_eq_sdiff_sup, sup_biUnion, sup_cons, sup_eq_right, sup_mono, sup_sdiff_left_self
-/
lemma disjointed_partialSups (f : ι -> α) :
    disjointed (partialSups f) = disjointed f := by
  classical
  ext i
  have step1 : f i \ (Iio i).sup f = partialSups f i \ (Iio i).sup f := by
    rw [sdiff_eq_symm (sdiff_le.trans (le_partialSups f i))]
    simp only [funext (partialSups_apply f), sup'_eq_sup]
    rw [sdiff_sdiff_eq_sdiff_sup (sup_mono Iio_subset_Iic_self)]; rw [sup_eq_right]
    simp only [Iic_eq_cons_Iio, sup_cons, sup_sdiff_left_self, sdiff_le_iff, le_sup_right]
  simp only [disjointed_apply, step1, funext (partialSups_apply f), sup'_eq_sup, ← sup_biUnion]
  congr 2 with r
  simpa only [mem_biUnion, mem_Iio, mem_Iic] using
    ⟨fun ⟨a, ha⟩ => ha.2.trans_lt ha.1, fun hr => ⟨r, hr, le_rfl⟩⟩

/--
theorem `disjointed_unique` / 定理 `disjointed_unique`

English:
theorem disjointed_unique
  statement: {f d : ι -> α} (hdisj : forall {i j : ι} (_ : i < j), Disjoint (d i) (d j))
  proof: by
  rw [← disjointed_partialSups]; rw [← hsups]; rw [disjointed_partialSups]
  exact funext fun _ => (disjointed_eq_self (fun _ hj => hdisj hj)).symm

中文:
定理 disjointed_unique
  结论: {f d : ι -> α} (hdisj : 对任意 {i j : ι} (_ : i < j), Disjoint (d i) (d j))
  证明: by
  rw [← disjointed_partialSups]; rw [← hsups]; rw [disjointed_partialSups]
  exact funext fun _ => (disjointed_eq_self (fun _ hj => hdisj hj)).symm

Depends on / 依赖: disjointed_eq_self, disjointed_partialSups
-/
theorem disjointed_unique {f d : ι -> α} (hdisj : forall {i j : ι} (_ : i < j), Disjoint (d i) (d j))
    (hsups : partialSups d = partialSups f) :
    d = disjointed f := by
  rw [← disjointed_partialSups]; rw [← hsups]; rw [disjointed_partialSups]
  exact funext fun _ => (disjointed_eq_self (fun _ hj => hdisj hj)).symm

/--
lemma `biUnion_Iic_disjointed` / 引理 `biUnion_Iic_disjointed`

English:
lemma biUnion_Iic_disjointed
  given: {α : Type*} (f : ι -> Set α) (n : ι)
  proof: by
  rw [← partialSups_disjointed]; rw [partialSups_eq_biSup]
  simp

中文:
引理 biUnion_Iic_disjointed
  条件: {α : 类型} (f : ι -> Set α) (n : ι)
  证明: by
  rw [← partialSups_disjointed]; rw [partialSups_eq_biSup]
  simp

Depends on / 依赖: partialSups_disjointed, partialSups_eq_biSup
-/
lemma biUnion_Iic_disjointed {α : Type*} (f : ι -> Set α) (n : ι) :
    (⋃ i in Finset.Iic n, disjointed f i) = partialSups f n := by
  rw [← partialSups_disjointed]; rw [partialSups_eq_biSup]
  simp

/--
lemma `biUnion_range_succ_disjointed` / 引理 `biUnion_range_succ_disjointed`

English:
lemma biUnion_range_succ_disjointed
  given: {α : Type*} (f : Nat -> Set α) (n : Nat)
  proof: by
  rw [Nat.range_succ_eq_Iic]; rw [biUnion_Iic_disjointed]

中文:
引理 biUnion_range_succ_disjointed
  条件: {α : 类型} (f : 自然数 -> Set α) (n : 自然数)
  证明: by
  rw [Nat.range_succ_eq_Iic]; rw [biUnion_Iic_disjointed]

Depends on / 依赖: Nat.range_succ_eq_Iic, biUnion_Iic_disjointed, range_succ_eq_Iic
-/
lemma biUnion_range_succ_disjointed {α : Type*} (f : Nat -> Set α) (n : Nat) :
    (⋃ i in Finset.range (n + 1), disjointed f i) = partialSups f n := by
  rw [Nat.range_succ_eq_Iic]; rw [biUnion_Iic_disjointed]

end PartialOrder

section LinearOrder -- the index type is a linear order

/-!
### Linear orders
-/

variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/--
theorem `disjoint_disjointed` / 定理 `disjoint_disjointed`

English:
theorem disjoint_disjointed
  given: (f : ι -> α)
  statement: Pairwise (Disjoint on disjointed f)
  proof: (pairwise_disjoint_on _).mpr fun _ _ => disjoint_disjointed_of_lt f

中文:
定理 disjoint_disjointed
  条件: (f : ι -> α)
  结论: Pairwise (Disjoint on disjointed f)
  证明: (pairwise_disjoint_on _).mpr fun _ _ => disjoint_disjointed_of_lt f

Depends on / 依赖: disjoint_disjointed_of_lt, pairwise_disjoint_on
-/
theorem disjoint_disjointed (f : ι -> α) : Pairwise (Disjoint on disjointed f) :=
  (pairwise_disjoint_on _).mpr fun _ _ => disjoint_disjointed_of_lt f

/--
theorem `disjointed_unique'` / 定理 `disjointed_unique'`

English:
theorem disjointed_unique'
  statement: {f d : ι -> α} (hdisj : Pairwise (Disjoint on d))
  proof: disjointed_unique (fun hij => hdisj hij.ne) hsups

中文:
定理 disjointed_unique'
  结论: {f d : ι -> α} (hdisj : Pairwise (Disjoint on d))
  证明: disjointed_unique (fun hij => hdisj hij.ne) hsups

Depends on / 依赖: disjointed_unique, hij.ne
-/
theorem disjointed_unique' {f d : ι -> α} (hdisj : Pairwise (Disjoint on d))
    (hsups : partialSups d = partialSups f) : d = disjointed f :=
  disjointed_unique (fun hij => hdisj hij.ne) hsups

set_option backward.isDefEq.respectTransparency false in
omit [GeneralizedBooleanAlgebra α] in
/--
lemma `Finset.disjiUnion_Iic_disjointed` / 引理 `Finset.disjiUnion_Iic_disjointed`

English:
lemma Finset.disjiUnion_Iic_disjointed
  given: [DecidableEq α] (n : ι) (t : ι -> Finset α)
  proof: by
  rw [← partialSups_disjointed]; rw [partialSups_apply]; rw [Finset.sup'_eq_sup]; rw [Finset.sup_eq_biUnion]; rw [disjiUnion_eq_biUnion]

中文:
引理 Finset.disjiUnion_Iic_disjointed
  条件: [DecidableEq α] (n : ι) (t : ι -> Finset α)
  证明: by
  rw [← partialSups_disjointed]; rw [partialSups_apply]; rw [Finset.sup'_eq_sup]; rw [Finset.sup_eq_biUnion]; rw [disjiUnion_eq_biUnion]

Depends on / 依赖: Finset, Finset.sup, Finset.sup_eq_biUnion, _eq_sup, disjiUnion_eq_biUnion, partialSups_apply, partialSups_disjointed, sup_eq_biUnion
-/
lemma Finset.disjiUnion_Iic_disjointed [DecidableEq α] (n : ι) (t : ι -> Finset α) :
    (Iic n).disjiUnion (disjointed t) ((disjoint_disjointed t).set_pairwise _) =
      partialSups t n := by
  rw [← partialSups_disjointed]; rw [partialSups_apply]; rw [Finset.sup'_eq_sup]; rw [Finset.sup_eq_biUnion]; rw [disjiUnion_eq_biUnion]

section SuccOrder

variable [SuccOrder ι]

/--
lemma `disjointed_succ` / 引理 `disjointed_succ`

English:
lemma disjointed_succ
  given: (f : ι -> α) {i : ι} (hi : ¬IsMax i)
  proof: by
  rw [disjointed_apply]; rw [partialSups_apply]; rw [sup'_eq_sup]
  congr 2 with m
  simpa only [mem_Iio, mem_Iic] using lt_succ_iff_of_not_isMax hi

中文:
引理 disjointed_succ
  条件: (f : ι -> α) {i : ι} (hi : ¬IsMax i)
  证明: by
  rw [disjointed_apply]; rw [partialSups_apply]; rw [sup'_eq_sup]
  congr 2 with m
  simpa only [mem_Iio, mem_Iic] using lt_succ_iff_of_not_isMax hi

Depends on / 依赖: _eq_sup, disjointed_apply, lt_succ_iff_of_not_isMax, mem_Iic, mem_Iio, partialSups_apply
-/
lemma disjointed_succ (f : ι -> α) {i : ι} (hi : ¬IsMax i) :
    disjointed f (succ i) = f (succ i) \ partialSups f i := by
  rw [disjointed_apply]; rw [partialSups_apply]; rw [sup'_eq_sup]
  congr 2 with m
  simpa only [mem_Iio, mem_Iic] using lt_succ_iff_of_not_isMax hi

/--
lemma `Monotone.disjointed_succ` / 引理 `Monotone.disjointed_succ`

English:
lemma Monotone.disjointed_succ
  given: {f : ι -> α} (hf : Monotone f) {i : ι} (hn : ¬IsMax i)
  proof: by
  rwa [disjointed_succ, hf.partialSups_eq]

中文:
引理 Monotone.disjointed_succ
  条件: {f : ι -> α} (hf : Monotone f) {i : ι} (hn : ¬IsMax i)
  证明: by
  rwa [disjointed_succ, hf.partialSups_eq]
-/
protected lemma Monotone.disjointed_succ {f : ι -> α} (hf : Monotone f) {i : ι} (hn : ¬IsMax i) :
    disjointed f (succ i) = f (succ i) \ f i := by
  rwa [disjointed_succ, hf.partialSups_eq]

/--
lemma `Monotone.disjointed_succ_sup` / 引理 `Monotone.disjointed_succ_sup`

English:
lemma Monotone.disjointed_succ_sup
  given: {f : ι -> α} (hf : Monotone f) (i : ι)
  proof: by
  by_cases h : IsMax i
  · simpa only [succ_eq_iff_isMax.mpr h, sup_eq_right] using disjointed_le f i
  · rw [disjointed_apply]
    have : Iio (succ i) = Iic i := by
      ext
      simp only [mem_Iio, lt_succ_iff_eq_or_lt_of_not_isMax h, mem_Iic, le_iff_lt_or_eq, Or.comm]
    rw [this]; rw [← su

中文:
引理 Monotone.disjointed_succ_sup
  条件: {f : ι -> α} (hf : Monotone f) (i : ι)
  证明: by
  by_cases h : IsMax i
  · simpa only [succ_eq_iff_isMax.mpr h, sup_eq_right] using disjointed_le f i
  · rw [disjointed_apply]
    have : Iio (succ i) = Iic i := by
      ext
      simp only [mem_Iio, lt_succ_iff_eq_or_lt_of_not_isMax h, mem_Iic, le_iff_lt_or_eq, Or.comm]
    rw [this]; rw [← su

Depends on / 依赖: Or.comm, _eq_sup, disjointed_apply, disjointed_le, hf.partialSups_eq, le_iff_lt_or_eq, le_succ, lt_succ_iff_eq_or_lt_of_not_isMax, mem_Iic, mem_Iio, nonempty_Iic, partialSups_apply, partialSups_eq, sdiff_sup_cancel, succ_eq_iff_isMax, succ_eq_iff_isMax.mpr, sup_eq_right
-/
lemma Monotone.disjointed_succ_sup {f : ι -> α} (hf : Monotone f) (i : ι) :
    disjointed f (succ i) ⊔ f i = f (succ i) := by
  by_cases h : IsMax i
  · simpa only [succ_eq_iff_isMax.mpr h, sup_eq_right] using disjointed_le f i
  · rw [disjointed_apply]
    have : Iio (succ i) = Iic i := by
      ext
      simp only [mem_Iio, lt_succ_iff_eq_or_lt_of_not_isMax h, mem_Iic, le_iff_lt_or_eq, Or.comm]
    rw [this]; rw [← sup'_eq_sup nonempty_Iic]; rw [← partialSups_apply]; rw [hf.partialSups_eq]; rw [sdiff_sup_cancel hf le_succ i]

end SuccOrder

/--
lemma `sup_Ioc_disjointed_of_monotone` / 引理 `sup_Ioc_disjointed_of_monotone`

English:
lemma sup_Ioc_disjointed_of_monotone
  proof: by
  let : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  induction hm using Succ.rec with
  | rfl => simp
  | succ m hm ih =>
    by_cases h'm : IsMax m
    · simpa [Order.succ_eq_iff_isMax.mpr h'm] using ih
    · rw [← Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax hm h'm]
      simp only

中文:
引理 sup_Ioc_disjointed_of_monotone
  证明: by
  let : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  induction hm using Succ.rec with
  | rfl => simp
  | succ m hm ih =>
    by_cases h'm : IsMax m
    · simpa [Order.succ_eq_iff_isMax.mpr h'm] using ih
    · rw [← Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax hm h'm]
      simp only

Depends on / 依赖: Finset, Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax, LinearLocallyFiniteOrder, LinearLocallyFiniteOrder.succOrder, Order.le_succ, Order.succ_eq_iff_isMax.mpr, Succ.rec, SuccOrder, disjointed_succ, hf.disjointed_succ, insert_Ioc_right_eq_Ioc_succ_of_not_isMax, le_succ, sdiff_sup_sdiff_cancel, succOrder, succ_eq_iff_isMax, sup_insert
-/
lemma sup_Ioc_disjointed_of_monotone
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    {f : ι -> α} (hf : Monotone f) {m n : ι} (hm : n <= m) :
    (Finset.Ioc n m).sup (disjointed f) = f m \ f n := by
  let : SuccOrder ι := LinearLocallyFiniteOrder.succOrder ι
  induction hm using Succ.rec with
  | rfl => simp
  | succ m hm ih =>
    by_cases h'm : IsMax m
    · simpa [Order.succ_eq_iff_isMax.mpr h'm] using ih
    · rw [← Finset.insert_Ioc_right_eq_Ioc_succ_of_not_isMax hm h'm]
      simp only [sup_insert, hf.disjointed_succ h'm, ih]
      exact sdiff_sup_sdiff_cancel (hf (Order.le_succ m)) (hf hm)

/--
lemma `biUnion_Ioc_disjointed_of_monotone` / 引理 `biUnion_Ioc_disjointed_of_monotone`

English:
lemma biUnion_Ioc_disjointed_of_monotone
  proof: by
  simp [← sup_Ioc_disjointed_of_monotone hf hm]

中文:
引理 biUnion_Ioc_disjointed_of_monotone
  证明: by
  simp [← sup_Ioc_disjointed_of_monotone hf hm]

Depends on / 依赖: sup_Ioc_disjointed_of_monotone
-/
lemma biUnion_Ioc_disjointed_of_monotone
    {α ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    {f : ι -> Set α} (hf : Monotone f) {m n : ι} (hm : n <= m) :
    ⋃ i in Finset.Ioc n m, disjointed f i = f m \ f n := by
  simp [← sup_Ioc_disjointed_of_monotone hf hm]

end LinearOrder

/-!
### Functions on an arbitrary fintype
-/

/--
lemma `Fintype.exists_disjointed_le` / 引理 `Fintype.exists_disjointed_le`

English:
lemma Fintype.exists_disjointed_le
  given: {ι : Type*} [Fintype ι] (f : ι -> α)
  proof: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- do `ι = ∅` separately since `⊤ : Fin n` isn't defined for `n = 0`
    exact ⟨f, le_rfl, rfl, Subsingleton.pairwise⟩
  let R : ι ≃ Fin _ := equivFin ι
  let f' : Fin _ -> α := f ∘ R.symm
  have hf' : f = f' ∘ R := by ext; simp only [Function.comp_

中文:
引理 Fintype.exists_disjointed_le
  条件: {ι : 类型} [Fintype ι] (f : ι -> α)
  证明: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- do `ι = ∅` separately since `⊤ : Fin n` isn't defined for `n = 0`
    exact ⟨f, le_rfl, rfl, Subsingleton.pairwise⟩
  let R : ι ≃ Fin _ := equivFin ι
  let f' : Fin _ -> α := f ∘ R.symm
  have hf' : f = f' ∘ R := by ext; simp only [Function.comp_

Depends on / 依赖: Equiv.symm_apply_apply, Function, Function.comp_apply, R.symm, Subsingleton, Subsingleton.pairwise, comp_apply, defined, disjointed, disjointed_le, equivFin, image_univ_equiv, isEmpty_or_nonempty, le_rfl, pairwise, separately, sup_disjointed, sup_image, symm_apply_apply
-/
lemma Fintype.exists_disjointed_le {ι : Type*} [Fintype ι] (f : ι -> α) :
    exists g, g <= f ∧ univ.sup g = univ.sup f ∧ Pairwise (Disjoint on g) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- do `ι = ∅` separately since `⊤ : Fin n` isn't defined for `n = 0`
    exact ⟨f, le_rfl, rfl, Subsingleton.pairwise⟩
  let R : ι ≃ Fin _ := equivFin ι
  let f' : Fin _ -> α := f ∘ R.symm
  have hf' : f = f' ∘ R := by ext; simp only [Function.comp_apply, Equiv.symm_apply_apply, f']
  refine ⟨disjointed f' ∘ R, ?_, ?_, ?_⟩
  · intro n
    simpa only [hf'] using! disjointed_le f' (R n)
  · simpa only [← sup_image, image_univ_equiv, hf'] using! sup_disjointed f'
  · exact fun i j hij => disjoint_disjointed f' (R.injective.ne hij)

end GeneralizedBooleanAlgebra

section CompleteBooleanAlgebra

/-! ### Complete Boolean algebras -/

variable [CompleteBooleanAlgebra α]

/--
theorem `iSup_disjointed` / 定理 `iSup_disjointed`

English:
theorem iSup_disjointed
  given: [PartialOrder ι] [LocallyFiniteOrderBot ι] (f : ι -> α)
  proof: iSup_eq_iSup_of_partialSups_eq_partialSups (partialSups_disjointed f)

中文:
定理 iSup_disjointed
  条件: [PartialOrder ι] [LocallyFiniteOrderBot ι] (f : ι -> α)
  证明: iSup_eq_iSup_of_partialSups_eq_partialSups (partialSups_disjointed f)

Depends on / 依赖: iSup_eq_iSup_of_partialSups_eq_partialSups, partialSups_disjointed
-/
theorem iSup_disjointed [PartialOrder ι] [LocallyFiniteOrderBot ι] (f : ι -> α) :
    ⨆ i, disjointed f i = ⨆ i, f i :=
  iSup_eq_iSup_of_partialSups_eq_partialSups (partialSups_disjointed f)

/--
theorem `disjointed_eq_inf_compl` / 定理 `disjointed_eq_inf_compl`

English:
theorem disjointed_eq_inf_compl
  given: [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> α) (i : ι)
  proof: by
  simp only [disjointed_apply, Finset.sup_eq_iSup, mem_Iio, sdiff_eq, compl_iSup]

中文:
定理 disjointed_eq_inf_compl
  条件: [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> α) (i : ι)
  证明: by
  simp only [disjointed_apply, Finset.sup_eq_iSup, mem_Iio, sdiff_eq, compl_iSup]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, compl_iSup, disjointed_apply, mem_Iio, sdiff_eq, sup_eq_iSup
-/
theorem disjointed_eq_inf_compl [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> α) (i : ι) :
    disjointed f i = f i ⊓ ⨅ j < i, (f j)ᶜ := by
  simp only [disjointed_apply, Finset.sup_eq_iSup, mem_Iio, sdiff_eq, compl_iSup]

end CompleteBooleanAlgebra

section Set


/--
theorem `disjointed_subset` / 定理 `disjointed_subset`

English:
theorem disjointed_subset
  given: [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) (i : ι)
  proof: disjointed_le f i

中文:
定理 disjointed_subset
  条件: [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) (i : ι)
  证明: disjointed_le f i

Depends on / 依赖: disjointed_le
-/
theorem disjointed_subset [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) (i : ι) :
    disjointed f i subseteq f i :=
  disjointed_le f i

/--
theorem `iUnion_disjointed` / 定理 `iUnion_disjointed`

English:
theorem iUnion_disjointed
  given: [PartialOrder ι] [LocallyFiniteOrderBot ι] {f : ι -> Set α}
  proof: iSup_disjointed f

中文:
定理 iUnion_disjointed
  条件: [PartialOrder ι] [LocallyFiniteOrderBot ι] {f : ι -> Set α}
  证明: iSup_disjointed f

Depends on / 依赖: iSup_disjointed
-/
theorem iUnion_disjointed [PartialOrder ι] [LocallyFiniteOrderBot ι] {f : ι -> Set α} :
    ⋃ i, disjointed f i = ⋃ i, f i :=
  iSup_disjointed f

/--
theorem `disjointed_eq_inter_compl` / 定理 `disjointed_eq_inter_compl`

English:
theorem disjointed_eq_inter_compl
  given: [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) (i : ι)
  proof: disjointed_eq_inf_compl f i

中文:
定理 disjointed_eq_inter_compl
  条件: [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) (i : ι)
  证明: disjointed_eq_inf_compl f i

Depends on / 依赖: disjointed_eq_inf_compl
-/
theorem disjointed_eq_inter_compl [Preorder ι] [LocallyFiniteOrderBot ι] (f : ι -> Set α) (i : ι) :
    disjointed f i = f i inter ⋂ j < i, (f j)ᶜ :=
  disjointed_eq_inf_compl f i

/--
theorem `preimage_find_eq_disjointed` / 定理 `preimage_find_eq_disjointed`

English:
theorem preimage_find_eq_disjointed
  statement: (s : Nat -> Set α) (H : forall x, exists n, x in s n)
  proof: by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]

中文:
定理 preimage_find_eq_disjointed
  结论: (s : 自然数 -> Set α) (H : 对任意 x, 存在 n, x in s n)
  证明: by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]

Depends on / 依赖: Nat.find_eq_iff, disjointed_eq_inter_compl, find_eq_iff
-/
theorem preimage_find_eq_disjointed (s : Nat -> Set α) (H : forall x, exists n, x in s n)
    [forall x n, Decidable (x in s n)] (n : Nat) : (fun x => Nat.find (H x)) ⁻¹' {n} = disjointed s n := by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]

end Set

section Nat

/-!
### Functions on `ℕ`

(See also `Mathlib/Algebra/Order/Disjointed.lean` for results with more algebra pre-requisites.)
-/

variable [GeneralizedBooleanAlgebra α]

@[simp]
/--
theorem `disjointed_zero` / 定理 `disjointed_zero`

English:
theorem disjointed_zero
  given: (f : Nat -> α)
  statement: disjointed f 0 = f 0
  proof: disjointed_bot f

中文:
定理 disjointed_zero
  条件: (f : 自然数 -> α)
  结论: disjointed f 0 = f 0
  证明: disjointed_bot f

Depends on / 依赖: disjointed_bot
-/
theorem disjointed_zero (f : Nat -> α) : disjointed f 0 = f 0 :=
  disjointed_bot f

end Nat
