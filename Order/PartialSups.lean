/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Finset.Max

import Mathlib.Data.Fintype.Order

/-!
# The monotone sequence of partial supremums of a sequence

For `ι` a preorder in which all bounded-above intervals are finite (such as `ℕ`), and `α` a
`⊔`-semilattice, we define `partialSups : (ι → α) → ι →o α` by the formula
`partialSups f i = (Finset.Iic i).sup' ⋯ f`, where the `⋯` denotes a proof that `Finset.Iic i` is
nonempty. This is a way of spelling `⊔ k ≤ i, f k` which does not require a `α` to have a bottom
element, and makes sense in conditionally-complete lattices (where indexed suprema over sets are
badly-behaved).

Under stronger hypotheses on `α` and `ι`, we show that this coincides with other candidate
definitions, see e.g. `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range`.

We show this construction gives a Galois insertion between functions `ι → α` and monotone functions
`ι →o α`, see `partialSups.gi`.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because:
* Starting at `⊥` requires... having a bottom element.
* `fun f i ↦ (Finset.Iio i).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

-/

@[expose] public section

open Finset

variable {α β ι : Type*}

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β]

section Preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

/--
Definition of `partialSups` / `partialSups` 的定义

English:
definition partialSups
  signature: (f : ι -> α)
  body: (Iic i).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic

中文:
定义 partialSups
  签名: (f : ι -> α)
  定义体: (Iic i).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic

Depends on / 依赖: nonempty_Iic
-/
def partialSups (f : ι -> α) : ι ->o α where
  toFun i := (Iic i).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic

/--
lemma `partialSups_apply` / 引理 `partialSups_apply`

English:
lemma partialSups_apply
  given: (f : ι -> α) (i : ι)
  proof: rfl

中文:
引理 partialSups_apply
  条件: (f : ι -> α) (i : ι)
  证明: rfl
-/
lemma partialSups_apply (f : ι -> α) (i : ι) :
    partialSups f i = (Iic i).sup' nonempty_Iic f :=
  rfl

/--
lemma `partialSups_iff_forall` / 引理 `partialSups_iff_forall`

English:
lemma partialSups_iff_forall
  statement: {f : ι -> α} (p : α -> Prop)
  proof: by
  rw [partialSups_apply]; rw [apply_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p]; rw [sup'_eq_sup]
  · change (Iic i).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl

@[simp]

中文:
引理 partialSups_iff_对任意
  结论: {f : ι -> α} (p : α -> 命题)
  证明: by
  rw [partialSups_apply]; rw [apply_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p]; rw [sup'_eq_sup]
  · change (Iic i).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl

@[simp]

Depends on / 依赖: Finset, Finset.inf_eq_iInf, _comp, _eq_sup, apply_sup, inf_eq_iInf, partialSups_apply
-/
lemma partialSups_iff_forall {f : ι -> α} (p : α -> Prop)
    (hp : forall {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} :
    p (partialSups f i) ↔ forall j <= i, p (f j) := by
  rw [partialSups_apply]; rw [apply_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p]; rw [sup'_eq_sup]
  · change (Iic i).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl

@[simp]
/--
lemma `partialSups_le_iff` / 引理 `partialSups_le_iff`

English:
lemma partialSups_le_iff
  given: {f : ι -> α} {i : ι} {a : α}
  proof: partialSups_iff_forall (· <= a) sup_le_iff

中文:
引理 partialSups_le_iff
  条件: {f : ι -> α} {i : ι} {a : α}
  证明: partialSups_iff_forall (· <= a) sup_le_iff

Depends on / 依赖: CommRing, IsReduced, IsSemisimpleRing, partialSups_iff_forall, sup_le_iff
-/
lemma partialSups_le_iff {f : ι -> α} {i : ι} {a : α} :
    partialSups f i <= a ↔ forall j <= i, f j <= a :=
  partialSups_iff_forall (· <= a) sup_le_iff

/--
theorem `le_partialSups_of_le` / 定理 `le_partialSups_of_le`

English:
theorem le_partialSups_of_le
  given: (f : ι -> α) {i j : ι} (h : i <= j)
  proof: partialSups_le_iff.1 le_rfl i h

中文:
定理 le_partialSups_of_le
  条件: (f : ι -> α) {i j : ι} (h : i <= j)
  证明: partialSups_le_iff.1 le_rfl i h

Depends on / 依赖: le_rfl, partialSups_le_iff
-/
theorem le_partialSups_of_le (f : ι -> α) {i j : ι} (h : i <= j) :
    f i <= partialSups f j :=
  partialSups_le_iff.1 le_rfl i h

/--
theorem `le_partialSups` / 定理 `le_partialSups`

English:
theorem le_partialSups
  given: (f : ι -> α)
  proof: fun _ => le_partialSups_of_le f le_rfl

中文:
定理 le_partialSups
  条件: (f : ι -> α)
  证明: fun _ => le_partialSups_of_le f le_rfl

Depends on / 依赖: le_partialSups_of_le, le_rfl
-/
theorem le_partialSups (f : ι -> α) :
    f <= partialSups f :=
  fun _ => le_partialSups_of_le f le_rfl

/--
theorem `partialSups_le` / 定理 `partialSups_le`

English:
theorem partialSups_le
  given: (f : ι -> α) (i : ι) (a : α) (w : forall j <= i, f j <= a)
  proof: partialSups_le_iff.2 w

@[simp]

中文:
定理 partialSups_le
  条件: (f : ι -> α) (i : ι) (a : α) (w : 对任意 j <= i, f j <= a)
  证明: partialSups_le_iff.2 w

@[simp]

Depends on / 依赖: partialSups_le_iff
-/
theorem partialSups_le (f : ι -> α) (i : ι) (a : α) (w : forall j <= i, f j <= a) :
    partialSups f i <= a :=
  partialSups_le_iff.2 w

@[simp]
/--
lemma `upperBounds_range_partialSups` / 引理 `upperBounds_range_partialSups`

English:
lemma upperBounds_range_partialSups
  given: (f : ι -> α)
  proof: by
  ext a
  simp only [mem_upperBounds, Set.forall_mem_range, partialSups_le_iff]
  exact ⟨fun h _ => h _ _ le_rfl, fun h _ _ _ => h _⟩

@[simp]

中文:
引理 upperBounds_range_partialSups
  条件: (f : ι -> α)
  证明: by
  ext a
  simp only [mem_upperBounds, Set.forall_mem_range, partialSups_le_iff]
  exact ⟨fun h _ => h _ _ le_rfl, fun h _ _ _ => h _⟩

@[simp]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, le_rfl, mem_upperBounds, partialSups_le_iff
-/
lemma upperBounds_range_partialSups (f : ι -> α) :
    upperBounds (Set.range (partialSups f)) = upperBounds (Set.range f) := by
  ext a
  simp only [mem_upperBounds, Set.forall_mem_range, partialSups_le_iff]
  exact ⟨fun h _ => h _ _ le_rfl, fun h _ _ _ => h _⟩

@[simp]
/--
theorem `bddAbove_range_partialSups` / 定理 `bddAbove_range_partialSups`

English:
theorem bddAbove_range_partialSups
  given: {f : ι -> α}
  proof: .of_eq congr_arg Set.Nonempty upperBounds_range_partialSups f

中文:
定理 bddAbove_range_partialSups
  条件: {f : ι -> α}
  证明: .of_eq congr_arg Set.Nonempty upperBounds_range_partialSups f

Depends on / 依赖: Nonempty, Set.Nonempty, congr_arg, of_eq, upperBounds_range_partialSups
-/
theorem bddAbove_range_partialSups {f : ι -> α} :
    BddAbove (Set.range (partialSups f)) ↔ BddAbove (Set.range f) :=
.of_eq congr_arg Set.Nonempty upperBounds_range_partialSups f

/--
theorem `Monotone.partialSups_eq` / 定理 `Monotone.partialSups_eq`

English:
theorem Monotone.partialSups_eq
  given: {f : ι -> α} (hf : Monotone f)
  proof: funext fun i => le_antisymm (partialSups_le _ _ _ (@hf · i)) (le_partialSups _ _)

中文:
定理 递增.partialSups_eq
  条件: {f : ι -> α} (hf : 递增 f)
  证明: funext fun i => le_antisymm (partialSups_le _ _ _ (@hf · i)) (le_partialSups _ _)

Depends on / 依赖: le_antisymm, le_partialSups, partialSups_le
-/
theorem Monotone.partialSups_eq {f : ι -> α} (hf : Monotone f) :
    partialSups f = f :=
  funext fun i => le_antisymm (partialSups_le _ _ _ (@hf · i)) (le_partialSups _ _)

/--
theorem `partialSups_mono` / 定理 `partialSups_mono`

English:
theorem partialSups_mono
  proof: fun _ _ h _ => partialSups_le_iff.2 fun j hj => (h j).trans (le_partialSups_of_le _ hj)

中文:
定理 partialSups_mono
  证明: fun _ _ h _ => partialSups_le_iff.2 fun j hj => (h j).trans (le_partialSups_of_le _ hj)

Depends on / 依赖: le_partialSups_of_le, partialSups_le_iff
-/
theorem partialSups_mono :
    Monotone (partialSups : (ι -> α) -> ι ->o α) :=
  fun _ _ h _ => partialSups_le_iff.2 fun j hj => (h j).trans (le_partialSups_of_le _ hj)

/--
lemma `partialSups_monotone` / 引理 `partialSups_monotone`

English:
lemma partialSups_monotone
  given: (f : ι -> α)
  proof: fun i _ hnm => partialSups_le f i _ (fun _ hm'n => le_partialSups_of_le _ (hm'n.trans hnm))

中文:
引理 partialSups_monotone
  条件: (f : ι -> α)
  证明: fun i _ hnm => partialSups_le f i _ (fun _ hm'n => le_partialSups_of_le _ (hm'n.trans hnm))

Depends on / 依赖: le_partialSups_of_le, n.trans, partialSups_le
-/
lemma partialSups_monotone (f : ι -> α) :
    Monotone (partialSups f) :=
  fun i _ hnm => partialSups_le f i _ (fun _ hm'n => le_partialSups_of_le _ (hm'n.trans hnm))

/--
Definition of `partialSups.gi` / `partialSups.gi` 的定义

English:
definition partialSups.gi
  signature: :
  body: ⟨f, by convert! (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine ⟨(le_partialSups f).trans, fun h => ?_⟩
    convert! partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHo

中文:
定义 partialSups.gi
  签名: :
  定义体: ⟨f, by convert! (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine ⟨(le_partialSups f).trans, fun h => ?_⟩
    convert! partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHo

Depends on / 依赖: OrderHom, OrderHom.ext, antisymm, choice_eq, convert, g.monotone.partialSups_eq.symm, le_l_u, le_partialSups, monotone, partialSups, partialSups_eq, partialSups_mono
-/
def partialSups.gi :
    GaloisInsertion (partialSups : (ι -> α) -> ι ->o α) (↑) where
  choice f h :=
    ⟨f, by convert! (partialSups f).monotone using 1; exact (le_partialSups f).antisymm h⟩
  gc f g := by
    refine ⟨(le_partialSups f).trans, fun h => ?_⟩
    convert! partialSups_mono h
    exact OrderHom.ext _ _ g.monotone.partialSups_eq.symm
  le_l_u f := le_partialSups f
  choice_eq f h := OrderHom.ext _ _ ((le_partialSups f).antisymm h)

/--
lemma `Pi.partialSups_apply` / 引理 `Pi.partialSups_apply`

English:
lemma Pi.partialSups_apply
  statement: {τ : Type*} {π : τ -> Type*} [forall t, SemilatticeSup (π t)]
  proof: by
  simp only [partialSups_apply, Finset.sup'_apply]

中文:
引理 依赖函数类型.partialSups_apply
  结论: {τ : 类型} {π : τ -> 类型} [对任意 t, SemilatticeSup (π t)]
  证明: by
  simp only [partialSups_apply, Finset.sup'_apply]
-/
protected lemma Pi.partialSups_apply {τ : Type*} {π : τ -> Type*} [forall t, SemilatticeSup (π t)]
    (f : ι -> (t : τ) -> π t) (i : ι) (t : τ) :
    partialSups f i t = partialSups (f · t) i := by
  simp only [partialSups_apply, Finset.sup'_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `comp_partialSups` / 引理 `comp_partialSups`

English:
lemma comp_partialSups
  given: {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : ι -> α) (g : F)
  proof: by
  funext _; simp [partialSups]

中文:
引理 comp_partialSups
  条件: {F : 类型} [函数状 F α β] [并态射类 F α β] (f : ι -> α) (g : F)
  证明: by
  funext _; simp [partialSups]

Depends on / 依赖: partialSups
-/
lemma comp_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : ι -> α) (g : F) :
    partialSups (g ∘ f) = g ∘ partialSups f := by
  funext _; simp [partialSups]

/--
lemma `map_partialSups` / 引理 `map_partialSups`

English:
lemma map_partialSups
  given: {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) (g : ι -> α) (i : ι)
  proof: congr($(comp_partialSups ..) i)

中文:
引理 map_partialSups
  条件: {F : 类型} [函数状 F α β] [并态射类 F α β] (f : F) (g : ι -> α) (i : ι)
  证明: congr($(comp_partialSups ..) i)

Depends on / 依赖: comp_partialSups
-/
lemma map_partialSups {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) (g : ι -> α) (i : ι) :
    partialSups (fun j => f (g j)) i = f (partialSups g i) := congr($(comp_partialSups ..) i)

end Preorder

@[simp]
/--
theorem `partialSups_succ` / 定理 `partialSups_succ`

English:
theorem partialSups_succ
  statement: [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι]
  proof: by
  suffices Iic (Order.succ i) = Iic i union {Order.succ i} by simp only [partialSups_apply, this,
    sup'_union nonempty_Iic ⟨_, mem_singleton_self _⟩ f, sup'_singleton]
  ext
  simp only [mem_Iic, mem_union, mem_singleton]
  constructor
  · exact fun h => (Order.le_succ_iff_eq_or_le.mp h).symm


中文:
定理 partialSups_succ
  结论: [线性序 ι] [LocallyFiniteOrderBot ι] [Succ序 ι]
  证明: by
  suffices Iic (Order.succ i) = Iic i union {Order.succ i} by simp only [partialSups_apply, this,
    sup'_union nonempty_Iic ⟨_, mem_singleton_self _⟩ f, sup'_singleton]
  ext
  simp only [mem_Iic, mem_union, mem_singleton]
  constructor
  · exact fun h => (Order.le_succ_iff_eq_or_le.mp h).symm


Depends on / 依赖: Order.le_succ, Order.le_succ_iff_eq_or_le.mp, Order.succ, _singleton, _union, h.elim, le_of_eq, le_succ, le_succ_iff_eq_or_le, le_trans, mem_Iic, mem_singleton, mem_singleton_self, mem_union, nonempty_Iic, partialSups_apply
-/
theorem partialSups_succ [LinearOrder ι] [LocallyFiniteOrderBot ι] [SuccOrder ι]
    (f : ι -> α) (i : ι) :
    partialSups f (Order.succ i) = partialSups f i ⊔ f (Order.succ i) := by
  suffices Iic (Order.succ i) = Iic i union {Order.succ i} by simp only [partialSups_apply, this,
    sup'_union nonempty_Iic ⟨_, mem_singleton_self _⟩ f, sup'_singleton]
  ext
  simp only [mem_Iic, mem_union, mem_singleton]
  constructor
  · exact fun h => (Order.le_succ_iff_eq_or_le.mp h).symm
  · exact fun h => h.elim (le_trans · <| Order.le_succ _) le_of_eq

@[simp]
/--
theorem `partialSups_bot` / 定理 `partialSups_bot`

English:
theorem partialSups_bot
  statement: [PartialOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
  proof: by
  simp only [partialSups_apply]
  -- should we add a lemma `Finset.Iic_bot`?
  suffices Iic (⊥ : ι) = {⊥} by simp only [this, sup'_singleton]
  simp only [← coe_eq_singleton, coe_Iic, Set.Iic_bot]

中文:
定理 partialSups_bot
  结论: [偏序 ι] [局部有限序 ι] [有底序 ι]
  证明: by
  simp only [partialSups_apply]
  -- should we add a lemma `Finset.Iic_bot`?
  suffices Iic (⊥ : ι) = {⊥} by simp only [this, sup'_singleton]
  simp only [← coe_eq_singleton, coe_Iic, Set.Iic_bot]

Depends on / 依赖: partialSups_apply
-/
theorem partialSups_bot [PartialOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    (f : ι -> α) : partialSups f ⊥ = f ⊥ := by
  simp only [partialSups_apply]
  -- should we add a lemma `Finset.Iic_bot`?
  suffices Iic (⊥ : ι) = {⊥} by simp only [this, sup'_singleton]
  simp only [← coe_eq_singleton, coe_Iic, Set.Iic_bot]

/-!
### Functions out of `ℕ`
-/

@[simp]
/--
theorem `partialSups_zero` / 定理 `partialSups_zero`

English:
theorem partialSups_zero
  given: (f : Nat -> α)
  statement: partialSups f 0 = f 0
  proof: partialSups_bot f

中文:
定理 partialSups_zero
  条件: (f : 自然数 -> α)
  结论: partialSups f 0 = f 0
  证明: partialSups_bot f

Depends on / 依赖: partialSups_bot
-/
theorem partialSups_zero (f : Nat -> α) : partialSups f 0 = f 0 :=
  partialSups_bot f

/--
theorem `partialSups_eq_sup'_range` / 定理 `partialSups_eq_sup'_range`

English:
theorem partialSups_eq_sup'_range
  given: (f : Nat -> α) (n : Nat)
  proof: eq_of_forall_ge_iff fun _ => by simp [Nat.lt_succ_iff]

中文:
定理 partialSups_eq_sup'_range
  条件: (f : 自然数 -> α) (n : 自然数)
  证明: eq_of_forall_ge_iff fun _ => by simp [Nat.lt_succ_iff]

Depends on / 依赖: Nat.lt_succ_iff, eq_of_forall_ge_iff, lt_succ_iff
-/
theorem partialSups_eq_sup'_range (f : Nat -> α) (n : Nat) :
    partialSups f n = (Finset.range (n + 1)).sup' nonempty_range_add_one f :=
  eq_of_forall_ge_iff fun _ => by simp [Nat.lt_succ_iff]

/--
theorem `partialSups_eq_sup_range` / 定理 `partialSups_eq_sup_range`

English:
theorem partialSups_eq_sup_range
  given: [OrderBot α] (f : Nat -> α) (n : Nat)
  proof: eq_of_forall_ge_iff fun _ => by simp [Nat.lt_succ_iff]

中文:
定理 partialSups_eq_sup_range
  条件: [有底序 α] (f : 自然数 -> α) (n : 自然数)
  证明: eq_of_forall_ge_iff fun _ => by simp [Nat.lt_succ_iff]

Depends on / 依赖: Nat.lt_succ_iff, eq_of_forall_ge_iff, lt_succ_iff
-/
theorem partialSups_eq_sup_range [OrderBot α] (f : Nat -> α) (n : Nat) :
    partialSups f n = (Finset.range (n + 1)).sup f :=
  eq_of_forall_ge_iff fun _ => by simp [Nat.lt_succ_iff]

end SemilatticeSup

section DistribLattice

/-!
### Functions valued in a distributive lattice

These lemmas require the target to be a distributive lattice, so they are not useful (or true) in
situations such as submodules.
-/

variable [Preorder ι] [LocallyFiniteOrderBot ι] [DistribLattice α] [OrderBot α]

@[simp]
/--
lemma `disjoint_partialSups_left` / 引理 `disjoint_partialSups_left`

English:
lemma disjoint_partialSups_left
  given: {f : ι -> α} {i : ι} {x : α}
  proof: partialSups_iff_forall (Disjoint · x) disjoint_sup_left

@[simp]

中文:
引理 disjoint_partialSups_left
  条件: {f : ι -> α} {i : ι} {x : α}
  证明: partialSups_iff_forall (Disjoint · x) disjoint_sup_left

@[simp]

Depends on / 依赖: Disjoint, disjoint_sup_left, partialSups_iff_forall
-/
lemma disjoint_partialSups_left {f : ι -> α} {i : ι} {x : α} :
    Disjoint (partialSups f i) x ↔ forall j <= i, Disjoint (f j) x :=
  partialSups_iff_forall (Disjoint · x) disjoint_sup_left

@[simp]
/--
lemma `disjoint_partialSups_right` / 引理 `disjoint_partialSups_right`

English:
lemma disjoint_partialSups_right
  given: {f : ι -> α} {i : ι} {x : α}
  proof: partialSups_iff_forall (Disjoint x) disjoint_sup_right

中文:
引理 disjoint_partialSups_right
  条件: {f : ι -> α} {i : ι} {x : α}
  证明: partialSups_iff_forall (Disjoint x) disjoint_sup_right

Depends on / 依赖: Disjoint, disjoint_sup_right, partialSups_iff_forall
-/
lemma disjoint_partialSups_right {f : ι -> α} {i : ι} {x : α} :
    Disjoint x (partialSups f i) ↔ forall j <= i, Disjoint x (f j) :=
  partialSups_iff_forall (Disjoint x) disjoint_sup_right

open scoped Function in -- required for scoped `on` notation
/--
theorem `partialSups_disjoint_of_disjoint` / 定理 `partialSups_disjoint_of_disjoint`

English:
theorem partialSups_disjoint_of_disjoint
  statement: (f : ι -> α) (h : Pairwise (Disjoint on f))
  proof: disjoint_partialSups_left.2 fun _ hk => h (hk.trans_lt hij).ne

中文:
定理 partialSups_disjoint_of_disjoint
  结论: (f : ι -> α) (h : 两两 (Disjoint on f))
  证明: disjoint_partialSups_left.2 fun _ hk => h (hk.trans_lt hij).ne

Depends on / 依赖: disjoint_partialSups_left, hk.trans_lt, trans_lt
-/
theorem partialSups_disjoint_of_disjoint (f : ι -> α) (h : Pairwise (Disjoint on f))
    {i j : ι} (hij : i < j) :
    Disjoint (partialSups f i) (f j) :=
  disjoint_partialSups_left.2 fun _ hk => h (hk.trans_lt hij).ne

end DistribLattice

section ConditionallyCompleteLattice

/-!
### Lemmas about the supremum over the whole domain

These lemmas require some completeness assumptions on the target space.
-/
variable [Preorder ι] [LocallyFiniteOrderBot ι]

/--
theorem `partialSups_eq_ciSup_Iic` / 定理 `partialSups_eq_ciSup_Iic`

English:
theorem partialSups_eq_ciSup_Iic
  given: [ConditionallyCompleteLattice α] (f : ι -> α) (i : ι)
  proof: by
  simp only [partialSups_apply]
  apply le_antisymm
  · exact sup'_le _ _ fun j hj => Finite.le_ciSup_of_le
      ⟨j, by simpa only [Set.mem_Iic, mem_Iic] using hj⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ => le_sup' f (by simpa only [mem_Iic, Set.mem_Iic] using hj)

@[simp]

中文:
定理 partialSups_eq_ciSup_Iic
  条件: [条件完备格 α] (f : ι -> α) (i : ι)
  证明: by
  simp only [partialSups_apply]
  apply le_antisymm
  · exact sup'_le _ _ fun j hj => Finite.le_ciSup_of_le
      ⟨j, by simpa only [Set.mem_Iic, mem_Iic] using hj⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ => le_sup' f (by simpa only [mem_Iic, Set.mem_Iic] using hj)

@[simp]

Depends on / 依赖: Finite, Finite.le_ciSup_of_le, Set.mem_Iic, ciSup_le, le_antisymm, le_ciSup_of_le, le_rfl, le_sup, mem_Iic, partialSups_apply
-/
theorem partialSups_eq_ciSup_Iic [ConditionallyCompleteLattice α] (f : ι -> α) (i : ι) :
    partialSups f i = ⨆ i : Set.Iic i, f i := by
  simp only [partialSups_apply]
  apply le_antisymm
  · exact sup'_le _ _ fun j hj => Finite.le_ciSup_of_le
      ⟨j, by simpa only [Set.mem_Iic, mem_Iic] using hj⟩ le_rfl
  · exact ciSup_le fun ⟨j, hj⟩ => le_sup' f (by simpa only [mem_Iic, Set.mem_Iic] using hj)

@[simp]
/--
theorem `ciSup_partialSups_eq` / 定理 `ciSup_partialSups_eq`

English:
theorem ciSup_partialSups_eq
  statement: [ConditionallyCompleteLattice α]
  proof: by
  by_cases hι : Nonempty ι
  · refine (ciSup_le fun i => ?_).antisymm (ciSup_mono ?_ <| le_partialSups f)
    · simpa only [partialSups_eq_ciSup_Iic] using ciSup_le fun i => le_ciSup h _
    · rwa [bddAbove_range_partialSups]
  · exact congr_arg _ (funext (not_nonempty_iff.mp hι).elim)

中文:
定理 ciSup_partialSups_eq
  结论: [条件完备格 α]
  证明: by
  by_cases hι : Nonempty ι
  · refine (ciSup_le fun i => ?_).antisymm (ciSup_mono ?_ <| le_partialSups f)
    · simpa only [partialSups_eq_ciSup_Iic] using ciSup_le fun i => le_ciSup h _
    · rwa [bddAbove_range_partialSups]
  · exact congr_arg _ (funext (not_nonempty_iff.mp hι).elim)

Depends on / 依赖: Nonempty, antisymm, bddAbove_range_partialSups, ciSup_le, ciSup_mono, congr_arg, le_ciSup, le_partialSups, not_nonempty_iff, not_nonempty_iff.mp, partialSups_eq_ciSup_Iic
-/
theorem ciSup_partialSups_eq [ConditionallyCompleteLattice α]
    {f : ι -> α} (h : BddAbove (Set.range f)) :
    ⨆ i, partialSups f i = ⨆ i, f i := by
  by_cases hι : Nonempty ι
  · refine (ciSup_le fun i => ?_).antisymm (ciSup_mono ?_ <| le_partialSups f)
    · simpa only [partialSups_eq_ciSup_Iic] using ciSup_le fun i => le_ciSup h _
    · rwa [bddAbove_range_partialSups]
  · exact congr_arg _ (funext (not_nonempty_iff.mp hι).elim)

/-- Version of `ciSup_partialSups_eq` without boundedness assumptions, but requiring a
`ConditionallyCompleteLinearOrder` rather than just a `ConditionallyCompleteLattice`. -/
@[simp]
/--
theorem `ciSup_partialSups_eq'` / 定理 `ciSup_partialSups_eq'`

English:
theorem ciSup_partialSups_eq'
  given: [ConditionallyCompleteLinearOrder α] (f : ι -> α)
  proof: by
  by_cases h : BddAbove (Set.range f)
  · exact ciSup_partialSups_eq h
  · rw [iSup, iSup, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ h,
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _
        (bddAbove_range_partialSups.not.mpr h)]

中文:
定理 ciSup_partialSups_eq'
  条件: [条件完备线性序 α] (f : ι -> α)
  证明: by
  by_cases h : BddAbove (Set.range f)
  · exact ciSup_partialSups_eq h
  · rw [iSup, iSup, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ h,
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _
        (bddAbove_range_partialSups.not.mpr h)]

Depends on / 依赖: BddAbove, ConditionallyCompleteLinearOrder, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove, Set.range, bddAbove_range_partialSups, bddAbove_range_partialSups.not.mpr, ciSup_partialSups_eq, csSup_of_not_bddAbove
-/
theorem ciSup_partialSups_eq' [ConditionallyCompleteLinearOrder α] (f : ι -> α) :
    ⨆ i, partialSups f i = ⨆ i, f i := by
  by_cases h : BddAbove (Set.range f)
  · exact ciSup_partialSups_eq h
  · rw [iSup, iSup, ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _ h,
      ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove _
        (bddAbove_range_partialSups.not.mpr h)]

end ConditionallyCompleteLattice

section CompleteLattice

variable [Preorder ι] [LocallyFiniteOrderBot ι] [CompleteLattice α]

/--
theorem `iSup_partialSups_eq` / 定理 `iSup_partialSups_eq`

English:
theorem iSup_partialSups_eq
  given: (f : ι -> α)
  proof: ciSup_partialSups_eq OrderTop.bddAbove _

中文:
定理 iSup_partialSups_eq
  条件: (f : ι -> α)
  证明: ciSup_partialSups_eq OrderTop.bddAbove _

Depends on / 依赖: OrderTop, OrderTop.bddAbove, bddAbove, ciSup_partialSups_eq
-/
theorem iSup_partialSups_eq (f : ι -> α) :
    ⨆ i, partialSups f i = ⨆ i, f i :=
ciSup_partialSups_eq OrderTop.bddAbove _

/--
theorem `partialSups_eq_biSup` / 定理 `partialSups_eq_biSup`

English:
theorem partialSups_eq_biSup
  given: (f : ι -> α) (i : ι)
  proof: by
  simpa only [iSup_subtype] using! partialSups_eq_ciSup_Iic f i

中文:
定理 partialSups_eq_biSup
  条件: (f : ι -> α) (i : ι)
  证明: by
  simpa only [iSup_subtype] using! partialSups_eq_ciSup_Iic f i

Depends on / 依赖: iSup_subtype, partialSups_eq_ciSup_Iic
-/
theorem partialSups_eq_biSup (f : ι -> α) (i : ι) :
    partialSups f i = ⨆ j <= i, f j := by
  simpa only [iSup_subtype] using! partialSups_eq_ciSup_Iic f i

/--
theorem `iSup_le_iSup_of_partialSups_le_partialSups` / 定理 `iSup_le_iSup_of_partialSups_le_partialSups`

English:
theorem iSup_le_iSup_of_partialSups_le_partialSups
  statement: {f g : ι -> α}
  proof: by
  rw [← iSup_partialSups_eq f]; rw [← iSup_partialSups_eq g]
  exact iSup_mono h

中文:
定理 iSup_le_iSup_of_partialSups_le_partialSups
  结论: {f g : ι -> α}
  证明: by
  rw [← iSup_partialSups_eq f]; rw [← iSup_partialSups_eq g]
  exact iSup_mono h

Depends on / 依赖: iSup_mono, iSup_partialSups_eq
-/
theorem iSup_le_iSup_of_partialSups_le_partialSups {f g : ι -> α}
    (h : partialSups f <= partialSups g) : ⨆ i, f i <= ⨆ i, g i := by
  rw [← iSup_partialSups_eq f]; rw [← iSup_partialSups_eq g]
  exact iSup_mono h

/--
theorem `iSup_eq_iSup_of_partialSups_eq_partialSups` / 定理 `iSup_eq_iSup_of_partialSups_eq_partialSups`

English:
theorem iSup_eq_iSup_of_partialSups_eq_partialSups
  statement: {f g : ι -> α}
  proof: by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]

中文:
定理 iSup_eq_iSup_of_partialSups_eq_partialSups
  结论: {f g : ι -> α}
  证明: by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]

Depends on / 依赖: iSup_partialSups_eq, simp_rw
-/
theorem iSup_eq_iSup_of_partialSups_eq_partialSups {f g : ι -> α}
    (h : partialSups f = partialSups g) : ⨆ i, f i = ⨆ i, g i := by
  simp_rw [← iSup_partialSups_eq f, ← iSup_partialSups_eq g, h]

end CompleteLattice

section Set

/--
lemma `partialSups_eq_sUnion_image` / 引理 `partialSups_eq_sUnion_image`

English:
lemma partialSups_eq_sUnion_image
  given: (s : Nat -> Set α) (n : Nat)
  proof: by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

中文:
引理 partialSups_eq_sUnion_image
  条件: (s : 自然数 -> 集合 α) (n : 自然数)
  证明: by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

Depends on / 依赖: Nat.lt_succ_iff, lt_succ_iff, partialSups_eq_biSup
-/
lemma partialSups_eq_sUnion_image (s : Nat -> Set α) (n : Nat) :
    partialSups s n = ⋃₀ ↑((Finset.range (n + 1)).image s) := by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

/--
lemma `partialSups_eq_biUnion_range` / 引理 `partialSups_eq_biUnion_range`

English:
lemma partialSups_eq_biUnion_range
  given: (s : Nat -> Set α) (n : Nat)
  proof: by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

中文:
引理 partialSups_eq_biUnion_range
  条件: (s : 自然数 -> 集合 α) (n : 自然数)
  证明: by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

Depends on / 依赖: Nat.lt_succ_iff, lt_succ_iff, partialSups_eq_biSup
-/
lemma partialSups_eq_biUnion_range (s : Nat -> Set α) (n : Nat) :
    partialSups s n = ⋃ i in Finset.range (n + 1), s i := by
  simp [partialSups_eq_biSup, Nat.lt_succ_iff]

end Set

section LinearOrder
/-!
### Functions taking values on some `LinearOrder`.
-/

variable [Preorder ι] [LocallyFiniteOrderBot ι] [LinearOrder α]

/--
theorem `exists_partialSups_eq` / 定理 `exists_partialSups_eq`

English:
theorem exists_partialSups_eq
  given: (f : ι -> α) (i : ι)
  proof: by
  obtain ⟨j, hj_mem, hj_le⟩ : exists j in Finset.Iic i, forall k in Finset.Iic i, f k <= f j :=
    Finset.exists_max_image _ _ ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  simp only [Finset.mem_Iic] at hj_mem hj_le
  use j, hj_mem
  apply le_antisymm
  · exact partialSups_le _ _ _ fun k hk => hj_le k hk
  ·

中文:
定理 存在_partialSups_eq
  条件: (f : ι -> α) (i : ι)
  证明: by
  obtain ⟨j, hj_mem, hj_le⟩ : exists j in Finset.Iic i, forall k in Finset.Iic i, f k <= f j :=
    Finset.exists_max_image _ _ ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  simp only [Finset.mem_Iic] at hj_mem hj_le
  use j, hj_mem
  apply le_antisymm
  · exact partialSups_le _ _ _ fun k hk => hj_le k hk
  ·

Depends on / 依赖: Finset, Finset.Iic, Finset.exists_max_image, Finset.mem_Iic, Finset.mem_Iic.mpr, exists_max_image, hj_le, hj_mem, le_antisymm, le_partialSups_of_le, le_rfl, mem_Iic, partialSups_le
-/
theorem exists_partialSups_eq (f : ι -> α) (i : ι) :
    exists j <= i, partialSups f i = f j := by
  obtain ⟨j, hj_mem, hj_le⟩ : exists j in Finset.Iic i, forall k in Finset.Iic i, f k <= f j :=
    Finset.exists_max_image _ _ ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  simp only [Finset.mem_Iic] at hj_mem hj_le
  use j, hj_mem
  apply le_antisymm
  · exact partialSups_le _ _ _ fun k hk => hj_le k hk
  · exact le_partialSups_of_le f hj_mem

end LinearOrder
