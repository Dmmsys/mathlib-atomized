/-
Copyright (c) 2020 Jean Lo, Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Topology.Bornology.Basic

/-!
# Absorption of sets

Let `M` act on `α`, let `A` and `B` be sets in `α`.
We say that `A` *absorbs* `B` if for sufficiently large `a : M`, we have `B ⊆ a • A`.
Formally, "for sufficiently large `a : M`" means "for all but a bounded set of `a`".

Traditionally, this definition is formulated
for the action of a (semi)normed ring on a module over that ring.

We formulate it in a more general settings for two reasons:

- this way we don't have to depend on metric spaces, normed rings etc;
- some proofs look nicer with this definition than with something like
  `∃ r : ℝ, ∀ a : R, r ≤ ‖a‖ → B ⊆ a • A`.

If `M` is a `GroupWithZero` (e.g., a division ring),
the sets absorbing a given set form a filter, see `Filter.absorbing`.

## Implementation notes

For now, all theorems assume that we deal with (a generalization of) a module over a division ring.
Some lemmas have multiplicative versions for `MulDistribMulAction`s.
They can be added later when someone needs them.

## Keywords

absorbs, absorbent
-/

@[expose] public section

assert_not_exists Real

open Set Bornology Filter
open scoped Pointwise

section Defs

variable (M : Type*) {α : Type*} [Bornology M] [SMul M α]

/--
Definition of `Absorbs` / `Absorbs` 的定义

English:
definition Absorbs
  signature: (s t : Set α)
  body: forallᶠ a in cobounded M, t subseteq a • s

中文:
定义 Absorbs
  签名: (s t : 集合 α)
  定义体: forallᶠ a in cobounded M, t subseteq a • s

Depends on / 依赖: cobounded, subseteq
-/
def Absorbs (s t : Set α) : Prop :=
  forallᶠ a in cobounded M, t subseteq a • s

/--
Definition of `Absorbent` / `Absorbent` 的定义

English:
definition Absorbent
  signature: (s : Set α)
  body: forall x, Absorbs M s {x}

中文:
定义 Absorbent
  签名: (s : 集合 α)
  定义体: forall x, Absorbs M s {x}

Depends on / 依赖: Absorbs
-/
def Absorbent (s : Set α) : Prop :=
  forall x, Absorbs M s {x}

end Defs

namespace Absorbs

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s s₁ s₂ t t₁ t₂ : Set α} {S T : Set (Set α)}

/--
lemma `empty` / 引理 `empty`

English:
lemma empty
  statement: Absorbs M s ∅
  proof: by simp [Absorbs]

中文:
引理 empty
  结论: Absorbs M s ∅
  证明: by simp [Absorbs]
-/
protected lemma empty : Absorbs M s ∅ := by simp [Absorbs]

/--
lemma `eventually` / 引理 `eventually`

English:
lemma eventually
  given: (h : Absorbs M s t)
  statement: forallᶠ a in cobounded M, t subseteq a • s
  proof: h

中文:
引理 eventually
  条件: (h : Absorbs M s t)
  结论: 对任意ᶠ a in cobounded M, t subseteq a • s
  证明: h
-/
protected lemma eventually (h : Absorbs M s t) : forallᶠ a in cobounded M, t subseteq a • s := h

/--
lemma `of_boundedSpace` / 引理 `of_boundedSpace`

English:
lemma of_boundedSpace
  given: [BoundedSpace M]
  statement: Absorbs M s t
  proof: by simp [Absorbs]

中文:
引理 of_boundedSpace
  条件: [有界空间 M]
  结论: Absorbs M s t
  证明: by simp [Absorbs]
-/
@[simp] lemma of_boundedSpace [BoundedSpace M] : Absorbs M s t := by simp [Absorbs]

/--
lemma `mono_left` / 引理 `mono_left`

English:
lemma mono_left
  given: (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂)
  statement: Absorbs M s₂ t
  proof: h.mono fun _a ha => ha.trans smul_set_mono hs

中文:
引理 mono_left
  条件: (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂)
  结论: Absorbs M s₂ t
  证明: h.mono fun _a ha => ha.trans smul_set_mono hs

Depends on / 依赖: h.mono, ha.trans, smul_set_mono
-/
lemma mono_left (h : Absorbs M s₁ t) (hs : s₁ subseteq s₂) : Absorbs M s₂ t :=
h.mono fun _a ha => ha.trans smul_set_mono hs

/--
lemma `mono_right` / 引理 `mono_right`

English:
lemma mono_right
  given: (h : Absorbs M s t₁) (ht : t₂ subseteq t₁)
  statement: Absorbs M s t₂
  proof: h.mono fun _ => ht.trans

中文:
引理 mono_right
  条件: (h : Absorbs M s t₁) (ht : t₂ subseteq t₁)
  结论: Absorbs M s t₂
  证明: h.mono fun _ => ht.trans

Depends on / 依赖: h.mono, ht.trans
-/
lemma mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁) : Absorbs M s t₂ :=
  h.mono fun _ => ht.trans

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: (h : Absorbs M s₁ t₁) (hs : s₁ subseteq s₂) (ht : t₂ subseteq t₁)
  statement: Absorbs M s₂ t₂
  proof: (h.mono_left hs).mono_right ht

@[simp]

中文:
引理 mono
  条件: (h : Absorbs M s₁ t₁) (hs : s₁ subseteq s₂) (ht : t₂ subseteq t₁)
  结论: Absorbs M s₂ t₂
  证明: (h.mono_left hs).mono_right ht

@[simp]

Depends on / 依赖: h.mono_left, mono_left, mono_right
-/
lemma mono (h : Absorbs M s₁ t₁) (hs : s₁ subseteq s₂) (ht : t₂ subseteq t₁) : Absorbs M s₂ t₂ :=
  (h.mono_left hs).mono_right ht

@[simp]
/--
lemma `_root_.absorbs_union` / 引理 `_root_.absorbs_union`

English:
lemma _root_.absorbs_union
  statement: Absorbs M s (t₁ union t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂
  proof: by
  simp [Absorbs]

中文:
引理 _root_.absorbs_union
  结论: Absorbs M s (t₁ union t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂
  证明: by
  simp [Absorbs]

Depends on / 依赖: Absorbs
-/
lemma _root_.absorbs_union : Absorbs M s (t₁ union t₂) ↔ Absorbs M s t₁ ∧ Absorbs M s t₂ := by
  simp [Absorbs]

/--
lemma `union` / 引理 `union`

English:
lemma union
  given: (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂)
  statement: Absorbs M s (t₁ union t₂)
  proof: absorbs_union.2 ⟨h₁, h₂⟩

中文:
引理 union
  条件: (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂)
  结论: Absorbs M s (t₁ union t₂)
  证明: absorbs_union.2 ⟨h₁, h₂⟩
-/
protected lemma union (h₁ : Absorbs M s t₁) (h₂ : Absorbs M s t₂) : Absorbs M s (t₁ union t₂) :=
  absorbs_union.2 ⟨h₁, h₂⟩

/--
lemma `_root_.Set.Finite.absorbs_sUnion` / 引理 `_root_.Set.Finite.absorbs_sUnion`

English:
lemma _root_.Set.Finite.absorbs_sUnion
  given: {T : Set (Set α)} (hT : T.Finite)
  proof: by
  simp [Absorbs, hT]

中文:
引理 _root_.集合.有限.absorbs_sUnion
  条件: {T : 集合 (集合 α)} (hT : T.有限)
  证明: by
  simp [Absorbs, hT]

Depends on / 依赖: Absorbs
-/
lemma _root_.Set.Finite.absorbs_sUnion {T : Set (Set α)} (hT : T.Finite) :
    Absorbs M s (⋃₀ T) ↔ forall t in T, Absorbs M s t := by
  simp [Absorbs, hT]

/--
lemma `sUnion` / 引理 `sUnion`

English:
lemma sUnion
  given: (hT : T.Finite) (hs : forall t in T, Absorbs M s t)
  proof: hT.absorbs_sUnion.2 hs

@[simp]

中文:
引理 集合并集
  条件: (hT : T.有限) (hs : 对任意 t in T, Absorbs M s t)
  证明: hT.absorbs_sUnion.2 hs

@[simp]
-/
protected lemma sUnion (hT : T.Finite) (hs : forall t in T, Absorbs M s t) :
    Absorbs M s (⋃₀ T) :=
  hT.absorbs_sUnion.2 hs

@[simp]
/--
lemma `_root_.absorbs_iUnion` / 引理 `_root_.absorbs_iUnion`

English:
lemma _root_.absorbs_iUnion
  given: {ι : Sort*} [Finite ι] {t : ι -> Set α}
  proof: (finite_range t).absorbs_sUnion.trans forall_mem_range

protected alias ⟨_, iUnion⟩ := absorbs_iUnion

中文:
引理 _root_.absorbs_iUnion
  条件: {ι : 类型层*} [有限 ι] {t : ι -> 集合 α}
  证明: (finite_range t).absorbs_sUnion.trans forall_mem_range

protected alias ⟨_, iUnion⟩ := absorbs_iUnion

Depends on / 依赖: absorbs_sUnion, absorbs_sUnion.trans, finite_range, forall_mem_range
-/
lemma _root_.absorbs_iUnion {ι : Sort*} [Finite ι] {t : ι -> Set α} :
    Absorbs M s (⋃ i, t i) ↔ forall i, Absorbs M s (t i) :=
  (finite_range t).absorbs_sUnion.trans forall_mem_range

protected alias ⟨_, iUnion⟩ := absorbs_iUnion

/--
lemma `_root_.Set.Finite.absorbs_biUnion` / 引理 `_root_.Set.Finite.absorbs_biUnion`

English:
lemma _root_.Set.Finite.absorbs_biUnion
  given: {ι : Type*} {t : ι -> Set α} {I : Set ι} (hI : I.Finite)
  proof: by
  simp [Absorbs, hI]

protected alias ⟨_, biUnion⟩ := Set.Finite.absorbs_biUnion

@[simp]

中文:
引理 _root_.集合.有限.absorbs_biUnion
  条件: {ι : 类型} {t : ι -> 集合 α} {I : 集合 ι} (hI : I.有限)
  证明: by
  simp [Absorbs, hI]

protected alias ⟨_, biUnion⟩ := Set.Finite.absorbs_biUnion

@[simp]

Depends on / 依赖: Absorbs
-/
lemma _root_.Set.Finite.absorbs_biUnion {ι : Type*} {t : ι -> Set α} {I : Set ι} (hI : I.Finite) :
    Absorbs M s (⋃ i in I, t i) ↔ forall i in I, Absorbs M s (t i) := by
  simp [Absorbs, hI]

protected alias ⟨_, biUnion⟩ := Set.Finite.absorbs_biUnion

@[simp]
/--
lemma `_root_.absorbs_biUnion_finset` / 引理 `_root_.absorbs_biUnion_finset`

English:
lemma _root_.absorbs_biUnion_finset
  given: {ι : Type*} {t : ι -> Set α} {I : Finset ι}
  proof: I.finite_toSet.absorbs_biUnion

protected alias ⟨_, biUnion_finset⟩ := absorbs_biUnion_finset

中文:
引理 _root_.absorbs_biUnion_finset
  条件: {ι : 类型} {t : ι -> 集合 α} {I : 有限集 ι}
  证明: I.finite_toSet.absorbs_biUnion

protected alias ⟨_, biUnion_finset⟩ := absorbs_biUnion_finset

Depends on / 依赖: I.finite_toSet.absorbs_biUnion, absorbs_biUnion, finite_toSet
-/
lemma _root_.absorbs_biUnion_finset {ι : Type*} {t : ι -> Set α} {I : Finset ι} :
    Absorbs M s (⋃ i in I, t i) ↔ forall i in I, Absorbs M s (t i) :=
  I.finite_toSet.absorbs_biUnion

protected alias ⟨_, biUnion_finset⟩ := absorbs_biUnion_finset

end SMul

section AddZero

variable {M E : Type*} [Bornology M] {s₁ s₂ t₁ t₂ : Set E}

/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: [AddZeroClass E] [DistribSMul M E]
  proof: h₂.mp h₁.eventually.mono fun x hx₁ hx₂ => by rw [smul_add]; exact add_subset_add hx₁ hx₂

中文:
引理 add
  结论: [加法零类 E] [分配标量乘法 M E]
  证明: h₂.mp h₁.eventually.mono fun x hx₁ hx₂ => by rw [smul_add]; exact add_subset_add hx₁ hx₂
-/
protected lemma add [AddZeroClass E] [DistribSMul M E]
    (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) : Absorbs M (s₁ + s₂) (t₁ + t₂) :=
h₂.mp h₁.eventually.mono fun x hx₁ hx₂ => by rw [smul_add]; exact add_subset_add hx₁ hx₂

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  given: [Zero E] [SMulZeroClass M E] {s : Set E} (hs : 0 in s)
  statement: Absorbs M s 0
  proof: Eventually.of_forall fun _ => zero_subset.2 zero_mem_smul_set hs

中文:
引理 zero
  条件: [零 E] [SMulZero类 M E] {s : 集合 E} (hs : 0 in s)
  结论: Absorbs M s 0
  证明: Eventually.of_forall fun _ => zero_subset.2 zero_mem_smul_set hs
-/
protected lemma zero [Zero E] [SMulZeroClass M E] {s : Set E} (hs : 0 in s) : Absorbs M s 0 :=
Eventually.of_forall fun _ => zero_subset.2 zero_mem_smul_set hs

end AddZero

end Absorbs

section GroupWithZero

variable {G₀ α : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]
  {s t u : Set α} {S : Set (Set α)}

@[simp]
/--
lemma `Absorbs.univ` / 引理 `Absorbs.univ`

English:
lemma Absorbs.univ
  statement: Absorbs G₀ univ s
  proof: (eventually_ne_cobounded 0).mono fun a ha => by rw [smul_set_univ₀ ha]; apply subset_univ

中文:
引理 Absorbs.univ
  结论: Absorbs G₀ univ s
  证明: (eventually_ne_cobounded 0).mono fun a ha => by rw [smul_set_univ₀ ha]; apply subset_univ
-/
protected lemma Absorbs.univ : Absorbs G₀ univ s :=
  (eventually_ne_cobounded 0).mono fun a ha => by rw [smul_set_univ₀ ha]; apply subset_univ

/--
lemma `absorbs_iff_eventually_cobounded_mapsTo` / 引理 `absorbs_iff_eventually_cobounded_mapsTo`

English:
lemma absorbs_iff_eventually_cobounded_mapsTo
  proof: eventually_congr (eventually_ne_cobounded 0).mono fun c hc => by
    rw [← preimage_smul_inv₀ hc]; rfl

alias ⟨eventually_cobounded_mapsTo, _⟩ := absorbs_iff_eventually_cobounded_mapsTo

@[simp]

中文:
引理 absorbs_iff_eventually_cobounded_mapsTo
  证明: eventually_congr (eventually_ne_cobounded 0).mono fun c hc => by
    rw [← preimage_smul_inv₀ hc]; rfl

alias ⟨eventually_cobounded_mapsTo, _⟩ := absorbs_iff_eventually_cobounded_mapsTo

@[simp]

Depends on / 依赖: eventually_congr, eventually_ne_cobounded
-/
lemma absorbs_iff_eventually_cobounded_mapsTo :
    Absorbs G₀ s t ↔ forallᶠ c in cobounded G₀, MapsTo (c⁻¹ • ·) t s :=
eventually_congr (eventually_ne_cobounded 0).mono fun c hc => by
    rw [← preimage_smul_inv₀ hc]; rfl

alias ⟨eventually_cobounded_mapsTo, _⟩ := absorbs_iff_eventually_cobounded_mapsTo

@[simp]
/--
lemma `absorbs_inter` / 引理 `absorbs_inter`

English:
lemma absorbs_inter
  statement: Absorbs G₀ (s inter t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u
  proof: by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_inter, eventually_and]

中文:
引理 absorbs_inter
  结论: Absorbs G₀ (s inter t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u
  证明: by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_inter, eventually_and]

Depends on / 依赖: absorbs_iff_eventually_cobounded_mapsTo, eventually_and, mapsTo_inter
-/
lemma absorbs_inter : Absorbs G₀ (s inter t) u ↔ Absorbs G₀ s u ∧ Absorbs G₀ t u := by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_inter, eventually_and]

/--
lemma `Absorbs.inter` / 引理 `Absorbs.inter`

English:
lemma Absorbs.inter
  given: (hs : Absorbs G₀ s u) (ht : Absorbs G₀ t u)
  statement: Absorbs G₀ (s inter t) u
  proof: absorbs_inter.2 ⟨hs, ht⟩

中文:
引理 Absorbs.inter
  条件: (hs : Absorbs G₀ s u) (ht : Absorbs G₀ t u)
  结论: Absorbs G₀ (s inter t) u
  证明: absorbs_inter.2 ⟨hs, ht⟩
-/
protected lemma Absorbs.inter (hs : Absorbs G₀ s u) (ht : Absorbs G₀ t u) : Absorbs G₀ (s inter t) u :=
  absorbs_inter.2 ⟨hs, ht⟩

variable (G₀ u) in
/--
Definition of `Filter.absorbing` / `Filter.absorbing` 的定义

English:
definition Filter.absorbing
  signature: : Filter α where
  body: {s | Absorbs G₀ s u}
  univ_sets := .univ
  sets_of_superset h := h.mono_left
  inter_sets := .inter

@[simp]

中文:
定义 滤子.absorbing
  签名: : 滤子 α where
  定义体: {s | Absorbs G₀ s u}
  univ_sets := .univ
  sets_of_superset h := h.mono_left
  inter_sets := .inter

@[simp]

Depends on / 依赖: Absorbs
-/
def Filter.absorbing : Filter α where
  sets := {s | Absorbs G₀ s u}
  univ_sets := .univ
  sets_of_superset h := h.mono_left
  inter_sets := .inter

@[simp]
/--
lemma `Filter.mem_absorbing` / 引理 `Filter.mem_absorbing`

English:
lemma Filter.mem_absorbing
  statement: s in absorbing G₀ u ↔ Absorbs G₀ s u
  proof: .rfl

中文:
引理 滤子.mem_absorbing
  结论: s in absorbing G₀ u ↔ Absorbs G₀ s u
  证明: .rfl
-/
lemma Filter.mem_absorbing : s in absorbing G₀ u ↔ Absorbs G₀ s u := .rfl

/--
lemma `Set.Finite.absorbs_sInter` / 引理 `Set.Finite.absorbs_sInter`

English:
lemma Set.Finite.absorbs_sInter
  given: (hS : S.Finite)
  proof: sInter_mem (f := absorbing G₀ t) hS

protected alias ⟨_, Absorbs.sInter⟩ := Set.Finite.absorbs_sInter

@[simp]

中文:
引理 集合.有限.absorbs_s整数er
  条件: (hS : S.有限)
  证明: sInter_mem (f := absorbing G₀ t) hS

protected alias ⟨_, Absorbs.sInter⟩ := Set.Finite.absorbs_sInter

@[simp]

Depends on / 依赖: absorbing, sInter_mem
-/
lemma Set.Finite.absorbs_sInter (hS : S.Finite) :
    Absorbs G₀ (⋂₀ S) t ↔ forall s in S, Absorbs G₀ s t :=
  sInter_mem (f := absorbing G₀ t) hS

protected alias ⟨_, Absorbs.sInter⟩ := Set.Finite.absorbs_sInter

@[simp]
/--
lemma `absorbs_iInter` / 引理 `absorbs_iInter`

English:
lemma absorbs_iInter
  given: {ι : Sort*} [Finite ι] {s : ι -> Set α}
  proof: iInter_mem (f := absorbing G₀ t)

protected alias ⟨_, Absorbs.iInter⟩ := absorbs_iInter

中文:
引理 absorbs_i整数er
  条件: {ι : 类型层*} [有限 ι] {s : ι -> 集合 α}
  证明: iInter_mem (f := absorbing G₀ t)

protected alias ⟨_, Absorbs.iInter⟩ := absorbs_iInter

Depends on / 依赖: absorbing, iInter_mem
-/
lemma absorbs_iInter {ι : Sort*} [Finite ι] {s : ι -> Set α} :
    Absorbs G₀ (⋂ i, s i) t ↔ forall i, Absorbs G₀ (s i) t :=
  iInter_mem (f := absorbing G₀ t)

protected alias ⟨_, Absorbs.iInter⟩ := absorbs_iInter

/--
lemma `Set.Finite.absorbs_biInter` / 引理 `Set.Finite.absorbs_biInter`

English:
lemma Set.Finite.absorbs_biInter
  given: {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set α}
  proof: biInter_mem (f := absorbing G₀ t) hI

protected alias ⟨_, Absorbs.biInter⟩ := Set.Finite.absorbs_biInter

@[simp]

中文:
引理 集合.有限.absorbs_bi整数er
  条件: {ι : 类型} {I : 集合 ι} (hI : I.有限) {s : ι -> 集合 α}
  证明: biInter_mem (f := absorbing G₀ t) hI

protected alias ⟨_, Absorbs.biInter⟩ := Set.Finite.absorbs_biInter

@[simp]

Depends on / 依赖: absorbing, biInter_mem
-/
lemma Set.Finite.absorbs_biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set α} :
    Absorbs G₀ (⋂ i in I, s i) t ↔ forall i in I, Absorbs G₀ (s i) t :=
  biInter_mem (f := absorbing G₀ t) hI

protected alias ⟨_, Absorbs.biInter⟩ := Set.Finite.absorbs_biInter

@[simp]
/--
lemma `absorbs_zero_iff` / 引理 `absorbs_zero_iff`

English:
lemma absorbs_zero_iff
  statement: [NeBot (cobounded G₀)]
  proof: by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, ← singleton_zero,
    mapsTo_singleton, smul_zero, eventually_const]

中文:
引理 absorbs_zero_iff
  结论: [NeBot (cobounded G₀)]
  证明: by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, ← singleton_zero,
    mapsTo_singleton, smul_zero, eventually_const]

Depends on / 依赖: absorbs_iff_eventually_cobounded_mapsTo, eventually_const, mapsTo_singleton, singleton_zero, smul_zero
-/
lemma absorbs_zero_iff [NeBot (cobounded G₀)]
    {E : Type*} [AddMonoid E] [DistribMulAction G₀ E] {s : Set E} :
    Absorbs G₀ s 0 ↔ 0 in s := by
  simp only [absorbs_iff_eventually_cobounded_mapsTo, ← singleton_zero,
    mapsTo_singleton, smul_zero, eventually_const]

end GroupWithZero

section AddGroup

variable {M E : Type*} [Monoid M] [AddGroup E] [DistribMulAction M E] [Bornology M]

@[simp]
/--
lemma `absorbs_neg_neg` / 引理 `absorbs_neg_neg`

English:
lemma absorbs_neg_neg
  given: {s t : Set E}
  statement: Absorbs M (-s) (-t) ↔ Absorbs M s t
  proof: by simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg

中文:
引理 absorbs_neg_neg
  条件: {s t : 集合 E}
  结论: Absorbs M (-s) (-t) ↔ Absorbs M s t
  证明: by simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg

Depends on / 依赖: Absorbs
-/
lemma absorbs_neg_neg {s t : Set E} : Absorbs M (-s) (-t) ↔ Absorbs M s t := by simp [Absorbs]

alias ⟨Absorbs.of_neg_neg, Absorbs.neg_neg⟩ := absorbs_neg_neg

/--
lemma `Absorbs.sub` / 引理 `Absorbs.sub`

English:
lemma Absorbs.sub
  given: {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂)
  proof: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg

中文:
引理 Absorbs.sub
  条件: {s₁ s₂ t₁ t₂ : 集合 E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂)
  证明: by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg

Depends on / 依赖: neg_neg, sub_eq_add_neg
-/
lemma Absorbs.sub {s₁ s₂ t₁ t₂ : Set E} (h₁ : Absorbs M s₁ t₁) (h₂ : Absorbs M s₂ t₂) :
    Absorbs M (s₁ - s₂) (t₁ - t₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_neg

end AddGroup

namespace Absorbent

section SMul

variable {M α : Type*} [Bornology M] [SMul M α] {s t : Set α}

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (ht : Absorbent M s) (hsub : s subseteq t)
  statement: Absorbent M t
  proof: fun x =>
  (ht x).mono_left hsub

中文:
定理 mono
  条件: (ht : Absorbent M s) (hsub : s subseteq t)
  结论: Absorbent M t
  证明: fun x =>
  (ht x).mono_left hsub
-/
protected theorem mono (ht : Absorbent M s) (hsub : s subseteq t) : Absorbent M t := fun x =>
  (ht x).mono_left hsub

/--
theorem `_root_.absorbent_iff_forall_absorbs_singleton` / 定理 `_root_.absorbent_iff_forall_absorbs_singleton`

English:
theorem _root_.absorbent_iff_forall_absorbs_singleton
  statement: Absorbent M s ↔ forall x, Absorbs M s {x}
  proof: .rfl

中文:
定理 _root_.absorbent_iff_对任意_absorbs_singleton
  结论: Absorbent M s ↔ 对任意 x, Absorbs M s {x}
  证明: .rfl
-/
theorem _root_.absorbent_iff_forall_absorbs_singleton : Absorbent M s ↔ forall x, Absorbs M s {x} := .rfl

/--
theorem `absorbs` / 定理 `absorbs`

English:
theorem absorbs
  given: (hs : Absorbent M s) {x : α}
  statement: Absorbs M s {x}
  proof: hs x

中文:
定理 absorbs
  条件: (hs : Absorbent M s) {x : α}
  结论: Absorbs M s {x}
  证明: hs x
-/
protected theorem absorbs (hs : Absorbent M s) {x : α} : Absorbs M s {x} := hs x

/--
theorem `absorbs_finite` / 定理 `absorbs_finite`

English:
theorem absorbs_finite
  given: (hs : Absorbent M s) (ht : t.Finite)
  statement: Absorbs M s t
  proof: by
  rw [← Set.biUnion_of_singleton t]
  exact .biUnion ht fun _ _ => hs.absorbs

中文:
定理 absorbs_finite
  条件: (hs : Absorbent M s) (ht : t.有限)
  结论: Absorbs M s t
  证明: by
  rw [← Set.biUnion_of_singleton t]
  exact .biUnion ht fun _ _ => hs.absorbs

Depends on / 依赖: Set.biUnion_of_singleton, absorbs, biUnion, biUnion_of_singleton, hs.absorbs
-/
theorem absorbs_finite (hs : Absorbent M s) (ht : t.Finite) : Absorbs M s t := by
  rw [← Set.biUnion_of_singleton t]
  exact .biUnion ht fun _ _ => hs.absorbs

end SMul

/--
theorem `vadd_absorbs` / 定理 `vadd_absorbs`

English:
theorem vadd_absorbs
  statement: {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E]
  proof: by
  rw [← singleton_vadd]; exact (h₁ x).add h₂

中文:
定理 vadd_absorbs
  结论: {M E : 类型} [有界结构 M] [加法零类 E] [分配标量乘法 M E]
  证明: by
  rw [← singleton_vadd]; exact (h₁ x).add h₂

Depends on / 依赖: singleton_vadd
-/
theorem vadd_absorbs {M E : Type*} [Bornology M] [AddZeroClass E] [DistribSMul M E]
    {s₁ s₂ t : Set E} {x : E} (h₁ : Absorbent M s₁) (h₂ : Absorbs M s₂ t) :
    Absorbs M (s₁ + s₂) (x +ᵥ t) := by
  rw [← singleton_vadd]; exact (h₁ x).add h₂

end Absorbent

section GroupWithZero

variable {G₀ α E : Type*} [GroupWithZero G₀] [Bornology G₀] [MulAction G₀ α]

/--
lemma `absorbent_univ` / 引理 `absorbent_univ`

English:
lemma absorbent_univ
  statement: Absorbent G₀ (univ : Set α)
  proof: fun _ => .univ

中文:
引理 absorbent_univ
  结论: Absorbent G₀ (univ : 集合 α)
  证明: fun _ => .univ
-/
lemma absorbent_univ : Absorbent G₀ (univ : Set α) := fun _ => .univ

/--
lemma `absorbent_iff_inv_smul` / 引理 `absorbent_iff_inv_smul`

English:
lemma absorbent_iff_inv_smul
  given: {s : Set α}
  proof: forall_congr' fun x => by simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_singleton]

中文:
引理 absorbent_iff_inv_smul
  条件: {s : 集合 α}
  证明: forall_congr' fun x => by simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_singleton]

Depends on / 依赖: absorbs_iff_eventually_cobounded_mapsTo, forall_congr, mapsTo_singleton
-/
lemma absorbent_iff_inv_smul {s : Set α} :
    Absorbent G₀ s ↔ forall x, forallᶠ c in cobounded G₀, c⁻¹ • x in s :=
  forall_congr' fun x => by simp only [absorbs_iff_eventually_cobounded_mapsTo, mapsTo_singleton]

/--
lemma `Absorbent.zero_mem` / 引理 `Absorbent.zero_mem`

English:
lemma Absorbent.zero_mem
  statement: [NeBot (cobounded G₀)] [AddMonoid E] [DistribMulAction G₀ E]
  proof: absorbs_zero_iff.1 (hs 0)

中文:
引理 Absorbent.zero_mem
  结论: [NeBot (cobounded G₀)] [加法幺半群 E] [分配乘法作用 G₀ E]
  证明: absorbs_zero_iff.1 (hs 0)

Depends on / 依赖: absorbs_zero_iff
-/
lemma Absorbent.zero_mem [NeBot (cobounded G₀)] [AddMonoid E] [DistribMulAction G₀ E]
    {s : Set E} (hs : Absorbent G₀ s) : (0 : E) in s :=
  absorbs_zero_iff.1 (hs 0)

end GroupWithZero

/--
theorem `Absorbs.restrict_scalars` / 定理 `Absorbs.restrict_scalars`

English:
theorem Absorbs.restrict_scalars
  proof: (hbdd.eventually h).mono fun x hx => by rwa [smul_one_smul N x s] at hx

中文:
定理 Absorbs.restrict_scalars
  证明: (hbdd.eventually h).mono fun x hx => by rwa [smul_one_smul N x s] at hx
-/
protected theorem Absorbs.restrict_scalars
    {M N α : Type*} [Monoid N] [SMul M N] [SMul M α] [MulAction N α]
    [IsScalarTower M N α] [Bornology M] [Bornology N] {s t : Set α} (h : Absorbs N s t)
    (hbdd : Tendsto (· • 1 : M -> N) (cobounded M) (cobounded N)) :
    Absorbs M s t :=
(hbdd.eventually h).mono fun x hx => by rwa [smul_one_smul N x s] at hx
