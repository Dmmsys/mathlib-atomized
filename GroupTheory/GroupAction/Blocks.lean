/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.Setoid.Partition
public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.IntervalCases

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `MulAction.IsBlock G B` states that `B : Set X` is a block,
  which means that the sets `g • B`, for `g ∈ G`, are equal or disjoint.
  Under `Group G` and `MulAction G X`, this is equivalent to the classical
  definition `MulAction.IsBlock.def_one`

- a bunch of lemmas that give examples of “trivial” blocks : ⊥, ⊤, singletons,
  and non-trivial blocks: orbit of the group, orbit of a normal subgroup…

The non-existence of nontrivial blocks is the definition of primitive actions.

## Results for actions on finite sets

- `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq` : The cardinality of a block
  multiplied by the number of its translates is the cardinal of the ambient type

- `MulAction.IsBlock.eq_univ_of_card_lt` : a too large block is equal to `Set.univ`

- `MulAction.IsBlock.subsingleton_of_card_lt` : a too small block is a subsingleton

- `MulAction.IsBlock.of_subset` : the intersections of the translates of a finite subset
  that contain a given point is a block

- `MulAction.BlockMem` : the type of blocks containing a given element

- `MulAction.BlockMem.instBoundedOrder` :
  the type of blocks containing a given element is a bounded order.

## References

We follow [Wielandt-1964].

-/

@[expose] public section

open Set
open scoped Pointwise

namespace MulAction

section orbits

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

@[to_additive]
/--
theorem `orbit.eq_or_disjoint` / 定理 `orbit.eq_or_disjoint`

English:
theorem orbit.eq_or_disjoint
  given: (a b : X)
  proof: by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp +contextual
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, eq_comm, implies_true]

@[to_additive]

中文:
定理 orbit.eq_or_disjoint
  条件: (a b : X)
  证明: by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp +contextual
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, eq_comm, implies_true]

@[to_additive]

Depends on / 依赖: Disjoint, Set.not_disjoint_iff, contextual, eq_comm, forall_exists_index, implies_true, not_disjoint_iff, orbit_eq_iff, symm.imp
-/
theorem orbit.eq_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) := by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp +contextual
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, eq_comm, implies_true]

@[to_additive]
/--
theorem `orbit.pairwiseDisjoint` / 定理 `orbit.pairwiseDisjoint`

English:
theorem orbit.pairwiseDisjoint
  proof: by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

中文:
定理 orbit.pairwiseDisjoint
  证明: by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

Depends on / 依赖: contrapose, eq_or_disjoint, orbit.eq_or_disjoint, resolve_right
-/
theorem orbit.pairwiseDisjoint :
    (Set.range fun x : X => orbit G x).PairwiseDisjoint id := by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

/-- Orbits of an element form a partition -/
@[to_additive /-- Orbits of an element form a partition -/]
/--
theorem `IsPartition.of_orbits` / 定理 `IsPartition.of_orbits`

English:
theorem IsPartition.of_orbits
  proof: by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MulAction.nonempty_orbit a).ne_empty ha

中文:
定理 IsPartition.of_orbits
  证明: by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MulAction.nonempty_orbit a).ne_empty ha

Depends on / 依赖: MulAction, MulAction.nonempty_orbit, isPartition_of_exists_of_ne_empty, mem_orbit_self, ne_empty, nonempty_orbit, orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty, pairwiseDisjoint
-/
theorem IsPartition.of_orbits :
    Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MulAction.nonempty_orbit a).ne_empty ha

end orbits

section SMul

variable (G : Type*) {X : Type*} [SMul G X] {B : Set X} {a : X}

-- Change terminology to IsFullyInvariant?
/-- A set `B` is a `G`-fixed block if `g • B = B` for all `g : G`. -/
@[to_additive /-- A set `B` is a `G`-fixed block if `g +ᵥ B = B` for all `g : G`. -/]
/--
Definition of `IsFixedBlock` / `IsFixedBlock` 的定义

English:
definition IsFixedBlock
  signature: (B : Set X)
  body: forall g : G, g • B = B

中文:
定义 IsFixedBlock
  签名: (B : Set X)
  定义体: forall g : G, g • B = B
-/
def IsFixedBlock (B : Set X) := forall g : G, g • B = B

/-- A set `B` is a `G`-invariant block if `g • B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A set `B` is a `G`-invariant block if `g +ᵥ B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/]
/--
Definition of `IsInvariantBlock` / `IsInvariantBlock` 的定义

English:
definition IsInvariantBlock
  signature: (B : Set X)
  body: forall g : G, g • B subseteq B

中文:
定义 IsInvariantBlock
  签名: (B : Set X)
  定义体: forall g : G, g • B subseteq B

Depends on / 依赖: subseteq
-/
def IsInvariantBlock (B : Set X) := forall g : G, g • B subseteq B

section IsTrivialBlock

/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/]
/--
Definition of `IsTrivialBlock` / `IsTrivialBlock` 的定义

English:
definition IsTrivialBlock
  signature: (B : Set X)
  body: B.Subsingleton ∨ B = univ

中文:
定义 IsTrivialBlock
  签名: (B : Set X)
  定义体: B.Subsingleton ∨ B = univ

Depends on / 依赖: B.Subsingleton, Subsingleton
-/
def IsTrivialBlock (B : Set X) := B.Subsingleton ∨ B = univ

variable {M α N β : Type*}

section monoid

variable [Monoid M] [MulAction M α] [Monoid N] [MulAction N β]

@[to_additive]
/--
theorem `IsTrivialBlock.image` / 定理 `IsTrivialBlock.image`

English:
theorem IsTrivialBlock.image
  statement: {φ : M -> N} {f : α ->ₑ[φ] β}
  proof: by
  obtain hB | hB := hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.image_univ, Set.range_eq_univ, hf]

@[to_additive]

中文:
定理 IsTrivialBlock.image
  结论: {φ : M -> N} {f : α ->ₑ[φ] β}
  证明: by
  obtain hB | hB := hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.image_univ, Set.range_eq_univ, hf]

@[to_additive]

Depends on / 依赖: Or.intro_left, Or.intro_right, Set.Subsingleton.image, Set.image_univ, Set.range_eq_univ, Subsingleton, image_univ, intro_left, intro_right, range_eq_univ
-/
theorem IsTrivialBlock.image {φ : M -> N} {f : α ->ₑ[φ] β}
    (hf : Function.Surjective f) {B : Set α} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f '' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.image_univ, Set.range_eq_univ, hf]

@[to_additive]
/--
theorem `IsTrivialBlock.preimage` / 定理 `IsTrivialBlock.preimage`

English:
theorem IsTrivialBlock.preimage
  statement: {φ : M -> N} {f : α ->ₑ[φ] β}
  proof: by
  obtain hB | hB := hB
  · apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  · apply Or.intro_right; simp only [hB]; apply Set.preimage_univ

中文:
定理 IsTrivialBlock.preimage
  结论: {φ : M -> N} {f : α ->ₑ[φ] β}
  证明: by
  obtain hB | hB := hB
  · apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  · apply Or.intro_right; simp only [hB]; apply Set.preimage_univ

Depends on / 依赖: Or.intro_left, Or.intro_right, Set.Subsingleton.preimage, Set.preimage_univ, Subsingleton, intro_left, intro_right, preimage, preimage_univ
-/
theorem IsTrivialBlock.preimage {φ : M -> N} {f : α ->ₑ[φ] β}
    (hf : Function.Injective f) {B : Set β} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f ⁻¹' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  · apply Or.intro_right; simp only [hB]; apply Set.preimage_univ

end monoid

variable [Group M] [MulAction M α] [Monoid N] [MulAction N β]

@[to_additive]
/--
theorem `IsTrivialBlock.smul` / 定理 `IsTrivialBlock.smul`

English:
theorem IsTrivialBlock.smul
  given: {B : Set α} (hB : IsTrivialBlock B) (g : M)
  proof: by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MulAction.injective g)).mpr h
  | inr h =>
    right
    rw [h]; rw [← Set.image_smul]; rw [Set.image_univ_of_surjective (MulAction.surjective g)]

@[to_additive]

中文:
定理 IsTrivialBlock.smul
  条件: {B : Set α} (hB : IsTrivialBlock B) (g : M)
  证明: by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MulAction.injective g)).mpr h
  | inr h =>
    right
    rw [h]; rw [← Set.image_smul]; rw [Set.image_univ_of_surjective (MulAction.surjective g)]

@[to_additive]

Depends on / 依赖: Function, Function.Injective.subsingleton_image_iff, Injective, MulAction, MulAction.injective, MulAction.surjective, Set.image_smul, Set.image_univ_of_surjective, image_smul, image_univ_of_surjective, injective, subsingleton_image_iff, surjective
-/
theorem IsTrivialBlock.smul {B : Set α} (hB : IsTrivialBlock B) (g : M) :
    IsTrivialBlock (g • B) := by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MulAction.injective g)).mpr h
  | inr h =>
    right
    rw [h]; rw [← Set.image_smul]; rw [Set.image_univ_of_surjective (MulAction.surjective g)]

@[to_additive]
/--
theorem `IsTrivialBlock.smul_iff` / 定理 `IsTrivialBlock.smul_iff`

English:
theorem IsTrivialBlock.smul_iff
  given: {B : Set α} (g : M)
  proof: by
  constructor
  · intro H
    convert! IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

中文:
定理 IsTrivialBlock.smul_iff
  条件: {B : Set α} (g : M)
  证明: by
  constructor
  · intro H
    convert! IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

Depends on / 依赖: IsTrivialBlock, IsTrivialBlock.smul, convert, inv_smul_smul
-/
theorem IsTrivialBlock.smul_iff {B : Set α} (g : M) :
    IsTrivialBlock (g • B) ↔ IsTrivialBlock B := by
  constructor
  · intro H
    convert! IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

end IsTrivialBlock

/-- A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint. -/
@[to_additive
/-- A set `B` is a `G`-block iff the sets of the form `g +ᵥ B` are pairwise equal or disjoint. -/]
/--
Definition of `IsBlock` / `IsBlock` 的定义

English:
definition IsBlock
  signature: (B : Set X)
  body: forall ⦃g₁ g₂ : G⦄, g₁ • B != g₂ • B -> Disjoint (g₁ • B) (g₂ • B)

中文:
定义 IsBlock
  签名: (B : Set X)
  定义体: forall ⦃g₁ g₂ : G⦄, g₁ • B != g₂ • B -> Disjoint (g₁ • B) (g₂ • B)

Depends on / 依赖: Disjoint
-/
def IsBlock (B : Set X) := forall ⦃g₁ g₂ : G⦄, g₁ • B != g₂ • B -> Disjoint (g₁ • B) (g₂ • B)

variable {G} {s : Set G} {g g₁ g₂ : G}

@[to_additive]
/--
lemma `isBlock_iff_smul_eq_smul_of_nonempty` / 引理 `isBlock_iff_smul_eq_smul_of_nonempty`

English:
lemma isBlock_iff_smul_eq_smul_of_nonempty
  proof: by
  simp_rw [IsBlock, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]

中文:
引理 isBlock_iff_smul_eq_smul_of_nonempty
  证明: by
  simp_rw [IsBlock, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]

Depends on / 依赖: IsBlock, not_disjoint_iff_nonempty_inter, not_imp_comm, simp_rw
-/
lemma isBlock_iff_smul_eq_smul_of_nonempty :
    IsBlock G B ↔ forall ⦃g₁ g₂ : G⦄, (g₁ • B inter g₂ • B).Nonempty -> g₁ • B = g₂ • B := by
  simp_rw [IsBlock, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]
/--
lemma `isBlock_iff_pairwiseDisjoint_range_smul` / 引理 `isBlock_iff_pairwiseDisjoint_range_smul`

English:
lemma isBlock_iff_pairwiseDisjoint_range_smul
  proof: pairwiseDisjoint_range_iff.symm

@[to_additive]

中文:
引理 isBlock_iff_pairwiseDisjoint_range_smul
  证明: pairwiseDisjoint_range_iff.symm

@[to_additive]

Depends on / 依赖: pairwiseDisjoint_range_iff, pairwiseDisjoint_range_iff.symm
-/
lemma isBlock_iff_pairwiseDisjoint_range_smul :
    IsBlock G B ↔ (range fun g : G => g • B).PairwiseDisjoint id := pairwiseDisjoint_range_iff.symm

@[to_additive]
/--
lemma `isBlock_iff_smul_eq_smul_or_disjoint` / 引理 `isBlock_iff_smul_eq_smul_or_disjoint`

English:
lemma isBlock_iff_smul_eq_smul_or_disjoint
  proof: forall₂_congr fun _ _ => or_iff_not_imp_left.symm

@[to_additive]

中文:
引理 isBlock_iff_smul_eq_smul_or_disjoint
  证明: forall₂_congr fun _ _ => or_iff_not_imp_left.symm

@[to_additive]

Depends on / 依赖: or_iff_not_imp_left, or_iff_not_imp_left.symm
-/
lemma isBlock_iff_smul_eq_smul_or_disjoint :
    IsBlock G B ↔ forall g₁ g₂ : G, g₁ • B = g₂ • B ∨ Disjoint (g₁ • B) (g₂ • B) :=
  forall₂_congr fun _ _ => or_iff_not_imp_left.symm

@[to_additive]
/--
lemma `IsBlock.smul_eq_smul_of_subset` / 引理 `IsBlock.smul_eq_smul_of_subset`

English:
lemma IsBlock.smul_eq_smul_of_subset
  given: (hB : IsBlock G B) (hg : g₁ • B subseteq g₂ • B)
  proof: by
  by_contra! hg'
  obtain rfl : B = ∅ := by simpa using (hB hg').eq_bot_of_le hg
  simp at hg'

@[to_additive]

中文:
引理 IsBlock.smul_eq_smul_of_subset
  条件: (hB : IsBlock G B) (hg : g₁ • B subseteq g₂ • B)
  证明: by
  by_contra! hg'
  obtain rfl : B = ∅ := by simpa using (hB hg').eq_bot_of_le hg
  simp at hg'

@[to_additive]

Depends on / 依赖: eq_bot_of_le
-/
lemma IsBlock.smul_eq_smul_of_subset (hB : IsBlock G B) (hg : g₁ • B subseteq g₂ • B) :
    g₁ • B = g₂ • B := by
  by_contra! hg'
  obtain rfl : B = ∅ := by simpa using (hB hg').eq_bot_of_le hg
  simp at hg'

@[to_additive]
/--
lemma `IsBlock.not_smul_set_ssubset_smul_set` / 引理 `IsBlock.not_smul_set_ssubset_smul_set`

English:
lemma IsBlock.not_smul_set_ssubset_smul_set
  given: (hB : IsBlock G B)
  statement: ¬ g₁ • B ⊂ g₂ • B
  proof: fun hab => hab.ne hB.smul_eq_smul_of_subset hab.subset

@[to_additive]

中文:
引理 IsBlock.not_smul_set_ssubset_smul_set
  条件: (hB : IsBlock G B)
  结论: ¬ g₁ • B ⊂ g₂ • B
  证明: fun hab => hab.ne hB.smul_eq_smul_of_subset hab.subset

@[to_additive]

Depends on / 依赖: hB.smul_eq_smul_of_subset, hab.ne, hab.subset, smul_eq_smul_of_subset, subset
-/
lemma IsBlock.not_smul_set_ssubset_smul_set (hB : IsBlock G B) : ¬ g₁ • B ⊂ g₂ • B :=
fun hab => hab.ne hB.smul_eq_smul_of_subset hab.subset

@[to_additive]
/--
lemma `IsBlock.disjoint_smul_set_smul` / 引理 `IsBlock.disjoint_smul_set_smul`

English:
lemma IsBlock.disjoint_smul_set_smul
  given: (hB : IsBlock G B) (hgs : ¬ g • B subseteq s • B)
  proof: by
  rw [← iUnion_smul_set]; rw [disjoint_iUnion₂_right]
exact fun b hb => hB fun h => hgs h.trans_subset smul_set_subset_smul hb

@[to_additive]

中文:
引理 IsBlock.disjoint_smul_set_smul
  条件: (hB : IsBlock G B) (hgs : ¬ g • B subseteq s • B)
  证明: by
  rw [← iUnion_smul_set]; rw [disjoint_iUnion₂_right]
exact fun b hb => hB fun h => hgs h.trans_subset smul_set_subset_smul hb

@[to_additive]

Depends on / 依赖: h.trans_subset, iUnion_smul_set, smul_set_subset_smul, trans_subset
-/
lemma IsBlock.disjoint_smul_set_smul (hB : IsBlock G B) (hgs : ¬ g • B subseteq s • B) :
    Disjoint (g • B) (s • B) := by
  rw [← iUnion_smul_set]; rw [disjoint_iUnion₂_right]
exact fun b hb => hB fun h => hgs h.trans_subset smul_set_subset_smul hb

@[to_additive]
/--
lemma `IsBlock.disjoint_smul_smul_set` / 引理 `IsBlock.disjoint_smul_smul_set`

English:
lemma IsBlock.disjoint_smul_smul_set
  given: (hB : IsBlock G B) (hgs : ¬ g • B subseteq s • B)
  proof: (hB.disjoint_smul_set_smul hgs).symm

@[to_additive]
alias ⟨IsBlock.smul_eq_smul_of_nonempty, _⟩ := isBlock_iff_smul_eq_smul_of_nonempty
@[to_additive]
alias ⟨IsBlock.pairwiseDisjoint_range_smul, _⟩ := isBlock_iff_pairwiseDisjoint_range_smul
@[to_additive]
alias ⟨IsBlock.smul_eq_smul_or_disjoint, _⟩

中文:
引理 IsBlock.disjoint_smul_smul_set
  条件: (hB : IsBlock G B) (hgs : ¬ g • B subseteq s • B)
  证明: (hB.disjoint_smul_set_smul hgs).symm

@[to_additive]
alias ⟨IsBlock.smul_eq_smul_of_nonempty, _⟩ := isBlock_iff_smul_eq_smul_of_nonempty
@[to_additive]
alias ⟨IsBlock.pairwiseDisjoint_range_smul, _⟩ := isBlock_iff_pairwiseDisjoint_range_smul
@[to_additive]
alias ⟨IsBlock.smul_eq_smul_or_disjoint, _⟩

Depends on / 依赖: disjoint_smul_set_smul, hB.disjoint_smul_set_smul
-/
lemma IsBlock.disjoint_smul_smul_set (hB : IsBlock G B) (hgs : ¬ g • B subseteq s • B) :
    Disjoint (s • B) (g • B) := (hB.disjoint_smul_set_smul hgs).symm

@[to_additive]
alias ⟨IsBlock.smul_eq_smul_of_nonempty, _⟩ := isBlock_iff_smul_eq_smul_of_nonempty
@[to_additive]
alias ⟨IsBlock.pairwiseDisjoint_range_smul, _⟩ := isBlock_iff_pairwiseDisjoint_range_smul
@[to_additive]
alias ⟨IsBlock.smul_eq_smul_or_disjoint, _⟩ := isBlock_iff_smul_eq_smul_or_disjoint

/-- A fixed block is a block. -/
@[to_additive /-- A fixed block is a block. -/]
/--
lemma `IsFixedBlock.isBlock` / 引理 `IsFixedBlock.isBlock`

English:
lemma IsFixedBlock.isBlock
  given: (hfB : IsFixedBlock G B)
  statement: IsBlock G B
  proof: by simp [IsBlock, hfB _]

中文:
引理 IsFixedBlock.isBlock
  条件: (hfB : IsFixedBlock G B)
  结论: IsBlock G B
  证明: by simp [IsBlock, hfB _]

Depends on / 依赖: IsBlock
-/
lemma IsFixedBlock.isBlock (hfB : IsFixedBlock G B) : IsBlock G B := by simp [IsBlock, hfB _]

/-- The empty set is a block. -/
@[to_additive (attr := simp) /-- The empty set is a block. -/]
/--
lemma `IsBlock.empty` / 引理 `IsBlock.empty`

English:
lemma IsBlock.empty
  statement: IsBlock G (∅ : Set X)
  proof: by simp [IsBlock]

中文:
引理 IsBlock.empty
  结论: IsBlock G (∅ : Set X)
  证明: by simp [IsBlock]

Depends on / 依赖: IsBlock
-/
lemma IsBlock.empty : IsBlock G (∅ : Set X) := by simp [IsBlock]

/-- A singleton is a block. -/
@[to_additive /-- A singleton is a block. -/]
/--
lemma `IsBlock.singleton` / 引理 `IsBlock.singleton`

English:
lemma IsBlock.singleton
  statement: IsBlock G ({a} : Set X)
  proof: by simp [IsBlock]

中文:
引理 IsBlock.singleton
  结论: IsBlock G ({a} : Set X)
  证明: by simp [IsBlock]

Depends on / 依赖: IsBlock
-/
lemma IsBlock.singleton : IsBlock G ({a} : Set X) := by simp [IsBlock]

/-- Subsingletons are (trivial) blocks. -/
@[to_additive /-- Subsingletons are (trivial) blocks. -/]
/--
lemma `IsBlock.of_subsingleton` / 引理 `IsBlock.of_subsingleton`

English:
lemma IsBlock.of_subsingleton
  given: (hB : B.Subsingleton)
  statement: IsBlock G B
  proof: hB.induction_on .empty fun _ => .singleton

中文:
引理 IsBlock.of_subsingleton
  条件: (hB : B.Subsingleton)
  结论: IsBlock G B
  证明: hB.induction_on .empty fun _ => .singleton

Depends on / 依赖: hB.induction_on, induction_on, singleton
-/
lemma IsBlock.of_subsingleton (hB : B.Subsingleton) : IsBlock G B :=
  hB.induction_on .empty fun _ => .singleton

/-- A fixed block is an invariant block. -/
@[to_additive /-- A fixed block is an invariant block. -/]
/--
lemma `IsFixedBlock.isInvariantBlock` / 引理 `IsFixedBlock.isInvariantBlock`

English:
lemma IsFixedBlock.isInvariantBlock
  given: (hB : IsFixedBlock G B)
  statement: IsInvariantBlock G B
  proof: fun _ => (hB _).le

中文:
引理 IsFixedBlock.isInvariantBlock
  条件: (hB : IsFixedBlock G B)
  结论: IsInvariantBlock G B
  证明: fun _ => (hB _).le
-/
lemma IsFixedBlock.isInvariantBlock (hB : IsFixedBlock G B) : IsInvariantBlock G B :=
  fun _ => (hB _).le

end SMul

section Monoid
variable {M X : Type*} [Monoid M] [MulAction M X] {B : Set X} {s : Set M}

@[to_additive]
/--
lemma `IsBlock.disjoint_smul_right` / 引理 `IsBlock.disjoint_smul_right`

English:
lemma IsBlock.disjoint_smul_right
  given: (hB : IsBlock M B) (hs : ¬ B subseteq s • B)
  statement: Disjoint B (s • B)
  proof: by
  simpa using hB.disjoint_smul_set_smul (g := 1) (by simpa using hs)

@[to_additive]

中文:
引理 IsBlock.disjoint_smul_right
  条件: (hB : IsBlock M B) (hs : ¬ B subseteq s • B)
  结论: Disjoint B (s • B)
  证明: by
  simpa using hB.disjoint_smul_set_smul (g := 1) (by simpa using hs)

@[to_additive]

Depends on / 依赖: disjoint_smul_set_smul, hB.disjoint_smul_set_smul
-/
lemma IsBlock.disjoint_smul_right (hB : IsBlock M B) (hs : ¬ B subseteq s • B) : Disjoint B (s • B) := by
  simpa using hB.disjoint_smul_set_smul (g := 1) (by simpa using hs)

@[to_additive]
/--
lemma `IsBlock.disjoint_smul_left` / 引理 `IsBlock.disjoint_smul_left`

English:
lemma IsBlock.disjoint_smul_left
  given: (hB : IsBlock M B) (hs : ¬ B subseteq s • B)
  statement: Disjoint (s • B) B
  proof: (hB.disjoint_smul_right hs).symm

中文:
引理 IsBlock.disjoint_smul_left
  条件: (hB : IsBlock M B) (hs : ¬ B subseteq s • B)
  结论: Disjoint (s • B) B
  证明: (hB.disjoint_smul_right hs).symm

Depends on / 依赖: disjoint_smul_right, hB.disjoint_smul_right
-/
lemma IsBlock.disjoint_smul_left (hB : IsBlock M B) (hs : ¬ B subseteq s • B) : Disjoint (s • B) B :=
  (hB.disjoint_smul_right hs).symm

end Monoid

section Group

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] {B : Set X}

@[to_additive]
/--
lemma `isBlock_iff_disjoint_smul_of_ne` / 引理 `isBlock_iff_disjoint_smul_of_ne`

English:
lemma isBlock_iff_disjoint_smul_of_ne
  proof: by
  refine ⟨fun hB g => by simpa using hB (g₂ := 1), fun hB g₁ g₂ h => ?_⟩
  simp only [disjoint_smul_set_right, ne_eq, ← inv_smul_eq_iff, smul_smul] at h ⊢
  exact hB h

@[to_additive]

中文:
引理 isBlock_iff_disjoint_smul_of_ne
  证明: by
  refine ⟨fun hB g => by simpa using hB (g₂ := 1), fun hB g₁ g₂ h => ?_⟩
  simp only [disjoint_smul_set_right, ne_eq, ← inv_smul_eq_iff, smul_smul] at h ⊢
  exact hB h

@[to_additive]

Depends on / 依赖: disjoint_smul_set_right, inv_smul_eq_iff, ne_eq, smul_smul
-/
lemma isBlock_iff_disjoint_smul_of_ne :
    IsBlock G B ↔ forall ⦃g : G⦄, g • B != B -> Disjoint (g • B) B := by
  refine ⟨fun hB g => by simpa using hB (g₂ := 1), fun hB g₁ g₂ h => ?_⟩
  simp only [disjoint_smul_set_right, ne_eq, ← inv_smul_eq_iff, smul_smul] at h ⊢
  exact hB h

@[to_additive]
/--
lemma `isBlock_iff_smul_eq_of_nonempty` / 引理 `isBlock_iff_smul_eq_of_nonempty`

English:
lemma isBlock_iff_smul_eq_of_nonempty
  proof: by
  simp_rw [isBlock_iff_disjoint_smul_of_ne, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]

中文:
引理 isBlock_iff_smul_eq_of_nonempty
  证明: by
  simp_rw [isBlock_iff_disjoint_smul_of_ne, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]

Depends on / 依赖: isBlock_iff_disjoint_smul_of_ne, not_disjoint_iff_nonempty_inter, not_imp_comm, simp_rw
-/
lemma isBlock_iff_smul_eq_of_nonempty :
    IsBlock G B ↔ forall ⦃g : G⦄, (g • B inter B).Nonempty -> g • B = B := by
  simp_rw [isBlock_iff_disjoint_smul_of_ne, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]
/--
lemma `isBlock_iff_smul_eq_or_disjoint` / 引理 `isBlock_iff_smul_eq_or_disjoint`

English:
lemma isBlock_iff_smul_eq_or_disjoint
  proof: isBlock_iff_disjoint_smul_of_ne.trans forall_congr' fun _ => or_iff_not_imp_left.symm

@[to_additive]

中文:
引理 isBlock_iff_smul_eq_or_disjoint
  证明: isBlock_iff_disjoint_smul_of_ne.trans forall_congr' fun _ => or_iff_not_imp_left.symm

@[to_additive]

Depends on / 依赖: forall_congr, isBlock_iff_disjoint_smul_of_ne, isBlock_iff_disjoint_smul_of_ne.trans, or_iff_not_imp_left, or_iff_not_imp_left.symm
-/
lemma isBlock_iff_smul_eq_or_disjoint :
    IsBlock G B ↔ forall g : G, g • B = B ∨ Disjoint (g • B) B :=
isBlock_iff_disjoint_smul_of_ne.trans forall_congr' fun _ => or_iff_not_imp_left.symm

@[to_additive]
/--
lemma `isBlock_iff_smul_eq_of_mem` / 引理 `isBlock_iff_smul_eq_of_mem`

English:
lemma isBlock_iff_smul_eq_of_mem
  proof: by
  simp [isBlock_iff_smul_eq_of_nonempty, Set.Nonempty, mem_smul_set]

@[to_additive] alias ⟨IsBlock.disjoint_smul_of_ne, _⟩ := isBlock_iff_disjoint_smul_of_ne
@[to_additive] alias ⟨IsBlock.smul_eq_of_nonempty, _⟩ := isBlock_iff_smul_eq_of_nonempty
@[to_additive] alias ⟨IsBlock.smul_eq_or_disjoint

中文:
引理 isBlock_iff_smul_eq_of_mem
  证明: by
  simp [isBlock_iff_smul_eq_of_nonempty, Set.Nonempty, mem_smul_set]

@[to_additive] alias ⟨IsBlock.disjoint_smul_of_ne, _⟩ := isBlock_iff_disjoint_smul_of_ne
@[to_additive] alias ⟨IsBlock.smul_eq_of_nonempty, _⟩ := isBlock_iff_smul_eq_of_nonempty
@[to_additive] alias ⟨IsBlock.smul_eq_or_disjoint

Depends on / 依赖: Nonempty, Set.Nonempty, isBlock_iff_smul_eq_of_nonempty, mem_smul_set
-/
lemma isBlock_iff_smul_eq_of_mem :
    IsBlock G B ↔ forall ⦃g : G⦄ ⦃a : X⦄, a in B -> g • a in B -> g • B = B := by
  simp [isBlock_iff_smul_eq_of_nonempty, Set.Nonempty, mem_smul_set]

@[to_additive] alias ⟨IsBlock.disjoint_smul_of_ne, _⟩ := isBlock_iff_disjoint_smul_of_ne
@[to_additive] alias ⟨IsBlock.smul_eq_of_nonempty, _⟩ := isBlock_iff_smul_eq_of_nonempty
@[to_additive] alias ⟨IsBlock.smul_eq_or_disjoint, _⟩ := isBlock_iff_smul_eq_or_disjoint
@[to_additive] alias ⟨IsBlock.smul_eq_of_mem, _⟩ := isBlock_iff_smul_eq_of_mem

-- TODO: Generalise to `SubgroupClass`
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/
@[to_additive
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/]
/--
lemma `IsBlock.subgroup` / 引理 `IsBlock.subgroup`

English:
lemma IsBlock.subgroup
  given: {H : Subgroup G} (hB : IsBlock G B)
  statement: IsBlock H B
  proof: fun _ _ h => hB h

中文:
引理 IsBlock.subgroup
  条件: {H : Subgroup G} (hB : IsBlock G B)
  结论: IsBlock H B
  证明: fun _ _ h => hB h
-/
lemma IsBlock.subgroup {H : Subgroup G} (hB : IsBlock G B) : IsBlock H B := fun _ _ h => hB h

/-- A block of a group action is invariant iff it is fixed. -/
@[to_additive /-- A block of a group action is invariant iff it is fixed. -/]
/--
lemma `isInvariantBlock_iff_isFixedBlock` / 引理 `isInvariantBlock_iff_isFixedBlock`

English:
lemma isInvariantBlock_iff_isFixedBlock
  statement: IsInvariantBlock G B ↔ IsFixedBlock G B
  proof: ⟨fun hB g => (hB g).antisymm subset_smul_set_iff.2 hB _, IsFixedBlock.isInvariantBlock⟩

中文:
引理 isInvariantBlock_iff_isFixedBlock
  结论: IsInvariantBlock G B ↔ IsFixedBlock G B
  证明: ⟨fun hB g => (hB g).antisymm subset_smul_set_iff.2 hB _, IsFixedBlock.isInvariantBlock⟩

Depends on / 依赖: IsFixedBlock, IsFixedBlock.isInvariantBlock, antisymm, isInvariantBlock, subset_smul_set_iff
-/
lemma isInvariantBlock_iff_isFixedBlock : IsInvariantBlock G B ↔ IsFixedBlock G B :=
⟨fun hB g => (hB g).antisymm subset_smul_set_iff.2 hB _, IsFixedBlock.isInvariantBlock⟩

/-- An invariant block of a group action is a fixed block. -/
@[to_additive /-- An invariant block of a group action is a fixed block. -/]
alias ⟨IsInvariantBlock.isFixedBlock, _⟩ := isInvariantBlock_iff_isFixedBlock

/-- An invariant block of a group action is a block. -/
@[to_additive /-- An invariant block of a group action is a block. -/]
/--
lemma `IsInvariantBlock.isBlock` / 引理 `IsInvariantBlock.isBlock`

English:
lemma IsInvariantBlock.isBlock
  given: (hB : IsInvariantBlock G B)
  statement: IsBlock G B
  proof: hB.isFixedBlock.isBlock

中文:
引理 IsInvariantBlock.isBlock
  条件: (hB : IsInvariantBlock G B)
  结论: IsBlock G B
  证明: hB.isFixedBlock.isBlock

Depends on / 依赖: hB.isFixedBlock.isBlock, isBlock, isFixedBlock
-/
lemma IsInvariantBlock.isBlock (hB : IsInvariantBlock G B) : IsBlock G B := hB.isFixedBlock.isBlock

/-- The full set is a fixed block. -/
@[to_additive /-- The full set is a fixed block. -/]
/--
lemma `IsFixedBlock.univ` / 引理 `IsFixedBlock.univ`

English:
lemma IsFixedBlock.univ
  statement: IsFixedBlock G (univ : Set X)
  proof: fun _ => by simp

中文:
引理 IsFixedBlock.univ
  结论: IsFixedBlock G (univ : Set X)
  证明: fun _ => by simp
-/
lemma IsFixedBlock.univ : IsFixedBlock G (univ : Set X) := fun _ => by simp

/-- The full set is a block. -/
@[to_additive (attr := simp) /-- The full set is a block. -/]
/--
lemma `IsBlock.univ` / 引理 `IsBlock.univ`

English:
lemma IsBlock.univ
  statement: IsBlock G (univ : Set X)
  proof: IsFixedBlock.univ.isBlock

中文:
引理 IsBlock.univ
  结论: IsBlock G (univ : Set X)
  证明: IsFixedBlock.univ.isBlock

Depends on / 依赖: IsFixedBlock, IsFixedBlock.univ.isBlock, isBlock
-/
lemma IsBlock.univ : IsBlock G (univ : Set X) := IsFixedBlock.univ.isBlock

/-- The intersection of two blocks is a block. -/
@[to_additive /-- The intersection of two blocks is a block. -/]
/--
lemma `IsBlock.inter` / 引理 `IsBlock.inter`

English:
lemma IsBlock.inter
  given: {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂)
  proof: by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter] at h₁ h₂ ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  rw [h₁ ⟨a]; rw [ha₁.1]; rw [ha₂.1⟩]; rw [h₂ ⟨a]; rw [ha₁.2]; rw [ha₂.2⟩]

中文:
引理 IsBlock.inter
  条件: {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂)
  证明: by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter] at h₁ h₂ ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  rw [h₁ ⟨a]; rw [ha₁.1]; rw [ha₂.1⟩]; rw [h₂ ⟨a]; rw [ha₁.2]; rw [ha₂.2⟩]

Depends on / 依赖: isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter
-/
lemma IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ inter B₂) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter] at h₁ h₂ ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  rw [h₁ ⟨a]; rw [ha₁.1]; rw [ha₂.1⟩]; rw [h₂ ⟨a]; rw [ha₁.2]; rw [ha₂.2⟩]

/-- An intersection of blocks is a block. -/
@[to_additive /-- An intersection of blocks is a block. -/]
/--
lemma `IsBlock.iInter` / 引理 `IsBlock.iInter`

English:
lemma IsBlock.iInter
  given: {ι : Sort*} {B : ι -> Set X} (hB : forall i, IsBlock G (B i))
  proof: by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_iInter] at hB ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  simp_rw [fun i => hB i ⟨a, iInter_subset _ i ha₁, iInter_subset _ i ha₂⟩]

中文:
引理 IsBlock.iInter
  条件: {ι : Sort*} {B : ι -> Set X} (hB : 对任意 i, IsBlock G (B i))
  证明: by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_iInter] at hB ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  simp_rw [fun i => hB i ⟨a, iInter_subset _ i ha₁, iInter_subset _ i ha₂⟩]

Depends on / 依赖: iInter_subset, isBlock_iff_smul_eq_smul_of_nonempty, simp_rw, smul_set_iInter
-/
lemma IsBlock.iInter {ι : Sort*} {B : ι -> Set X} (hB : forall i, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_iInter] at hB ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  simp_rw [fun i => hB i ⟨a, iInter_subset _ i ha₁, iInter_subset _ i ha₂⟩]

/-- A trivial block is a block. -/
@[to_additive /-- A trivial block is a block. -/]
/--
lemma `IsTrivialBlock.isBlock` / 引理 `IsTrivialBlock.isBlock`

English:
lemma IsTrivialBlock.isBlock
  given: (hB : IsTrivialBlock B)
  statement: IsBlock G B
  proof: by
  obtain hB | rfl := hB
  · exact .of_subsingleton hB
  · exact .univ

中文:
引理 IsTrivialBlock.isBlock
  条件: (hB : IsTrivialBlock B)
  结论: IsBlock G B
  证明: by
  obtain hB | rfl := hB
  · exact .of_subsingleton hB
  · exact .univ

Depends on / 依赖: of_subsingleton
-/
lemma IsTrivialBlock.isBlock (hB : IsTrivialBlock B) : IsBlock G B := by
  obtain hB | rfl := hB
  · exact .of_subsingleton hB
  · exact .univ

/-- An orbit is a fixed block. -/
@[to_additive /-- An orbit is a fixed block. -/]
/--
lemma `IsFixedBlock.orbit` / 引理 `IsFixedBlock.orbit`

English:
lemma IsFixedBlock.orbit
  given: (a : X)
  statement: IsFixedBlock G (orbit G a)
  proof: (smul_orbit · a)

中文:
引理 IsFixedBlock.orbit
  条件: (a : X)
  结论: IsFixedBlock G (orbit G a)
  证明: (smul_orbit · a)
-/
protected lemma IsFixedBlock.orbit (a : X) : IsFixedBlock G (orbit G a) := (smul_orbit · a)

/-- An orbit is a block. -/
@[to_additive /-- An orbit is a block. -/]
/--
lemma `IsBlock.orbit` / 引理 `IsBlock.orbit`

English:
lemma IsBlock.orbit
  given: (a : X)
  statement: IsBlock G (orbit G a)
  proof: (IsFixedBlock.orbit a).isBlock

@[to_additive]

中文:
引理 IsBlock.orbit
  条件: (a : X)
  结论: IsBlock G (orbit G a)
  证明: (IsFixedBlock.orbit a).isBlock

@[to_additive]
-/
protected lemma IsBlock.orbit (a : X) : IsBlock G (orbit G a) := (IsFixedBlock.orbit a).isBlock

@[to_additive]
/--
lemma `isBlock_top` / 引理 `isBlock_top`

English:
lemma isBlock_top
  statement: IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B
  proof: Subgroup.topEquiv.toEquiv.forall_congr fun _ => Subgroup.topEquiv.toEquiv.forall_congr_left

@[to_additive]

中文:
引理 isBlock_top
  结论: IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B
  证明: Subgroup.topEquiv.toEquiv.forall_congr fun _ => Subgroup.topEquiv.toEquiv.forall_congr_left

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.topEquiv.toEquiv.forall_congr, Subgroup.topEquiv.toEquiv.forall_congr_left, forall_congr, forall_congr_left, toEquiv, topEquiv
-/
lemma isBlock_top : IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B :=
  Subgroup.topEquiv.toEquiv.forall_congr fun _ => Subgroup.topEquiv.toEquiv.forall_congr_left

@[to_additive]
/--
lemma `IsBlock.preimage` / 引理 `IsBlock.preimage`

English:
lemma IsBlock.preimage
  statement: {H Y : Type*} [Group H] [MulAction H Y]
  proof: by
  rintro g₁ g₂ hg
  rw [← Group.preimage_smul_setₛₗ]; rw [← Group.preimage_smul_setₛₗ] at hg ⊢
  exact (hB <| ne_of_apply_ne _ hg).preimage _

@[to_additive]

中文:
引理 IsBlock.preimage
  结论: {H Y : 类型} [Group H] [MulAction H Y]
  证明: by
  rintro g₁ g₂ hg
  rw [← Group.preimage_smul_setₛₗ]; rw [← Group.preimage_smul_setₛₗ] at hg ⊢
  exact (hB <| ne_of_apply_ne _ hg).preimage _

@[to_additive]

Depends on / 依赖: Group.preimage_smul_set, ne_of_apply_ne, preimage
-/
lemma IsBlock.preimage {H Y : Type*} [Group H] [MulAction H Y]
    {φ : H -> G} (j : Y ->ₑ[φ] X) (hB : IsBlock G B) :
    IsBlock H (j ⁻¹' B) := by
  rintro g₁ g₂ hg
  rw [← Group.preimage_smul_setₛₗ]; rw [← Group.preimage_smul_setₛₗ] at hg ⊢
  exact (hB <| ne_of_apply_ne _ hg).preimage _

@[to_additive]
/--
theorem `IsBlock.image` / 定理 `IsBlock.image`

English:
theorem IsBlock.image
  statement: {H Y : Type*} [SMul H Y] {φ : G -> H} (j : X ->ₑ[φ] Y)
  proof: by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
exact fun g₁ g₂ hg => disjoint_image_of_injective hj hB ne_of_apply_ne _ hg

@[to_additive]

中文:
定理 IsBlock.image
  结论: {H Y : 类型} [SMul H Y] {φ : G -> H} (j : X ->ₑ[φ] Y)
  证明: by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
exact fun g₁ g₂ hg => disjoint_image_of_injective hj hB ne_of_apply_ne _ hg

@[to_additive]

Depends on / 依赖: IsBlock, disjoint_image_of_injective, ne_of_apply_ne
-/
theorem IsBlock.image {H Y : Type*} [SMul H Y] {φ : G -> H} (j : X ->ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j) (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
exact fun g₁ g₂ hg => disjoint_image_of_injective hj hB ne_of_apply_ne _ hg

@[to_additive]
/--
theorem `IsBlock.subtype_val_preimage` / 定理 `IsBlock.subtype_val_preimage`

English:
theorem IsBlock.subtype_val_preimage
  given: {C : SubMulAction G X} (hB : IsBlock G B)
  proof: hB.preimage C.inclusion

@[to_additive]

中文:
定理 IsBlock.subtype_val_preimage
  条件: {C : SubMulAction G X} (hB : IsBlock G B)
  证明: hB.preimage C.inclusion

@[to_additive]

Depends on / 依赖: C.inclusion, hB.preimage, inclusion, preimage
-/
theorem IsBlock.subtype_val_preimage {C : SubMulAction G X} (hB : IsBlock G B) :
    IsBlock G (Subtype.val ⁻¹' B : Set C) :=
  hB.preimage C.inclusion

@[to_additive]
/--
theorem `isBlock_subtypeVal` / 定理 `isBlock_subtypeVal`

English:
theorem isBlock_subtypeVal
  given: {C : SubMulAction G X} {B : Set C}
  proof: by
  refine forall₂_congr fun g₁ g₂ => ?_
  rw [← SubMulAction.inclusion.coe_eq]; rw [← image_smul_set]; rw [← image_smul_set]; rw [ne_eq]; rw [Set.image_eq_image C.inclusion_injective]; rw [disjoint_image_iff C.inclusion_injective]

@[to_additive]

中文:
定理 isBlock_subtypeVal
  条件: {C : SubMulAction G X} {B : Set C}
  证明: by
  refine forall₂_congr fun g₁ g₂ => ?_
  rw [← SubMulAction.inclusion.coe_eq]; rw [← image_smul_set]; rw [← image_smul_set]; rw [ne_eq]; rw [Set.image_eq_image C.inclusion_injective]; rw [disjoint_image_iff C.inclusion_injective]

@[to_additive]

Depends on / 依赖: C.inclusion_injective, Set.image_eq_image, SubMulAction, SubMulAction.inclusion.coe_eq, coe_eq, disjoint_image_iff, image_eq_image, image_smul_set, inclusion, inclusion_injective, ne_eq
-/
theorem isBlock_subtypeVal {C : SubMulAction G X} {B : Set C} :
    IsBlock G (Subtype.val '' B : Set X) ↔ IsBlock G B := by
  refine forall₂_congr fun g₁ g₂ => ?_
  rw [← SubMulAction.inclusion.coe_eq]; rw [← image_smul_set]; rw [← image_smul_set]; rw [ne_eq]; rw [Set.image_eq_image C.inclusion_injective]; rw [disjoint_image_iff C.inclusion_injective]

@[to_additive]
/--
theorem `IsBlock.of_subgroup_of_conjugate` / 定理 `IsBlock.of_subgroup_of_conjugate`

English:
theorem IsBlock.of_subgroup_of_conjugate
  given: {H : Subgroup G} (hB : IsBlock H B) (g : G)
  proof: by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    apply (hB.smul_eq_or_disjoint ⟨h, hH⟩).imp
    · intro; 

中文:
定理 IsBlock.of_subgroup_of_conjugate
  条件: {H : Subgroup G} (hB : IsBlock H B) (g : G)
  证明: by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    apply (hB.smul_eq_or_disjoint ⟨h, hH⟩).imp
    · intro; 

Depends on / 依赖: MulAction, MulAction.injective, MulAut, MulAut.conj_apply, MulEquiv, MulEquiv.coe_toMonoidHom, Set.disjoint_image_of_injective, SetLike, SetLike.coe_mem, Subgroup, Subgroup.mem_map.mp, coe_mem, coe_toMonoidHom, conj_apply, disjoint_image_of_injective, hB.smul_eq_or_disjoint, injective, inv_mul_cancel_right, isBlock_iff_smul_eq_or_disjoint, mem_map
-/
theorem IsBlock.of_subgroup_of_conjugate {H : Subgroup G} (hB : IsBlock H B) (g : G) :
    IsBlock (H.map (MulAut.conj g).toMonoidHom) (g • B) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    apply (hB.smul_eq_or_disjoint ⟨h, hH⟩).imp
    · intro; congr
    · exact Set.disjoint_image_of_injective (MulAction.injective g)
  suffices (h' : G) • g • B = g • h • B by
    rw [← this]; rfl
  rw [← hh]; rw [smul_smul (g * h * g⁻¹) g B]; rw [smul_smul g h B]; rw [inv_mul_cancel_right]

/-- A translate of a block is a block -/
@[to_additive]
/--
theorem `IsBlock.translate` / 定理 `IsBlock.translate`

English:
theorem IsBlock.translate
  given: (g : G) (hB : IsBlock G B)
  proof: by
  rw [← isBlock_top] at hB ⊢
  rw [← Subgroup.map_comap_eq_self_of_surjective
          (G := G) (f := MulAut.conj g) (MulAut.conj g).surjective ⊤]
  apply IsBlock.of_subgroup_of_conjugate
  rwa [Subgroup.comap_top]

中文:
定理 IsBlock.translate
  条件: (g : G) (hB : IsBlock G B)
  证明: by
  rw [← isBlock_top] at hB ⊢
  rw [← Subgroup.map_comap_eq_self_of_surjective
          (G := G) (f := MulAut.conj g) (MulAut.conj g).surjective ⊤]
  apply IsBlock.of_subgroup_of_conjugate
  rwa [Subgroup.comap_top]

Depends on / 依赖: IsBlock, IsBlock.of_subgroup_of_conjugate, MulAut, MulAut.conj, Subgroup, Subgroup.comap_top, Subgroup.map_comap_eq_self_of_surjective, comap_top, isBlock_top, map_comap_eq_self_of_surjective, of_subgroup_of_conjugate, surjective
-/
theorem IsBlock.translate (g : G) (hB : IsBlock G B) :
    IsBlock G (g • B) := by
  rw [← isBlock_top] at hB ⊢
  rw [← Subgroup.map_comap_eq_self_of_surjective
          (G := G) (f := MulAut.conj g) (MulAut.conj g).surjective ⊤]
  apply IsBlock.of_subgroup_of_conjugate
  rwa [Subgroup.comap_top]

variable (G) in
/-- For `SMul G X`, a block system of `X` is a partition of `X` into blocks
for the action of `G` -/
@[to_additive /-- For `VAdd G X`, a block system of `X` is a partition of `X` into blocks
for the additive action of `G` -/]
/--
Definition of `IsBlockSystem` / `IsBlockSystem` 的定义

English:
definition IsBlockSystem
  signature: (ℬ : Set (Set X))
  body: Setoid.IsPartition ℬ ∧ forall ⦃B⦄, B in ℬ -> IsBlock G B

中文:
定义 IsBlockSystem
  签名: (ℬ : Set (Set X))
  定义体: Setoid.IsPartition ℬ ∧ forall ⦃B⦄, B in ℬ -> IsBlock G B

Depends on / 依赖: IsBlock, IsPartition, Setoid, Setoid.IsPartition
-/
def IsBlockSystem (ℬ : Set (Set X)) := Setoid.IsPartition ℬ ∧ forall ⦃B⦄, B in ℬ -> IsBlock G B

/-- Translates of a block form a block system -/
@[to_additive /-- Translates of a block form a block system -/]
/--
theorem `IsBlock.isBlockSystem` / 定理 `IsBlock.isBlockSystem`

English:
theorem IsBlock.isBlockSystem
  statement: [hGX : MulAction.IsPretransitive G X]
  proof: by
  refine ⟨⟨?nonempty, ?cover⟩, ?mem_blocks⟩
  case mem_blocks => rintro B' ⟨g, rfl⟩; exact hB.translate g
  · simp only [Set.mem_range, not_exists]
    intro g hg
    apply hBe.ne_empty
    simpa only [Set.smul_set_eq_empty] using hg
  · intro a
    obtain ⟨b : X, hb : b in B⟩ := hBe
    obtain ⟨

中文:
定理 IsBlock.isBlockSystem
  结论: [hGX : MulAction.IsPretransitive G X]
  证明: by
  refine ⟨⟨?nonempty, ?cover⟩, ?mem_blocks⟩
  case mem_blocks => rintro B' ⟨g, rfl⟩; exact hB.translate g
  · simp only [Set.mem_range, not_exists]
    intro g hg
    apply hBe.ne_empty
    simpa only [Set.smul_set_eq_empty] using hg
  · intro a
    obtain ⟨b : X, hb : b in B⟩ := hBe
    obtain ⟨

Depends on / 依赖: Set.mem_range, Set.smul_mem_smul_set_iff, Set.smul_set_eq_empty, and_imp, exists_apply_eq_apply, exists_smul_eq, forall_apply_eq_imp_iff, forall_exists_index, hB.smul_eq_smul_of_non, hB.translate, hBe.ne_empty, mem_blocks, mem_range, ne_empty, nonempty, not_exists, smul_eq_smul_of_non, smul_mem_smul_set_iff, smul_set_eq_empty, translate
-/
theorem IsBlock.isBlockSystem [hGX : MulAction.IsPretransitive G X]
    (hB : IsBlock G B) (hBe : B.Nonempty) :
    IsBlockSystem G (Set.range fun g : G => g • B) := by
  refine ⟨⟨?nonempty, ?cover⟩, ?mem_blocks⟩
  case mem_blocks => rintro B' ⟨g, rfl⟩; exact hB.translate g
  · simp only [Set.mem_range, not_exists]
    intro g hg
    apply hBe.ne_empty
    simpa only [Set.smul_set_eq_empty] using hg
  · intro a
    obtain ⟨b : X, hb : b in B⟩ := hBe
    obtain ⟨g, rfl⟩ := exists_smul_eq G b a
    use g • B
    simp only [Set.smul_mem_smul_set_iff, hb, Set.mem_range,
      exists_apply_eq_apply, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff, true_and]
    exact fun g' ha => hB.smul_eq_smul_of_nonempty ⟨g • b, ha, ⟨b, hb, rfl⟩⟩

section Normal

@[to_additive]
/--
lemma `smul_orbit_eq_orbit_smul` / 引理 `smul_orbit_eq_orbit_smul`

English:
lemma smul_orbit_eq_orbit_smul
  given: (N : Subgroup G) [nN : N.Normal] (a : X) (g : G)
  proof: by
  simp only [orbit, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g * k * g⁻¹, nN.conj_mem k hk g⟩
    simp only [Subgroup.mk_smul]
    rw [smul_smul]; rw [inv_mul_cancel_right]; rw [← smul_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g⁻¹ * k *

中文:
引理 smul_orbit_eq_orbit_smul
  条件: (N : Subgroup G) [nN : N.Normal] (a : X) (g : G)
  证明: by
  simp only [orbit, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g * k * g⁻¹, nN.conj_mem k hk g⟩
    simp only [Subgroup.mk_smul]
    rw [smul_smul]; rw [inv_mul_cancel_right]; rw [← smul_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g⁻¹ * k *

Depends on / 依赖: Set.mem_range, Set.smul_set_range, Subgroup, Subgroup.mk_smul, conj_mem, inv_mul_cancel_right, mem_range, mk_smul, nN.conj_mem, smul_inv_smul, smul_set_range, smul_smul
-/
lemma smul_orbit_eq_orbit_smul (N : Subgroup G) [nN : N.Normal] (a : X) (g : G) :
    g • orbit N a = orbit N (g • a) := by
  simp only [orbit, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g * k * g⁻¹, nN.conj_mem k hk g⟩
    simp only [Subgroup.mk_smul]
    rw [smul_smul]; rw [inv_mul_cancel_right]; rw [← smul_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g⁻¹ * k * g, nN.conj_mem' k hk g⟩
    simp only [Subgroup.mk_smul]
    simp only [← smul_smul, smul_inv_smul]

/-- An orbit of a normal subgroup is a block -/
@[to_additive /-- An orbit of a normal subgroup is a block -/]
/--
theorem `IsBlock.orbit_of_normal` / 定理 `IsBlock.orbit_of_normal`

English:
theorem IsBlock.orbit_of_normal
  given: {N : Subgroup G} [N.Normal] (a : X)
  proof: by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  rw [smul_orbit_eq_orbit_smul]
  apply orbit.eq_or_disjoint

中文:
定理 IsBlock.orbit_of_normal
  条件: {N : Subgroup G} [N.Normal] (a : X)
  证明: by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  rw [smul_orbit_eq_orbit_smul]
  apply orbit.eq_or_disjoint

Depends on / 依赖: eq_or_disjoint, isBlock_iff_smul_eq_or_disjoint, orbit.eq_or_disjoint, smul_orbit_eq_orbit_smul
-/
theorem IsBlock.orbit_of_normal {N : Subgroup G} [N.Normal] (a : X) :
    IsBlock G (orbit N a) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  rw [smul_orbit_eq_orbit_smul]
  apply orbit.eq_or_disjoint

/-- The orbits of a normal subgroup form a block system -/
@[to_additive /-- The orbits of a normal subgroup form a block system -/]
/--
theorem `IsBlockSystem.of_normal` / 定理 `IsBlockSystem.of_normal`

English:
theorem IsBlockSystem.of_normal
  given: {N : Subgroup G} [N.Normal]
  proof: by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact .orbit_of_normal a

中文:
定理 IsBlockSystem.of_normal
  条件: {N : Subgroup G} [N.Normal]
  证明: by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact .orbit_of_normal a

Depends on / 依赖: IsPartition, IsPartition.of_orbits, of_orbits, orbit_of_normal
-/
theorem IsBlockSystem.of_normal {N : Subgroup G} [N.Normal] :
    IsBlockSystem G (Set.range fun a : X => orbit N a) := by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact .orbit_of_normal a

section Group
variable {S H : Type*} [Group H] [SetLike S H] [SubgroupClass S H] {s : S} {a : G}

/-!
Annoyingly, it seems like the following two lemmas cannot be unified.
-/

section Left
variable [MulAction G H] [IsScalarTower G H H]

/-- See `MulAction.isBlock_subgroup'` for a version that works for the right action of a group on
itself. -/
@[to_additive /-- See `AddAction.isBlock_subgroup'` for a version that works for the right action
of a group on itself. -/]
/--
lemma `isBlock_subgroup` / 引理 `isBlock_subgroup`

English:
lemma isBlock_subgroup
  statement: IsBlock G (s : Set H)
  proof: by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc]; rw [← smul_assoc]; rw [← hcd]; rw [smul_assoc]; rw [smul_coe_set hc]; rw [smul_coe_set hd]

中文:
引理 isBlock_subgroup
  结论: IsBlock G (s : Set H)
  证明: by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc]; rw [← smul_assoc]; rw [← hcd]; rw [smul_assoc]; rw [smul_coe_set hc]; rw [smul_coe_set hd]

Depends on / 依赖: IsBlock, disjoint_left, smul_assoc, smul_coe_set
-/
lemma isBlock_subgroup : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc]; rw [← smul_assoc]; rw [← hcd]; rw [smul_assoc]; rw [smul_coe_set hc]; rw [smul_coe_set hd]

end Left

section Right
variable [MulAction G H] [IsScalarTower G Hᵐᵒᵖ H]

open MulOpposite

/-- See `MulAction.isBlock_subgroup` for a version that works for the left action of a group on
itself. -/
@[to_additive /-- See `AddAction.isBlock_subgroup` for a version that works for the left action
of a group on itself. -/]
/--
lemma `isBlock_subgroup'` / 引理 `isBlock_subgroup'`

English:
lemma isBlock_subgroup'
  statement: IsBlock G (s : Set H)
  proof: by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc]; rw [← smul_assoc]; rw [← op_smul]; rw [← hcd]; rw [op_smul]; rw [smul_assoc]; rw [op_smul_coe_set hc]; rw [op_smul_coe_set hd]

中文:
引理 isBlock_subgroup'
  结论: IsBlock G (s : Set H)
  证明: by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc]; rw [← smul_assoc]; rw [← op_smul]; rw [← hcd]; rw [op_smul]; rw [smul_assoc]; rw [op_smul_coe_set hc]; rw [op_smul_coe_set hd]

Depends on / 依赖: IsBlock, disjoint_left, op_smul, op_smul_coe_set, smul_assoc
-/
lemma isBlock_subgroup' : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc]; rw [← smul_assoc]; rw [← op_smul]; rw [← hcd]; rw [op_smul]; rw [smul_assoc]; rw [op_smul_coe_set hc]; rw [op_smul_coe_set hd]

end Right
end Group

end Normal

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `block_stabilizerOrderIso` between
  - blocks of `MulAction G X` containing a point `a ∈ X`,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/
@[to_additive /-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/]
/--
theorem `IsBlock.of_orbit` / 定理 `IsBlock.of_orbit`

English:
theorem IsBlock.of_orbit
  given: {H : Subgroup G} {a : X} (hH : stabilizer G a <= H)
  proof: by
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨-, ⟨-, ⟨h₁, rfl⟩, h⟩, h₂, rfl⟩
  suffices g in H by
    rw [← Subgroup.coe_mk H g this]; rw [← H.toSubmonoid.smul_def]; rw [smul_orbit (⟨g]; rw [this⟩ : H) a]
  rw [← mul_mem_cancel_left h₂⁻¹.2]; rw [← mul_mem_cancel_right h₁.2]
  apply hH
  simp

中文:
定理 IsBlock.of_orbit
  条件: {H : Subgroup G} {a : X} (hH : stabilizer G a <= H)
  证明: by
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨-, ⟨-, ⟨h₁, rfl⟩, h⟩, h₂, rfl⟩
  suffices g in H by
    rw [← Subgroup.coe_mk H g this]; rw [← H.toSubmonoid.smul_def]; rw [smul_orbit (⟨g]; rw [this⟩ : H) a]
  rw [← mul_mem_cancel_left h₂⁻¹.2]; rw [← mul_mem_cancel_right h₁.2]
  apply hH
  simp

Depends on / 依赖: H.toSubmonoid.smul_def, InvMemClass, InvMemClass.coe_inv, Subgroup, Subgroup.coe_mk, coe_inv, coe_mk, inv_smul_eq_iff, isBlock_iff_smul_eq_of_nonempty, mem_stabilizer_iff, mul_mem_cancel_left, mul_mem_cancel_right, mul_smul, smul_def, smul_orbit, toSubmonoid
-/
theorem IsBlock.of_orbit {H : Subgroup G} {a : X} (hH : stabilizer G a <= H) :
    IsBlock G (MulAction.orbit H a) := by
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨-, ⟨-, ⟨h₁, rfl⟩, h⟩, h₂, rfl⟩
  suffices g in H by
    rw [← Subgroup.coe_mk H g this]; rw [← H.toSubmonoid.smul_def]; rw [smul_orbit (⟨g]; rw [this⟩ : H) a]
  rw [← mul_mem_cancel_left h₂⁻¹.2]; rw [← mul_mem_cancel_right h₁.2]
  apply hH
  simpa only [mem_stabilizer_iff, InvMemClass.coe_inv, mul_smul, inv_smul_eq_iff]

/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/
@[to_additive
/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/]
/--
theorem `IsBlock.stabilizer_le` / 定理 `IsBlock.stabilizer_le`

English:
theorem IsBlock.stabilizer_le
  given: (hB : IsBlock G B) {a : X} (ha : a in B)
  proof: fun g hg => hB.smul_eq_of_nonempty ⟨a, by rwa [← hg, smul_mem_smul_set_iff], ha⟩

中文:
定理 IsBlock.stabilizer_le
  条件: (hB : IsBlock G B) {a : X} (ha : a in B)
  证明: fun g hg => hB.smul_eq_of_nonempty ⟨a, by rwa [← hg, smul_mem_smul_set_iff], ha⟩

Depends on / 依赖: hB.smul_eq_of_nonempty, smul_eq_of_nonempty, smul_mem_smul_set_iff
-/
theorem IsBlock.stabilizer_le (hB : IsBlock G B) {a : X} (ha : a in B) :
    stabilizer G a <= stabilizer G B :=
  fun g hg => hB.smul_eq_of_nonempty ⟨a, by rwa [← hg, smul_mem_smul_set_iff], ha⟩

/-- A block containing `a` is the orbit of `a` under its stabilizer -/
@[to_additive /-- A block containing `a` is the orbit of `a` under its stabilizer -/]
/--
theorem `IsBlock.orbit_stabilizer_eq` / 定理 `IsBlock.orbit_stabilizer_eq`

English:
theorem IsBlock.orbit_stabilizer_eq
  given: [IsPretransitive G X] (hB : IsBlock G B) {a : X} (ha : a in B)
  proof: by
  ext x
  constructor
  · rintro ⟨⟨k, k_mem⟩, rfl⟩
    simp only [Subgroup.mk_smul]
    rw [← k_mem]; rw [Set.smul_mem_smul_set_iff]
    exact ha
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    exact ⟨⟨k, hB.smul_eq_of_mem ha hx⟩, rfl⟩

中文:
定理 IsBlock.orbit_stabilizer_eq
  条件: [IsPretransitive G X] (hB : IsBlock G B) {a : X} (ha : a in B)
  证明: by
  ext x
  constructor
  · rintro ⟨⟨k, k_mem⟩, rfl⟩
    simp only [Subgroup.mk_smul]
    rw [← k_mem]; rw [Set.smul_mem_smul_set_iff]
    exact ha
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    exact ⟨⟨k, hB.smul_eq_of_mem ha hx⟩, rfl⟩

Depends on / 依赖: Set.smul_mem_smul_set_iff, Subgroup, Subgroup.mk_smul, exists_smul_eq, hB.smul_eq_of_mem, k_mem, mk_smul, smul_eq_of_mem, smul_mem_smul_set_iff
-/
theorem IsBlock.orbit_stabilizer_eq [IsPretransitive G X] (hB : IsBlock G B) {a : X} (ha : a in B) :
    MulAction.orbit (stabilizer G B) a = B := by
  ext x
  constructor
  · rintro ⟨⟨k, k_mem⟩, rfl⟩
    simp only [Subgroup.mk_smul]
    rw [← k_mem]; rw [Set.smul_mem_smul_set_iff]
    exact ha
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    exact ⟨⟨k, hB.smul_eq_of_mem ha hx⟩, rfl⟩

/-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/
@[to_additive
  /-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/]
/--
theorem `stabilizer_orbit_eq` / 定理 `stabilizer_orbit_eq`

English:
theorem stabilizer_orbit_eq
  given: {a : X} {H : Subgroup G} (hH : stabilizer G a <= H)
  proof: by
  ext g
  constructor
  · intro hg
    obtain ⟨-, ⟨b, rfl⟩, h⟩ := hg.symm ▸ mem_orbit_self a
    simp_rw [H.toSubmonoid.smul_def, ← mul_smul, ← mem_stabilizer_iff] at h
    exact (mul_mem_cancel_right b.2).mp (hH h)
  · intro hg
    rw [mem_stabilizer_iff]; rw [← Subgroup.coe_mk H g hg]; rw [← Su

中文:
定理 stabilizer_orbit_eq
  条件: {a : X} {H : Subgroup G} (hH : stabilizer G a <= H)
  证明: by
  ext g
  constructor
  · intro hg
    obtain ⟨-, ⟨b, rfl⟩, h⟩ := hg.symm ▸ mem_orbit_self a
    simp_rw [H.toSubmonoid.smul_def, ← mul_smul, ← mem_stabilizer_iff] at h
    exact (mul_mem_cancel_right b.2).mp (hH h)
  · intro hg
    rw [mem_stabilizer_iff]; rw [← Subgroup.coe_mk H g hg]; rw [← Su

Depends on / 依赖: H.toSubmonoid, H.toSubmonoid.smul_def, Subgroup, Subgroup.coe_mk, Submonoid, Submonoid.smul_def, coe_mk, hg.symm, mem_orbit_self, mem_stabilizer_iff, mul_mem_cancel_right, mul_smul, simp_rw, smul_def, smul_orbit, toSubmonoid
-/
theorem stabilizer_orbit_eq {a : X} {H : Subgroup G} (hH : stabilizer G a <= H) :
    stabilizer G (orbit H a) = H := by
  ext g
  constructor
  · intro hg
    obtain ⟨-, ⟨b, rfl⟩, h⟩ := hg.symm ▸ mem_orbit_self a
    simp_rw [H.toSubmonoid.smul_def, ← mul_smul, ← mem_stabilizer_iff] at h
    exact (mul_mem_cancel_right b.2).mp (hH h)
  · intro hg
    rw [mem_stabilizer_iff]; rw [← Subgroup.coe_mk H g hg]; rw [← Submonoid.smul_def (S := H.toSubmonoid)]
    apply smul_orbit (G := H)

variable (G)

/-- Order equivalence between blocks in `X` containing a point `a`
and subgroups of `G` containing the stabilizer of `a` (Wielandt, th. 7.5) -/
@[to_additive
/-- Order equivalence between blocks in `X` containing a point `a`
and subgroups of `G` containing the stabilizer of `a` (Wielandt, th. 7.5) -/]
/--
Definition of `block_stabilizerOrderIso` / `block_stabilizerOrderIso` 的定义

English:
definition block_stabilizerOrderIso
  signature: [htGX : IsPretransitive G X] (a : X)
  body: fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, hB.stabilizer_le ha⟩
  invFun := fun ⟨H, hH⟩ =>
    ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock.of_orbit hH⟩
  left_inv := fun ⟨_, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨_, hH⟩ =>
    (id (p

中文:
定义 block_stabilizerOrderIso
  签名: [htGX : IsPretransitive G X] (a : X)
  定义体: fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, hB.stabilizer_le ha⟩
  invFun := fun ⟨H, hH⟩ =>
    ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock.of_orbit hH⟩
  left_inv := fun ⟨_, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨_, hH⟩ =>
    (id (p

Depends on / 依赖: hB.stabilizer_le, stabilizer, stabilizer_le
-/
def block_stabilizerOrderIso [htGX : IsPretransitive G X] (a : X) :
    { B : Set X // a in B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a) where
  toFun := fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, hB.stabilizer_le ha⟩
  invFun := fun ⟨H, hH⟩ =>
    ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock.of_orbit hH⟩
  left_inv := fun ⟨_, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨_, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_orbit_eq hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
    constructor
    · rintro hBB' b hb
      obtain ⟨k, rfl⟩ := htGX.exists_smul_eq a b
      suffices k in stabilizer G B' by
        exact this.symm ▸ (Set.smul_mem_smul_set ha')
      exact hBB' (hB.smul_eq_of_mem ha hb)
    · intro hBB' g hgB
      apply hB'.smul_eq_of_mem ha'
exact hBB' hgB.symm ▸ (Set.smul_mem_smul_set ha)

/-- The type of blocks for a group action containing a given element -/
@[to_additive
/-- The type of blocks for an additive group action containing a given element -/]
/--
Definition of `BlockMem` / `BlockMem` 的定义

English:
abbreviation BlockMem
  signature: (a : X)
  body: {B : Set X // a in B ∧ IsBlock G B}

中文:
缩写 BlockMem
  签名: (a : X)
  定义体: {B : Set X // a in B ∧ IsBlock G B}

Depends on / 依赖: IsBlock
-/
abbrev BlockMem (a : X) : Type _ := {B : Set X // a in B ∧ IsBlock G B}

namespace BlockMem

/-- The type of blocks for a group action containing a given element is a bounded order. -/
@[to_additive /-- The type of blocks for an additive group action containing a given element is a
bounded order. -/]
instance (a : X) : BoundedOrder (BlockMem G a) where
  top := ⟨Set.univ, Set.mem_univ a, .univ⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, IsBlock.singleton⟩
  bot_le := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, Set.singleton_subset_iff]
    exact ha

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: (a : X)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_top
  条件: (a : X)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: nonempty_lifts, nonempty_subtype, nonempty_subtype.mpr
-/
theorem coe_top (a : X) :
    ((⊤ : BlockMem G a) : Set X) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  given: (a : X)
  proof: rfl

@[to_additive]

中文:
定理 coe_bot
  条件: (a : X)
  证明: rfl

@[to_additive]
-/
theorem coe_bot (a : X) :
    ((⊥ : BlockMem G a) : Set X) = {a} :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: X] (a
  body: by
  rw [nontrivial_iff]
  use ⊥, ⊤
  intro h
  rw [← Subtype.coe_inj] at h
  simp only [coe_top, coe_bot] at h
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff]; rw [h]
  apply Set.mem_univ

中文:
实例 [Nontrivial
  签名: X] (a
  定义体: by
  rw [nontrivial_iff]
  use ⊥, ⊤
  intro h
  rw [← Subtype.coe_inj] at h
  simp only [coe_top, coe_bot] at h
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff]; rw [h]
  apply Set.mem_univ

Depends on / 依赖: Set.mem_singleton_iff, Set.mem_univ, Subtype, Subtype.coe_inj, coe_bot, coe_inj, coe_top, exists_ne, mem_singleton_iff, mem_univ, nontrivial_iff
-/
instance [Nontrivial X] (a : X) : Nontrivial (BlockMem G a) := by
  rw [nontrivial_iff]
  use ⊥, ⊤
  intro h
  rw [← Subtype.coe_inj] at h
  simp only [coe_top, coe_bot] at h
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff]; rw [h]
  apply Set.mem_univ

end BlockMem

end Stabilizer

section Finite

namespace IsBlock

variable [IsPretransitive G X] {B : Set X}

@[to_additive]
/--
theorem `ncard_block_eq_relIndex` / 定理 `ncard_block_eq_relIndex`

English:
theorem ncard_block_eq_relIndex
  given: (hB : IsBlock G B) {x : X} (hx : x in B)
  proof: by
  have key : (stabilizer G x).subgroupOf (stabilizer G B) = stabilizer (stabilizer G B) x := by
    ext; rfl
  rw [Subgroup.relIndex]; rw [key]; rw [index_stabilizer]; rw [hB.orbit_stabilizer_eq hx]

中文:
定理 ncard_block_eq_relIndex
  条件: (hB : IsBlock G B) {x : X} (hx : x in B)
  证明: by
  have key : (stabilizer G x).subgroupOf (stabilizer G B) = stabilizer (stabilizer G B) x := by
    ext; rfl
  rw [Subgroup.relIndex]; rw [key]; rw [index_stabilizer]; rw [hB.orbit_stabilizer_eq hx]

Depends on / 依赖: Subgroup, Subgroup.relIndex, hB.orbit_stabilizer_eq, index_stabilizer, orbit_stabilizer_eq, relIndex, stabilizer, subgroupOf
-/
theorem ncard_block_eq_relIndex (hB : IsBlock G B) {x : X} (hx : x in B) :
    B.ncard = (stabilizer G x).relIndex (stabilizer G B) := by
  have key : (stabilizer G x).subgroupOf (stabilizer G B) = stabilizer (stabilizer G B) x := by
    ext; rfl
  rw [Subgroup.relIndex]; rw [key]; rw [index_stabilizer]; rw [hB.orbit_stabilizer_eq hx]

/-- The cardinality of the ambient space is the product of the cardinality of a block
  by the cardinality of the set of translates of that block -/
@[to_additive
  /-- The cardinality of the ambient space is the product of the cardinality of a block
  by the cardinality of the set of translates of that block -/]
/--
theorem `ncard_block_mul_ncard_orbit_eq` / 定理 `ncard_block_mul_ncard_orbit_eq`

English:
theorem ncard_block_mul_ncard_orbit_eq
  given: (hB : IsBlock G B) (hB_ne : B.Nonempty)
  proof: by
  obtain ⟨x, hx⟩ := hB_ne
  rw [ncard_block_eq_relIndex hB hx]; rw [← index_stabilizer]; rw [Subgroup.relIndex_mul_index (hB.stabilizer_le hx)]; rw [index_stabilizer_of_transitive]

中文:
定理 ncard_block_mul_ncard_orbit_eq
  条件: (hB : IsBlock G B) (hB_ne : B.Nonempty)
  证明: by
  obtain ⟨x, hx⟩ := hB_ne
  rw [ncard_block_eq_relIndex hB hx]; rw [← index_stabilizer]; rw [Subgroup.relIndex_mul_index (hB.stabilizer_le hx)]; rw [index_stabilizer_of_transitive]

Depends on / 依赖: Subgroup, Subgroup.relIndex_mul_index, hB.stabilizer_le, hB_ne, index_stabilizer, index_stabilizer_of_transitive, ncard_block_eq_relIndex, relIndex_mul_index, stabilizer_le
-/
theorem ncard_block_mul_ncard_orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B * Set.ncard (orbit G B) = Nat.card X := by
  obtain ⟨x, hx⟩ := hB_ne
  rw [ncard_block_eq_relIndex hB hx]; rw [← index_stabilizer]; rw [Subgroup.relIndex_mul_index (hB.stabilizer_le hx)]; rw [index_stabilizer_of_transitive]

/-- The cardinality of a block divides the cardinality of the ambient type -/
@[to_additive /-- The cardinality of a block divides the cardinality of the ambient type -/]
/--
theorem `ncard_dvd_card` / 定理 `ncard_dvd_card`

English:
theorem ncard_dvd_card
  given: (hB : IsBlock G B) (hB_ne : B.Nonempty)
  proof: Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

中文:
定理 ncard_dvd_card
  条件: (hB : IsBlock G B) (hB_ne : B.Nonempty)
  证明: Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

Depends on / 依赖: Dvd.intro, hB.ncard_block_mul_ncard_orbit_eq, hB_ne, ncard_block_mul_ncard_orbit_eq
-/
theorem ncard_dvd_card (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B ∣ Nat.card X :=
  Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

/-- A too large block is equal to `univ` -/
@[to_additive /-- A too large block is equal to `univ` -/]
/--
theorem `eq_univ_of_card_lt` / 定理 `eq_univ_of_card_lt`

English:
theorem eq_univ_of_card_lt
  given: [hX : Finite X] (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2)
  proof: by
  rcases Set.eq_empty_or_nonempty B with rfl | hB_ne
  · simp at hB'
  have key := hB.ncard_block_mul_ncard_orbit_eq hB_ne
  rw [← key]; rw [mul_lt_mul_iff_of_pos_left (by rwa [Set.ncard_pos])] at hB'
  interval_cases (orbit G B).ncard
  · rw [mul_zero, eq_comm, Nat.card_eq_zero, or_iff_left hX.n

中文:
定理 eq_univ_of_card_lt
  条件: [hX : Finite X] (hB : IsBlock G B) (hB' : 自然数.card X < Set.ncard B * 2)
  证明: by
  rcases Set.eq_empty_or_nonempty B with rfl | hB_ne
  · simp at hB'
  have key := hB.ncard_block_mul_ncard_orbit_eq hB_ne
  rw [← key]; rw [mul_lt_mul_iff_of_pos_left (by rwa [Set.ncard_pos])] at hB'
  interval_cases (orbit G B).ncard
  · rw [mul_zero, eq_comm, Nat.card_eq_zero, or_iff_left hX.n

Depends on / 依赖: IsEmpty, IsEmpty.exists_iff.mp, Nat.card_eq_zero, Set.eq_empty_or_nonempty, Set.eq_of_subset_of_ncard_le, Set.ncard_pos, Set.ncard_univ, Set.subset_univ, card_eq_zero, eq_comm, eq_empty_or_nonempty, eq_of_subset_of_ncard_le, exists_iff, hB.ncard_block_mul_ncard_orbit_eq, hB_ne, hX.not_infinite, interval_cases, key.ge, mul_lt_mul_iff_of_pos_left, mul_one
-/
theorem eq_univ_of_card_lt [hX : Finite X] (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) :
    B = Set.univ := by
  rcases Set.eq_empty_or_nonempty B with rfl | hB_ne
  · simp at hB'
  have key := hB.ncard_block_mul_ncard_orbit_eq hB_ne
  rw [← key]; rw [mul_lt_mul_iff_of_pos_left (by rwa [Set.ncard_pos])] at hB'
  interval_cases (orbit G B).ncard
  · rw [mul_zero, eq_comm, Nat.card_eq_zero, or_iff_left hX.not_infinite] at key
    exact (IsEmpty.exists_iff.mp hB_ne).elim
  · rw [mul_one, ← Set.ncard_univ] at key
    rw [Set.eq_of_subset_of_ncard_le (Set.subset_univ B) key.ge]

/-- If a block has too many translates, then it is a (sub)singleton -/
@[to_additive /-- If a block has too many translates, then it is a (sub)singleton -/]
/--
theorem `subsingleton_of_card_lt` / 定理 `subsingleton_of_card_lt`

English:
theorem subsingleton_of_card_lt
  statement: [Finite X] (hB : IsBlock G B)
  proof: by
  suffices Set.ncard B < 2 by simp_all
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; simp
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h]; rw [lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb => hB' (Nat.mul_le_mul_right _ hb)

中文:
定理 subsingleton_of_card_lt
  结论: [Finite X] (hB : IsBlock G B)
  证明: by
  suffices Set.ncard B < 2 by simp_all
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; simp
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h]; rw [lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb => hB' (Nat.mul_le_mul_right _ hb)

Depends on / 依赖: Nat.mul_le_mul_right, Set.eq_empty_or_nonempty, Set.ncard, Set.ncard_empty, eq_empty_or_nonempty, hB.ncard_block_mul_ncard_orbit_eq, lt_iff_not_ge, mul_le_mul_right, ncard_block_mul_ncard_orbit_eq, ncard_empty, not_le
-/
theorem subsingleton_of_card_lt [Finite X] (hB : IsBlock G B)
    (hB' : Nat.card X < 2 * Set.ncard (orbit G B)) :
    B.Subsingleton := by
  suffices Set.ncard B < 2 by simp_all
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; simp
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h]; rw [lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb => hB' (Nat.mul_le_mul_right _ hb)

/- The assumption `B.Finite` is necessary :
  For G = ℤ acting on itself, a = 0 and B = ℕ, the translates `k • B` of the statement
  are just `k + ℕ`, for `k ≤ 0`, and the corresponding intersection is `ℕ`, which is not a block.
  (Remark by Thomas Browning) -/
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3). -/
@[to_additive
  /-- The intersection of the translates of a *finite* subset which contain a given point
  is a block (Wielandt, th. 7.3). -/]
/--
theorem `of_subset` / 定理 `of_subset`

English:
theorem of_subset
  given: (a : X) (hfB : B.Finite)
  proof: by
  let B' := ⋂ (k : G) (_ : a in k • B), k • B
  rcases Set.eq_empty_or_nonempty B with hfB_e | hfB_ne
  · simp [hfB_e]
  have hB'₀ : forall (k : G) (_ : a in k • B), B' <= k • B := by
    intro k hk
    exact Set.biInter_subset_of_mem hk
  have hfB' : B'.Finite := by
    obtain ⟨b, hb : b in B⟩ :

中文:
定理 of_subset
  条件: (a : X) (hfB : B.Finite)
  证明: by
  let B' := ⋂ (k : G) (_ : a in k • B), k • B
  rcases Set.eq_empty_or_nonempty B with hfB_e | hfB_ne
  · simp [hfB_e]
  have hB'₀ : forall (k : G) (_ : a in k • B), B' <= k • B := by
    intro k hk
    exact Set.biInter_subset_of_mem hk
  have hfB' : B'.Finite := by
    obtain ⟨b, hb : b in B⟩ :

Depends on / 依赖: Finite, Set.Finite.map, Set.Finite.subset, Set.biInter_subset_of_mem, Set.eq_empty_or_nonempty, biInter_subset_of_mem, eq_empty_or_nonempty, exists_smul_eq, hfB_e, hfB_ne, subset
-/
theorem of_subset (a : X) (hfB : B.Finite) :
    IsBlock G (⋂ (k : G) (_ : a in k • B), k • B) := by
  let B' := ⋂ (k : G) (_ : a in k • B), k • B
  rcases Set.eq_empty_or_nonempty B with hfB_e | hfB_ne
  · simp [hfB_e]
  have hB'₀ : forall (k : G) (_ : a in k • B), B' <= k • B := by
    intro k hk
    exact Set.biInter_subset_of_mem hk
  have hfB' : B'.Finite := by
    obtain ⟨b, hb : b in B⟩ := hfB_ne
    obtain ⟨k, hk : k • b = a⟩ := exists_smul_eq G b a
    apply Set.Finite.subset (Set.Finite.map _ hfB) (hB'₀ k ⟨b, hb, hk⟩)
  have hag : forall g : G, a in g • B' -> B' <= g • B' := by
    intro g hg x hx
    -- a = g • b; b ∈ B'; a ∈ k • B → b ∈ k • B
    simp only [B', Set.mem_iInter, Set.mem_smul_set_iff_inv_smul_mem,
      smul_smul, ← mul_inv_rev] at hg hx ⊢
    exact fun _ => hx _ ∘ hg _
  have hag' (g : G) (hg : a in g • B') : B' = g • B' := by
    rw [eq_comm]; rw [← mem_stabilizer_iff]; rw [mem_stabilizer_set_iff_subset_smul_set hfB']
    exact hag g hg
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨b : X, hb' : b in g • B', hb : b in B'⟩
  obtain ⟨k : G, hk : k • a = b⟩ := exists_smul_eq G a b
  have hak : a in k⁻¹ • B' := by
    refine ⟨b, hb, ?_⟩
    simp only [← hk, inv_smul_smul]
  have hagk : a in (k⁻¹ * g) • B' := by
    rw [mul_smul]; rw [Set.mem_smul_set_iff_inv_smul_mem]; rw [inv_inv]; rw [hk]
    exact hb'
  have hkB' : B' = k⁻¹ • B' := hag' k⁻¹ hak
  have hgkB' : B' = (k⁻¹ * g) • B' := hag' (k⁻¹ * g) hagk
  rw [mul_smul] at hgkB'
  rw [← smul_eq_iff_eq_inv_smul] at hkB' hgkB'
  rw [← hgkB']; rw [hkB']

end IsBlock

end Finite

end Group

end MulAction
