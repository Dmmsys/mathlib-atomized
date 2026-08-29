/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Lift
public import Mathlib.Topology.Basic

/-!
# Interior, closure and frontier of a set

This file provides lemmas relating to the functions `interior`, `closure` and `frontier` of a set
endowed with a topology.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≠] x`: the filter `nhdsWithin x {x}ᶜ` of punctured neighborhoods of `x`.

## Tags

interior, closure, frontier
-/

public section

open Set

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {x : X} {s s₁ s₂ t : Set X}

section Interior

/--
theorem `mem_interior` / 定理 `mem_interior`

English:
theorem mem_interior
  statement: x in interior s ↔ exists t subseteq s, IsOpen t ∧ x in t
  proof: by
  simp only [interior, mem_sUnion, mem_ofPred_eq, and_assoc, and_left_comm]

@[simp]

中文:
定理 mem_interior
  结论: x in interior s ↔ 存在 t subseteq s, 是开集 t ∧ x in t
  证明: by
  simp only [interior, mem_sUnion, mem_ofPred_eq, and_assoc, and_left_comm]

@[simp]

Depends on / 依赖: and_assoc, and_left_comm, interior, mem_ofPred_eq, mem_sUnion
-/
theorem mem_interior : x in interior s ↔ exists t subseteq s, IsOpen t ∧ x in t := by
  simp only [interior, mem_sUnion, mem_ofPred_eq, and_assoc, and_left_comm]

@[simp]
/--
theorem `isOpen_interior` / 定理 `isOpen_interior`

English:
theorem isOpen_interior
  statement: IsOpen (interior s)
  proof: isOpen_sUnion fun _ => And.left

中文:
定理 isOpen_interior
  结论: 是开集 (interior s)
  证明: isOpen_sUnion fun _ => And.left

Depends on / 依赖: And.left, isOpen_sUnion
-/
theorem isOpen_interior : IsOpen (interior s) :=
  isOpen_sUnion fun _ => And.left

/--
theorem `interior_subset` / 定理 `interior_subset`

English:
theorem interior_subset
  statement: interior s subseteq s
  proof: sUnion_subset fun _ => And.right

中文:
定理 interior_subset
  结论: interior s subseteq s
  证明: sUnion_subset fun _ => And.right

Depends on / 依赖: And.right, sUnion_subset
-/
theorem interior_subset : interior s subseteq s :=
  sUnion_subset fun _ => And.right

/--
theorem `interior_maximal` / 定理 `interior_maximal`

English:
theorem interior_maximal
  given: (h₁ : t subseteq s) (h₂ : IsOpen t)
  statement: t subseteq interior s
  proof: subset_sUnion_of_mem ⟨h₂, h₁⟩

@[grind =]

中文:
定理 interior_maximal
  条件: (h₁ : t subseteq s) (h₂ : 是开集 t)
  结论: t subseteq interior s
  证明: subset_sUnion_of_mem ⟨h₂, h₁⟩

@[grind =]

Depends on / 依赖: subset_sUnion_of_mem
-/
theorem interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) : t subseteq interior s :=
  subset_sUnion_of_mem ⟨h₂, h₁⟩

@[grind =]
/--
theorem `IsOpen.interior_eq` / 定理 `IsOpen.interior_eq`

English:
theorem IsOpen.interior_eq
  given: (h : IsOpen s)
  statement: interior s = s
  proof: interior_subset.antisymm (interior_maximal (Subset.refl s) h)

中文:
定理 是开集.interior_eq
  条件: (h : 是开集 s)
  结论: interior s = s
  证明: interior_subset.antisymm (interior_maximal (Subset.refl s) h)

Depends on / 依赖: Subset, Subset.refl, antisymm, interior_maximal, interior_subset, interior_subset.antisymm
-/
theorem IsOpen.interior_eq (h : IsOpen s) : interior s = s :=
  interior_subset.antisymm (interior_maximal (Subset.refl s) h)

/--
theorem `forall_isOpen_iff` / 定理 `forall_isOpen_iff`

English:
theorem forall_isOpen_iff
  given: {p : Set X -> Prop}
  proof: ⟨fun h t => h (interior t) isOpen_interior, fun h t ht => ht.interior_eq ▸ h t⟩

中文:
定理 对任意_isOpen_iff
  条件: {p : 集合 X -> 命题}
  证明: ⟨fun h t => h (interior t) isOpen_interior, fun h t ht => ht.interior_eq ▸ h t⟩

Depends on / 依赖: ht.interior_eq, interior, interior_eq, isOpen_interior
-/
theorem forall_isOpen_iff {p : Set X -> Prop} :
    (forall t, IsOpen t -> p t) ↔ forall t, p (interior t) :=
  ⟨fun h t => h (interior t) isOpen_interior, fun h t ht => ht.interior_eq ▸ h t⟩

/--
theorem `exists_isOpen_iff` / 定理 `exists_isOpen_iff`

English:
theorem exists_isOpen_iff
  given: {p : Set X -> Prop}
  proof: ⟨fun ⟨_, h⟩ => ⟨_, h.1.interior_eq ▸ h.2⟩, fun ⟨_, h⟩ => ⟨_, isOpen_interior, h⟩⟩

中文:
定理 存在_isOpen_iff
  条件: {p : 集合 X -> 命题}
  证明: ⟨fun ⟨_, h⟩ => ⟨_, h.1.interior_eq ▸ h.2⟩, fun ⟨_, h⟩ => ⟨_, isOpen_interior, h⟩⟩

Depends on / 依赖: interior_eq, isOpen_interior
-/
theorem exists_isOpen_iff {p : Set X -> Prop} :
    (exists t, IsOpen t ∧ p t) ↔ exists t, p (interior t) :=
  ⟨fun ⟨_, h⟩ => ⟨_, h.1.interior_eq ▸ h.2⟩, fun ⟨_, h⟩ => ⟨_, isOpen_interior, h⟩⟩

/--
theorem `interior_eq_iff_isOpen` / 定理 `interior_eq_iff_isOpen`

English:
theorem interior_eq_iff_isOpen
  statement: interior s = s ↔ IsOpen s
  proof: ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩

中文:
定理 interior_eq_iff_isOpen
  结论: interior s = s ↔ 是开集 s
  证明: ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩

Depends on / 依赖: IsOpen, IsOpen.interior_eq, interior_eq, isOpen_interior
-/
theorem interior_eq_iff_isOpen : interior s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩

/--
theorem `subset_interior_iff_isOpen` / 定理 `subset_interior_iff_isOpen`

English:
theorem subset_interior_iff_isOpen
  statement: s subseteq interior s ↔ IsOpen s
  proof: by
  simp only [interior_eq_iff_isOpen.symm, Subset.antisymm_iff, interior_subset, true_and]

中文:
定理 subset_interior_iff_isOpen
  结论: s subseteq interior s ↔ 是开集 s
  证明: by
  simp only [interior_eq_iff_isOpen.symm, Subset.antisymm_iff, interior_subset, true_and]

Depends on / 依赖: Subset, Subset.antisymm_iff, antisymm_iff, interior_eq_iff_isOpen, interior_eq_iff_isOpen.symm, interior_subset, true_and
-/
theorem subset_interior_iff_isOpen : s subseteq interior s ↔ IsOpen s := by
  simp only [interior_eq_iff_isOpen.symm, Subset.antisymm_iff, interior_subset, true_and]

/--
theorem `IsOpen.subset_interior_iff` / 定理 `IsOpen.subset_interior_iff`

English:
theorem IsOpen.subset_interior_iff
  given: (h₁ : IsOpen s)
  statement: s subseteq interior t ↔ s subseteq t
  proof: ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩

中文:
定理 是开集.subset_interior_iff
  条件: (h₁ : 是开集 s)
  结论: s subseteq interior t ↔ s subseteq t
  证明: ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩

Depends on / 依赖: Subset, Subset.trans, interior_maximal, interior_subset
-/
theorem IsOpen.subset_interior_iff (h₁ : IsOpen s) : s subseteq interior t ↔ s subseteq t :=
  ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩

/--
theorem `subset_interior_iff` / 定理 `subset_interior_iff`

English:
theorem subset_interior_iff
  statement: t subseteq interior s ↔ exists U, IsOpen U ∧ t subseteq U ∧ U subseteq s
  proof: ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨_U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩

中文:
定理 subset_interior_iff
  结论: t subseteq interior s ↔ 存在 U, 是开集 U ∧ t subseteq U ∧ U subseteq s
  证明: ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨_U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩

Depends on / 依赖: htU.trans, interior, interior_maximal, interior_subset, isOpen_interior
-/
theorem subset_interior_iff : t subseteq interior s ↔ exists U, IsOpen U ∧ t subseteq U ∧ U subseteq s :=
  ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨_U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩

/--
lemma `interior_subset_iff` / 引理 `interior_subset_iff`

English:
lemma interior_subset_iff
  statement: interior s subseteq t ↔ forall U, IsOpen U -> U subseteq s -> U subseteq t
  proof: by
  simp [interior]

@[mono, gcongr]

中文:
引理 interior_subset_iff
  结论: interior s subseteq t ↔ 对任意 U, 是开集 U -> U subseteq s -> U subseteq t
  证明: by
  simp [interior]

@[mono, gcongr]

Depends on / 依赖: interior
-/
lemma interior_subset_iff : interior s subseteq t ↔ forall U, IsOpen U -> U subseteq s -> U subseteq t := by
  simp [interior]

@[mono, gcongr]
/--
theorem `interior_mono` / 定理 `interior_mono`

English:
theorem interior_mono
  given: (h : s subseteq t)
  statement: interior s subseteq interior t
  proof: interior_maximal (Subset.trans interior_subset h) isOpen_interior

中文:
定理 interior_mono
  条件: (h : s subseteq t)
  结论: interior s subseteq interior t
  证明: interior_maximal (Subset.trans interior_subset h) isOpen_interior

Depends on / 依赖: Subset, Subset.trans, interior_maximal, interior_subset, isOpen_interior
-/
theorem interior_mono (h : s subseteq t) : interior s subseteq interior t :=
  interior_maximal (Subset.trans interior_subset h) isOpen_interior

/--
theorem `subset_interior_union` / 定理 `subset_interior_union`

English:
theorem subset_interior_union
  statement: interior s union interior t subseteq interior (s union t)
  proof: union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

@[simp]

中文:
定理 subset_interior_union
  结论: interior s union interior t subseteq interior (s union t)
  证明: union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

@[simp]

Depends on / 依赖: interior_mono, subset_union_left, subset_union_right, union_subset
-/
theorem subset_interior_union : interior s union interior t subseteq interior (s union t) :=
  union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

@[simp]
/--
theorem `interior_empty` / 定理 `interior_empty`

English:
theorem interior_empty
  statement: interior (∅ : Set X) = ∅
  proof: isOpen_empty.interior_eq

@[simp]

中文:
定理 interior_empty
  结论: interior (∅ : 集合 X) = ∅
  证明: isOpen_empty.interior_eq

@[simp]

Depends on / 依赖: interior_eq, isOpen_empty, isOpen_empty.interior_eq
-/
theorem interior_empty : interior (∅ : Set X) = ∅ :=
  isOpen_empty.interior_eq

@[simp]
/--
theorem `interior_univ` / 定理 `interior_univ`

English:
theorem interior_univ
  statement: interior (univ : Set X) = univ
  proof: isOpen_univ.interior_eq

@[simp]

中文:
定理 interior_univ
  结论: interior (univ : 集合 X) = univ
  证明: isOpen_univ.interior_eq

@[simp]

Depends on / 依赖: interior_eq, isOpen_univ, isOpen_univ.interior_eq
-/
theorem interior_univ : interior (univ : Set X) = univ :=
  isOpen_univ.interior_eq

@[simp]
/--
theorem `interior_eq_univ` / 定理 `interior_eq_univ`

English:
theorem interior_eq_univ
  statement: interior s = univ ↔ s = univ
  proof: ⟨fun h => univ_subset_iff.mp h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩

@[simp]

中文:
定理 interior_eq_univ
  结论: interior s = univ ↔ s = univ
  证明: ⟨fun h => univ_subset_iff.mp h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩

@[simp]

Depends on / 依赖: h.symm, h.symm.trans_le, interior_subset, interior_univ, trans_le, univ_subset_iff, univ_subset_iff.mp
-/
theorem interior_eq_univ : interior s = univ ↔ s = univ :=
⟨fun h => univ_subset_iff.mp h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩

@[simp]
/--
theorem `interior_interior` / 定理 `interior_interior`

English:
theorem interior_interior
  statement: interior (interior s) = interior s
  proof: isOpen_interior.interior_eq

@[simp]

中文:
定理 interior_interior
  结论: interior (interior s) = interior s
  证明: isOpen_interior.interior_eq

@[simp]

Depends on / 依赖: interior_eq, isOpen_interior, isOpen_interior.interior_eq
-/
theorem interior_interior : interior (interior s) = interior s :=
  isOpen_interior.interior_eq

@[simp]
/--
theorem `interior_inter` / 定理 `interior_inter`

English:
theorem interior_inter
  statement: interior (s inter t) = interior s inter interior t
  proof: (Monotone.map_inf_le (fun _ _ => interior_mono) s t).antisymm
interior_maximal (inter_subset_inter interior_subset interior_subset)
      isOpen_interior.inter isOpen_interior

中文:
定理 interior_inter
  结论: interior (s inter t) = interior s inter interior t
  证明: (Monotone.map_inf_le (fun _ _ => interior_mono) s t).antisymm
interior_maximal (inter_subset_inter interior_subset interior_subset)
      isOpen_interior.inter isOpen_interior

Depends on / 依赖: Monotone, Monotone.map_inf_le, antisymm, inter_subset_inter, interior_maximal, interior_mono, interior_subset, isOpen_interior, isOpen_interior.inter, map_inf_le
-/
theorem interior_inter : interior (s inter t) = interior s inter interior t :=
(Monotone.map_inf_le (fun _ _ => interior_mono) s t).antisymm
interior_maximal (inter_subset_inter interior_subset interior_subset)
      isOpen_interior.inter isOpen_interior

/--
theorem `Set.Finite.interior_biInter` / 定理 `Set.Finite.interior_biInter`

English:
theorem Set.Finite.interior_biInter
  given: {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> Set X)
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ _ => simp [*]

中文:
定理 集合.有限.interior_bi整数er
  条件: {ι : 类型} {s : 集合 ι} (hs : s.有限) (f : ι -> 集合 X)
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ _ => simp [*]

Depends on / 依赖: Finite, Set.Finite.induction_on, induction_on, insert
-/
theorem Set.Finite.interior_biInter {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> Set X) :
    interior (⋂ i in s, f i) = ⋂ i in s, interior (f i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ _ => simp [*]

/--
theorem `Set.Finite.interior_sInter` / 定理 `Set.Finite.interior_sInter`

English:
theorem Set.Finite.interior_sInter
  given: {S : Set (Set X)} (hS : S.Finite)
  proof: by
  rw [sInter_eq_biInter]; rw [hS.interior_biInter]

@[simp]

中文:
定理 集合.有限.interior_s整数er
  条件: {S : 集合 (集合 X)} (hS : S.有限)
  证明: by
  rw [sInter_eq_biInter]; rw [hS.interior_biInter]

@[simp]

Depends on / 依赖: hS.interior_biInter, interior_biInter, sInter_eq_biInter
-/
theorem Set.Finite.interior_sInter {S : Set (Set X)} (hS : S.Finite) :
    interior (⋂₀ S) = ⋂ s in S, interior s := by
  rw [sInter_eq_biInter]; rw [hS.interior_biInter]

@[simp]
/--
theorem `Finset.interior_iInter` / 定理 `Finset.interior_iInter`

English:
theorem Finset.interior_iInter
  given: {ι : Type*} (s : Finset ι) (f : ι -> Set X)
  proof: s.finite_toSet.interior_biInter f

@[simp]

中文:
定理 有限集.interior_i整数er
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 集合 X)
  证明: s.finite_toSet.interior_biInter f

@[simp]

Depends on / 依赖: finite_toSet, interior_biInter, s.finite_toSet.interior_biInter
-/
theorem Finset.interior_iInter {ι : Type*} (s : Finset ι) (f : ι -> Set X) :
    interior (⋂ i in s, f i) = ⋂ i in s, interior (f i) :=
  s.finite_toSet.interior_biInter f

@[simp]
/--
theorem `interior_iInter_of_finite` / 定理 `interior_iInter_of_finite`

English:
theorem interior_iInter_of_finite
  given: [Finite ι] (f : ι -> Set X)
  proof: by
  rw [← sInter_range]; rw [(finite_range f).interior_sInter]; rw [biInter_range]

@[simp]

中文:
定理 interior_i整数er_of_finite
  条件: [有限 ι] (f : ι -> 集合 X)
  证明: by
  rw [← sInter_range]; rw [(finite_range f).interior_sInter]; rw [biInter_range]

@[simp]

Depends on / 依赖: biInter_range, finite_range, interior_sInter, sInter_range
-/
theorem interior_iInter_of_finite [Finite ι] (f : ι -> Set X) :
    interior (⋂ i, f i) = ⋂ i, interior (f i) := by
  rw [← sInter_range]; rw [(finite_range f).interior_sInter]; rw [biInter_range]

@[simp]
/--
theorem `interior_iInter₂_lt_nat` / 定理 `interior_iInter₂_lt_nat`

English:
theorem interior_iInter₂_lt_nat
  given: {n : Nat} (f : Nat -> Set X)
  proof: (finite_lt_nat n).interior_biInter f

@[simp]

中文:
定理 interior_i整数er₂_lt_nat
  条件: {n : 自然数} (f : 自然数 -> 集合 X)
  证明: (finite_lt_nat n).interior_biInter f

@[simp]

Depends on / 依赖: finite_lt_nat, interior_biInter
-/
theorem interior_iInter₂_lt_nat {n : Nat} (f : Nat -> Set X) :
    interior (⋂ m < n, f m) = ⋂ m < n, interior (f m) :=
  (finite_lt_nat n).interior_biInter f

@[simp]
/--
theorem `interior_iInter₂_le_nat` / 定理 `interior_iInter₂_le_nat`

English:
theorem interior_iInter₂_le_nat
  given: {n : Nat} (f : Nat -> Set X)
  proof: (finite_le_nat n).interior_biInter f

中文:
定理 interior_i整数er₂_le_nat
  条件: {n : 自然数} (f : 自然数 -> 集合 X)
  证明: (finite_le_nat n).interior_biInter f

Depends on / 依赖: finite_le_nat, interior_biInter
-/
theorem interior_iInter₂_le_nat {n : Nat} (f : Nat -> Set X) :
    interior (⋂ m <= n, f m) = ⋂ m <= n, interior (f m) :=
  (finite_le_nat n).interior_biInter f

/--
theorem `interior_union_inter_interior_compl_left_subset` / 定理 `interior_union_inter_interior_compl_left_subset`

English:
theorem interior_union_inter_interior_compl_left_subset
  proof: interior_inter.symm.trans_subset interior_mono (union_inter_compl_left_subset ..)

中文:
定理 interior_union_inter_interior_compl_left_subset
  证明: interior_inter.symm.trans_subset interior_mono (union_inter_compl_left_subset ..)

Depends on / 依赖: interior_inter, interior_inter.symm.trans_subset, interior_mono, trans_subset, union_inter_compl_left_subset
-/
theorem interior_union_inter_interior_compl_left_subset :
    interior (s union t) inter interior sᶜ subseteq interior t :=
interior_inter.symm.trans_subset interior_mono (union_inter_compl_left_subset ..)

/--
theorem `interior_union_inter_interior_compl_right_subset` / 定理 `interior_union_inter_interior_compl_right_subset`

English:
theorem interior_union_inter_interior_compl_right_subset
  proof: interior_inter.symm.trans_subset interior_mono (union_inter_compl_right_subset ..)

中文:
定理 interior_union_inter_interior_compl_right_subset
  证明: interior_inter.symm.trans_subset interior_mono (union_inter_compl_right_subset ..)

Depends on / 依赖: interior_inter, interior_inter.symm.trans_subset, interior_mono, trans_subset, union_inter_compl_right_subset
-/
theorem interior_union_inter_interior_compl_right_subset :
    interior (s union t) inter interior tᶜ subseteq interior s :=
interior_inter.symm.trans_subset interior_mono (union_inter_compl_right_subset ..)

/--
theorem `interior_union_isClosed_of_interior_empty` / 定理 `interior_union_isClosed_of_interior_empty`

English:
theorem interior_union_isClosed_of_interior_empty
  statement: (h₁ : IsClosed s)
  proof: have : interior (s union t) subseteq s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u subseteq s union t)⟩, (hx₁ : x in u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s subseteq t := fun _ ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s subseteq interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s subseteq ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono subset_union_left)

中文:
定理 interior_union_isClosed_of_interior_empty
  结论: (h₁ : 是闭集 s)
  证明: have : interior (s union t) subseteq s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u subseteq s union t)⟩, (hx₁ : x in u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s subseteq t := fun _ ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s subseteq interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s subseteq ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono subset_union_left)

Depends on / 依赖: IsOpen, IsOpen.sdiff, Or.resolve_left, Subset, Subset.antisymm, antisymm, by_contradiction, interior, interior_maximal, interior_mono, isOpen_interior, resolve_left, subset_interior_iff, subset_union_left, subseteq
-/
theorem interior_union_isClosed_of_interior_empty (h₁ : IsClosed s)
    (h₂ : interior t = ∅) : interior (s union t) = interior s :=
  have : interior (s union t) subseteq s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u subseteq s union t)⟩, (hx₁ : x in u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s subseteq t := fun _ ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s subseteq interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s subseteq ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono subset_union_left)

/--
theorem `isOpen_iff_forall_mem_open` / 定理 `isOpen_iff_forall_mem_open`

English:
theorem isOpen_iff_forall_mem_open
  statement: IsOpen s ↔ forall x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
  proof: by
  rw [← subset_interior_iff_isOpen]
  simp only [subset_def, mem_interior]

中文:
定理 isOpen_iff_对任意_mem_open
  结论: 是开集 s ↔ 对任意 x in s, 存在 t, t subseteq s ∧ 是开集 t ∧ x in t
  证明: by
  rw [← subset_interior_iff_isOpen]
  simp only [subset_def, mem_interior]

Depends on / 依赖: mem_interior, subset_def, subset_interior_iff_isOpen
-/
theorem isOpen_iff_forall_mem_open : IsOpen s ↔ forall x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t := by
  rw [← subset_interior_iff_isOpen]
  simp only [subset_def, mem_interior]

/--
theorem `interior_iInter_subset` / 定理 `interior_iInter_subset`

English:
theorem interior_iInter_subset
  given: (s : ι -> Set X)
  statement: interior (⋂ i, s i) subseteq ⋂ i, interior (s i)
  proof: subset_iInter fun _ => interior_mono iInter_subset _ _

中文:
定理 interior_i整数er_subset
  条件: (s : ι -> 集合 X)
  结论: interior (⋂ i, s i) subseteq ⋂ i, interior (s i)
  证明: subset_iInter fun _ => interior_mono iInter_subset _ _

Depends on / 依赖: iInter_subset, interior_mono, subset_iInter
-/
theorem interior_iInter_subset (s : ι -> Set X) : interior (⋂ i, s i) subseteq ⋂ i, interior (s i) :=
subset_iInter fun _ => interior_mono iInter_subset _ _

/--
theorem `interior_iInter₂_subset` / 定理 `interior_iInter₂_subset`

English:
theorem interior_iInter₂_subset
  given: (p : ι -> Sort*) (s : forall i, p i -> Set X)
  proof: (interior_iInter_subset _).trans iInter_mono fun _ => interior_iInter_subset _

中文:
定理 interior_i整数er₂_subset
  条件: (p : ι -> 类型层*) (s : 对任意 i, p i -> 集合 X)
  证明: (interior_iInter_subset _).trans iInter_mono fun _ => interior_iInter_subset _

Depends on / 依赖: iInter_mono, interior_iInter_subset
-/
theorem interior_iInter₂_subset (p : ι -> Sort*) (s : forall i, p i -> Set X) :
    interior (⋂ (i) (j), s i j) subseteq ⋂ (i) (j), interior (s i j) :=
(interior_iInter_subset _).trans iInter_mono fun _ => interior_iInter_subset _

/--
theorem `interior_sInter_subset` / 定理 `interior_sInter_subset`

English:
theorem interior_sInter_subset
  given: (S : Set (Set X))
  statement: interior (⋂₀ S) subseteq ⋂ s in S, interior s
  proof: calc
    interior (⋂₀ S) = interior (⋂ s in S, s) := by rw [sInter_eq_biInter]
    _ subseteq ⋂ s in S, interior s := interior_iInter₂_subset _ _

中文:
定理 interior_s整数er_subset
  条件: (S : 集合 (集合 X))
  结论: interior (⋂₀ S) subseteq ⋂ s in S, interior s
  证明: calc
    interior (⋂₀ S) = interior (⋂ s in S, s) := by rw [sInter_eq_biInter]
    _ subseteq ⋂ s in S, interior s := interior_iInter₂_subset _ _

Depends on / 依赖: interior, sInter_eq_biInter, subseteq
-/
theorem interior_sInter_subset (S : Set (Set X)) : interior (⋂₀ S) subseteq ⋂ s in S, interior s :=
  calc
    interior (⋂₀ S) = interior (⋂ s in S, s) := by rw [sInter_eq_biInter]
    _ subseteq ⋂ s in S, interior s := interior_iInter₂_subset _ _

/--
theorem `Filter.HasBasis.lift'_interior` / 定理 `Filter.HasBasis.lift'_interior`

English:
theorem Filter.HasBasis.lift'_interior
  statement: {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
  proof: h.lift' fun _ _ => interior_mono

中文:
定理 滤子.有基.lift'_interior
  结论: {l : 滤子 X} {p : ι -> 命题} {s : ι -> 集合 X}
  证明: h.lift' fun _ _ => interior_mono

Depends on / 依赖: h.lift, interior_mono
-/
theorem Filter.HasBasis.lift'_interior {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
    (h : l.HasBasis p s) : (l.lift' interior).HasBasis p fun i => interior (s i) :=
  h.lift' fun _ _ => interior_mono

/--
theorem `Filter.lift'_interior_le` / 定理 `Filter.lift'_interior_le`

English:
theorem Filter.lift'_interior_le
  given: (l : Filter X)
  statement: l.lift' interior <= l
  proof: fun _s hs =>
  mem_of_superset (mem_lift' hs) interior_subset

中文:
定理 滤子.lift'_interior_le
  条件: (l : 滤子 X)
  结论: l.lift' interior <= l
  证明: fun _s hs =>
  mem_of_superset (mem_lift' hs) interior_subset
-/
theorem Filter.lift'_interior_le (l : Filter X) : l.lift' interior <= l := fun _s hs =>
  mem_of_superset (mem_lift' hs) interior_subset

/--
theorem `Filter.HasBasis.lift'_interior_eq_self` / 定理 `Filter.HasBasis.lift'_interior_eq_self`

English:
theorem Filter.HasBasis.lift'_interior_eq_self
  statement: {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
  proof: le_antisymm l.lift'_interior_le h.lift'_interior.ge_iff.2 fun i hi => by
    simpa only [(ho i hi).interior_eq] using h.mem_of_mem hi

中文:
定理 滤子.有基.lift'_interior_eq_self
  结论: {l : 滤子 X} {p : ι -> 命题} {s : ι -> 集合 X}
  证明: le_antisymm l.lift'_interior_le h.lift'_interior.ge_iff.2 fun i hi => by
    simpa only [(ho i hi).interior_eq] using h.mem_of_mem hi
-/
theorem Filter.HasBasis.lift'_interior_eq_self {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
    (h : l.HasBasis p s) (ho : forall i, p i -> IsOpen (s i)) : l.lift' interior = l :=
le_antisymm l.lift'_interior_le h.lift'_interior.ge_iff.2 fun i hi => by
    simpa only [(ho i hi).interior_eq] using h.mem_of_mem hi

end Interior

section Closure

@[simp, closedness ., grind .]
/--
theorem `isClosed_closure` / 定理 `isClosed_closure`

English:
theorem isClosed_closure
  statement: IsClosed (closure s)
  proof: isClosed_sInter fun _ => And.left

中文:
定理 isClosed_closure
  结论: 是闭集 (closure s)
  证明: isClosed_sInter fun _ => And.left

Depends on / 依赖: And.left, isClosed_sInter
-/
theorem isClosed_closure : IsClosed (closure s) :=
  isClosed_sInter fun _ => And.left

/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  statement: s subseteq closure s
  proof: subset_sInter fun _ => And.right

中文:
定理 subset_closure
  结论: s subseteq closure s
  证明: subset_sInter fun _ => And.right

Depends on / 依赖: And.right, subset_sInter
-/
theorem subset_closure : s subseteq closure s :=
  subset_sInter fun _ => And.right

/--
theorem `notMem_of_notMem_closure` / 定理 `notMem_of_notMem_closure`

English:
theorem notMem_of_notMem_closure
  given: {P : X} (hP : P ∉ closure s)
  statement: P ∉ s
  proof: fun h =>
  hP (subset_closure h)

中文:
定理 notMem_of_notMem_closure
  条件: {P : X} (hP : P ∉ closure s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure h)
-/
theorem notMem_of_notMem_closure {P : X} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/--
theorem `closure_minimal` / 定理 `closure_minimal`

English:
theorem closure_minimal
  given: (h₁ : s subseteq t) (h₂ : IsClosed t)
  statement: closure s subseteq t
  proof: sInter_subset_of_mem ⟨h₂, h₁⟩

中文:
定理 closure_minimal
  条件: (h₁ : s subseteq t) (h₂ : 是闭集 t)
  结论: closure s subseteq t
  证明: sInter_subset_of_mem ⟨h₂, h₁⟩

Depends on / 依赖: sInter_subset_of_mem
-/
theorem closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) : closure s subseteq t :=
  sInter_subset_of_mem ⟨h₂, h₁⟩

/--
theorem `Disjoint.closure_left` / 定理 `Disjoint.closure_left`

English:
theorem Disjoint.closure_left
  given: (hd : Disjoint s t) (ht : IsOpen t)
  proof: disjoint_compl_left.mono_left closure_minimal hd.subset_compl_right ht.isClosed_compl

中文:
定理 Disjoint.closure_left
  条件: (hd : Disjoint s t) (ht : 是开集 t)
  证明: disjoint_compl_left.mono_left closure_minimal hd.subset_compl_right ht.isClosed_compl

Depends on / 依赖: closure_minimal, disjoint_compl_left, disjoint_compl_left.mono_left, hd.subset_compl_right, ht.isClosed_compl, isClosed_compl, mono_left, subset_compl_right
-/
theorem Disjoint.closure_left (hd : Disjoint s t) (ht : IsOpen t) :
    Disjoint (closure s) t :=
disjoint_compl_left.mono_left closure_minimal hd.subset_compl_right ht.isClosed_compl

/--
theorem `Disjoint.closure_right` / 定理 `Disjoint.closure_right`

English:
theorem Disjoint.closure_right
  given: (hd : Disjoint s t) (hs : IsOpen s)
  proof: (hd.symm.closure_left hs).symm

@[simp, closedness =]

中文:
定理 Disjoint.closure_right
  条件: (hd : Disjoint s t) (hs : 是开集 s)
  证明: (hd.symm.closure_left hs).symm

@[simp, closedness =]

Depends on / 依赖: closure_left, hd.symm.closure_left
-/
theorem Disjoint.closure_right (hd : Disjoint s t) (hs : IsOpen s) :
    Disjoint s (closure t) :=
  (hd.symm.closure_left hs).symm

@[simp, closedness =]
/--
theorem `IsClosed.closure_eq` / 定理 `IsClosed.closure_eq`

English:
theorem IsClosed.closure_eq
  given: (h : IsClosed s)
  statement: closure s = s
  proof: Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure

中文:
定理 是闭集.closure_eq
  条件: (h : 是闭集 s)
  结论: closure s = s
  证明: Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure
-/
theorem IsClosed.closure_eq (h : IsClosed s) : closure s = s :=
  Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure

/--
theorem `forall_isClosed_iff` / 定理 `forall_isClosed_iff`

English:
theorem forall_isClosed_iff
  given: {p : Set X -> Prop}
  proof: ⟨fun h t => h (closure t) isClosed_closure, fun h t ht => ht.closure_eq ▸ h t⟩

中文:
定理 对任意_isClosed_iff
  条件: {p : 集合 X -> 命题}
  证明: ⟨fun h t => h (closure t) isClosed_closure, fun h t ht => ht.closure_eq ▸ h t⟩

Depends on / 依赖: closure, closure_eq, ht.closure_eq, isClosed_closure
-/
theorem forall_isClosed_iff {p : Set X -> Prop} :
    (forall t, IsClosed t -> p t) ↔ forall t, p (closure t) :=
  ⟨fun h t => h (closure t) isClosed_closure, fun h t ht => ht.closure_eq ▸ h t⟩

/--
theorem `exists_isClosed_iff` / 定理 `exists_isClosed_iff`

English:
theorem exists_isClosed_iff
  given: {p : Set X -> Prop}
  proof: ⟨fun ⟨_, h⟩ => ⟨_, h.1.closure_eq ▸ h.2⟩, fun ⟨_, h⟩ => ⟨_, isClosed_closure, h⟩⟩

中文:
定理 存在_isClosed_iff
  条件: {p : 集合 X -> 命题}
  证明: ⟨fun ⟨_, h⟩ => ⟨_, h.1.closure_eq ▸ h.2⟩, fun ⟨_, h⟩ => ⟨_, isClosed_closure, h⟩⟩

Depends on / 依赖: closure_eq, isClosed_closure
-/
theorem exists_isClosed_iff {p : Set X -> Prop} :
    (exists t, IsClosed t ∧ p t) ↔ exists t, p (closure t) :=
  ⟨fun ⟨_, h⟩ => ⟨_, h.1.closure_eq ▸ h.2⟩, fun ⟨_, h⟩ => ⟨_, isClosed_closure, h⟩⟩

/--
theorem `IsClosed.closure_subset` / 定理 `IsClosed.closure_subset`

English:
theorem IsClosed.closure_subset
  given: (hs : IsClosed s)
  statement: closure s subseteq s
  proof: closure_minimal (Subset.refl _) hs

中文:
定理 是闭集.closure_subset
  条件: (hs : 是闭集 s)
  结论: closure s subseteq s
  证明: closure_minimal (Subset.refl _) hs

Depends on / 依赖: Subset, Subset.refl, closure_minimal
-/
theorem IsClosed.closure_subset (hs : IsClosed s) : closure s subseteq s :=
  closure_minimal (Subset.refl _) hs

/--
theorem `IsClosed.closure_subset_iff` / 定理 `IsClosed.closure_subset_iff`

English:
theorem IsClosed.closure_subset_iff
  given: (h₁ : IsClosed t)
  statement: closure s subseteq t ↔ s subseteq t
  proof: ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩

中文:
定理 是闭集.closure_subset_iff
  条件: (h₁ : 是闭集 t)
  结论: closure s subseteq t ↔ s subseteq t
  证明: ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩

Depends on / 依赖: Subset, Subset.trans, closure_minimal, subset_closure
-/
theorem IsClosed.closure_subset_iff (h₁ : IsClosed t) : closure s subseteq t ↔ s subseteq t :=
  ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩

/--
theorem `IsClosed.mem_iff_closure_subset` / 定理 `IsClosed.mem_iff_closure_subset`

English:
theorem IsClosed.mem_iff_closure_subset
  given: (hs : IsClosed s)
  proof: (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm

@[mono, gcongr]

中文:
定理 是闭集.mem_iff_closure_subset
  条件: (hs : 是闭集 s)
  证明: (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm

@[mono, gcongr]

Depends on / 依赖: Set.singleton_subset_iff, closure_subset_iff, hs.closure_subset_iff.trans, singleton_subset_iff
-/
theorem IsClosed.mem_iff_closure_subset (hs : IsClosed s) :
    x in s ↔ closure ({x} : Set X) subseteq s :=
  (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm

@[mono, gcongr]
/--
theorem `closure_mono` / 定理 `closure_mono`

English:
theorem closure_mono
  given: (h : s subseteq t)
  statement: closure s subseteq closure t
  proof: closure_minimal (Subset.trans h subset_closure) isClosed_closure

中文:
定理 closure_mono
  条件: (h : s subseteq t)
  结论: closure s subseteq closure t
  证明: closure_minimal (Subset.trans h subset_closure) isClosed_closure

Depends on / 依赖: Subset, Subset.trans, closure_minimal, isClosed_closure, subset_closure
-/
theorem closure_mono (h : s subseteq t) : closure s subseteq closure t :=
  closure_minimal (Subset.trans h subset_closure) isClosed_closure

/--
theorem `monotone_closure` / 定理 `monotone_closure`

English:
theorem monotone_closure
  given: (X : Type*) [TopologicalSpace X]
  statement: Monotone (@closure X _)
  proof: fun _ _ =>
  closure_mono

中文:
定理 monotone_closure
  条件: (X : 类型) [拓扑空间 X]
  结论: 递增 (@closure X _)
  证明: fun _ _ =>
  closure_mono
-/
theorem monotone_closure (X : Type*) [TopologicalSpace X] : Monotone (@closure X _) := fun _ _ =>
  closure_mono

/--
theorem `closure_inter_subset` / 定理 `closure_inter_subset`

English:
theorem closure_inter_subset
  statement: closure (s inter t) subseteq closure s inter closure t
  proof: subset_inter (closure_mono inter_subset_left) (closure_mono inter_subset_right)

中文:
定理 closure_inter_subset
  结论: closure (s inter t) subseteq closure s inter closure t
  证明: subset_inter (closure_mono inter_subset_left) (closure_mono inter_subset_right)

Depends on / 依赖: closure_mono, inter_subset_left, inter_subset_right, subset_inter
-/
theorem closure_inter_subset : closure (s inter t) subseteq closure s inter closure t :=
  subset_inter (closure_mono inter_subset_left) (closure_mono inter_subset_right)

/--
theorem `sdiff_subset_closure_iff` / 定理 `sdiff_subset_closure_iff`

English:
theorem sdiff_subset_closure_iff
  statement: s \ t subseteq closure t ↔ s subseteq closure t
  proof: by
  rw [sdiff_subset_iff]; rw [union_eq_self_of_subset_left subset_closure]

@[deprecated (since := "2026-06-03")] alias diff_subset_closure_iff := sdiff_subset_closure_iff

中文:
定理 sdiff_subset_closure_iff
  结论: s \ t subseteq closure t ↔ s subseteq closure t
  证明: by
  rw [sdiff_subset_iff]; rw [union_eq_self_of_subset_left subset_closure]

@[deprecated (since := "2026-06-03")] alias diff_subset_closure_iff := sdiff_subset_closure_iff

Depends on / 依赖: sdiff_subset_iff, subset_closure, union_eq_self_of_subset_left
-/
theorem sdiff_subset_closure_iff : s \ t subseteq closure t ↔ s subseteq closure t := by
  rw [sdiff_subset_iff]; rw [union_eq_self_of_subset_left subset_closure]

@[deprecated (since := "2026-06-03")] alias diff_subset_closure_iff := sdiff_subset_closure_iff

/--
theorem `closure_inter_subset_inter_closure` / 定理 `closure_inter_subset_inter_closure`

English:
theorem closure_inter_subset_inter_closure
  given: (s t : Set X)
  proof: (monotone_closure X).map_inf_le s t

中文:
定理 closure_inter_subset_inter_closure
  条件: (s t : 集合 X)
  证明: (monotone_closure X).map_inf_le s t

Depends on / 依赖: map_inf_le, monotone_closure
-/
theorem closure_inter_subset_inter_closure (s t : Set X) :
    closure (s inter t) subseteq closure s inter closure t :=
  (monotone_closure X).map_inf_le s t

/--
theorem `isClosed_of_closure_subset` / 定理 `isClosed_of_closure_subset`

English:
theorem isClosed_of_closure_subset
  given: (h : closure s subseteq s)
  statement: IsClosed s
  proof: by
  rw [subset_closure.antisymm h]; exact isClosed_closure

中文:
定理 isClosed_of_closure_subset
  条件: (h : closure s subseteq s)
  结论: 是闭集 s
  证明: by
  rw [subset_closure.antisymm h]; exact isClosed_closure

Depends on / 依赖: antisymm, isClosed_closure, subset_closure, subset_closure.antisymm
-/
theorem isClosed_of_closure_subset (h : closure s subseteq s) : IsClosed s := by
  rw [subset_closure.antisymm h]; exact isClosed_closure

/--
theorem `closure_eq_iff_isClosed` / 定理 `closure_eq_iff_isClosed`

English:
theorem closure_eq_iff_isClosed
  statement: closure s = s ↔ IsClosed s
  proof: ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩

中文:
定理 closure_eq_iff_isClosed
  结论: closure s = s ↔ 是闭集 s
  证明: ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩

Depends on / 依赖: IsClosed, IsClosed.closure_eq, closure_eq, isClosed_closure
-/
theorem closure_eq_iff_isClosed : closure s = s ↔ IsClosed s :=
  ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩

/--
theorem `closure_subset_iff_isClosed` / 定理 `closure_subset_iff_isClosed`

English:
theorem closure_subset_iff_isClosed
  statement: closure s subseteq s ↔ IsClosed s
  proof: ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩

中文:
定理 closure_subset_iff_isClosed
  结论: closure s subseteq s ↔ 是闭集 s
  证明: ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩

Depends on / 依赖: IsClosed, IsClosed.closure_subset, closure_subset, isClosed_of_closure_subset
-/
theorem closure_subset_iff_isClosed : closure s subseteq s ↔ IsClosed s :=
  ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩

/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set X) = ∅
  proof: isClosed_empty.closure_eq

@[simp]

中文:
定理 closure_empty
  结论: closure (∅ : 集合 X) = ∅
  证明: isClosed_empty.closure_eq

@[simp]

Depends on / 依赖: closure_eq, isClosed_empty, isClosed_empty.closure_eq
-/
theorem closure_empty : closure (∅ : Set X) = ∅ :=
  isClosed_empty.closure_eq

@[simp]
/--
theorem `closure_empty_iff` / 定理 `closure_empty_iff`

English:
theorem closure_empty_iff
  given: (s : Set X)
  statement: closure s = ∅ ↔ s = ∅
  proof: ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]

中文:
定理 closure_empty_iff
  条件: (s : 集合 X)
  结论: closure s = ∅ ↔ s = ∅
  证明: ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]

Depends on / 依赖: closure_empty, h.symm, subset_closure, subset_eq_empty
-/
theorem closure_empty_iff (s : Set X) : closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]
/--
theorem `closure_nonempty_iff` / 定理 `closure_nonempty_iff`

English:
theorem closure_nonempty_iff
  statement: (closure s).Nonempty ↔ s.Nonempty
  proof: by
  simp only [nonempty_iff_ne_empty, Ne, closure_empty_iff]

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff

中文:
定理 closure_nonempty_iff
  结论: (closure s).非空 ↔ s.非空
  证明: by
  simp only [nonempty_iff_ne_empty, Ne, closure_empty_iff]

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff

Depends on / 依赖: closure_empty_iff, nonempty_iff_ne_empty
-/
theorem closure_nonempty_iff : (closure s).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, closure_empty_iff]

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff

/--
theorem `closure_univ` / 定理 `closure_univ`

English:
theorem closure_univ
  statement: closure (univ : Set X) = univ
  proof: isClosed_univ.closure_eq

中文:
定理 closure_univ
  结论: closure (univ : 集合 X) = univ
  证明: isClosed_univ.closure_eq

Depends on / 依赖: closure_eq, isClosed_univ, isClosed_univ.closure_eq
-/
theorem closure_univ : closure (univ : Set X) = univ :=
  isClosed_univ.closure_eq

/--
theorem `closure_closure` / 定理 `closure_closure`

English:
theorem closure_closure
  statement: closure (closure s) = closure s
  proof: isClosed_closure.closure_eq

中文:
定理 closure_closure
  结论: closure (closure s) = closure s
  证明: isClosed_closure.closure_eq

Depends on / 依赖: closure_eq, isClosed_closure, isClosed_closure.closure_eq
-/
theorem closure_closure : closure (closure s) = closure s :=
  isClosed_closure.closure_eq

/--
theorem `closure_eq_compl_interior_compl` / 定理 `closure_eq_compl_interior_compl`

English:
theorem closure_eq_compl_interior_compl
  statement: closure s = (interior sᶜ)ᶜ
  proof: by
  rw [interior]; rw [closure]; rw [compl_sUnion]; rw [compl_image_ofPred]
  simp only [compl_subset_compl, isOpen_compl_iff]

@[simp]

中文:
定理 closure_eq_compl_interior_compl
  结论: closure s = (interior sᶜ)ᶜ
  证明: by
  rw [interior]; rw [closure]; rw [compl_sUnion]; rw [compl_image_ofPred]
  simp only [compl_subset_compl, isOpen_compl_iff]

@[simp]

Depends on / 依赖: closure, compl_image_ofPred, compl_sUnion, compl_subset_compl, interior, isOpen_compl_iff
-/
theorem closure_eq_compl_interior_compl : closure s = (interior sᶜ)ᶜ := by
  rw [interior]; rw [closure]; rw [compl_sUnion]; rw [compl_image_ofPred]
  simp only [compl_subset_compl, isOpen_compl_iff]

@[simp]
/--
theorem `closure_union` / 定理 `closure_union`

English:
theorem closure_union
  statement: closure (s union t) = closure s union closure t
  proof: by
  simp [closure_eq_compl_interior_compl, compl_inter]

中文:
定理 closure_union
  结论: closure (s union t) = closure s union closure t
  证明: by
  simp [closure_eq_compl_interior_compl, compl_inter]

Depends on / 依赖: closure_eq_compl_interior_compl, compl_inter
-/
theorem closure_union : closure (s union t) = closure s union closure t := by
  simp [closure_eq_compl_interior_compl, compl_inter]

/--
theorem `Set.Finite.closure_biUnion` / 定理 `Set.Finite.closure_biUnion`

English:
theorem Set.Finite.closure_biUnion
  given: {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> Set X)
  proof: by
  simp [closure_eq_compl_interior_compl, hs.interior_biInter]

中文:
定理 集合.有限.closure_biUnion
  条件: {ι : 类型} {s : 集合 ι} (hs : s.有限) (f : ι -> 集合 X)
  证明: by
  simp [closure_eq_compl_interior_compl, hs.interior_biInter]

Depends on / 依赖: closure_eq_compl_interior_compl, hs.interior_biInter, interior_biInter
-/
theorem Set.Finite.closure_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> Set X) :
    closure (⋃ i in s, f i) = ⋃ i in s, closure (f i) := by
  simp [closure_eq_compl_interior_compl, hs.interior_biInter]

/--
theorem `Set.Finite.closure_sUnion` / 定理 `Set.Finite.closure_sUnion`

English:
theorem Set.Finite.closure_sUnion
  given: {S : Set (Set X)} (hS : S.Finite)
  proof: by
  rw [sUnion_eq_biUnion]; rw [hS.closure_biUnion]

@[simp]

中文:
定理 集合.有限.closure_sUnion
  条件: {S : 集合 (集合 X)} (hS : S.有限)
  证明: by
  rw [sUnion_eq_biUnion]; rw [hS.closure_biUnion]

@[simp]

Depends on / 依赖: closure_biUnion, hS.closure_biUnion, sUnion_eq_biUnion
-/
theorem Set.Finite.closure_sUnion {S : Set (Set X)} (hS : S.Finite) :
    closure (⋃₀ S) = ⋃ s in S, closure s := by
  rw [sUnion_eq_biUnion]; rw [hS.closure_biUnion]

@[simp]
/--
theorem `Finset.closure_biUnion` / 定理 `Finset.closure_biUnion`

English:
theorem Finset.closure_biUnion
  given: {ι : Type*} (s : Finset ι) (f : ι -> Set X)
  proof: s.finite_toSet.closure_biUnion f

@[simp]

中文:
定理 有限集.closure_biUnion
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 集合 X)
  证明: s.finite_toSet.closure_biUnion f

@[simp]

Depends on / 依赖: closure_biUnion, finite_toSet, s.finite_toSet.closure_biUnion
-/
theorem Finset.closure_biUnion {ι : Type*} (s : Finset ι) (f : ι -> Set X) :
    closure (⋃ i in s, f i) = ⋃ i in s, closure (f i) :=
  s.finite_toSet.closure_biUnion f

@[simp]
/--
theorem `closure_iUnion_of_finite` / 定理 `closure_iUnion_of_finite`

English:
theorem closure_iUnion_of_finite
  given: [Finite ι] (f : ι -> Set X)
  proof: by
  rw [← sUnion_range]; rw [(finite_range _).closure_sUnion]; rw [biUnion_range]

@[simp]

中文:
定理 closure_iUnion_of_finite
  条件: [有限 ι] (f : ι -> 集合 X)
  证明: by
  rw [← sUnion_range]; rw [(finite_range _).closure_sUnion]; rw [biUnion_range]

@[simp]

Depends on / 依赖: biUnion_range, closure_sUnion, finite_range, sUnion_range
-/
theorem closure_iUnion_of_finite [Finite ι] (f : ι -> Set X) :
    closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  rw [← sUnion_range]; rw [(finite_range _).closure_sUnion]; rw [biUnion_range]

@[simp]
/--
theorem `closure_iUnion₂_lt_nat` / 定理 `closure_iUnion₂_lt_nat`

English:
theorem closure_iUnion₂_lt_nat
  given: {n : Nat} (f : Nat -> Set X)
  proof: (finite_lt_nat n).closure_biUnion f

@[simp]

中文:
定理 closure_iUnion₂_lt_nat
  条件: {n : 自然数} (f : 自然数 -> 集合 X)
  证明: (finite_lt_nat n).closure_biUnion f

@[simp]

Depends on / 依赖: closure_biUnion, finite_lt_nat
-/
theorem closure_iUnion₂_lt_nat {n : Nat} (f : Nat -> Set X) :
    closure (⋃ m < n, f m) = ⋃ m < n, closure (f m) :=
  (finite_lt_nat n).closure_biUnion f

@[simp]
/--
theorem `closure_iUnion₂_le_nat` / 定理 `closure_iUnion₂_le_nat`

English:
theorem closure_iUnion₂_le_nat
  given: {n : Nat} (f : Nat -> Set X)
  proof: (finite_le_nat n).closure_biUnion f

中文:
定理 closure_iUnion₂_le_nat
  条件: {n : 自然数} (f : 自然数 -> 集合 X)
  证明: (finite_le_nat n).closure_biUnion f

Depends on / 依赖: closure_biUnion, finite_le_nat
-/
theorem closure_iUnion₂_le_nat {n : Nat} (f : Nat -> Set X) :
    closure (⋃ m <= n, f m) = ⋃ m <= n, closure (f m) :=
  (finite_le_nat n).closure_biUnion f

/--
theorem `subset_closure_inter_union_closure_compl_left` / 定理 `subset_closure_inter_union_closure_compl_left`

English:
theorem subset_closure_inter_union_closure_compl_left
  proof: (closure_mono <| subset_inter_union_compl_left ..).trans_eq closure_union

中文:
定理 subset_closure_inter_union_closure_compl_left
  证明: (closure_mono <| subset_inter_union_compl_left ..).trans_eq closure_union

Depends on / 依赖: closure_mono, closure_union, subset_inter_union_compl_left, trans_eq
-/
theorem subset_closure_inter_union_closure_compl_left :
    closure t subseteq closure (s inter t) union closure sᶜ :=
  (closure_mono <| subset_inter_union_compl_left ..).trans_eq closure_union

/--
theorem `subset_closure_inter_union_closure_compl_right` / 定理 `subset_closure_inter_union_closure_compl_right`

English:
theorem subset_closure_inter_union_closure_compl_right
  proof: (closure_mono <| subset_inter_union_compl_right ..).trans_eq closure_union

中文:
定理 subset_closure_inter_union_closure_compl_right
  证明: (closure_mono <| subset_inter_union_compl_right ..).trans_eq closure_union

Depends on / 依赖: closure_mono, closure_union, subset_inter_union_compl_right, trans_eq
-/
theorem subset_closure_inter_union_closure_compl_right :
    closure s subseteq closure (s inter t) union closure tᶜ :=
  (closure_mono <| subset_inter_union_compl_right ..).trans_eq closure_union

/--
theorem `interior_subset_closure` / 定理 `interior_subset_closure`

English:
theorem interior_subset_closure
  statement: interior s subseteq closure s
  proof: Subset.trans interior_subset subset_closure

@[simp]

中文:
定理 interior_subset_closure
  结论: interior s subseteq closure s
  证明: Subset.trans interior_subset subset_closure

@[simp]

Depends on / 依赖: Subset, Subset.trans, interior_subset, subset_closure
-/
theorem interior_subset_closure : interior s subseteq closure s :=
  Subset.trans interior_subset subset_closure

@[simp]
/--
theorem `interior_compl` / 定理 `interior_compl`

English:
theorem interior_compl
  statement: interior sᶜ = (closure s)ᶜ
  proof: by
  simp [closure_eq_compl_interior_compl]

@[simp]

中文:
定理 interior_compl
  结论: interior sᶜ = (closure s)ᶜ
  证明: by
  simp [closure_eq_compl_interior_compl]

@[simp]

Depends on / 依赖: closure_eq_compl_interior_compl
-/
theorem interior_compl : interior sᶜ = (closure s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

@[simp]
/--
theorem `closure_compl` / 定理 `closure_compl`

English:
theorem closure_compl
  statement: closure sᶜ = (interior s)ᶜ
  proof: by
  simp [closure_eq_compl_interior_compl]

中文:
定理 closure_compl
  结论: closure sᶜ = (interior s)ᶜ
  证明: by
  simp [closure_eq_compl_interior_compl]

Depends on / 依赖: closure_eq_compl_interior_compl
-/
theorem closure_compl : closure sᶜ = (interior s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

/--
theorem `interior_eq_compl_closure_compl` / 定理 `interior_eq_compl_closure_compl`

English:
theorem interior_eq_compl_closure_compl
  statement: interior s = (closure sᶜ)ᶜ
  proof: by simp

中文:
定理 interior_eq_compl_closure_compl
  结论: interior s = (closure sᶜ)ᶜ
  证明: by simp
-/
theorem interior_eq_compl_closure_compl : interior s = (closure sᶜ)ᶜ := by simp

/--
theorem `interior_union_of_disjoint_closure` / 定理 `interior_union_of_disjoint_closure`

English:
theorem interior_union_of_disjoint_closure
  given: (h : Disjoint (closure s) (closure t))
  proof: by
  have full : interior sᶜ union interior tᶜ = univ := by simpa [disjoint_iff, ← compl_inter] using h
  refine subset_antisymm ?_ subset_interior_union
  rw [← (interior _).inter_univ]; rw [← full]; rw [inter_union_distrib_left]
  exact union_subset
    (interior_union_inter_interior_compl_left_subset.trans subset_union_right)
    (interior_union_inter_interior_compl_right_subset.trans subset_union_left)

中文:
定理 interior_union_of_disjoint_closure
  条件: (h : Disjoint (closure s) (closure t))
  证明: by
  have full : interior sᶜ union interior tᶜ = univ := by simpa [disjoint_iff, ← compl_inter] using h
  refine subset_antisymm ?_ subset_interior_union
  rw [← (interior _).inter_univ]; rw [← full]; rw [inter_union_distrib_left]
  exact union_subset
    (interior_union_inter_interior_compl_left_subset.trans subset_union_right)
    (interior_union_inter_interior_compl_right_subset.trans subset_union_left)

Depends on / 依赖: compl_inter, disjoint_iff, inter_union_distrib_left, inter_univ, interior, interior_union_inter_interior_compl_left_subset, interior_union_inter_interior_compl_left_subset.trans, interior_union_inter_interior_compl_right_subset, interior_union_inter_interior_compl_right_subset.trans, subset_antisymm, subset_interior_union, subset_union_left, subset_union_right, union_subset
-/
theorem interior_union_of_disjoint_closure (h : Disjoint (closure s) (closure t)) :
    interior (s union t) = interior s union interior t := by
  have full : interior sᶜ union interior tᶜ = univ := by simpa [disjoint_iff, ← compl_inter] using h
  refine subset_antisymm ?_ subset_interior_union
  rw [← (interior _).inter_univ]; rw [← full]; rw [inter_union_distrib_left]
  exact union_subset
    (interior_union_inter_interior_compl_left_subset.trans subset_union_right)
    (interior_union_inter_interior_compl_right_subset.trans subset_union_left)

/--
theorem `closure_inter_of_codisjoint_interior` / 定理 `closure_inter_of_codisjoint_interior`

English:
theorem closure_inter_of_codisjoint_interior
  given: (h : Codisjoint (interior s) (interior t))
  proof: by
  rw [← compl_inj_iff]
  simp only [← interior_compl, compl_inter]
  apply interior_union_of_disjoint_closure
  simpa only [closure_compl, disjoint_compl_left_iff, ← codisjoint_iff_compl_le_left]

中文:
定理 closure_inter_of_codisjoint_interior
  条件: (h : Codisjoint (interior s) (interior t))
  证明: by
  rw [← compl_inj_iff]
  simp only [← interior_compl, compl_inter]
  apply interior_union_of_disjoint_closure
  simpa only [closure_compl, disjoint_compl_left_iff, ← codisjoint_iff_compl_le_left]

Depends on / 依赖: closure_compl, codisjoint_iff_compl_le_left, compl_inj_iff, compl_inter, disjoint_compl_left_iff, interior_compl, interior_union_of_disjoint_closure
-/
theorem closure_inter_of_codisjoint_interior (h : Codisjoint (interior s) (interior t)) :
    closure (s inter t) = closure s inter closure t := by
  rw [← compl_inj_iff]
  simp only [← interior_compl, compl_inter]
  apply interior_union_of_disjoint_closure
  simpa only [closure_compl, disjoint_compl_left_iff, ← codisjoint_iff_compl_le_left]

/--
theorem `mem_closure_iff` / 定理 `mem_closure_iff`

English:
theorem mem_closure_iff
  proof: ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s subseteq oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H _ ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨_, hc, hs⟩ := H _ h₁.isOpen_compl nc
      hc (h₂ hs)⟩

中文:
定理 mem_closure_iff
  证明: ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s subseteq oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H _ ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨_, hc, hs⟩ := H _ h₁.isOpen_compl nc
      hc (h₂ hs)⟩

Depends on / 依赖: by_contradiction, closure_minimal, isClosed_compl_iff, isOpen_compl, subseteq
-/
theorem mem_closure_iff :
    x in closure s ↔ forall o, IsOpen o -> x in o -> (o inter s).Nonempty :=
  ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s subseteq oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H _ ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨_, hc, hs⟩ := H _ h₁.isOpen_compl nc
      hc (h₂ hs)⟩

/--
theorem `closure_inter_open_nonempty_iff` / 定理 `closure_inter_open_nonempty_iff`

English:
theorem closure_inter_open_nonempty_iff
  given: (h : IsOpen t)
  proof: ⟨fun ⟨_x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
h.mono inf_le_inf_right t subset_closure⟩

中文:
定理 closure_inter_open_nonempty_iff
  条件: (h : 是开集 t)
  证明: ⟨fun ⟨_x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
h.mono inf_le_inf_right t subset_closure⟩

Depends on / 依赖: h.mono, inf_le_inf_right, inter_comm, mem_closure_iff, subset_closure
-/
theorem closure_inter_open_nonempty_iff (h : IsOpen t) :
    (closure s inter t).Nonempty ↔ (s inter t).Nonempty :=
  ⟨fun ⟨_x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
h.mono inf_le_inf_right t subset_closure⟩

/--
theorem `Filter.le_lift'_closure` / 定理 `Filter.le_lift'_closure`

English:
theorem Filter.le_lift'_closure
  given: (l : Filter X)
  statement: l <= l.lift' closure
  proof: le_lift'.2 fun _ h => mem_of_superset h subset_closure

中文:
定理 滤子.le_lift'_closure
  条件: (l : 滤子 X)
  结论: l <= l.lift' closure
  证明: le_lift'.2 fun _ h => mem_of_superset h subset_closure
-/
theorem Filter.le_lift'_closure (l : Filter X) : l <= l.lift' closure :=
  le_lift'.2 fun _ h => mem_of_superset h subset_closure

/--
theorem `Filter.HasBasis.lift'_closure` / 定理 `Filter.HasBasis.lift'_closure`

English:
theorem Filter.HasBasis.lift'_closure
  statement: {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
  proof: h.lift' (monotone_closure X)

中文:
定理 滤子.有基.lift'_closure
  结论: {l : 滤子 X} {p : ι -> 命题} {s : ι -> 集合 X}
  证明: h.lift' (monotone_closure X)
-/
theorem Filter.HasBasis.lift'_closure {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
    (h : l.HasBasis p s) : (l.lift' closure).HasBasis p fun i => closure (s i) :=
  h.lift' (monotone_closure X)

/--
theorem `Filter.HasBasis.lift'_closure_eq_self` / 定理 `Filter.HasBasis.lift'_closure_eq_self`

English:
theorem Filter.HasBasis.lift'_closure_eq_self
  statement: {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
  proof: le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure

@[simp]

中文:
定理 滤子.有基.lift'_closure_eq_self
  结论: {l : 滤子 X} {p : ι -> 命题} {s : ι -> 集合 X}
  证明: le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure

@[simp]
-/
theorem Filter.HasBasis.lift'_closure_eq_self {l : Filter X} {p : ι -> Prop} {s : ι -> Set X}
    (h : l.HasBasis p s) (hc : forall i, p i -> IsClosed (s i)) : l.lift' closure = l :=
  le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure

@[simp]
/--
theorem `Filter.lift'_closure_eq_bot` / 定理 `Filter.lift'_closure_eq_bot`

English:
theorem Filter.lift'_closure_eq_bot
  given: {l : Filter X}
  statement: l.lift' closure = ⊥ ↔ l = ⊥
  proof: ⟨fun h => bot_unique h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩

中文:
定理 滤子.lift'_closure_eq_bot
  条件: {l : 滤子 X}
  结论: l.lift' closure = ⊥ ↔ l = ⊥
  证明: ⟨fun h => bot_unique h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩
-/
theorem Filter.lift'_closure_eq_bot {l : Filter X} : l.lift' closure = ⊥ ↔ l = ⊥ :=
⟨fun h => bot_unique h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩

/--
theorem `dense_iff_closure_eq` / 定理 `dense_iff_closure_eq`

English:
theorem dense_iff_closure_eq
  statement: Dense s ↔ closure s = univ
  proof: eq_univ_iff_forall.symm

alias ⟨Dense.closure_eq, _⟩ := dense_iff_closure_eq

中文:
定理 dense_iff_closure_eq
  结论: 稠密 s ↔ closure s = univ
  证明: eq_univ_iff_forall.symm

alias ⟨Dense.closure_eq, _⟩ := dense_iff_closure_eq

Depends on / 依赖: eq_univ_iff_forall, eq_univ_iff_forall.symm
-/
theorem dense_iff_closure_eq : Dense s ↔ closure s = univ :=
  eq_univ_iff_forall.symm

alias ⟨Dense.closure_eq, _⟩ := dense_iff_closure_eq

/--
theorem `interior_eq_empty_iff_dense_compl` / 定理 `interior_eq_empty_iff_dense_compl`

English:
theorem interior_eq_empty_iff_dense_compl
  statement: interior s = ∅ ↔ Dense sᶜ
  proof: by
  rw [dense_iff_closure_eq]; rw [closure_compl]; rw [compl_univ_iff]

中文:
定理 interior_eq_empty_iff_dense_compl
  结论: interior s = ∅ ↔ 稠密 sᶜ
  证明: by
  rw [dense_iff_closure_eq]; rw [closure_compl]; rw [compl_univ_iff]

Depends on / 依赖: closure_compl, compl_univ_iff, dense_iff_closure_eq
-/
theorem interior_eq_empty_iff_dense_compl : interior s = ∅ ↔ Dense sᶜ := by
  rw [dense_iff_closure_eq]; rw [closure_compl]; rw [compl_univ_iff]

/--
theorem `Dense.interior_compl` / 定理 `Dense.interior_compl`

English:
theorem Dense.interior_compl
  given: (h : Dense s)
  statement: interior sᶜ = ∅
  proof: interior_eq_empty_iff_dense_compl.2 by rwa [compl_compl]

中文:
定理 稠密.interior_compl
  条件: (h : 稠密 s)
  结论: interior sᶜ = ∅
  证明: interior_eq_empty_iff_dense_compl.2 by rwa [compl_compl]

Depends on / 依赖: compl_compl, interior_eq_empty_iff_dense_compl
-/
theorem Dense.interior_compl (h : Dense s) : interior sᶜ = ∅ :=
interior_eq_empty_iff_dense_compl.2 by rwa [compl_compl]

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp]
/--
theorem `dense_closure` / 定理 `dense_closure`

English:
theorem dense_closure
  statement: Dense (closure s) ↔ Dense s
  proof: by
  rw [Dense]; rw [Dense]; rw [closure_closure]

protected alias ⟨_, Dense.closure⟩ := dense_closure
alias ⟨Dense.of_closure, _⟩ := dense_closure

@[simp]

中文:
定理 dense_closure
  结论: 稠密 (closure s) ↔ 稠密 s
  证明: by
  rw [Dense]; rw [Dense]; rw [closure_closure]

protected alias ⟨_, Dense.closure⟩ := dense_closure
alias ⟨Dense.of_closure, _⟩ := dense_closure

@[simp]

Depends on / 依赖: closure_closure
-/
theorem dense_closure : Dense (closure s) ↔ Dense s := by
  rw [Dense]; rw [Dense]; rw [closure_closure]

protected alias ⟨_, Dense.closure⟩ := dense_closure
alias ⟨Dense.of_closure, _⟩ := dense_closure

@[simp]
/--
theorem `dense_univ` / 定理 `dense_univ`

English:
theorem dense_univ
  statement: Dense (univ : Set X)
  proof: fun _ => subset_closure trivial

中文:
定理 dense_univ
  结论: 稠密 (univ : 集合 X)
  证明: fun _ => subset_closure trivial

Depends on / 依赖: subset_closure
-/
theorem dense_univ : Dense (univ : Set X) := fun _ => subset_closure trivial

/--
theorem `dense_iff_inter_open` / 定理 `dense_iff_inter_open`

English:
theorem dense_iff_inter_open
  proof: by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩

alias ⟨Dense.inter_open_nonempty, _⟩ := dense_iff_inter_open

中文:
定理 dense_iff_inter_open
  证明: by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩

alias ⟨Dense.inter_open_nonempty, _⟩ := dense_iff_inter_open

Depends on / 依赖: U_op, mem_closure_iff, x_in
-/
theorem dense_iff_inter_open :
    Dense s ↔ forall U, IsOpen U -> U.Nonempty -> (U inter s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩

alias ⟨Dense.inter_open_nonempty, _⟩ := dense_iff_inter_open

/--
theorem `Dense.exists_mem_open` / 定理 `Dense.exists_mem_open`

English:
theorem Dense.exists_mem_open
  statement: (hs : Dense s) {U : Set X} (ho : IsOpen U)
  proof: let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩

中文:
定理 稠密.存在_mem_open
  结论: (hs : 稠密 s) {U : 集合 X} (ho : 是开集 U)
  证明: let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩

Depends on / 依赖: hs.inter_open_nonempty, inter_open_nonempty
-/
theorem Dense.exists_mem_open (hs : Dense s) {U : Set X} (ho : IsOpen U)
    (hne : U.Nonempty) : exists x in s, x in U :=
  let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩

/--
theorem `Dense.nonempty_iff` / 定理 `Dense.nonempty_iff`

English:
theorem Dense.nonempty_iff
  given: (hs : Dense s)
  statement: s.Nonempty ↔ Nonempty X
  proof: ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩

中文:
定理 稠密.nonempty_iff
  条件: (hs : 稠密 s)
  结论: s.非空 ↔ 非空 X
  证明: ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩

Depends on / 依赖: hs.inter_open_nonempty, inter_open_nonempty, isOpen_univ
-/
theorem Dense.nonempty_iff (hs : Dense s) : s.Nonempty ↔ Nonempty X :=
  ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩

/--
theorem `Dense.nonempty` / 定理 `Dense.nonempty`

English:
theorem Dense.nonempty
  given: [h : Nonempty X] (hs : Dense s)
  statement: s.Nonempty
  proof: hs.nonempty_iff.2 h

@[mono, gcongr]

中文:
定理 稠密.nonempty
  条件: [h : 非空 X] (hs : 稠密 s)
  结论: s.非空
  证明: hs.nonempty_iff.2 h

@[mono, gcongr]

Depends on / 依赖: hs.nonempty_iff, nonempty_iff
-/
theorem Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonempty :=
  hs.nonempty_iff.2 h

@[mono, gcongr]
/--
theorem `Dense.mono` / 定理 `Dense.mono`

English:
theorem Dense.mono
  given: (h : s₁ subseteq s₂) (hd : Dense s₁)
  statement: Dense s₂
  proof: fun x =>
  closure_mono h (hd x)

中文:
定理 稠密.mono
  条件: (h : s₁ subseteq s₂) (hd : 稠密 s₁)
  结论: 稠密 s₂
  证明: fun x =>
  closure_mono h (hd x)
-/
theorem Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂ := fun x =>
  closure_mono h (hd x)

/--
lemma `DenseRange.of_comp` / 引理 `DenseRange.of_comp`

English:
lemma DenseRange.of_comp
  statement: {α β : Type*} {f : α -> X} {g : β -> α}
  proof: Dense.mono (range_comp_subset_range g f) h

中文:
引理 DenseRange.of_comp
  结论: {α β : 类型} {f : α -> X} {g : β -> α}
  证明: Dense.mono (range_comp_subset_range g f) h

Depends on / 依赖: Dense.mono, range_comp_subset_range
-/
lemma DenseRange.of_comp {α β : Type*} {f : α -> X} {g : β -> α}
    (h : DenseRange (f ∘ g)) : DenseRange f :=
  Dense.mono (range_comp_subset_range g f) h

/--
theorem `dense_compl_singleton_iff_not_open` / 定理 `dense_compl_singleton_iff_not_open`

English:
theorem dense_compl_singleton_iff_not_open
  proof: by
  constructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => ?_
    obtain rfl : U = {x} := eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU

中文:
定理 dense_compl_singleton_iff_not_open
  证明: by
  constructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => ?_
    obtain rfl : U = {x} := eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU

Depends on / 依赖: dense_iff_inter_open, eq_singleton_iff_nonempty_unique_mem, hd.inter_open_nonempty, inter_compl_nonempty_iff, inter_compl_self, inter_open_nonempty, ne_empty, singleton_nonempty
-/
theorem dense_compl_singleton_iff_not_open :
    Dense ({x}ᶜ : Set X) ↔ ¬IsOpen ({x} : Set X) := by
  constructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => ?_
    obtain rfl : U = {x} := eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU

/-- If a closed property holds for a dense subset, it holds for the whole space. -/
@[elab_as_elim]
/--
lemma `Dense.induction` / 引理 `Dense.induction`

English:
lemma Dense.induction
  statement: (hs : Dense s) {P : X -> Prop}
  proof: hs.closure_eq.symm.subset.trans (isClosed.closure_subset_iff.mpr mem) (Set.mem_univ _)

中文:
引理 稠密.induction
  结论: (hs : 稠密 s) {P : X -> 命题}
  证明: hs.closure_eq.symm.subset.trans (isClosed.closure_subset_iff.mpr mem) (Set.mem_univ _)

Depends on / 依赖: Set.mem_univ, closure_eq, closure_subset_iff, hs.closure_eq.symm.subset.trans, isClosed, isClosed.closure_subset_iff.mpr, mem_univ, subset
-/
lemma Dense.induction (hs : Dense s) {P : X -> Prop}
    (mem : forall x in s, P x) (isClosed : IsClosed { x | P x }) (x : X) : P x :=
  hs.closure_eq.symm.subset.trans (isClosed.closure_subset_iff.mpr mem) (Set.mem_univ _)

/--
theorem `IsOpen.subset_interior_closure` / 定理 `IsOpen.subset_interior_closure`

English:
theorem IsOpen.subset_interior_closure
  given: {s : Set X} (s_open : IsOpen s)
  proof: s_open.subset_interior_iff.mpr subset_closure

中文:
定理 是开集.subset_interior_closure
  条件: {s : 集合 X} (s_open : 是开集 s)
  证明: s_open.subset_interior_iff.mpr subset_closure

Depends on / 依赖: s_open, s_open.subset_interior_iff.mpr, subset_closure, subset_interior_iff
-/
theorem IsOpen.subset_interior_closure {s : Set X} (s_open : IsOpen s) :
    s subseteq interior (closure s) := s_open.subset_interior_iff.mpr subset_closure

/--
theorem `IsClosed.closure_interior_subset` / 定理 `IsClosed.closure_interior_subset`

English:
theorem IsClosed.closure_interior_subset
  given: {s : Set X} (s_closed : IsClosed s)
  proof: s_closed.closure_subset_iff.mpr interior_subset

中文:
定理 是闭集.closure_interior_subset
  条件: {s : 集合 X} (s_closed : 是闭集 s)
  证明: s_closed.closure_subset_iff.mpr interior_subset

Depends on / 依赖: closure_subset_iff, interior_subset, s_closed, s_closed.closure_subset_iff.mpr
-/
theorem IsClosed.closure_interior_subset {s : Set X} (s_closed : IsClosed s) :
    closure (interior s) subseteq s := s_closed.closure_subset_iff.mpr interior_subset

/--
theorem `closure_interior_idem` / 定理 `closure_interior_idem`

English:
theorem closure_interior_idem
  proof: isClosed_closure.closure_interior_subset.antisymm
    (closure_mono isOpen_interior.subset_interior_closure)

中文:
定理 closure_interior_idem
  证明: isClosed_closure.closure_interior_subset.antisymm
    (closure_mono isOpen_interior.subset_interior_closure)
-/
@[simp] theorem closure_interior_idem :
    closure (interior (closure (interior s))) = closure (interior s) :=
  isClosed_closure.closure_interior_subset.antisymm
    (closure_mono isOpen_interior.subset_interior_closure)

/--
theorem `interior_closure_idem` / 定理 `interior_closure_idem`

English:
theorem interior_closure_idem
  proof: (interior_mono isClosed_closure.closure_interior_subset).antisymm
    isOpen_interior.subset_interior_closure

中文:
定理 interior_closure_idem
  证明: (interior_mono isClosed_closure.closure_interior_subset).antisymm
    isOpen_interior.subset_interior_closure
-/
@[simp] theorem interior_closure_idem :
    interior (closure (interior (closure s))) = interior (closure s) :=
  (interior_mono isClosed_closure.closure_interior_subset).antisymm
    isOpen_interior.subset_interior_closure

end Closure

section Frontier

@[simp]
/--
theorem `closure_sdiff_interior` / 定理 `closure_sdiff_interior`

English:
theorem closure_sdiff_interior
  given: (s : Set X)
  statement: closure s \ interior s = frontier s
  proof: rfl

@[deprecated (since := "2026-06-03")] alias closure_diff_interior := closure_sdiff_interior

中文:
定理 closure_sdiff_interior
  条件: (s : 集合 X)
  结论: closure s \ interior s = frontier s
  证明: rfl

@[deprecated (since := "2026-06-03")] alias closure_diff_interior := closure_sdiff_interior
-/
theorem closure_sdiff_interior (s : Set X) : closure s \ interior s = frontier s :=
  rfl

@[deprecated (since := "2026-06-03")] alias closure_diff_interior := closure_sdiff_interior

/--
lemma `disjoint_interior_frontier` / 引理 `disjoint_interior_frontier`

English:
lemma disjoint_interior_frontier
  statement: Disjoint (interior s) (frontier s)
  proof: by
  rw [disjoint_iff_inter_eq_empty]; rw [← closure_sdiff_interior]; rw [sdiff_eq]; rw [← inter_assoc]; rw [inter_comm]; rw [← inter_assoc]; rw [compl_inter_self]; rw [empty_inter]

@[simp]

中文:
引理 disjoint_interior_frontier
  结论: Disjoint (interior s) (frontier s)
  证明: by
  rw [disjoint_iff_inter_eq_empty]; rw [← closure_sdiff_interior]; rw [sdiff_eq]; rw [← inter_assoc]; rw [inter_comm]; rw [← inter_assoc]; rw [compl_inter_self]; rw [empty_inter]

@[simp]

Depends on / 依赖: closure_sdiff_interior, compl_inter_self, disjoint_iff_inter_eq_empty, empty_inter, inter_assoc, inter_comm, sdiff_eq
-/
lemma disjoint_interior_frontier : Disjoint (interior s) (frontier s) := by
  rw [disjoint_iff_inter_eq_empty]; rw [← closure_sdiff_interior]; rw [sdiff_eq]; rw [← inter_assoc]; rw [inter_comm]; rw [← inter_assoc]; rw [compl_inter_self]; rw [empty_inter]

@[simp]
/--
theorem `closure_sdiff_frontier` / 定理 `closure_sdiff_frontier`

English:
theorem closure_sdiff_frontier
  given: (s : Set X)
  statement: closure s \ frontier s = interior s
  proof: by
  rw [frontier]; rw [sdiff_sdiff_right_self]; rw [inter_eq_self_of_subset_right interior_subset_closure]

@[deprecated (since := "2026-06-03")] alias closure_diff_frontier := closure_sdiff_frontier

@[simp]

中文:
定理 closure_sdiff_frontier
  条件: (s : 集合 X)
  结论: closure s \ frontier s = interior s
  证明: by
  rw [frontier]; rw [sdiff_sdiff_right_self]; rw [inter_eq_self_of_subset_right interior_subset_closure]

@[deprecated (since := "2026-06-03")] alias closure_diff_frontier := closure_sdiff_frontier

@[simp]

Depends on / 依赖: frontier, inter_eq_self_of_subset_right, interior_subset_closure, sdiff_sdiff_right_self
-/
theorem closure_sdiff_frontier (s : Set X) : closure s \ frontier s = interior s := by
  rw [frontier]; rw [sdiff_sdiff_right_self]; rw [inter_eq_self_of_subset_right interior_subset_closure]

@[deprecated (since := "2026-06-03")] alias closure_diff_frontier := closure_sdiff_frontier

@[simp]
/--
theorem `self_sdiff_frontier` / 定理 `self_sdiff_frontier`

English:
theorem self_sdiff_frontier
  given: (s : Set X)
  statement: s \ frontier s = interior s
  proof: by
  rw [frontier]; rw [sdiff_sdiff_right]; rw [sdiff_eq_empty.2 subset_closure]; rw [inter_eq_self_of_subset_right interior_subset]; rw [empty_union]

@[deprecated (since := "2026-06-03")] alias self_diff_frontier := self_sdiff_frontier

中文:
定理 self_sdiff_frontier
  条件: (s : 集合 X)
  结论: s \ frontier s = interior s
  证明: by
  rw [frontier]; rw [sdiff_sdiff_right]; rw [sdiff_eq_empty.2 subset_closure]; rw [inter_eq_self_of_subset_right interior_subset]; rw [empty_union]

@[deprecated (since := "2026-06-03")] alias self_diff_frontier := self_sdiff_frontier

Depends on / 依赖: empty_union, frontier, inter_eq_self_of_subset_right, interior_subset, sdiff_eq_empty, sdiff_sdiff_right, subset_closure
-/
theorem self_sdiff_frontier (s : Set X) : s \ frontier s = interior s := by
  rw [frontier]; rw [sdiff_sdiff_right]; rw [sdiff_eq_empty.2 subset_closure]; rw [inter_eq_self_of_subset_right interior_subset]; rw [empty_union]

@[deprecated (since := "2026-06-03")] alias self_diff_frontier := self_sdiff_frontier

/--
lemma `mem_interior_iff_notMem_frontier` / 引理 `mem_interior_iff_notMem_frontier`

English:
lemma mem_interior_iff_notMem_frontier
  given: {s : Set X} {x : X} (hx : x in s)
  proof: by
  simp [← self_sdiff_frontier, hx]

中文:
引理 mem_interior_iff_notMem_frontier
  条件: {s : 集合 X} {x : X} (hx : x in s)
  证明: by
  simp [← self_sdiff_frontier, hx]

Depends on / 依赖: self_sdiff_frontier
-/
lemma mem_interior_iff_notMem_frontier {s : Set X} {x : X} (hx : x in s) :
    x in interior s ↔ x ∉ frontier s := by
  simp [← self_sdiff_frontier, hx]

/--
lemma `mem_frontier_iff_notMem_interior` / 引理 `mem_frontier_iff_notMem_interior`

English:
lemma mem_frontier_iff_notMem_interior
  given: {s : Set X} {x : X} (hx : x in s)
  proof: by
  simp [← self_sdiff_frontier, hx]

中文:
引理 mem_frontier_iff_notMem_interior
  条件: {s : 集合 X} {x : X} (hx : x in s)
  证明: by
  simp [← self_sdiff_frontier, hx]

Depends on / 依赖: self_sdiff_frontier
-/
lemma mem_frontier_iff_notMem_interior {s : Set X} {x : X} (hx : x in s) :
    x in frontier s ↔ x ∉ interior s := by
  simp [← self_sdiff_frontier, hx]

/--
theorem `frontier_eq_closure_inter_closure` / 定理 `frontier_eq_closure_inter_closure`

English:
theorem frontier_eq_closure_inter_closure
  statement: frontier s = closure s inter closure sᶜ
  proof: by
  rw [closure_compl]; rw [frontier]; rw [sdiff_eq]

中文:
定理 frontier_eq_closure_inter_closure
  结论: frontier s = closure s inter closure sᶜ
  证明: by
  rw [closure_compl]; rw [frontier]; rw [sdiff_eq]

Depends on / 依赖: closure_compl, frontier, sdiff_eq
-/
theorem frontier_eq_closure_inter_closure : frontier s = closure s inter closure sᶜ := by
  rw [closure_compl]; rw [frontier]; rw [sdiff_eq]

/--
theorem `frontier_subset_closure` / 定理 `frontier_subset_closure`

English:
theorem frontier_subset_closure
  statement: frontier s subseteq closure s
  proof: sdiff_subset

中文:
定理 frontier_subset_closure
  结论: frontier s subseteq closure s
  证明: sdiff_subset

Depends on / 依赖: sdiff_subset
-/
theorem frontier_subset_closure : frontier s subseteq closure s :=
  sdiff_subset

/--
theorem `frontier_subset_iff_isClosed` / 定理 `frontier_subset_iff_isClosed`

English:
theorem frontier_subset_iff_isClosed
  statement: frontier s subseteq s ↔ IsClosed s
  proof: by
  rw [frontier]; rw [sdiff_subset_iff]; rw [union_eq_right.mpr interior_subset]; rw [closure_subset_iff_isClosed]

alias ⟨_, IsClosed.frontier_subset⟩ := frontier_subset_iff_isClosed

中文:
定理 frontier_subset_iff_isClosed
  结论: frontier s subseteq s ↔ 是闭集 s
  证明: by
  rw [frontier]; rw [sdiff_subset_iff]; rw [union_eq_right.mpr interior_subset]; rw [closure_subset_iff_isClosed]

alias ⟨_, IsClosed.frontier_subset⟩ := frontier_subset_iff_isClosed

Depends on / 依赖: closure_subset_iff_isClosed, frontier, interior_subset, sdiff_subset_iff, union_eq_right, union_eq_right.mpr
-/
theorem frontier_subset_iff_isClosed : frontier s subseteq s ↔ IsClosed s := by
  rw [frontier]; rw [sdiff_subset_iff]; rw [union_eq_right.mpr interior_subset]; rw [closure_subset_iff_isClosed]

alias ⟨_, IsClosed.frontier_subset⟩ := frontier_subset_iff_isClosed

/--
theorem `frontier_closure_subset` / 定理 `frontier_closure_subset`

English:
theorem frontier_closure_subset
  statement: frontier (closure s) subseteq frontier s
  proof: sdiff_subset_sdiff closure_closure.subset interior_mono subset_closure

中文:
定理 frontier_closure_subset
  结论: frontier (closure s) subseteq frontier s
  证明: sdiff_subset_sdiff closure_closure.subset interior_mono subset_closure

Depends on / 依赖: closure_closure, closure_closure.subset, interior_mono, sdiff_subset_sdiff, subset, subset_closure
-/
theorem frontier_closure_subset : frontier (closure s) subseteq frontier s :=
sdiff_subset_sdiff closure_closure.subset interior_mono subset_closure

/--
theorem `frontier_interior_subset` / 定理 `frontier_interior_subset`

English:
theorem frontier_interior_subset
  statement: frontier (interior s) subseteq frontier s
  proof: sdiff_subset_sdiff (closure_mono interior_subset) interior_interior.symm.subset

中文:
定理 frontier_interior_subset
  结论: frontier (interior s) subseteq frontier s
  证明: sdiff_subset_sdiff (closure_mono interior_subset) interior_interior.symm.subset

Depends on / 依赖: closure_mono, interior_interior, interior_interior.symm.subset, interior_subset, sdiff_subset_sdiff, subset
-/
theorem frontier_interior_subset : frontier (interior s) subseteq frontier s :=
  sdiff_subset_sdiff (closure_mono interior_subset) interior_interior.symm.subset

/-- The complement of a set has the same frontier as the original set. -/
@[simp]
/--
theorem `frontier_compl` / 定理 `frontier_compl`

English:
theorem frontier_compl
  given: (s : Set X)
  statement: frontier sᶜ = frontier s
  proof: by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

@[simp]

中文:
定理 frontier_compl
  条件: (s : 集合 X)
  结论: frontier sᶜ = frontier s
  证明: by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

@[simp]

Depends on / 依赖: compl_compl, frontier_eq_closure_inter_closure, inter_comm
-/
theorem frontier_compl (s : Set X) : frontier sᶜ = frontier s := by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

@[simp]
/--
theorem `frontier_univ` / 定理 `frontier_univ`

English:
theorem frontier_univ
  statement: frontier (univ : Set X) = ∅
  proof: by simp [frontier]

@[simp]

中文:
定理 frontier_univ
  结论: frontier (univ : 集合 X) = ∅
  证明: by simp [frontier]

@[simp]

Depends on / 依赖: frontier
-/
theorem frontier_univ : frontier (univ : Set X) = ∅ := by simp [frontier]

@[simp]
/--
theorem `frontier_empty` / 定理 `frontier_empty`

English:
theorem frontier_empty
  statement: frontier (∅ : Set X) = ∅
  proof: by simp [frontier]

中文:
定理 frontier_empty
  结论: frontier (∅ : 集合 X) = ∅
  证明: by simp [frontier]

Depends on / 依赖: frontier
-/
theorem frontier_empty : frontier (∅ : Set X) = ∅ := by simp [frontier]

/--
theorem `frontier_inter_subset` / 定理 `frontier_inter_subset`

English:
theorem frontier_inter_subset
  given: (s t : Set X)
  proof: by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  refine (inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)).trans_eq ?_
  simp only [inter_union_distrib_left, inter_assoc,
    inter_comm (closure t)]

中文:
定理 frontier_inter_subset
  条件: (s t : 集合 X)
  证明: by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  refine (inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)).trans_eq ?_
  simp only [inter_union_distrib_left, inter_assoc,
    inter_comm (closure t)]

Depends on / 依赖: closure, closure_inter_subset_inter_closure, closure_union, compl_inter, frontier_eq_closure_inter_closure, inter_assoc, inter_comm, inter_subset_inter_left, inter_union_distrib_left, trans_eq
-/
theorem frontier_inter_subset (s t : Set X) :
    frontier (s inter t) subseteq frontier s inter closure t union closure s inter frontier t := by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  refine (inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)).trans_eq ?_
  simp only [inter_union_distrib_left, inter_assoc,
    inter_comm (closure t)]

/--
theorem `frontier_union_subset` / 定理 `frontier_union_subset`

English:
theorem frontier_union_subset
  given: (s t : Set X)
  proof: by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset sᶜ tᶜ

中文:
定理 frontier_union_subset
  条件: (s t : 集合 X)
  证明: by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset sᶜ tᶜ

Depends on / 依赖: compl_union, frontier_compl, frontier_inter_subset
-/
theorem frontier_union_subset (s t : Set X) :
    frontier (s union t) subseteq frontier s inter closure tᶜ union closure sᶜ inter frontier t := by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset sᶜ tᶜ

/--
theorem `IsClosed.frontier_eq` / 定理 `IsClosed.frontier_eq`

English:
theorem IsClosed.frontier_eq
  given: (hs : IsClosed s)
  statement: frontier s = s \ interior s
  proof: by
  rw [frontier]; rw [hs.closure_eq]

中文:
定理 是闭集.frontier_eq
  条件: (hs : 是闭集 s)
  结论: frontier s = s \ interior s
  证明: by
  rw [frontier]; rw [hs.closure_eq]

Depends on / 依赖: closure_eq, frontier, hs.closure_eq
-/
theorem IsClosed.frontier_eq (hs : IsClosed s) : frontier s = s \ interior s := by
  rw [frontier]; rw [hs.closure_eq]

/--
theorem `IsOpen.frontier_eq` / 定理 `IsOpen.frontier_eq`

English:
theorem IsOpen.frontier_eq
  given: (hs : IsOpen s)
  statement: frontier s = closure s \ s
  proof: by
  rw [frontier]; rw [hs.interior_eq]

中文:
定理 是开集.frontier_eq
  条件: (hs : 是开集 s)
  结论: frontier s = closure s \ s
  证明: by
  rw [frontier]; rw [hs.interior_eq]

Depends on / 依赖: frontier, hs.interior_eq, interior_eq
-/
theorem IsOpen.frontier_eq (hs : IsOpen s) : frontier s = closure s \ s := by
  rw [frontier]; rw [hs.interior_eq]

/--
theorem `IsOpen.inter_frontier_eq` / 定理 `IsOpen.inter_frontier_eq`

English:
theorem IsOpen.inter_frontier_eq
  given: (hs : IsOpen s)
  statement: s inter frontier s = ∅
  proof: by
  rw [hs.frontier_eq]; rw [inter_sdiff_self]

中文:
定理 是开集.inter_frontier_eq
  条件: (hs : 是开集 s)
  结论: s inter frontier s = ∅
  证明: by
  rw [hs.frontier_eq]; rw [inter_sdiff_self]

Depends on / 依赖: frontier_eq, hs.frontier_eq, inter_sdiff_self
-/
theorem IsOpen.inter_frontier_eq (hs : IsOpen s) : s inter frontier s = ∅ := by
  rw [hs.frontier_eq]; rw [inter_sdiff_self]

/--
theorem `disjoint_frontier_iff_isOpen` / 定理 `disjoint_frontier_iff_isOpen`

English:
theorem disjoint_frontier_iff_isOpen
  statement: Disjoint (frontier s) s ↔ IsOpen s
  proof: by
  rw [← isClosed_compl_iff]; rw [← frontier_subset_iff_isClosed]; rw [frontier_compl]; rw [subset_compl_iff_disjoint_right]

中文:
定理 disjoint_frontier_iff_isOpen
  结论: Disjoint (frontier s) s ↔ 是开集 s
  证明: by
  rw [← isClosed_compl_iff]; rw [← frontier_subset_iff_isClosed]; rw [frontier_compl]; rw [subset_compl_iff_disjoint_right]

Depends on / 依赖: frontier_compl, frontier_subset_iff_isClosed, isClosed_compl_iff, subset_compl_iff_disjoint_right
-/
theorem disjoint_frontier_iff_isOpen : Disjoint (frontier s) s ↔ IsOpen s := by
  rw [← isClosed_compl_iff]; rw [← frontier_subset_iff_isClosed]; rw [frontier_compl]; rw [subset_compl_iff_disjoint_right]

/--
theorem `isClosed_frontier` / 定理 `isClosed_frontier`

English:
theorem isClosed_frontier
  statement: IsClosed (frontier s)
  proof: by
  rw [frontier_eq_closure_inter_closure]; exact IsClosed.inter isClosed_closure isClosed_closure

中文:
定理 isClosed_frontier
  结论: 是闭集 (frontier s)
  证明: by
  rw [frontier_eq_closure_inter_closure]; exact IsClosed.inter isClosed_closure isClosed_closure

Depends on / 依赖: IsClosed, IsClosed.inter, frontier_eq_closure_inter_closure, isClosed_closure
-/
theorem isClosed_frontier : IsClosed (frontier s) := by
  rw [frontier_eq_closure_inter_closure]; exact IsClosed.inter isClosed_closure isClosed_closure

/--
theorem `interior_frontier` / 定理 `interior_frontier`

English:
theorem interior_frontier
  given: (h : IsClosed s)
  statement: interior (frontier s) = ∅
  proof: by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) subseteq interior s := by rw [A]; exact interior_mono sdiff_subset
  have C : interior (frontier s) subseteq frontier s := interior_subset
  have : interior (frontier s) subseteq interior s inter (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_sdiff_self, subset_empty_iff] at this

中文:
定理 interior_frontier
  条件: (h : 是闭集 s)
  结论: interior (frontier s) = ∅
  证明: by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) subseteq interior s := by rw [A]; exact interior_mono sdiff_subset
  have C : interior (frontier s) subseteq frontier s := interior_subset
  have : interior (frontier s) subseteq interior s inter (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_sdiff_self, subset_empty_iff] at this

Depends on / 依赖: frontier, frontier_eq, h.frontier_eq, inter_sdiff_self, interior, interior_mono, interior_subset, sdiff_subset, subset_empty_iff, subset_inter, subseteq
-/
theorem interior_frontier (h : IsClosed s) : interior (frontier s) = ∅ := by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) subseteq interior s := by rw [A]; exact interior_mono sdiff_subset
  have C : interior (frontier s) subseteq frontier s := interior_subset
  have : interior (frontier s) subseteq interior s inter (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_sdiff_self, subset_empty_iff] at this

/--
theorem `closure_eq_interior_union_frontier` / 定理 `closure_eq_interior_union_frontier`

English:
theorem closure_eq_interior_union_frontier
  given: (s : Set X)
  statement: closure s = interior s union frontier s
  proof: (union_sdiff_cancel interior_subset_closure).symm

中文:
定理 closure_eq_interior_union_frontier
  条件: (s : 集合 X)
  结论: closure s = interior s union frontier s
  证明: (union_sdiff_cancel interior_subset_closure).symm

Depends on / 依赖: interior_subset_closure, union_sdiff_cancel
-/
theorem closure_eq_interior_union_frontier (s : Set X) : closure s = interior s union frontier s :=
  (union_sdiff_cancel interior_subset_closure).symm

/--
theorem `closure_eq_self_union_frontier` / 定理 `closure_eq_self_union_frontier`

English:
theorem closure_eq_self_union_frontier
  given: (s : Set X)
  statement: closure s = s union frontier s
  proof: (union_sdiff_cancel' interior_subset subset_closure).symm

中文:
定理 closure_eq_self_union_frontier
  条件: (s : 集合 X)
  结论: closure s = s union frontier s
  证明: (union_sdiff_cancel' interior_subset subset_closure).symm

Depends on / 依赖: interior_subset, subset_closure, union_sdiff_cancel
-/
theorem closure_eq_self_union_frontier (s : Set X) : closure s = s union frontier s :=
  (union_sdiff_cancel' interior_subset subset_closure).symm

/--
theorem `Disjoint.frontier_left` / 定理 `Disjoint.frontier_left`

English:
theorem Disjoint.frontier_left
  given: (ht : IsOpen t) (hd : Disjoint s t)
  statement: Disjoint (frontier s) t
  proof: subset_compl_iff_disjoint_right.1
frontier_subset_closure.trans closure_minimal (disjoint_left.1 hd) isClosed_compl_iff.2 ht

中文:
定理 Disjoint.frontier_left
  条件: (ht : 是开集 t) (hd : Disjoint s t)
  结论: Disjoint (frontier s) t
  证明: subset_compl_iff_disjoint_right.1
frontier_subset_closure.trans closure_minimal (disjoint_left.1 hd) isClosed_compl_iff.2 ht

Depends on / 依赖: closure_minimal, disjoint_left, frontier_subset_closure, frontier_subset_closure.trans, isClosed_compl_iff, subset_compl_iff_disjoint_right
-/
theorem Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (frontier s) t :=
subset_compl_iff_disjoint_right.1
frontier_subset_closure.trans closure_minimal (disjoint_left.1 hd) isClosed_compl_iff.2 ht

/--
theorem `Disjoint.frontier_right` / 定理 `Disjoint.frontier_right`

English:
theorem Disjoint.frontier_right
  given: (hs : IsOpen s) (hd : Disjoint s t)
  statement: Disjoint s (frontier t)
  proof: (hd.symm.frontier_left hs).symm

中文:
定理 Disjoint.frontier_right
  条件: (hs : 是开集 s) (hd : Disjoint s t)
  结论: Disjoint s (frontier t)
  证明: (hd.symm.frontier_left hs).symm

Depends on / 依赖: frontier_left, hd.symm.frontier_left
-/
theorem Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (frontier t) :=
  (hd.symm.frontier_left hs).symm

/--
theorem `frontier_eq_inter_compl_interior` / 定理 `frontier_eq_inter_compl_interior`

English:
theorem frontier_eq_inter_compl_interior
  statement: frontier s = (interior s)ᶜ inter (interior sᶜ)ᶜ
  proof: by
  rw [← frontier_compl]; rw [← closure_compl]; rw [← sdiff_eq]; rw [closure_sdiff_interior]

中文:
定理 frontier_eq_inter_compl_interior
  结论: frontier s = (interior s)ᶜ inter (interior sᶜ)ᶜ
  证明: by
  rw [← frontier_compl]; rw [← closure_compl]; rw [← sdiff_eq]; rw [closure_sdiff_interior]

Depends on / 依赖: closure_compl, closure_sdiff_interior, frontier_compl, sdiff_eq
-/
theorem frontier_eq_inter_compl_interior : frontier s = (interior s)ᶜ inter (interior sᶜ)ᶜ := by
  rw [← frontier_compl]; rw [← closure_compl]; rw [← sdiff_eq]; rw [closure_sdiff_interior]

/--
theorem `compl_frontier_eq_union_interior` / 定理 `compl_frontier_eq_union_interior`

English:
theorem compl_frontier_eq_union_interior
  statement: (frontier s)ᶜ = interior s union interior sᶜ
  proof: by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]

中文:
定理 compl_frontier_eq_union_interior
  结论: (frontier s)ᶜ = interior s union interior sᶜ
  证明: by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]

Depends on / 依赖: compl_compl, compl_inter, frontier_eq_inter_compl_interior
-/
theorem compl_frontier_eq_union_interior : (frontier s)ᶜ = interior s union interior sᶜ := by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]

end Frontier
