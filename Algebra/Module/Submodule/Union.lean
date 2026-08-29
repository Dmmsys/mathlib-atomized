/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Unions of `Submodule`s

This file is a home for results about unions of submodules.

## Main results:
* `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`: a finite union of proper submodules is
  a proper subset, provided the coefficients are a sufficiently large field.

-/

public section

open Function Set

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/--
lemma `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt` / 引理 `Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`

English:
lemma Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
  statement: (s : Finset ι) (p : ι -> Submodule K M)
  proof: by
  -- Following https://mathoverflow.net/a/14241
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using! h₁ j
    replace h₂ : s.card + 1 < ENat.

中文:
引理 Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
  结论: (s : Finset ι) (p : ι -> Submodule K M)
  证明: by
  -- Following https://mathoverflow.net/a/14241
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using! h₁ j
    replace h₂ : s.card + 1 < ENat.
-/
lemma Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (s : Finset ι) (p : ι -> Submodule K M)
    (h₁ : forall i, p i != ⊤) (h₂ : s.card < ENat.card K) :
    ⋃ i in s, (p i : Set M) ⊂ univ := by
  -- Following https://mathoverflow.net/a/14241
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using! h₁ j
    replace h₂ : s.card + 1 < ENat.card K := by simpa [Finset.card_insert_of_notMem hj] using! h₂
    specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
    contrapose hj'
    replace hj' : (p j : Set M) union (⋃ i in s, p i) = univ := by
      simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using! hj'
    suffices (p j : Set M) subseteq ⋃ i in s, p i by rwa [union_eq_right.mpr this] at hj'
    intro x (hx : x in p j)
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa using! hs
    obtain ⟨y, hy⟩ : exists y, y ∉ p j := by specialize h₁ j; contrapose! h₁; ext; simp [h₁]
    have hy₀ : y != 0 := by aesop
    let sxy := {x + t • y | (t : K) (ht : t != 0)}
    have hsxy : sxy subseteq ⋃ i in s, p i := by
suffices Disjoint sxy (p j) from this.subset_right_of_subset_union hj' ▸ sxy.subset_univ
      rw [Set.disjoint_iff]
      rintro - ⟨⟨t, ht₀, rfl⟩, ht : x + t • y in p j⟩
      rw [(p j).add_mem_iff_right hx]; rw [(p j).smul_mem_iff ht₀] at ht
      contradiction
    obtain ⟨k, hk, t₁, t₂, ht, ht₁, ht₂⟩ : existsᵉ (k in s) (t₁ : K) (t₂ : K),
        t₁ != t₂ ∧ x + t₁ • y in p k ∧ x + t₂ • y in p k := by
      suffices existsᵉ (k in s) (z₁ in sxy) (z₂ in sxy), z₁ != z₂ ∧ z₁ in p k ∧ z₂ in p k by
        obtain ⟨k, hk, -, ⟨t₁, -, rfl⟩, -, ⟨t₂, -, rfl⟩, htne, ht₁, ht₂⟩ := this
        exact ⟨k, hk, t₁, t₂, by aesop, ht₁, ht₂⟩
      choose f hf using fun z : sxy => mem_iUnion.mp (hsxy z.property)
      have hf' : MapsTo f univ s := fun z _ => by specialize hf z; aesop
      suffices exists z₁ z₂, z₁ != z₂ ∧ f z₁ = f z₂ by
        obtain ⟨z₁, z₂, hne, heq⟩ := this
        exact ⟨f z₁, hf' (mem_univ _), z₁, z₁.property, z₂, z₂.property,
          Subtype.coe_ne_coe.mpr hne, by specialize hf z₁; simp_all, by specialize hf z₂; aesop⟩
      have key : s.card < sxy.encard := by
refine lt_of_add_lt_add_right lt_of_lt_of_le h₂ ?_
        have : Injective (fun t : K => x + t • y) :=
fun t₁ t₂ ht => smul_left_injective K hy₀ by simpa using! ht
        have aux : sxy = ((fun t : K => x + t • y) '' {t | t != 0}) := by ext; simp [sxy]
        rw [aux]; rw [this.encard_image]; rw [encard_ne_add_one]
      obtain ⟨z₁, -, z₂, -, h⟩ := exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
      exact ⟨z₁, z₂, h⟩
    replace ht : y in p k := by
      have : (t₁ - t₂) • y in p k := by convert sub_mem ht₁ ht₂; module
      refine ((p k).smul_mem_iff ?_).mp this
      rwa [sub_ne_zero]
    replace ht : x in p k := by convert sub_mem ht₁ ((p k).smul_mem t₁ ht); simp
    simpa using! ⟨k, hk, ht⟩

variable [Finite ι] [Infinite K]

/--
lemma `Submodule.exists_forall_notMem_of_forall_ne_top` / 引理 `Submodule.exists_forall_notMem_of_forall_ne_top`

English:
lemma Submodule.exists_forall_notMem_of_forall_ne_top
  given: (p : ι -> Submodule K M) (h : forall i, p i != ⊤)
  proof: by
  let _i : Fintype ι := Fintype.ofFinite ι
  suffices ⋃ i, (p i : Set M) ⊂ univ by simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h (by simp)

中文:
引理 Submodule.exists_forall_notMem_of_forall_ne_top
  条件: (p : ι -> Submodule K M) (h : 对任意 i, p i != ⊤)
  证明: by
  let _i : Fintype ι := Fintype.ofFinite ι
  suffices ⋃ i, (p i : Set M) ⊂ univ by simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h (by simp)

Depends on / 依赖: Finset, Finset.univ, Fintype, Fintype.ofFinite, iUnion_eq_univ_iff, iUnion_ssubset_of_forall_ne_top_of_card_lt, ofFinite, ssubset_univ_iff
-/
lemma Submodule.exists_forall_notMem_of_forall_ne_top (p : ι -> Submodule K M) (h : forall i, p i != ⊤) :
    exists x, forall i, x ∉ p i := by
  let _i : Fintype ι := Fintype.ofFinite ι
  suffices ⋃ i, (p i : Set M) ⊂ univ by simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h (by simp)

/--
lemma `Module.Dual.exists_forall_ne_zero_of_forall_exists` / 引理 `Module.Dual.exists_forall_ne_zero_of_forall_exists`

English:
lemma Module.Dual.exists_forall_ne_zero_of_forall_exists
  proof: by
  let p i := LinearMap.ker (f i)
  replace h i : p i != ⊤ := by specialize h i; aesop
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

中文:
引理 Module.Dual.exists_forall_ne_zero_of_forall_exists
  证明: by
  let p i := LinearMap.ker (f i)
  replace h i : p i != ⊤ := by specialize h i; aesop
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

Depends on / 依赖: LinearMap, LinearMap.ker, Submodule, Submodule.exists_forall_notMem_of_forall_ne_top, exists_forall_notMem_of_forall_ne_top, replace, specialize
-/
lemma Module.Dual.exists_forall_ne_zero_of_forall_exists
    (f : ι -> Dual K M) (h : forall i, exists x, f i x != 0) :
    exists x, forall i, f i x != 0 := by
  let p i := LinearMap.ker (f i)
  replace h i : p i != ⊤ := by specialize h i; aesop
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

/--
lemma `Module.Dual.exists_forall_mem_ne_zero_of_forall_exists` / 引理 `Module.Dual.exists_forall_mem_ne_zero_of_forall_exists`

English:
lemma Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
  statement: (p : Submodule K M)
  proof: by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : exists x : p, f' i x != 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_forall_ne_zero_of_forall_exists f' h
  exact ⟨x, hxp, hx₀⟩

中文:
引理 Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
  结论: (p : Submodule K M)
  证明: by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : exists x : p, f' i x != 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_forall_ne_zero_of_forall_exists f' h
  exact ⟨x, hxp, hx₀⟩

Depends on / 依赖: domRestrict, exists_forall_ne_zero_of_forall_exists, replace
-/
lemma Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (p : Submodule K M)
    (f : ι -> Dual K M) (h : forall i, exists x in p, f i x != 0) :
    exists x in p, forall i, f i x != 0 := by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : exists x : p, f' i x != 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_forall_ne_zero_of_forall_exists f' h
  exact ⟨x, hxp, hx₀⟩

/--
lemma `Module.exists_dual_forall_apply_ne_zero` / 引理 `Module.exists_dual_forall_apply_ne_zero`

English:
lemma Module.exists_dual_forall_apply_ne_zero
  given: (v : ι -> M) (hv : forall i, v i != 0)
  proof: by
  refine Dual.exists_forall_ne_zero_of_forall_exists (fun i => Dual.eval K M (v i)) fun i => ?_
  by_contra! contra
  simp_rw [Dual.eval_apply, forall_dual_apply_eq_zero_iff] at contra
  exact hv i contra

中文:
引理 Module.exists_dual_forall_apply_ne_zero
  条件: (v : ι -> M) (hv : 对任意 i, v i != 0)
  证明: by
  refine Dual.exists_forall_ne_zero_of_forall_exists (fun i => Dual.eval K M (v i)) fun i => ?_
  by_contra! contra
  simp_rw [Dual.eval_apply, forall_dual_apply_eq_zero_iff] at contra
  exact hv i contra

Depends on / 依赖: Dual.eval, Dual.eval_apply, Dual.exists_forall_ne_zero_of_forall_exists, contra, eval_apply, exists_forall_ne_zero_of_forall_exists, forall_dual_apply_eq_zero_iff, simp_rw
-/
lemma Module.exists_dual_forall_apply_ne_zero (v : ι -> M) (hv : forall i, v i != 0) :
    exists f : Dual K M, forall i, f (v i) != 0 := by
  refine Dual.exists_forall_ne_zero_of_forall_exists (fun i => Dual.eval K M (v i)) fun i => ?_
  by_contra! contra
  simp_rw [Dual.eval_apply, forall_dual_apply_eq_zero_iff] at contra
  exact hv i contra
