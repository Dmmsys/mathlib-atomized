/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Order.Group.Nat
/-!
# Adjoining elements to form subalgebras

This file contains basic results on `Algebra.adjoin`.

## Tags

adjoin, algebra

-/

public section

assert_not_exists Polynomial

universe uR uS uA uB

open Module Submodule Subsemiring
open scoped Pointwise

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

namespace Algebra

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]
variable {s t : Set A}

variable (R A)

variable {A} (s)

/--
theorem `adjoin_prod_le` / 定理 `adjoin_prod_le`

English:
theorem adjoin_prod_le
  given: (s : Set A) (t : Set B)
  proof: adjoin_le Set.prod_mono subset_adjoin subset_adjoin

中文:
定理 adjoin_prod_le
  条件: (s : 集合 A) (t : 集合 B)
  证明: adjoin_le Set.prod_mono subset_adjoin subset_adjoin

Depends on / 依赖: Set.prod_mono, adjoin_le, prod_mono, subset_adjoin
-/
theorem adjoin_prod_le (s : Set A) (t : Set B) :
    adjoin R (s ×ˢ t) <= (adjoin R s).prod (adjoin R t) :=
adjoin_le Set.prod_mono subset_adjoin subset_adjoin

/--
theorem `adjoin_inl_union_inr_eq_prod` / 定理 `adjoin_inl_union_inr_eq_prod`

English:
theorem adjoin_inl_union_inr_eq_prod
  given: (s) (t)
  proof: by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin, -- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1}))
    have Ha : (a, (0 : B)) in adjoin R (LinearMap.inl R A B '' (s union {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) in adjoin R (LinearMap.inr R A B '' (t union {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) in P := adjoin_mono Set.subset_union_left Ha
    replace Hb : ((0 : A), b) in P := adjoin_mono Set.subset_union_right Hb
    simpa [P] using Subalgebra.add_mem _ Ha Hb

中文:
定理 adjoin_inl_union_inr_eq_prod
  条件: (s) (t)
  证明: by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin, -- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1}))
    have Ha : (a, (0 : B)) in adjoin R (LinearMap.inl R A B '' (s union {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) in adjoin R (LinearMap.inr R A B '' (t union {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) in P := adjoin_mono Set.subset_union_left Ha
    replace Hb : ((0 : A), b) in P := adjoin_mono Set.subset_union_right Hb
    simpa [P] using Subalgebra.add_mem _ Ha Hb

Depends on / 依赖: LinearMap, LinearMap.coe_inl, LinearMap.coe_inr, LinearMap.inl, LinearMap.inr, Set.image_subset_iff, Set.insert_subset_iff, Set.mk_preimage_prod_left, Set.mk_preimage_prod_right, Set.union_singleton, Set.union_subset_iff, SetLike, SetLike.mem_coe, Subalgebra, Subalgebra.coe_prod, Subalgebra.one_mem, Subalgebra.zero_mem, adjoin, adjoin_le_iff, and_self_iff
-/
theorem adjoin_inl_union_inr_eq_prod (s) (t) :
    adjoin R (LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1})) =
      (adjoin R s).prod (adjoin R t) := by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin, -- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1}))
    have Ha : (a, (0 : B)) in adjoin R (LinearMap.inl R A B '' (s union {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) in adjoin R (LinearMap.inr R A B '' (t union {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) in P := adjoin_mono Set.subset_union_left Ha
    replace Hb : ((0 : A), b) in P := adjoin_mono Set.subset_union_right Hb
    simpa [P] using Subalgebra.add_mem _ Ha Hb

variable (A) in
/--
theorem `adjoin_algebraMap` / 定理 `adjoin_algebraMap`

English:
theorem adjoin_algebraMap
  given: (s : Set S)
  proof: adjoin_image R (IsScalarTower.toAlgHom R S A) s

中文:
定理 adjoin_algebraMap
  条件: (s : 集合 S)
  证明: adjoin_image R (IsScalarTower.toAlgHom R S A) s

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, adjoin_image, toAlgHom
-/
theorem adjoin_algebraMap (s : Set S) :
    adjoin R (algebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A) :=
  adjoin_image R (IsScalarTower.toAlgHom R S A) s

/--
theorem `adjoin_algebraMap_image_union_eq_adjoin_adjoin` / 定理 `adjoin_algebraMap_image_union_eq_adjoin_adjoin`

English:
theorem adjoin_algebraMap_image_union_eq_adjoin_adjoin
  given: (s : Set S) (t : Set A)
  proof: le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r,
        (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩)
        (Set.union_subset_union_left _ fun _ ⟨_x, hx, hxs⟩ => hxs ▸ ⟨⟨_, subset_adjoin hx⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono Set.subset_union_left <|
        Algebra.adjoin_algebraMap R A s ▸ ⟨x, x.prop, rfl⟩)
        (Set.Subset.trans Set.subset_union_right subset_adjoin))

中文:
定理 adjoin_algebraMap_image_union_eq_adjoin_adjoin
  条件: (s : 集合 S) (t : 集合 A)
  证明: le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r,
        (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩)
        (Set.union_subset_union_left _ fun _ ⟨_x, hx, hxs⟩ => hxs ▸ ⟨⟨_, subset_adjoin hx⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono Set.subset_union_left <|
        Algebra.adjoin_algebraMap R A s ▸ ⟨x, x.prop, rfl⟩)
        (Set.Subset.trans Set.subset_union_right subset_adjoin))

Depends on / 依赖: Algebra, Algebra.adjoin_algebraMap, IsScalarTower, IsScalarTower.algebraMap_apply, Or.inl, Set.Subset.trans, Set.range_subset_iff, Set.subset_union_left, Set.subset_union_right, Set.union_subset, Set.union_subset_union_left, Subset, adjoin, adjoin_algebraMap, adjoin_mono, algebraMap, algebraMap_apply, closure_le, closure_mono, le_antisymm
-/
theorem adjoin_algebraMap_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) :
    adjoin R (algebraMap S A '' s union t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r,
        (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩)
        (Set.union_subset_union_left _ fun _ ⟨_x, hx, hxs⟩ => hxs ▸ ⟨⟨_, subset_adjoin hx⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono Set.subset_union_left <|
        Algebra.adjoin_algebraMap R A s ▸ ⟨x, x.prop, rfl⟩)
        (Set.Subset.trans Set.subset_union_right subset_adjoin))

/--
theorem `adjoin_adjoin_of_tower` / 定理 `adjoin_adjoin_of_tower`

English:
theorem adjoin_adjoin_of_tower
  given: (s : Set A)
  statement: adjoin S (adjoin R s : Set A) = adjoin S s
  proof: by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · rw [← Subalgebra.coe_restrictScalars R (S := S), SetLike.coe_subset_coe]
    exact adjoin_le subset_adjoin

中文:
定理 adjoin_adjoin_of_tower
  条件: (s : 集合 A)
  结论: adjoin S (adjoin R s : 集合 A) = adjoin S s
  证明: by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · rw [← Subalgebra.coe_restrictScalars R (S := S), SetLike.coe_subset_coe]
    exact adjoin_le subset_adjoin

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, Subalgebra, Subalgebra.coe_restrictScalars, adjoin_le, adjoin_mono, coe_restrictScalars, coe_subset_coe, le_antisymm, subset_adjoin
-/
theorem adjoin_adjoin_of_tower (s : Set A) : adjoin S (adjoin R s : Set A) = adjoin S s := by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · rw [← Subalgebra.coe_restrictScalars R (S := S), SetLike.coe_subset_coe]
    exact adjoin_le subset_adjoin

/--
theorem `Subalgebra.restrictScalars_adjoin` / 定理 `Subalgebra.restrictScalars_adjoin`

English:
theorem Subalgebra.restrictScalars_adjoin
  given: {s : Set A}
  proof: by
  refine le_antisymm (fun _ hx => adjoin_induction
    (fun x hx => le_sup_right (α := Subalgebra R A) (subset_adjoin hx))
    (fun x => le_sup_left (α := Subalgebra R A) ⟨x, rfl⟩)
(fun _ _ _ _ => add_mem) (fun _ _ _ _ => mul_mem)
(Subalgebra.mem_restrictScalars _).mp hx) (sup_le ?_ adjoin_le subset_adjoin)
  rintro _ ⟨x, rfl⟩; exact algebraMap_mem (adjoin S s) x

@[simp]

中文:
定理 子代数.restrictScalars_adjoin
  条件: {s : 集合 A}
  证明: by
  refine le_antisymm (fun _ hx => adjoin_induction
    (fun x hx => le_sup_right (α := Subalgebra R A) (subset_adjoin hx))
    (fun x => le_sup_left (α := Subalgebra R A) ⟨x, rfl⟩)
(fun _ _ _ _ => add_mem) (fun _ _ _ _ => mul_mem)
(Subalgebra.mem_restrictScalars _).mp hx) (sup_le ?_ adjoin_le subset_adjoin)
  rintro _ ⟨x, rfl⟩; exact algebraMap_mem (adjoin S s) x

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.mem_restrictScalars, add_mem, adjoin, adjoin_induction, adjoin_le, algebraMap_mem, le_antisymm, le_sup_left, le_sup_right, mem_restrictScalars, mul_mem, subset_adjoin, sup_le
-/
theorem Subalgebra.restrictScalars_adjoin {s : Set A} :
    (adjoin S s).restrictScalars R = (IsScalarTower.toAlgHom R S A).range ⊔ adjoin R s := by
  refine le_antisymm (fun _ hx => adjoin_induction
    (fun x hx => le_sup_right (α := Subalgebra R A) (subset_adjoin hx))
    (fun x => le_sup_left (α := Subalgebra R A) ⟨x, rfl⟩)
(fun _ _ _ _ => add_mem) (fun _ _ _ _ => mul_mem)
(Subalgebra.mem_restrictScalars _).mp hx) (sup_le ?_ adjoin_le subset_adjoin)
  rintro _ ⟨x, rfl⟩; exact algebraMap_mem (adjoin S s) x

@[simp]
/--
theorem `adjoin_top` / 定理 `adjoin_top`

English:
theorem adjoin_top
  given: {A} [Semiring A] [Algebra S A] (t : Set A)
  proof: let equivTop : Subalgebra (⊤ : Subalgebra R S) A ≃o Subalgebra S A :=
    { toFun := fun s => { s with algebraMap_mem' := fun r => s.algebraMap_mem ⟨r, trivial⟩ }
      invFun := fun s => s.restrictScalars _
      left_inv := fun _ => SetLike.coe_injective rfl
      right_inv := fun _ => SetLike.coe_injective rfl
      map_rel_iff' := @fun _ _ => Iff.rfl }
  le_antisymm
    (adjoin_le <| show t subseteq adjoin S t from subset_adjoin)
    (equivTop.symm_apply_le.mpr <|
adjoin_le show t subseteq adjoin (⊤ : Subalgebra R S) t from subset_adjoin)

中文:
定理 adjoin_top
  条件: {A} [半环 A] [代数 S A] (t : 集合 A)
  证明: let equivTop : Subalgebra (⊤ : Subalgebra R S) A ≃o Subalgebra S A :=
    { toFun := fun s => { s with algebraMap_mem' := fun r => s.algebraMap_mem ⟨r, trivial⟩ }
      invFun := fun s => s.restrictScalars _
      left_inv := fun _ => SetLike.coe_injective rfl
      right_inv := fun _ => SetLike.coe_injective rfl
      map_rel_iff' := @fun _ _ => Iff.rfl }
  le_antisymm
    (adjoin_le <| show t subseteq adjoin S t from subset_adjoin)
    (equivTop.symm_apply_le.mpr <|
adjoin_le show t subseteq adjoin (⊤ : Subalgebra R S) t from subset_adjoin)

Depends on / 依赖: Iff.rfl, SetLike, SetLike.coe_injective, Subalgebra, adjoin, adjoin_le, algebraMap_mem, coe_injective, equivTop, equivTop.symm_apply_le.mpr, invFun, le_antisymm, left_inv, map_rel_iff, restrictScalars, right_inv, s.algebraMap_mem, s.restrictScalars, subset_adjoin, subseteq
-/
theorem adjoin_top {A} [Semiring A] [Algebra S A] (t : Set A) :
    adjoin (⊤ : Subalgebra R S) t = (adjoin S t).restrictScalars (⊤ : Subalgebra R S) :=
  let equivTop : Subalgebra (⊤ : Subalgebra R S) A ≃o Subalgebra S A :=
    { toFun := fun s => { s with algebraMap_mem' := fun r => s.algebraMap_mem ⟨r, trivial⟩ }
      invFun := fun s => s.restrictScalars _
      left_inv := fun _ => SetLike.coe_injective rfl
      right_inv := fun _ => SetLike.coe_injective rfl
      map_rel_iff' := @fun _ _ => Iff.rfl }
  le_antisymm
    (adjoin_le <| show t subseteq adjoin S t from subset_adjoin)
    (equivTop.symm_apply_le.mpr <|
adjoin_le show t subseteq adjoin (⊤ : Subalgebra R S) t from subset_adjoin)

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [Algebra R A] {s t : Set A}
variable (R s t)

/--
theorem `adjoin_union_eq_adjoin_adjoin` / 定理 `adjoin_union_eq_adjoin_adjoin`

English:
theorem adjoin_union_eq_adjoin_adjoin
  proof: by
  simpa using adjoin_algebraMap_image_union_eq_adjoin_adjoin R s t

中文:
定理 adjoin_union_eq_adjoin_adjoin
  证明: by
  simpa using adjoin_algebraMap_image_union_eq_adjoin_adjoin R s t

Depends on / 依赖: adjoin_algebraMap_image_union_eq_adjoin_adjoin
-/
theorem adjoin_union_eq_adjoin_adjoin :
    adjoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R := by
  simpa using adjoin_algebraMap_image_union_eq_adjoin_adjoin R s t

/--
theorem `adjoin_eq_adjoin_union` / 定理 `adjoin_eq_adjoin_union`

English:
theorem adjoin_eq_adjoin_union
  statement: [CommSemiring B] [Algebra R B] [Algebra A B]
  proof: by
  have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom R A B)) hS
  rw [Algebra.map_top]; rw [AlgHom.map_adjoin]; rw [IsScalarTower.coe_toAlgHom'] at this
  rw [adjoin_union_eq_adjoin_adjoin]; rw [this]; rw [← IsScalarTower.adjoin_range_toAlgHom]

中文:
定理 adjoin_eq_adjoin_union
  结论: [交换半环 B] [代数 R B] [代数 A B]
  证明: by
  have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom R A B)) hS
  rw [Algebra.map_top]; rw [AlgHom.map_adjoin]; rw [IsScalarTower.coe_toAlgHom'] at this
  rw [adjoin_union_eq_adjoin_adjoin]; rw [this]; rw [← IsScalarTower.adjoin_range_toAlgHom]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, IsScalarTower, IsScalarTower.adjoin_range_toAlgHom, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, Subalgebra, Subalgebra.map, adjoin_range_toAlgHom, adjoin_union_eq_adjoin_adjoin, coe_toAlgHom, congr_arg, map_adjoin, map_top, toAlgHom
-/
theorem adjoin_eq_adjoin_union [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (s : Set A) (t : Set B) (hS : adjoin R s = ⊤) :
    (adjoin A t).restrictScalars R = adjoin R ((algebraMap A B '' s) union t) := by
  have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom R A B)) hS
  rw [Algebra.map_top]; rw [AlgHom.map_adjoin]; rw [IsScalarTower.coe_toAlgHom'] at this
  rw [adjoin_union_eq_adjoin_adjoin]; rw [this]; rw [← IsScalarTower.adjoin_range_toAlgHom]

variable {R}

/--
theorem `pow_smul_mem_of_smul_subset_of_mem_adjoin` / 定理 `pow_smul_mem_of_smul_subset_of_mem_adjoin`

English:
theorem pow_smul_mem_of_smul_subset_of_mem_adjoin
  statement: [CommSemiring B] [Algebra R B] [Algebra A B]
  proof: by
  change x in Subalgebra.toSubmodule (adjoin R s) at hx
  rw [adjoin_eq_span]; rw [Finsupp.mem_span_iff_linearCombination] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • (i : B)) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine B'.toSubmodule.sum_mem ?_
  intro a ha
  have : n >= n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this]; rw [pow_add]; rw [← smul_smul]; rw [←
    IsScalarTower.algebraMap_smul A (l a) (a : B)]; rw [smul_smul (r ^ n₁ a)]; rw [mul_comm]; rw [← smul_smul]; rw [smul_def]; rw [map_pow]; rw [IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine Subalgebra.smul_mem _ ?_ _
  change _ in B'.toSubmonoid
  rw [← Submonoid.closure_eq B'.toSubmonoid]
  apply Submonoid.closure_mono hs (n₂ a)

中文:
定理 pow_smul_mem_of_smul_subset_of_mem_adjoin
  结论: [交换半环 B] [代数 R B] [代数 A B]
  证明: by
  change x in Subalgebra.toSubmodule (adjoin R s) at hx
  rw [adjoin_eq_span]; rw [Finsupp.mem_span_iff_linearCombination] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • (i : B)) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine B'.toSubmodule.sum_mem ?_
  intro a ha
  have : n >= n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this]; rw [pow_add]; rw [← smul_smul]; rw [←
    IsScalarTower.algebraMap_smul A (l a) (a : B)]; rw [smul_smul (r ^ n₁ a)]; rw [mul_comm]; rw [← smul_smul]; rw [smul_def]; rw [map_pow]; rw [IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine Subalgebra.smul_mem _ ?_ _
  change _ in B'.toSubmonoid
  rw [← Submonoid.closure_eq B'.toSubmonoid]
  apply Submonoid.closure_mono hs (n₂ a)

Depends on / 依赖: Finset, Finset.le_sup, Finsupp, Finsupp.mem_span_iff_linearCombination, Finsupp.smul_sum, Subalgebra, Subalgebra.toSubmodule, Submonoid, Submonoid.closure, Submonoid.pow_smul_mem_closure_smul, adjoin, adjoin_eq_span, closure, l.sum, l.support.sup, le_sup, le_trans, mem_span_iff_linearCombination, pow_smul_mem_closure_smul, smul_sum
-/
theorem pow_smul_mem_of_smul_subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (r : A) (s : Set B) (B' : Subalgebra R B) (hs : r • s subseteq B') {x : B}
    (hx : x in adjoin R s) (hr : algebraMap A B r in B') : exists n₀ : Nat, forall n >= n₀, r ^ n • x in B' := by
  change x in Subalgebra.toSubmodule (adjoin R s) at hx
  rw [adjoin_eq_span]; rw [Finsupp.mem_span_iff_linearCombination] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • (i : B)) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine B'.toSubmodule.sum_mem ?_
  intro a ha
  have : n >= n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this]; rw [pow_add]; rw [← smul_smul]; rw [←
    IsScalarTower.algebraMap_smul A (l a) (a : B)]; rw [smul_smul (r ^ n₁ a)]; rw [mul_comm]; rw [← smul_smul]; rw [smul_def]; rw [map_pow]; rw [IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine Subalgebra.smul_mem _ ?_ _
  change _ in B'.toSubmonoid
  rw [← Submonoid.closure_eq B'.toSubmonoid]
  apply Submonoid.closure_mono hs (n₂ a)

/--
theorem `pow_smul_mem_adjoin_smul` / 定理 `pow_smul_mem_adjoin_smul`

English:
theorem pow_smul_mem_adjoin_smul
  given: (r : R) (s : Set A) {x : A} (hx : x in adjoin R s)
  proof: pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)

中文:
定理 pow_smul_mem_adjoin_smul
  条件: (r : R) (s : 集合 A) {x : A} (hx : x in adjoin R s)
  证明: pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)

Depends on / 依赖: Subalgebra, Subalgebra.algebraMap_mem, algebraMap_mem, pow_smul_mem_of_smul_subset_of_mem_adjoin, subset_adjoin
-/
theorem pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x in adjoin R s) :
    exists n₀ : Nat, forall n >= n₀, r ^ n • x in adjoin R (r • s) :=
  pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)

/--
lemma `adjoin_nonUnitalSubalgebra_eq_span` / 引理 `adjoin_nonUnitalSubalgebra_eq_span`

English:
lemma adjoin_nonUnitalSubalgebra_eq_span
  given: (s : NonUnitalSubalgebra R A)
  proof: by
  rw [adjoin_eq_span]; rw [Submonoid.closure_eq_one_union]; rw [span_union]; rw [← NonUnitalAlgebra.adjoin_eq_span]; rw [NonUnitalAlgebra.adjoin_eq]

中文:
引理 adjoin_nonUnitalSubalgebra_eq_span
  条件: (s : NonUnital子代数 R A)
  证明: by
  rw [adjoin_eq_span]; rw [Submonoid.closure_eq_one_union]; rw [span_union]; rw [← NonUnitalAlgebra.adjoin_eq_span]; rw [NonUnitalAlgebra.adjoin_eq]

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin_eq, NonUnitalAlgebra.adjoin_eq_span, Submonoid, Submonoid.closure_eq_one_union, adjoin_eq, adjoin_eq_span, closure_eq_one_union, span_union
-/
lemma adjoin_nonUnitalSubalgebra_eq_span (s : NonUnitalSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)) = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span]; rw [Submonoid.closure_eq_one_union]; rw [span_union]; rw [← NonUnitalAlgebra.adjoin_eq_span]; rw [NonUnitalAlgebra.adjoin_eq]

end CommSemiring

end Algebra

open Algebra Subalgebra

section

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

variable [CommSemiring F] [Algebra F K] [IsScalarTower F E K] (L : Subalgebra F K) {F}

/--
theorem `Subalgebra.adjoin_eq_span_basis` / 定理 `Subalgebra.adjoin_eq_span_basis`

English:
theorem Subalgebra.adjoin_eq_span_basis
  given: {ι : Type*} (bL : Basis ι F L)
  proof: L.adjoin_eq_span_of_eq_span E by
    simpa only [← L.range_val, Submodule.map_span, Submodule.map_top, ← Set.range_comp]
      using! congr_arg (Submodule.map (L.val : L ->ₗ[F] K)) bL.span_eq.symm

中文:
定理 子代数.adjoin_eq_span_basis
  条件: {ι : 类型} (bL : 基 ι F L)
  证明: L.adjoin_eq_span_of_eq_span E by
    simpa only [← L.range_val, Submodule.map_span, Submodule.map_top, ← Set.range_comp]
      using! congr_arg (Submodule.map (L.val : L ->ₗ[F] K)) bL.span_eq.symm

Depends on / 依赖: L.adjoin_eq_span_of_eq_span, L.range_val, L.val, Set.range_comp, Submodule, Submodule.map, Submodule.map_span, Submodule.map_top, adjoin_eq_span_of_eq_span, bL.span_eq.symm, congr_arg, map_span, map_top, range_comp, range_val, span_eq
-/
theorem Subalgebra.adjoin_eq_span_basis {ι : Type*} (bL : Basis ι F L) :
    toSubmodule (adjoin E (L : Set K)) = span E (Set.range fun i : ι => (bL i).1) :=
L.adjoin_eq_span_of_eq_span E by
    simpa only [← L.range_val, Submodule.map_span, Submodule.map_top, ← Set.range_comp]
      using! congr_arg (Submodule.map (L.val : L ->ₗ[F] K)) bL.span_eq.symm

/--
theorem `Algebra.restrictScalars_adjoin` / 定理 `Algebra.restrictScalars_adjoin`

English:
theorem Algebra.restrictScalars_adjoin
  statement: (F : Type*) [CommSemiring F] {E : Type*} [CommSemiring E]
  proof: by
  conv_lhs => rw [← Algebra.adjoin_eq K, ← Algebra.adjoin_union_eq_adjoin_adjoin]

中文:
定理 代数.restrictScalars_adjoin
  结论: (F : 类型) [交换半环 F] {E : 类型} [交换半环 E]
  证明: by
  conv_lhs => rw [← Algebra.adjoin_eq K, ← Algebra.adjoin_union_eq_adjoin_adjoin]

Depends on / 依赖: Algebra, Algebra.adjoin_eq, Algebra.adjoin_union_eq_adjoin_adjoin, adjoin_eq, adjoin_union_eq_adjoin_adjoin, conv_lhs
-/
theorem Algebra.restrictScalars_adjoin (F : Type*) [CommSemiring F] {E : Type*} [CommSemiring E]
    [Algebra F E] (K : Subalgebra F E) (S : Set E) :
    (Algebra.adjoin K S).restrictScalars F = Algebra.adjoin F (K union S) := by
  conv_lhs => rw [← Algebra.adjoin_eq K, ← Algebra.adjoin_union_eq_adjoin_adjoin]

/--
theorem `Algebra.restrictScalars_adjoin_of_algEquiv` / 定理 `Algebra.restrictScalars_adjoin_of_algEquiv`

English:
theorem Algebra.restrictScalars_adjoin_of_algEquiv
  proof: by
  apply_fun Subalgebra.toSubsemiring using fun K K' h => by rwa [SetLike.ext'_iff] at h ⊢
  change Subsemiring.closure _ = Subsemiring.closure _
  rw [hi]; rw [Set.range_comp]; rw [EquivLike.range_eq_univ]; rw [Set.image_univ]

中文:
定理 代数.restrictScalars_adjoin_of_algEquiv
  证明: by
  apply_fun Subalgebra.toSubsemiring using fun K K' h => by rwa [SetLike.ext'_iff] at h ⊢
  change Subsemiring.closure _ = Subsemiring.closure _
  rw [hi]; rw [Set.range_comp]; rw [EquivLike.range_eq_univ]; rw [Set.image_univ]

Depends on / 依赖: EquivLike, EquivLike.range_eq_univ, Set.image_univ, Set.range_comp, SetLike, SetLike.ext, Subalgebra, Subalgebra.toSubsemiring, Subsemiring, Subsemiring.closure, _iff, apply_fun, closure, image_univ, range_comp, range_eq_univ, toSubsemiring
-/
theorem Algebra.restrictScalars_adjoin_of_algEquiv
    {F E L L' : Type*} [CommSemiring F] [CommSemiring L] [CommSemiring L'] [Semiring E]
    [Algebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E] [Algebra F E]
    [IsScalarTower F L E] [IsScalarTower F L' E] (i : L ≃ₐ[F] L')
    (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Set E) :
    (Algebra.adjoin L S).restrictScalars F = (Algebra.adjoin L' S).restrictScalars F := by
  apply_fun Subalgebra.toSubsemiring using fun K K' h => by rwa [SetLike.ext'_iff] at h ⊢
  change Subsemiring.closure _ = Subsemiring.closure _
  rw [hi]; rw [Set.range_comp]; rw [EquivLike.range_eq_univ]; rw [Set.image_univ]

end
