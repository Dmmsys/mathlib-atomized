/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Central.Defs

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Central Algebras

In this file, we prove some basic results about central algebras over a commutative ring.

## Main results

- `Algebra.IsCentral.center_eq_bot`: the center of a central algebra over `K` is equal to `K`.
- `Algebra.IsCentral.self`: a commutative ring is a central algebra over itself.
- `Algebra.IsCentral.baseField_essentially_unique`: Let `D/K/k` be a tower of scalars where
  `K` and `k` are fields. If `D` is a nontrivial central algebra over `k`, `K` is isomorphic to `k`.
-/

public section

universe u v

namespace Algebra.IsCentral

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

@[simp]
/--
lemma `center_eq_bot` / 引理 `center_eq_bot`

English:
lemma center_eq_bot
  statement: Subalgebra.center K D = ⊥
  proof: eq_bot_iff.2 IsCentral.out

中文:
引理 center_eq_bot
  结论: 子代数.center K D = ⊥
  证明: eq_bot_iff.2 IsCentral.out

Depends on / 依赖: IsCentral, IsCentral.out, eq_bot_iff
-/
lemma center_eq_bot : Subalgebra.center K D = ⊥ := eq_bot_iff.2 IsCentral.out

variable {D} in
/--
lemma `mem_center_iff` / 引理 `mem_center_iff`

English:
lemma mem_center_iff
  given: {x : D}
  statement: x in Subalgebra.center K D ↔ exists (a : K), x = algebraMap K D a
  proof: by
  rw [center_eq_bot]; rw [Algebra.mem_bot]
  simp [eq_comm]

中文:
引理 mem_center_iff
  条件: {x : D}
  结论: x in 子代数.center K D ↔ 存在 (a : K), x = algebraMap K D a
  证明: by
  rw [center_eq_bot]; rw [Algebra.mem_bot]
  simp [eq_comm]

Depends on / 依赖: Algebra, Algebra.mem_bot, center_eq_bot, eq_comm, mem_bot
-/
lemma mem_center_iff {x : D} : x in Subalgebra.center K D ↔ exists (a : K), x = algebraMap K D a := by
  rw [center_eq_bot]; rw [Algebra.mem_bot]
  simp [eq_comm]

/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : IsCentral K K where
  body: by simp [Algebra.mem_bot]

中文:
实例 self
  签名: : 是中心 K K where
  定义体: by simp [Algebra.mem_bot]

Depends on / 依赖: Algebra, Algebra.mem_bot, CommRingCat, CommRingCat.monoidAlgebraAdj, mem_bot, monoidAlgebraAdj
-/
instance self : IsCentral K K where
  out x := by simp [Algebra.mem_bot]

/--
lemma `baseField_essentially_unique` / 引理 `baseField_essentially_unique`

English:
lemma baseField_essentially_unique
  proof: by
  have : IsCentral K D :=
  { out := fun x => show x in Subalgebra.center k D -> _ by
      simp only [center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩ }
  refine ⟨FaithfulSMul.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x in (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
exact ⟨x', (algebraMap K D).injective by simp [← H, algebraMap_eq_smul_one]⟩

中文:
引理 baseField_essentially_unique
  证明: by
  have : IsCentral K D :=
  { out := fun x => show x in Subalgebra.center k D -> _ by
      simp only [center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩ }
  refine ⟨FaithfulSMul.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x in (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
exact ⟨x', (algebraMap K D).injective by simp [← H, algebraMap_eq_smul_one]⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsCentral, Set.mem_range, Subalgebra, Subalgebra.algebraMap_mem, Subalgebra.center, algebraMap, algebraMap_eq_smul_one, algebraMap_injective, algebraMap_mem, center, center_eq_bot, forall_exists_index, mem_bot, mem_range, smul_assoc
-/
lemma baseField_essentially_unique
    (k K D : Type*) [Field k] [Field K] [Ring D] [Nontrivial D]
    [Algebra k K] [Algebra K D] [Algebra k D] [IsScalarTower k K D]
    [IsCentral k D] :
    Function.Bijective (algebraMap k K) := by
  have : IsCentral K D :=
  { out := fun x => show x in Subalgebra.center k D -> _ by
      simp only [center_eq_bot, mem_bot, Set.mem_range, forall_exists_index]
      rintro x rfl
      exact ⟨algebraMap k K x, by simp [algebraMap_eq_smul_one, smul_assoc]⟩ }
  refine ⟨FaithfulSMul.algebraMap_injective k K, fun x => ?_⟩
  have H : algebraMap K D x in (Subalgebra.center K D : Set D) := Subalgebra.algebraMap_mem _ _
  rw [show (Subalgebra.center K D : Set D) = Subalgebra.center k D by rfl] at H
  simp only [center_eq_bot, coe_bot, Set.mem_range] at H
  obtain ⟨x', H⟩ := H
exact ⟨x', (algebraMap K D).injective by simp [← H, algebraMap_eq_smul_one]⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_algEquiv` / 引理 `of_algEquiv`

English:
lemma of_algEquiv
  given: (e : D ≃ₐ[K] D')
  statement: IsCentral K D' where
  proof: have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

中文:
引理 of_algEquiv
  条件: (e : D ≃ₐ[K] D')
  结论: 是中心 K D' where
  证明: have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

Depends on / 依赖: MulEquivClass, MulEquivClass.apply_mem_center_iff, apply_mem_center_iff, e.symm
-/
lemma of_algEquiv (e : D ≃ₐ[K] D') : IsCentral K D' where
  out x hx :=
    have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

open MulOpposite in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCentral K Dᵐᵒᵖ
  body: have ⟨k, hk⟩ := h.1 (MulOpposite.unop_mem_center_iff.mpr hz)
    ⟨k, by simpa using congr(op $hk)⟩

中文:
实例 :
  签名: 是中心 K Dᵐᵒᵖ
  定义体: have ⟨k, hk⟩ := h.1 (MulOpposite.unop_mem_center_iff.mpr hz)
    ⟨k, by simpa using congr(op $hk)⟩

Depends on / 依赖: MulOpposite, MulOpposite.unop_mem_center_iff.mpr, unop_mem_center_iff
-/
instance : IsCentral K Dᵐᵒᵖ where
  out z hz :=
    have ⟨k, hk⟩ := h.1 (MulOpposite.unop_mem_center_iff.mpr hz)
    ⟨k, by simpa using congr(op $hk)⟩

end Algebra.IsCentral
