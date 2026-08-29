/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Lemmas about bilinear maps with a basis over each argument
-/

public section

open Module

namespace LinearMap

variable {ι₁ ι₂ : Type*}
variable {R R₂ S S₂ M N P Rₗ : Type*}
variable {Mₗ Nₗ Pₗ : Type*}

-- Could weaken [CommSemiring Rₗ] to [SMulCommClass Rₗ Rₗ Pₗ], but might impact performance
variable [Semiring R] [Semiring S] [Semiring R₂] [Semiring S₂] [CommSemiring Rₗ]

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Mₗ] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]
variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]
variable [Module Rₗ Mₗ] [Module Rₗ Nₗ] [Module Rₗ Pₗ]
variable [SMulCommClass S₂ R₂ P]
variable {ρ₁₂ : R ->+* R₂} {σ₁₂ : S ->+* S₂}
variable (b₁ : Basis ι₁ R M) (b₂ : Basis ι₂ S N) (b₁' : Basis ι₁ Rₗ Mₗ) (b₂' : Basis ι₂ Rₗ Nₗ)

/--
theorem `ext_basis` / 定理 `ext_basis`

English:
theorem ext_basis
  given: {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : forall i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j))
  proof: b₁.ext fun i => b₂.ext fun j => h i j

中文:
定理 ext_basis
  条件: {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : 对任意 i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j))
  证明: b₁.ext fun i => b₂.ext fun j => h i j
-/
theorem ext_basis {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : forall i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) :
    B = B' :=
  b₁.ext fun i => b₂.ext fun j => h i j

/--
lemma `ext_iff_basis` / 引理 `ext_iff_basis`

English:
lemma ext_iff_basis
  given: {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P}
  proof: ⟨fun h _ _ => h ▸ rfl, ext_basis b₁ b₂⟩

中文:
引理 ext_iff_basis
  条件: {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P}
  证明: ⟨fun h _ _ => h ▸ rfl, ext_basis b₁ b₂⟩

Depends on / 依赖: ext_basis
-/
lemma ext_iff_basis {B B' : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} :
    B = B' ↔ forall (i : ι₁) (j : ι₂), B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j) :=
  ⟨fun h _ _ => h ▸ rfl, ext_basis b₁ b₂⟩

/--
lemma `BilinForm.ext_iff_basis` / 引理 `BilinForm.ext_iff_basis`

English:
lemma BilinForm.ext_iff_basis
  given: {B B' : LinearMap.BilinForm Rₗ Mₗ}
  proof: LinearMap.ext_iff_basis b₁' b₁'

中文:
引理 BilinForm.ext_iff_basis
  条件: {B B' : 线性映射.BilinForm Rₗ Mₗ}
  证明: LinearMap.ext_iff_basis b₁' b₁'

Depends on / 依赖: LinearMap, LinearMap.ext_iff_basis, ext_iff_basis
-/
lemma BilinForm.ext_iff_basis {B B' : LinearMap.BilinForm Rₗ Mₗ} :
    B = B' ↔ forall (i j : ι₁), B (b₁' i) (b₁' j) = B' (b₁' i) (b₁' j) :=
  LinearMap.ext_iff_basis b₁' b₁'

/--
theorem `sum_repr_mul_repr_mulₛₗ` / 定理 `sum_repr_mul_repr_mulₛₗ`

English:
theorem sum_repr_mul_repr_mulₛₗ
  given: {B : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (x y)
  proof: by
  conv_rhs => rw [← b₁.linearCombination_repr x, ← b₂.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smulₛₗ₂, map_smulₛₗ]

中文:
定理 sum_repr_mul_repr_mulₛₗ
  条件: {B : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (x y)
  证明: by
  conv_rhs => rw [← b₁.linearCombination_repr x, ← b₂.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smulₛₗ₂, map_smulₛₗ]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, conv_rhs, linearCombination_apply, linearCombination_repr, map_sum, simp_rw
-/
theorem sum_repr_mul_repr_mulₛₗ {B : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (x y) :
    ((b₁.repr x).sum fun i xi => (b₂.repr y).sum fun j yj => ρ₁₂ xi • σ₁₂ yj • B (b₁ i) (b₂ j)) =
      B x y := by
  conv_rhs => rw [← b₁.linearCombination_repr x, ← b₂.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smulₛₗ₂, map_smulₛₗ]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sum_repr_mul_repr_mul` / 定理 `sum_repr_mul_repr_mul`

English:
theorem sum_repr_mul_repr_mul
  given: {B : Mₗ ->ₗ[Rₗ] Nₗ ->ₗ[Rₗ] Pₗ} (x y)
  proof: by
  conv_rhs => rw [← b₁'.linearCombination_repr x, ← b₂'.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smul₂, map_smul]

中文:
定理 sum_repr_mul_repr_mul
  条件: {B : Mₗ ->ₗ[Rₗ] Nₗ ->ₗ[Rₗ] Pₗ} (x y)
  证明: by
  conv_rhs => rw [← b₁'.linearCombination_repr x, ← b₂'.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smul₂, map_smul]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, conv_rhs, linearCombination_apply, linearCombination_repr, map_smul, map_sum, simp_rw
-/
theorem sum_repr_mul_repr_mul {B : Mₗ ->ₗ[Rₗ] Nₗ ->ₗ[Rₗ] Pₗ} (x y) :
    ((b₁'.repr x).sum fun i xi => (b₂'.repr y).sum fun j yj => xi • yj • B (b₁' i) (b₂' j)) =
      B x y := by
  conv_rhs => rw [← b₁'.linearCombination_repr x, ← b₂'.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, map_smul₂, map_smul]

end AddCommMonoid

end LinearMap
