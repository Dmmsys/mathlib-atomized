/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Christopher Hoskin
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Orthogonal complement

This file defines the orthogonal submodule of a submodule with respect to a sesqui-blinear map.

## Main declarations

* `orthogonalBilin` provides the orthogonal complement with respect to a sesqui-bilinear map
-/

@[expose] public section

open Module LinearMap

variable {R R₁ R₂ M M₁ M₂ : Type*}

namespace Submodule

/-! ### The orthogonal complement -/

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R₁ M₁]
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {I₁ : R₁ ->+* R} {I₂ : R₂ ->+* R}
variable {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
variable {S T : Submodule R₁ M₁}

variable (B S) in
/--
Definition of `orthogonalBilin` / `orthogonalBilin` 的定义

English:
definition orthogonalBilin
  signature: : Submodule R₂ M₂ where
  body: {y | forall x in S, B x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by simp [hu _ hx, hv _ hx]
  smul_mem' c y hy x hx := by simp [hy _ hx]

中文:
定义 orthogonalBilin
  签名: : 子模 R₂ M₂ where
  定义体: {y | forall x in S, B x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by simp [hu _ hx, hv _ hx]
  smul_mem' c y hy x hx := by simp [hy _ hx]
-/
def orthogonalBilin : Submodule R₂ M₂ where
  carrier := {y | forall x in S, B x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by simp [hu _ hx, hv _ hx]
  smul_mem' c y hy x hx := by simp [hy _ hx]

/--
theorem `mem_orthogonalBilin_iff` / 定理 `mem_orthogonalBilin_iff`

English:
theorem mem_orthogonalBilin_iff
  given: {m : M₂}
  proof: .rfl

中文:
定理 mem_orthogonalBilin_iff
  条件: {m : M₂}
  证明: .rfl
-/
@[simp] theorem mem_orthogonalBilin_iff {m : M₂} :
  m in S.orthogonalBilin B ↔ forall n in S, B n m = 0 := .rfl

/--
theorem `orthogonalBilin_le` / 定理 `orthogonalBilin_le`

English:
theorem orthogonalBilin_le
  given: (h : S <= T)
  proof: fun _ hy _ hx => hy _ (h hx)

中文:
定理 orthogonalBilin_le
  条件: (h : S <= T)
  证明: fun _ hy _ hx => hy _ (h hx)
-/
@[gcongr] theorem orthogonalBilin_le (h : S <= T) :
    orthogonalBilin B T <= orthogonalBilin B S := fun _ hy _ hx => hy _ (h hx)

section IsRefl

variable {I₂ : R₁ ->+* R} {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M}

/--
theorem `le_orthogonalBilin_orthogonalBilin` / 定理 `le_orthogonalBilin_orthogonalBilin`

English:
theorem le_orthogonalBilin_orthogonalBilin
  given: (b : B.IsRefl)
  proof: fun n hn _m hm => b _ _ (hm n hn)

中文:
定理 le_orthogonalBilin_orthogonalBilin
  条件: (b : B.IsRefl)
  证明: fun n hn _m hm => b _ _ (hm n hn)
-/
theorem le_orthogonalBilin_orthogonalBilin (b : B.IsRefl) :
    S <= (S.orthogonalBilin B).orthogonalBilin B := fun n hn _m hm => b _ _ (hm n hn)

end IsRefl

end Submodule

namespace LinearMap

section Orthogonal

variable {K K₁ V V₁ V₂ : Type*}
variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [AddCommGroup V₂] [Module K V₂] {J : K ->+* K} {J₁ : K₁ ->+* K} {J₁' : K₁ ->+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
/--
theorem `span_singleton_inf_orthogonal_eq_bot` / 定理 `span_singleton_inf_orthogonal_eq_bot`

English:
theorem span_singleton_inf_orthogonal_eq_bot
  statement: (B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂) (x : V₁)
  proof: by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h => ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x in Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y => by simpa using y)
      (fun hfalse => False.elim <| hx hfalse)

中文:
定理 span_singleton_inf_orthogonal_eq_bot
  结论: (B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂) (x : V₁)
  证明: by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h => ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x in Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y => by simpa using y)
      (fun hfalse => False.elim <| hx hfalse)

Depends on / 依赖: False.elim, Finset, Finset.coe_singleton, Finset.sum_singleton, Or.elim, Submodule, Submodule.mem_bot, Submodule.mem_span, Submodule.mem_span_finset, Submodule.span, coe_singleton, eq_bot_iff, hfalse, mem_bot, mem_span, mem_span_finset, replace, smul_eq_zero, smul_eq_zero.mp, sum_singleton
-/
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂) (x : V₁)
    (hx : B x x != 0) : (K₁ ∙ x) ⊓ (K₁ ∙ x).orthogonalBilin B = ⊥ := by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h => ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x in Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y => by simpa using y)
      (fun hfalse => False.elim <| hx hfalse)

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
/--
theorem `orthogonal_span_singleton_eq_to_lin_ker` / 定理 `orthogonal_span_singleton_eq_to_lin_ker`

English:
theorem orthogonal_span_singleton_eq_to_lin_ker
  given: {B : V ->ₗ[K] V ->ₛₗ[J] V₂} (x : V)
  proof: by
  ext y
  simp_rw [Submodule.mem_orthogonalBilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [map_smulₛₗ₂]; rw [smul_eq_zero]
    exact Or.intro_right _ h

中文:
定理 orthogonal_span_singleton_eq_to_lin_ker
  条件: {B : V ->ₗ[K] V ->ₛₗ[J] V₂} (x : V)
  证明: by
  ext y
  simp_rw [Submodule.mem_orthogonalBilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [map_smulₛₗ₂]; rw [smul_eq_zero]
    exact Or.intro_right _ h

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Or.intro_right, Submodule, Submodule.mem_orthogonalBilin_iff, Submodule.mem_span_singleton, intro_right, mem_ker, mem_orthogonalBilin_iff, mem_span_singleton, one_smul, simp_rw, smul_eq_zero
-/
theorem orthogonal_span_singleton_eq_to_lin_ker {B : V ->ₗ[K] V ->ₛₗ[J] V₂} (x : V) :
    (K ∙ x).orthogonalBilin B = LinearMap.ker (B x) := by
  ext y
  simp_rw [Submodule.mem_orthogonalBilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [map_smulₛₗ₂]; rw [smul_eq_zero]
    exact Or.intro_right _ h

-- todo: Generalize this to sesquilinear maps
/--
theorem `span_singleton_sup_orthogonal_eq_top` / 定理 `span_singleton_sup_orthogonal_eq_top`

English:
theorem span_singleton_sup_orthogonal_eq_top
  given: {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0)
  proof: by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

中文:
定理 span_singleton_sup_orthogonal_eq_top
  条件: {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0)
  证明: by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

Depends on / 依赖: orthogonal_span_singleton_eq_to_lin_ker, span_singleton_sup_ker_eq_top
-/
theorem span_singleton_sup_orthogonal_eq_top {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0) :
    (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

-- todo: Generalize this to sesquilinear maps
/--
theorem `isCompl_span_singleton_orthogonal` / 定理 `isCompl_span_singleton_orthogonal`

English:
theorem isCompl_span_singleton_orthogonal
  given: {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0)
  proof: { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
codisjoint := codisjoint_iff.2 span_singleton_sup_orthogonal_eq_top hx }

中文:
定理 isCompl_span_singleton_orthogonal
  条件: {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0)
  证明: { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
codisjoint := codisjoint_iff.2 span_singleton_sup_orthogonal_eq_top hx }

Depends on / 依赖: codisjoint, codisjoint_iff, disjoint, disjoint_iff, span_singleton_inf_orthogonal_eq_bot, span_singleton_sup_orthogonal_eq_top
-/
theorem isCompl_span_singleton_orthogonal {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0) :
    IsCompl (K ∙ x) ((K ∙ x).orthogonalBilin B) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
codisjoint := codisjoint_iff.2 span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁] {I I' : R ->+* R}

/--
theorem `nondegenerate_restrict_of_disjoint_orthogonal` / 定理 `nondegenerate_restrict_of_disjoint_orthogonal`

English:
theorem nondegenerate_restrict_of_disjoint_orthogonal
  statement: {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
  proof: by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero]; rw [← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy => ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  exact hB.eq_zero b₁

中文:
定理 nondegenerate_restrict_of_disjoint_orthogonal
  结论: {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
  证明: by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero]; rw [← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy => ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  exact hB.eq_zero b₁

Depends on / 依赖: Submodule, Submodule.mem_bot, Submodule.mk_eq_zero, domRestrict, eq_zero, hB.domRestrict, hB.eq_zero, hW.le_bot, le_bot, mem_bot, mk_eq_zero, nondegenerate_iff_separatingLeft, simp_rw, specialize
-/
theorem nondegenerate_restrict_of_disjoint_orthogonal {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl)
    {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero]; rw [← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy => ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  exact hB.eq_zero b₁

end CommRing

end LinearMap
