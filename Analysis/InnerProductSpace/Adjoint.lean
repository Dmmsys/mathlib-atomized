/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Tactic.CrossRefAttribute


/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite-dimensional spaces.

## Main definitions

* `ContinuousLinearMap.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjointAux` is only an intermediate
  definition and is not meant to be used outside this file.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

adjoint

-/

noncomputable section

open Module RCLike

open scoped ComplexConjugate

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Adjoint operator -/


open InnerProductSpace

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace G]

/--
Definition of `adjointAux` / `adjointAux` 的定义

English:
definition adjointAux
  signature: : (E ->L[𝕜] F) ->L⋆[𝕜] F ->L[𝕜] E
  body: (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : StrongDual 𝕜 E ->L⋆[𝕜] E)).comp
    (toSesqForm : (E ->L[𝕜] F) ->L[𝕜] F ->L⋆[𝕜] StrongDual 𝕜 E)

@[simp]

中文:
定义 adjointAux
  签名: : (E ->L[𝕜] F) ->L⋆[𝕜] F ->L[𝕜] E
  定义体: (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : StrongDual 𝕜 E ->L⋆[𝕜] E)).comp
    (toSesqForm : (E ->L[𝕜] F) ->L[𝕜] F ->L⋆[𝕜] StrongDual 𝕜 E)

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compSL, StrongDual, compSL, toDual, toSesqForm
-/
def adjointAux : (E ->L[𝕜] F) ->L⋆[𝕜] F ->L[𝕜] E :=
  (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : StrongDual 𝕜 E ->L⋆[𝕜] E)).comp
    (toSesqForm : (E ->L[𝕜] F) ->L[𝕜] F ->L⋆[𝕜] StrongDual 𝕜 E)

@[simp]
/--
theorem `adjointAux_apply` / 定理 `adjointAux_apply`

English:
theorem adjointAux_apply
  given: (A : E ->L[𝕜] F) (x : F)
  proof: rfl

中文:
定理 adjointAux_apply
  条件: (A : E ->L[𝕜] F) (x : F)
  证明: rfl
-/
theorem adjointAux_apply (A : E ->L[𝕜] F) (x : F) :
    adjointAux A x = ((toDual 𝕜 E).symm : StrongDual 𝕜 E -> E) ((toSesqForm A) x) :=
  rfl

/--
theorem `adjointAux_inner_left` / 定理 `adjointAux_inner_left`

English:
theorem adjointAux_inner_left
  given: (A : E ->L[𝕜] F) (x : E) (y : F)
  statement: ⟪adjointAux A y, x⟫ = ⟪y, A x⟫
  proof: by
  simp

中文:
定理 adjointAux_inner_left
  条件: (A : E ->L[𝕜] F) (x : E) (y : F)
  结论: ⟪adjointAux A y, x⟫ = ⟪y, A x⟫
  证明: by
  simp
-/
theorem adjointAux_inner_left (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪adjointAux A y, x⟫ = ⟪y, A x⟫ := by
  simp

/--
theorem `adjointAux_inner_right` / 定理 `adjointAux_inner_right`

English:
theorem adjointAux_inner_right
  given: (A : E ->L[𝕜] F) (x : E) (y : F)
  proof: by
  rw [← inner_conj_symm]; rw [adjointAux_inner_left]; rw [inner_conj_symm]

中文:
定理 adjointAux_inner_right
  条件: (A : E ->L[𝕜] F) (x : E) (y : F)
  证明: by
  rw [← inner_conj_symm]; rw [adjointAux_inner_left]; rw [inner_conj_symm]

Depends on / 依赖: adjointAux_inner_left, inner_conj_symm
-/
theorem adjointAux_inner_right (A : E ->L[𝕜] F) (x : E) (y : F) :
    ⟪x, adjointAux A y⟫ = ⟪A x, y⟫ := by
  rw [← inner_conj_symm]; rw [adjointAux_inner_left]; rw [inner_conj_symm]

variable [CompleteSpace F]

/--
theorem `adjointAux_adjointAux` / 定理 `adjointAux_adjointAux`

English:
theorem adjointAux_adjointAux
  given: (A : E ->L[𝕜] F)
  statement: adjointAux (adjointAux A) = A
  proof: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjointAux_inner_right]; rw [adjointAux_inner_left]

@[simp]

中文:
定理 adjointAux_adjointAux
  条件: (A : E ->L[𝕜] F)
  结论: adjointAux (adjointAux A) = A
  证明: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjointAux_inner_right]; rw [adjointAux_inner_left]

@[simp]

Depends on / 依赖: adjointAux_inner_left, adjointAux_inner_right, ext_inner_left
-/
theorem adjointAux_adjointAux (A : E ->L[𝕜] F) : adjointAux (adjointAux A) = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjointAux_inner_right]; rw [adjointAux_inner_left]

@[simp]
/--
theorem `adjointAux_norm` / 定理 `adjointAux_norm`

English:
theorem adjointAux_norm
  given: (A : E ->L[𝕜] F)
  statement: ‖adjointAux A‖ = ‖A‖
  proof: by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply]; rw [LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le
  · nth_rw 1 [← adjointAux_adjointAux A]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply]; rw [LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le

public section

中文:
定理 adjointAux_norm
  条件: (A : E ->L[𝕜] F)
  结论: ‖adjointAux A‖ = ‖A‖
  证明: by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply]; rw [LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le
  · nth_rw 1 [← adjointAux_adjointAux A]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply]; rw [LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le

public section

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, LinearIsometryEquiv, LinearIsometryEquiv.norm_map, adjointAux_adjointAux, adjointAux_apply, le_antisymm, norm_map, norm_nonneg, nth_rw, opNorm_le_bound, toSesqForm_apply_norm_le
-/
theorem adjointAux_norm (A : E ->L[𝕜] F) : ‖adjointAux A‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply]; rw [LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le
  · nth_rw 1 [← adjointAux_adjointAux A]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply]; rw [LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le

public section

/-- The adjoint of a bounded operator `A` from a Hilbert space `E` to another Hilbert space `F`,
  denoted as `A†`. -/
@[wikidata Q1509647]
/--
Definition of `adjoint` / `adjoint` 的定义

English:
definition adjoint
  signature: : (E ->L[𝕜] F) ≃ₗᵢ⋆[𝕜] F ->L[𝕜] E
  body: LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjointAux_norm } fun A =>
    ⟨adjointAux A, adjointAux_adjointAux A⟩

@[inherit_doc]
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint

中文:
定义 adjoint
  签名: : (E ->L[𝕜] F) ≃ₗᵢ⋆[𝕜] F ->L[𝕜] E
  定义体: LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjointAux_norm } fun A =>
    ⟨adjointAux A, adjointAux_adjointAux A⟩

@[inherit_doc]
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ofSurjective, adjointAux, adjointAux_adjointAux, adjointAux_norm, norm_map, ofSurjective
-/
def adjoint : (E ->L[𝕜] F) ≃ₗᵢ⋆[𝕜] F ->L[𝕜] E :=
  LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjointAux_norm } fun A =>
    ⟨adjointAux A, adjointAux_adjointAux A⟩

@[inherit_doc]
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint
open InnerProduct

/--
theorem `adjoint_inner_left` / 定理 `adjoint_inner_left`

English:
theorem adjoint_inner_left
  given: (A : E ->L[𝕜] F) (x : E) (y : F)
  statement: ⟪(A†) y, x⟫ = ⟪y, A x⟫
  proof: adjointAux_inner_left A x y

中文:
定理 adjoint_inner_left
  条件: (A : E ->L[𝕜] F) (x : E) (y : F)
  结论: ⟪(A†) y, x⟫ = ⟪y, A x⟫
  证明: adjointAux_inner_left A x y

Depends on / 依赖: adjointAux_inner_left
-/
theorem adjoint_inner_left (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫ :=
  adjointAux_inner_left A x y

/--
theorem `adjoint_inner_right` / 定理 `adjoint_inner_right`

English:
theorem adjoint_inner_right
  given: (A : E ->L[𝕜] F) (x : E) (y : F)
  statement: ⟪x, (A†) y⟫ = ⟪A x, y⟫
  proof: adjointAux_inner_right A x y

中文:
定理 adjoint_inner_right
  条件: (A : E ->L[𝕜] F) (x : E) (y : F)
  结论: ⟪x, (A†) y⟫ = ⟪A x, y⟫
  证明: adjointAux_inner_right A x y

Depends on / 依赖: adjointAux_inner_right
-/
theorem adjoint_inner_right (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫ :=
  adjointAux_inner_right A x y

/-- The adjoint is involutive. -/
@[simp]
/--
theorem `adjoint_adjoint` / 定理 `adjoint_adjoint`

English:
theorem adjoint_adjoint
  given: (A : E ->L[𝕜] F)
  statement: A†† = A
  proof: adjointAux_adjointAux A

中文:
定理 adjoint_adjoint
  条件: (A : E ->L[𝕜] F)
  结论: A†† = A
  证明: adjointAux_adjointAux A

Depends on / 依赖: adjointAux_adjointAux
-/
theorem adjoint_adjoint (A : E ->L[𝕜] F) : A†† = A :=
  adjointAux_adjointAux A

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
/--
theorem `adjoint_comp` / 定理 `adjoint_comp`

English:
theorem adjoint_comp
  given: (A : F ->L[𝕜] G) (B : E ->L[𝕜] F)
  statement: (A ∘L B)† = B† ∘L A†
  proof: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp [adjoint_inner_right]

中文:
定理 adjoint_comp
  条件: (A : F ->L[𝕜] G) (B : E ->L[𝕜] F)
  结论: (A ∘L B)† = B† ∘L A†
  证明: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp [adjoint_inner_right]

Depends on / 依赖: adjoint_inner_right, ext_inner_left
-/
theorem adjoint_comp (A : F ->L[𝕜] G) (B : E ->L[𝕜] F) : (A ∘L B)† = B† ∘L A† := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp [adjoint_inner_right]

/--
theorem `apply_norm_sq_eq_inner_adjoint_left` / 定理 `apply_norm_sq_eq_inner_adjoint_left`

English:
theorem apply_norm_sq_eq_inner_adjoint_left
  given: (A : E ->L[𝕜] F) (x : E)
  proof: by
  have h : ⟪(A† ∘L A) x, x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_left]; rfl
  rw [h]; rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

中文:
定理 apply_norm_sq_eq_inner_adjoint_left
  条件: (A : E ->L[𝕜] F) (x : E)
  证明: by
  have h : ⟪(A† ∘L A) x, x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_left]; rfl
  rw [h]; rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

Depends on / 依赖: adjoint_inner_left, inner_self_eq_norm_sq
-/
theorem apply_norm_sq_eq_inner_adjoint_left (A : E ->L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫ := by
  have h : ⟪(A† ∘L A) x, x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_left]; rfl
  rw [h]; rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

/--
theorem `apply_norm_eq_sqrt_inner_adjoint_left` / 定理 `apply_norm_eq_sqrt_inner_adjoint_left`

English:
theorem apply_norm_eq_sqrt_inner_adjoint_left
  given: (A : E ->L[𝕜] F) (x : E)
  proof: by
  rw [← apply_norm_sq_eq_inner_adjoint_left]; rw [Real.sqrt_sq (norm_nonneg _)]

中文:
定理 apply_norm_eq_sqrt_inner_adjoint_left
  条件: (A : E ->L[𝕜] F) (x : E)
  证明: by
  rw [← apply_norm_sq_eq_inner_adjoint_left]; rw [Real.sqrt_sq (norm_nonneg _)]

Depends on / 依赖: Real.sqrt_sq, apply_norm_sq_eq_inner_adjoint_left, norm_nonneg, sqrt_sq
-/
theorem apply_norm_eq_sqrt_inner_adjoint_left (A : E ->L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_left]; rw [Real.sqrt_sq (norm_nonneg _)]

/--
theorem `apply_norm_sq_eq_inner_adjoint_right` / 定理 `apply_norm_sq_eq_inner_adjoint_right`

English:
theorem apply_norm_sq_eq_inner_adjoint_right
  given: (A : E ->L[𝕜] F) (x : E)
  proof: by
  have h : ⟪x, (A† ∘L A) x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_right]; rfl
  rw [h]; rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

中文:
定理 apply_norm_sq_eq_inner_adjoint_right
  条件: (A : E ->L[𝕜] F) (x : E)
  证明: by
  have h : ⟪x, (A† ∘L A) x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_right]; rfl
  rw [h]; rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

Depends on / 依赖: adjoint_inner_right, inner_self_eq_norm_sq
-/
theorem apply_norm_sq_eq_inner_adjoint_right (A : E ->L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪x, (A† ∘L A) x⟫ := by
  have h : ⟪x, (A† ∘L A) x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_right]; rfl
  rw [h]; rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) _]

/--
theorem `apply_norm_eq_sqrt_inner_adjoint_right` / 定理 `apply_norm_eq_sqrt_inner_adjoint_right`

English:
theorem apply_norm_eq_sqrt_inner_adjoint_right
  given: (A : E ->L[𝕜] F) (x : E)
  proof: by
  rw [← apply_norm_sq_eq_inner_adjoint_right]; rw [Real.sqrt_sq (norm_nonneg _)]

中文:
定理 apply_norm_eq_sqrt_inner_adjoint_right
  条件: (A : E ->L[𝕜] F) (x : E)
  证明: by
  rw [← apply_norm_sq_eq_inner_adjoint_right]; rw [Real.sqrt_sq (norm_nonneg _)]

Depends on / 依赖: Real.sqrt_sq, apply_norm_sq_eq_inner_adjoint_right, norm_nonneg, sqrt_sq
-/
theorem apply_norm_eq_sqrt_inner_adjoint_right (A : E ->L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪x, (A† ∘L A) x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_right]; rw [Real.sqrt_sq (norm_nonneg _)]

/--
theorem `eq_adjoint_iff` / 定理 `eq_adjoint_iff`

English:
theorem eq_adjoint_iff
  given: (A : E ->L[𝕜] F) (B : F ->L[𝕜] E)
  statement: A = B† ↔ forall x y, ⟪A x, y⟫ = ⟪x, B y⟫
  proof: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]

中文:
定理 eq_adjoint_iff
  条件: (A : E ->L[𝕜] F) (B : F ->L[𝕜] E)
  结论: A = B† ↔ 对任意 x y, ⟪A x, y⟫ = ⟪x, B y⟫
  证明: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]

Depends on / 依赖: adjoint_inner_left, ext_inner_right
-/
theorem eq_adjoint_iff (A : E ->L[𝕜] F) (B : F ->L[𝕜] E) : A = B† ↔ forall x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]
/--
theorem `_root_.LinearMap.IsSymmetric.clm_adjoint_eq` / 定理 `_root_.LinearMap.IsSymmetric.clm_adjoint_eq`

English:
theorem _root_.LinearMap.IsSymmetric.clm_adjoint_eq
  given: {A : E ->L[𝕜] E} (hA : A.IsSymmetric)
  proof: by
  rwa [eq_comm, eq_adjoint_iff A A]

中文:
定理 _root_.线性映射.IsSymmetric.clm_adjoint_eq
  条件: {A : E ->L[𝕜] E} (hA : A.IsSymmetric)
  证明: by
  rwa [eq_comm, eq_adjoint_iff A A]

Depends on / 依赖: eq_adjoint_iff, eq_comm
-/
theorem _root_.LinearMap.IsSymmetric.clm_adjoint_eq {A : E ->L[𝕜] E} (hA : A.IsSymmetric) :
    A† = A := by
  rwa [eq_comm, eq_adjoint_iff A A]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `adjoint_id` / 引理 `adjoint_id`

English:
lemma adjoint_id
  statement: (.id 𝕜 E)† = .id 𝕜 E
  proof: by simp

中文:
引理 adjoint_id
  结论: (.id 𝕜 E)† = .id 𝕜 E
  证明: by simp
-/
lemma adjoint_id : (.id 𝕜 E)† = .id 𝕜 E := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `adjoint_one` / 引理 `adjoint_one`

English:
lemma adjoint_one
  statement: (1 : E ->L[𝕜] E)† = 1
  proof: by simp

中文:
引理 adjoint_one
  结论: (1 : E ->L[𝕜] E)† = 1
  证明: by simp
-/
lemma adjoint_one : (1 : E ->L[𝕜] E)† = 1 := by simp

/--
theorem `_root_.Submodule.adjoint_subtypeL` / 定理 `_root_.Submodule.adjoint_subtypeL`

English:
theorem _root_.Submodule.adjoint_subtypeL
  given: (U : Submodule 𝕜 E) [CompleteSpace U]
  proof: by
  symm
  simp [eq_adjoint_iff]

中文:
定理 _root_.子模.adjoint_subtypeL
  条件: (U : 子模 𝕜 E) [完备空间 U]
  证明: by
  symm
  simp [eq_adjoint_iff]

Depends on / 依赖: eq_adjoint_iff
-/
theorem _root_.Submodule.adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL† = U.orthogonalProjectionOnto := by
  symm
  simp [eq_adjoint_iff]

/--
theorem `_root_.Submodule.adjoint_orthogonalProjectionOnto` / 定理 `_root_.Submodule.adjoint_orthogonalProjectionOnto`

English:
theorem _root_.Submodule.adjoint_orthogonalProjectionOnto
  given: (U : Submodule 𝕜 E) [CompleteSpace U]
  proof: by
  rw [← U.adjoint_subtypeL]; rw [adjoint_adjoint]

@[deprecated (since := "2026-05-05")] alias _root_.Submodule.adjoint_orthogonalProjection :=
  Submodule.adjoint_orthogonalProjectionOnto

中文:
定理 _root_.子模.adjoint_orthogonalProjectionOnto
  条件: (U : 子模 𝕜 E) [完备空间 U]
  证明: by
  rw [← U.adjoint_subtypeL]; rw [adjoint_adjoint]

@[deprecated (since := "2026-05-05")] alias _root_.Submodule.adjoint_orthogonalProjection :=
  Submodule.adjoint_orthogonalProjectionOnto

Depends on / 依赖: U.adjoint_subtypeL, adjoint_adjoint, adjoint_subtypeL
-/
theorem _root_.Submodule.adjoint_orthogonalProjectionOnto (U : Submodule 𝕜 E) [CompleteSpace U] :
    (U.orthogonalProjectionOnto : E ->L[𝕜] U)† = U.subtypeL := by
  rw [← U.adjoint_subtypeL]; rw [adjoint_adjoint]

@[deprecated (since := "2026-05-05")] alias _root_.Submodule.adjoint_orthogonalProjection :=
  Submodule.adjoint_orthogonalProjectionOnto

/--
theorem `orthogonal_ker` / 定理 `orthogonal_ker`

English:
theorem orthogonal_ker
  given: (T : E ->L[𝕜] F)
  proof: by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply le_antisymm
  all_goals refine Submodule.orthogonal_le fun x hx => ?_
  · refine ext_inner_left 𝕜 fun y => ?_
    simp [← T.adjoint_inner_left, hx _]
  · rintro _ ⟨y, rfl⟩
    simp_all [T.adjoint_inner_left]

中文:
定理 orthogonal_ker
  条件: (T : E ->L[𝕜] F)
  证明: by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply le_antisymm
  all_goals refine Submodule.orthogonal_le fun x hx => ?_
  · refine ext_inner_left 𝕜 fun y => ?_
    simp [← T.adjoint_inner_left, hx _]
  · rintro _ ⟨y, rfl⟩
    simp_all [T.adjoint_inner_left]

Depends on / 依赖: Submodule, Submodule.orthogonal_le, Submodule.orthogonal_orthogonal_eq_closure, T.adjoint_inner_left, adjoint_inner_left, all_goals, ext_inner_left, le_antisymm, orthogonal_le, orthogonal_orthogonal_eq_closure
-/
theorem orthogonal_ker (T : E ->L[𝕜] F) :
    T.kerᗮ = T†.range.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply le_antisymm
  all_goals refine Submodule.orthogonal_le fun x hx => ?_
  · refine ext_inner_left 𝕜 fun y => ?_
    simp [← T.adjoint_inner_left, hx _]
  · rintro _ ⟨y, rfl⟩
    simp_all [T.adjoint_inner_left]

/--
theorem `orthogonal_range` / 定理 `orthogonal_range`

English:
theorem orthogonal_range
  given: (T : E ->L[𝕜] F)
  statement: T.rangeᗮ = T†.ker
  proof: by
  rw [← T†.ker.orthogonal_orthogonal]; rw [T†.orthogonal_ker]
  simp

中文:
定理 orthogonal_range
  条件: (T : E ->L[𝕜] F)
  结论: T.rangeᗮ = T†.ker
  证明: by
  rw [← T†.ker.orthogonal_orthogonal]; rw [T†.orthogonal_ker]
  simp

Depends on / 依赖: ker.orthogonal_orthogonal, orthogonal_ker, orthogonal_orthogonal
-/
theorem orthogonal_range (T : E ->L[𝕜] F) : T.rangeᗮ = T†.ker := by
  rw [← T†.ker.orthogonal_orthogonal]; rw [T†.orthogonal_ker]
  simp

/--
theorem `norm_eq_iInf_range_iff_adjoint_apply_eq_zero` / 定理 `norm_eq_iInf_range_iff_adjoint_apply_eq_zero`

English:
theorem norm_eq_iInf_range_iff_adjoint_apply_eq_zero
  given: (A : E ->L[𝕜] F) (y : F) (x : E)
  proof: by
  rw [A.range.norm_eq_iInf_iff_inner_eq_zero (by simp)]; rw [← Submodule.mem_orthogonal']; rw [A.orthogonal_range]; rw [LinearMap.mem_ker]; rw [coe_coe]

中文:
定理 norm_eq_iInf_range_iff_adjoint_apply_eq_zero
  条件: (A : E ->L[𝕜] F) (y : F) (x : E)
  证明: by
  rw [A.range.norm_eq_iInf_iff_inner_eq_zero (by simp)]; rw [← Submodule.mem_orthogonal']; rw [A.orthogonal_range]; rw [LinearMap.mem_ker]; rw [coe_coe]

Depends on / 依赖: A.orthogonal_range, A.range.norm_eq_iInf_iff_inner_eq_zero, LinearMap, LinearMap.mem_ker, Submodule, Submodule.mem_orthogonal, coe_coe, mem_ker, mem_orthogonal, norm_eq_iInf_iff_inner_eq_zero, orthogonal_range
-/
theorem norm_eq_iInf_range_iff_adjoint_apply_eq_zero (A : E ->L[𝕜] F) (y : F) (x : E) :
    (‖y - A x‖ = ⨅ z : A.range, ‖y - z‖) ↔ (A†) (y - A x) = 0 := by
  rw [A.range.norm_eq_iInf_iff_inner_eq_zero (by simp)]; rw [← Submodule.mem_orthogonal']; rw [A.orthogonal_range]; rw [LinearMap.mem_ker]; rw [coe_coe]

/--
theorem `forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero` / 定理 `forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero`

English:
theorem forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero
  proof: by
  have hb : BddBelow (Set.range fun w : A.range => ‖y - w‖) := ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  rw [← A.norm_eq_iInf_range_iff_adjoint_apply_eq_zero y x]; rw [le_antisymm_iff]; rw [and_iff_left (ciInf_le hb ⟨A x]; rw [x]; rw [rfl⟩)]; rw [le_ciInf_iff hb]
  simp

omit [CompleteSpace E] in

中文:
定理 对任意_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero
  证明: by
  have hb : BddBelow (Set.range fun w : A.range => ‖y - w‖) := ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  rw [← A.norm_eq_iInf_range_iff_adjoint_apply_eq_zero y x]; rw [le_antisymm_iff]; rw [and_iff_left (ciInf_le hb ⟨A x]; rw [x]; rw [rfl⟩)]; rw [le_ciInf_iff hb]
  simp

omit [CompleteSpace E] in

Depends on / 依赖: A.norm_eq_iInf_range_iff_adjoint_apply_eq_zero, A.range, BddBelow, Set.range, and_iff_left, ciInf_le, le_antisymm_iff, le_ciInf_iff, norm_eq_iInf_range_iff_adjoint_apply_eq_zero
-/
theorem forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero
    (A : E ->L[𝕜] F) (y : F) (x : E) :
    (forall z : E, ‖y - A x‖ <= ‖y - A z‖) ↔ (A†) (y - A x) = 0 := by
  have hb : BddBelow (Set.range fun w : A.range => ‖y - w‖) := ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  rw [← A.norm_eq_iInf_range_iff_adjoint_apply_eq_zero y x]; rw [le_antisymm_iff]; rw [and_iff_left (ciInf_le hb ⟨A x]; rw [x]; rw [rfl⟩)]; rw [le_ciInf_iff hb]
  simp

omit [CompleteSpace E] in
/--
theorem `ker_le_ker_iff_range_le_range` / 定理 `ker_le_ker_iff_range_le_range`

English:
theorem ker_le_ker_iff_range_le_range
  statement: [FiniteDimensional 𝕜 E] {T U : E ->L[𝕜] E}
  proof: by
  refine ⟨fun h => ?_, LinearMap.ker_le_ker_of_range hT hU⟩
  have := FiniteDimensional.complete 𝕜 E
  simpa [orthogonal_ker, hT, hU] using Submodule.orthogonal_le h

中文:
定理 ker_le_ker_iff_range_le_range
  结论: [有限维 𝕜 E] {T U : E ->L[𝕜] E}
  证明: by
  refine ⟨fun h => ?_, LinearMap.ker_le_ker_of_range hT hU⟩
  have := FiniteDimensional.complete 𝕜 E
  simpa [orthogonal_ker, hT, hU] using Submodule.orthogonal_le h

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, LinearMap, LinearMap.ker_le_ker_of_range, Submodule, Submodule.orthogonal_le, complete, ker_le_ker_of_range, orthogonal_ker, orthogonal_le
-/
theorem ker_le_ker_iff_range_le_range [FiniteDimensional 𝕜 E] {T U : E ->L[𝕜] E}
    (hT : T.IsSymmetric) (hU : U.IsSymmetric) :
    U.ker <= T.ker ↔ T.range <= U.range := by
  refine ⟨fun h => ?_, LinearMap.ker_le_ker_of_range hT hU⟩
  have := FiniteDimensional.complete 𝕜 E
  simpa [orthogonal_ker, hT, hU] using Submodule.orthogonal_le h

/--
theorem `ker_adjoint_comp_self` / 定理 `ker_adjoint_comp_self`

English:
theorem ker_adjoint_comp_self
  given: (T : E ->L[𝕜] F)
  statement: (T† ∘L T).ker = T.ker
  proof: by
  refine le_antisymm (fun _ _ => ?_) fun _ _ => by simp_all
  rw [LinearMap.mem_ker]; rw [← inner_self_eq_zero (𝕜 := 𝕜)]; rw [coe_coe]; rw [← adjoint_inner_left]
  simp_all

中文:
定理 ker_adjoint_comp_self
  条件: (T : E ->L[𝕜] F)
  结论: (T† ∘L T).ker = T.ker
  证明: by
  refine le_antisymm (fun _ _ => ?_) fun _ _ => by simp_all
  rw [LinearMap.mem_ker]; rw [← inner_self_eq_zero (𝕜 := 𝕜)]; rw [coe_coe]; rw [← adjoint_inner_left]
  simp_all

Depends on / 依赖: LinearMap, LinearMap.mem_ker, adjoint_inner_left, coe_coe, inner_self_eq_zero, le_antisymm, mem_ker
-/
theorem ker_adjoint_comp_self (T : E ->L[𝕜] F) : (T† ∘L T).ker = T.ker := by
  refine le_antisymm (fun _ _ => ?_) fun _ _ => by simp_all
  rw [LinearMap.mem_ker]; rw [← inner_self_eq_zero (𝕜 := 𝕜)]; rw [coe_coe]; rw [← adjoint_inner_left]
  simp_all

/--
theorem `ker_self_comp_adjoint` / 定理 `ker_self_comp_adjoint`

English:
theorem ker_self_comp_adjoint
  given: (T : E ->L[𝕜] F)
  statement: (T ∘L T†).ker = T†.ker
  proof: by
  simpa using T†.ker_adjoint_comp_self

中文:
定理 ker_self_comp_adjoint
  条件: (T : E ->L[𝕜] F)
  结论: (T ∘L T†).ker = T†.ker
  证明: by
  simpa using T†.ker_adjoint_comp_self

Depends on / 依赖: ker_adjoint_comp_self
-/
theorem ker_self_comp_adjoint (T : E ->L[𝕜] F) : (T ∘L T†).ker = T†.ker := by
  simpa using T†.ker_adjoint_comp_self

/--
lemma `adjoint_comp_self_injective_iff` / 引理 `adjoint_comp_self_injective_iff`

English:
lemma adjoint_comp_self_injective_iff
  given: (T : E ->L[𝕜] F)
  proof: by
  rw [← coe_comp]; rw [← coe_coe]; rw [← LinearMap.ker_eq_bot]; rw [← coe_coe]; rw [← LinearMap.ker_eq_bot]; rw [ker_adjoint_comp_self]

中文:
引理 adjoint_comp_self_injective_iff
  条件: (T : E ->L[𝕜] F)
  证明: by
  rw [← coe_comp]; rw [← coe_coe]; rw [← LinearMap.ker_eq_bot]; rw [← coe_coe]; rw [← LinearMap.ker_eq_bot]; rw [ker_adjoint_comp_self]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, coe_coe, coe_comp, ker_adjoint_comp_self, ker_eq_bot
-/
lemma adjoint_comp_self_injective_iff (T : E ->L[𝕜] F) :
    Function.Injective (T† ∘ T) ↔ Function.Injective T := by
  rw [← coe_comp]; rw [← coe_coe]; rw [← LinearMap.ker_eq_bot]; rw [← coe_coe]; rw [← LinearMap.ker_eq_bot]; rw [ker_adjoint_comp_self]

/--
lemma `self_comp_adjoint_injective_iff` / 引理 `self_comp_adjoint_injective_iff`

English:
lemma self_comp_adjoint_injective_iff
  given: (T : E ->L[𝕜] F)
  proof: by
  simpa using T†.adjoint_comp_self_injective_iff

中文:
引理 self_comp_adjoint_injective_iff
  条件: (T : E ->L[𝕜] F)
  证明: by
  simpa using T†.adjoint_comp_self_injective_iff

Depends on / 依赖: adjoint_comp_self_injective_iff
-/
lemma self_comp_adjoint_injective_iff (T : E ->L[𝕜] F) :
    Function.Injective (T ∘ T†) ↔ Function.Injective (T†) := by
  simpa using T†.adjoint_comp_self_injective_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (E ->L[𝕜] E)
  body: ⟨adjoint⟩

中文:
实例 :
  签名: 对合 (E ->L[𝕜] E)
  定义体: ⟨adjoint⟩

Depends on / 依赖: adjoint
-/
instance : Star (E ->L[𝕜] E) :=
  ⟨adjoint⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar (E ->L[𝕜] E)
  body: ⟨adjoint_adjoint⟩

中文:
实例 :
  签名: InvolutiveStar (E ->L[𝕜] E)
  定义体: ⟨adjoint_adjoint⟩

Depends on / 依赖: adjoint_adjoint
-/
instance : InvolutiveStar (E ->L[𝕜] E) :=
  ⟨adjoint_adjoint⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (E ->L[𝕜] E)
  body: ⟨adjoint_comp⟩

中文:
实例 :
  签名: StarMul (E ->L[𝕜] E)
  定义体: ⟨adjoint_comp⟩

Depends on / 依赖: adjoint_comp
-/
instance : StarMul (E ->L[𝕜] E) :=
  ⟨adjoint_comp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (E ->L[𝕜] E)
  body: ⟨map_add adjoint⟩

中文:
实例 :
  签名: 对合环 (E ->L[𝕜] E)
  定义体: ⟨map_add adjoint⟩

Depends on / 依赖: adjoint, map_add
-/
instance : StarRing (E ->L[𝕜] E) :=
  ⟨map_add adjoint⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule 𝕜 (E ->L[𝕜] E)
  body: ⟨map_smulₛₗ adjoint⟩

中文:
实例 :
  签名: 对合模 𝕜 (E ->L[𝕜] E)
  定义体: ⟨map_smulₛₗ adjoint⟩

Depends on / 依赖: adjoint
-/
instance : StarModule 𝕜 (E ->L[𝕜] E) :=
  ⟨map_smulₛₗ adjoint⟩

/--
theorem `star_eq_adjoint` / 定理 `star_eq_adjoint`

English:
theorem star_eq_adjoint
  given: (A : E ->L[𝕜] E)
  statement: star A = A†
  proof: rfl

中文:
定理 star_eq_adjoint
  条件: (A : E ->L[𝕜] E)
  结论: star A = A†
  证明: rfl
-/
theorem star_eq_adjoint (A : E ->L[𝕜] E) : star A = A† :=
  rfl

/--
theorem `isSelfAdjoint_iff'` / 定理 `isSelfAdjoint_iff'`

English:
theorem isSelfAdjoint_iff'
  given: {A : E ->L[𝕜] E}
  statement: IsSelfAdjoint A ↔ A† = A
  proof: Iff.rfl

中文:
定理 isSelfAdjoint_iff'
  条件: {A : E ->L[𝕜] E}
  结论: IsSelfAdjoint A ↔ A† = A
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isSelfAdjoint_iff' {A : E ->L[𝕜] E} : IsSelfAdjoint A ↔ A† = A :=
  Iff.rfl

/--
lemma `id_mem_unitary` / 引理 `id_mem_unitary`

English:
lemma id_mem_unitary
  statement: .id 𝕜 E in unitary (E ->L[𝕜] E)
  proof: one_mem _

中文:
引理 id_mem_unitary
  结论: .id 𝕜 E in unitary (E ->L[𝕜] E)
  证明: one_mem _
-/
@[simp] lemma id_mem_unitary : .id 𝕜 E in unitary (E ->L[𝕜] E) := one_mem _

/--
theorem `norm_adjoint_comp_self` / 定理 `norm_adjoint_comp_self`

English:
theorem norm_adjoint_comp_self
  given: (A : E ->L[𝕜] F)
  proof: by
  refine le_antisymm ?_ ?_
  · calc
      ‖A† ∘L A‖ <= ‖A†‖ * ‖A‖ := opNorm_comp_le _ _
      _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have :=
      calc
        re ⟪(A† ∘L A) x, x⟫ <= ‖(A† ∘L A) x‖ * ‖x‖ := re_inner_le_norm _ _
        _ <= ‖A† ∘L A‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
    calc
      ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
      _ <= √(‖A† ∘L A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
      _ = √‖A† ∘L A‖ * ‖x‖ := by
        simp_rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]

中文:
定理 norm_adjoint_comp_self
  条件: (A : E ->L[𝕜] F)
  证明: by
  refine le_antisymm ?_ ?_
  · calc
      ‖A† ∘L A‖ <= ‖A†‖ * ‖A‖ := opNorm_comp_le _ _
      _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have :=
      calc
        re ⟪(A† ∘L A) x, x⟫ <= ‖(A† ∘L A) x‖ * ‖x‖ := re_inner_le_norm _ _
        _ <= ‖A† ∘L A‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
    calc
      ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
      _ <= √(‖A† ∘L A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
      _ = √‖A† ∘L A‖ * ‖x‖ := by
        simp_rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, Real.sqrt_le_sqrt_iff, Real.sqrt_nonneg, Real.sqrt_sq, apply_norm_eq_sqrt_inner_adjoint_left, le_antisymm, le_opNorm, norm_map, norm_nonneg, opNorm_comp_le, opNorm_le_bound, re_inner_le_norm, sqrt_le_sqrt_iff, sqrt_nonneg, sqrt_sq
-/
theorem norm_adjoint_comp_self (A : E ->L[𝕜] F) :
    ‖A† ∘L A‖ = ‖A‖ * ‖A‖ := by
  refine le_antisymm ?_ ?_
  · calc
      ‖A† ∘L A‖ <= ‖A†‖ * ‖A‖ := opNorm_comp_le _ _
      _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have :=
      calc
        re ⟪(A† ∘L A) x, x⟫ <= ‖(A† ∘L A) x‖ * ‖x‖ := re_inner_le_norm _ _
        _ <= ‖A† ∘L A‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
    calc
      ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
      _ <= √(‖A† ∘L A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
      _ = √‖A† ∘L A‖ * ‖x‖ := by
        simp_rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]

/--
theorem `adjoint_comp_self_eq_zero_iff` / 定理 `adjoint_comp_self_eq_zero_iff`

English:
theorem adjoint_comp_self_eq_zero_iff
  given: {A : E ->L[𝕜] F}
  proof: by rw [← norm_eq_zero]; simp [norm_adjoint_comp_self]

中文:
定理 adjoint_comp_self_eq_zero_iff
  条件: {A : E ->L[𝕜] F}
  证明: by rw [← norm_eq_zero]; simp [norm_adjoint_comp_self]
-/
@[simp] theorem adjoint_comp_self_eq_zero_iff {A : E ->L[𝕜] F} :
    adjoint A ∘L A = 0 ↔ A = 0 := by rw [← norm_eq_zero]; simp [norm_adjoint_comp_self]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CStarRing (E ->L[𝕜] E)
  body: le_of_eq Eq.symm norm_adjoint_comp_self x

中文:
实例 :
  签名: CStar环 (E ->L[𝕜] E)
  定义体: le_of_eq Eq.symm norm_adjoint_comp_self x

Depends on / 依赖: Eq.symm, le_of_eq, norm_adjoint_comp_self
-/
instance : CStarRing (E ->L[𝕜] E) where
norm_mul_self_le x := le_of_eq Eq.symm norm_adjoint_comp_self x

/--
theorem `isAdjointPair_inner` / 定理 `isAdjointPair_inner`

English:
theorem isAdjointPair_inner
  given: (A : E ->L[𝕜] F)
  proof: by
  intro x y
  simp [adjoint_inner_left]

中文:
定理 isAdjointPair_inner
  条件: (A : E ->L[𝕜] F)
  证明: by
  intro x y
  simp [adjoint_inner_left]
-/
theorem isAdjointPair_inner (A : E ->L[𝕜] F) :
    LinearMap.IsAdjointPair (LinearMap.flip (innerₛₗ 𝕜 (E := E)))
      (innerₛₗ 𝕜 (E := F)).flip A (A†) := by
  intro x y
  simp [adjoint_inner_left]

/--
theorem `adjoint_innerSL_apply` / 定理 `adjoint_innerSL_apply`

English:
theorem adjoint_innerSL_apply
  given: (x : E)
  proof: ext_ring ext_inner_left 𝕜 fun _ => by simp [adjoint_inner_right]

中文:
定理 adjoint_innerSL_apply
  条件: (x : E)
  证明: ext_ring ext_inner_left 𝕜 fun _ => by simp [adjoint_inner_right]

Depends on / 依赖: adjoint_inner_right, ext_inner_left, ext_ring
-/
theorem adjoint_innerSL_apply (x : E) :
    adjoint (innerSL 𝕜 x) = toSpanSingleton 𝕜 x :=
ext_ring ext_inner_left 𝕜 fun _ => by simp [adjoint_inner_right]

/--
theorem `adjoint_toSpanSingleton` / 定理 `adjoint_toSpanSingleton`

English:
theorem adjoint_toSpanSingleton
  given: (x : E)
  proof: by
  simp [← adjoint_innerSL_apply]

中文:
定理 adjoint_toSpanSingleton
  条件: (x : E)
  证明: by
  simp [← adjoint_innerSL_apply]

Depends on / 依赖: adjoint_innerSL_apply
-/
theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 x) = innerSL 𝕜 x := by
  simp [← adjoint_innerSL_apply]

/--
theorem `innerSL_apply_comp` / 定理 `innerSL_apply_comp`

English:
theorem innerSL_apply_comp
  given: (x : F) (f : E ->L[𝕜] F)
  proof: by
  ext; simp [adjoint_inner_left]

omit [CompleteSpace E] in

中文:
定理 innerSL_apply_comp
  条件: (x : F) (f : E ->L[𝕜] F)
  证明: by
  ext; simp [adjoint_inner_left]

omit [CompleteSpace E] in

Depends on / 依赖: adjoint_inner_left
-/
theorem innerSL_apply_comp (x : F) (f : E ->L[𝕜] F) :
    innerSL 𝕜 x ∘L f = innerSL 𝕜 (adjoint f x) := by
  ext; simp [adjoint_inner_left]

omit [CompleteSpace E] in
/--
theorem `innerSL_apply_comp_of_isSymmetric` / 定理 `innerSL_apply_comp_of_isSymmetric`

English:
theorem innerSL_apply_comp_of_isSymmetric
  given: (x : E) {f : E ->L[𝕜] E} (hf : f.IsSymmetric)
  proof: by
  ext; simp [hf]

中文:
定理 innerSL_apply_comp_of_isSymmetric
  条件: (x : E) {f : E ->L[𝕜] E} (hf : f.IsSymmetric)
  证明: by
  ext; simp [hf]
-/
theorem innerSL_apply_comp_of_isSymmetric (x : E) {f : E ->L[𝕜] E} (hf : f.IsSymmetric) :
    innerSL 𝕜 x ∘L f = innerSL 𝕜 (f x) := by
  ext; simp [hf]

/--
lemma `_root_.InnerProductSpace.adjoint_rankOne` / 引理 `_root_.InnerProductSpace.adjoint_rankOne`

English:
lemma _root_.InnerProductSpace.adjoint_rankOne
  given: (x : E) (y : F)
  proof: by
  simp [rankOne_def', adjoint_comp, ← adjoint_innerSL_apply]

中文:
引理 _root_.内积空间.adjoint_rankOne
  条件: (x : E) (y : F)
  证明: by
  simp [rankOne_def', adjoint_comp, ← adjoint_innerSL_apply]
-/
@[simp] lemma _root_.InnerProductSpace.adjoint_rankOne (x : E) (y : F) :
    adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x := by
  simp [rankOne_def', adjoint_comp, ← adjoint_innerSL_apply]

/--
lemma `_root_.InnerProductSpace.rankOne_comp` / 引理 `_root_.InnerProductSpace.rankOne_comp`

English:
lemma _root_.InnerProductSpace.rankOne_comp
  statement: {E G : Type*} [SeminormedAddCommGroup E]
  proof: by
  simp_rw [rankOne_def', comp_assoc, innerSL_apply_comp]

中文:
引理 _root_.内积空间.rankOne_comp
  结论: {E G : 类型} [SeminormedAddComm群 E]
  证明: by
  simp_rw [rankOne_def', comp_assoc, innerSL_apply_comp]

Depends on / 依赖: comp_assoc, innerSL_apply_comp, rankOne_def, simp_rw
-/
lemma _root_.InnerProductSpace.rankOne_comp {E G : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (x : E) (y : F) (f : G ->L[𝕜] F) :
    rankOne 𝕜 x y ∘L f = rankOne 𝕜 x (adjoint f y) := by
  simp_rw [rankOne_def', comp_assoc, innerSL_apply_comp]

end

end ContinuousLinearMap

@[expose] public section

/-! ### Self-adjoint operators -/


namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/--
theorem `adjoint_eq` / 定理 `adjoint_eq`

English:
theorem adjoint_eq
  given: {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A)
  statement: A.adjoint = A
  proof: hA

中文:
定理 adjoint_eq
  条件: {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A)
  结论: A.adjoint = A
  证明: hA
-/
theorem adjoint_eq {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A) : A.adjoint = A :=
  hA

/--
theorem `isSymmetric` / 定理 `isSymmetric`

English:
theorem isSymmetric
  given: {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A)
  statement: (A : E ->ₗ[𝕜] E).IsSymmetric
  proof: by
  intro x y
  rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]

中文:
定理 isSymmetric
  条件: {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A)
  结论: (A : E ->ₗ[𝕜] E).IsSymmetric
  证明: by
  intro x y
  rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]

Depends on / 依赖: A.adjoint_inner_right, adjoint_eq, adjoint_inner_right, hA.adjoint_eq, rw_mod_cast
-/
theorem isSymmetric {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E ->ₗ[𝕜] E).IsSymmetric := by
  intro x y
  rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]

/--
theorem `conj_adjoint` / 定理 `conj_adjoint`

English:
theorem conj_adjoint
  given: {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : E ->L[𝕜] F)
  proof: by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

中文:
定理 conj_adjoint
  条件: {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : E ->L[𝕜] F)
  证明: by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, adjoint_adjoint, adjoint_comp, comp_assoc, isSelfAdjoint_iff
-/
theorem conj_adjoint {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : E ->L[𝕜] F) :
    IsSelfAdjoint (S ∘L T ∘L S.adjoint) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

/--
theorem `adjoint_conj` / 定理 `adjoint_conj`

English:
theorem adjoint_conj
  given: {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : F ->L[𝕜] E)
  proof: by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

中文:
定理 adjoint_conj
  条件: {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : F ->L[𝕜] E)
  证明: by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, adjoint_adjoint, adjoint_comp, comp_assoc, isSelfAdjoint_iff
-/
theorem adjoint_conj {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : F ->L[𝕜] E) :
    IsSelfAdjoint (S.adjoint ∘L T ∘L S) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

/--
theorem `_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` / 定理 `_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`

English:
theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
  given: {A : E ->L[𝕜] E}
  proof: ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩

中文:
定理 _root_.连续线性映射.isSelfAdjoint_iff_isSymmetric
  条件: {A : E ->L[𝕜] E}
  证明: ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩

Depends on / 依赖: A.adjoint_inner_left, adjoint_inner_left, ext_inner_right, hA.isSymmetric, isSymmetric
-/
theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric {A : E ->L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E ->ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩

/--
theorem `_root_.LinearMap.IsSymmetric.isSelfAdjoint` / 定理 `_root_.LinearMap.IsSymmetric.isSelfAdjoint`

English:
theorem _root_.LinearMap.IsSymmetric.isSelfAdjoint
  statement: {A : E ->L[𝕜] E}
  proof: by
  rwa [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA

中文:
定理 _root_.线性映射.IsSymmetric.isSelfAdjoint
  结论: {A : E ->L[𝕜] E}
  证明: by
  rwa [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSelfAdjoint_iff_isSymmetric
-/
theorem _root_.LinearMap.IsSymmetric.isSelfAdjoint {A : E ->L[𝕜] E}
    (hA : (A : E ->ₗ[𝕜] E).IsSymmetric) : IsSelfAdjoint A := by
  rwa [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA

/-- The orthogonal projection is self-adjoint. -/
@[simp]
/--
theorem `_root_.isSelfAdjoint_starProjection` / 定理 `_root_.isSelfAdjoint_starProjection`

English:
theorem _root_.isSelfAdjoint_starProjection
  proof: U.starProjection_isSymmetric.isSelfAdjoint

中文:
定理 _root_.isSelfAdjoint_starProjection
  证明: U.starProjection_isSymmetric.isSelfAdjoint

Depends on / 依赖: U.starProjection_isSymmetric.isSelfAdjoint, isSelfAdjoint, starProjection_isSymmetric
-/
theorem _root_.isSelfAdjoint_starProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint U.starProjection :=
  U.starProjection_isSymmetric.isSelfAdjoint

/--
theorem `conj_starProjection` / 定理 `conj_starProjection`

English:
theorem conj_starProjection
  statement: {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T)
  proof: by
  rw [← mul_def]; rw [← mul_def]; rw [← mul_assoc]
exact hT.conjugate_self isSelfAdjoint_starProjection U

中文:
定理 conj_starProjection
  结论: {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T)
  证明: by
  rw [← mul_def]; rw [← mul_def]; rw [← mul_assoc]
exact hT.conjugate_self isSelfAdjoint_starProjection U

Depends on / 依赖: conjugate_self, hT.conjugate_self, isSelfAdjoint_starProjection, mul_assoc, mul_def
-/
theorem conj_starProjection {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint (U.starProjection ∘L T ∘L U.starProjection) := by
  rw [← mul_def]; rw [← mul_def]; rw [← mul_assoc]
exact hT.conjugate_self isSelfAdjoint_starProjection U

end IsSelfAdjoint

namespace ContinuousLinearMap

variable {T : E ->L[𝕜] E} [CompleteSpace E]

/--
theorem `isStarNormal_iff_norm_eq_adjoint` / 定理 `isStarNormal_iff_norm_eq_adjoint`

English:
theorem isStarNormal_iff_norm_eq_adjoint
  proof: by
  rw [isStarNormal_iff]; rw [Commute]; rw [SemiconjBy]; rw [← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← coe_coe, toLinearMap_sub, ← LinearMap.ext_iff,
    toLinearMap_zero]
  have := star_eq_adjoint T ▸ toLinearMap_sub (star _ * T) _ ▸
    ((IsSelfAdjoint.star_mul_self T).sub (IsSelfAdjoint.mul_star_self T)).isSymmetric
  simp_rw [star_eq_adjoint, ← LinearMap.IsSymmetric.inner_map_self_eq_zero this,
    LinearMap.sub_apply, inner_sub_left, coe_coe, mul_apply_eq_comp, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← adjoint_inner_right T, inner_self_eq_norm_sq_to_K,
    sub_eq_zero, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast

中文:
定理 isStarNormal_iff_norm_eq_adjoint
  证明: by
  rw [isStarNormal_iff]; rw [Commute]; rw [SemiconjBy]; rw [← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← coe_coe, toLinearMap_sub, ← LinearMap.ext_iff,
    toLinearMap_zero]
  have := star_eq_adjoint T ▸ toLinearMap_sub (star _ * T) _ ▸
    ((IsSelfAdjoint.star_mul_self T).sub (IsSelfAdjoint.mul_star_self T)).isSymmetric
  simp_rw [star_eq_adjoint, ← LinearMap.IsSymmetric.inner_map_self_eq_zero this,
    LinearMap.sub_apply, inner_sub_left, coe_coe, mul_apply_eq_comp, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← adjoint_inner_right T, inner_self_eq_norm_sq_to_K,
    sub_eq_zero, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast

Depends on / 依赖: Commute, ContinuousLinearMap, ContinuousLinearMap.ext_iff, IsSelfAdjoint, IsSelfAdjoint.mul_star_self, IsSelfAdjoint.star_mul_self, IsSymmetric, LinearMap, LinearMap.IsSymmetric.inner_map_self_eq_zero, LinearMap.ext_iff, LinearMap.sub_apply, SemiconjBy, adjoint_inner_left, coe_coe, ext_iff, inner_map_self_eq_zero, inner_self_e, inner_sub_left, isStarNormal_iff, isSymmetric
-/
theorem isStarNormal_iff_norm_eq_adjoint :
    IsStarNormal T ↔ forall v : E, ‖T v‖ = ‖adjoint T v‖ := by
  rw [isStarNormal_iff]; rw [Commute]; rw [SemiconjBy]; rw [← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← coe_coe, toLinearMap_sub, ← LinearMap.ext_iff,
    toLinearMap_zero]
  have := star_eq_adjoint T ▸ toLinearMap_sub (star _ * T) _ ▸
    ((IsSelfAdjoint.star_mul_self T).sub (IsSelfAdjoint.mul_star_self T)).isSymmetric
  simp_rw [star_eq_adjoint, ← LinearMap.IsSymmetric.inner_map_self_eq_zero this,
    LinearMap.sub_apply, inner_sub_left, coe_coe, mul_apply_eq_comp, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← adjoint_inner_right T, inner_self_eq_norm_sq_to_K,
    sub_eq_zero, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast

/--
lemma `IsStarNormal.adjoint_apply_eq_zero_iff` / 引理 `IsStarNormal.adjoint_apply_eq_zero_iff`

English:
lemma IsStarNormal.adjoint_apply_eq_zero_iff
  given: (hT : IsStarNormal T) (x : E)
  proof: by
  simp_rw [← norm_eq_zero (E := E), ← isStarNormal_iff_norm_eq_adjoint.mp hT]

中文:
引理 是StarNormal.adjoint_apply_eq_zero_iff
  条件: (hT : 是StarNormal T) (x : E)
  证明: by
  simp_rw [← norm_eq_zero (E := E), ← isStarNormal_iff_norm_eq_adjoint.mp hT]

Depends on / 依赖: isStarNormal_iff_norm_eq_adjoint, isStarNormal_iff_norm_eq_adjoint.mp, norm_eq_zero, simp_rw
-/
lemma IsStarNormal.adjoint_apply_eq_zero_iff (hT : IsStarNormal T) (x : E) :
    adjoint T x = 0 ↔ T x = 0 := by
  simp_rw [← norm_eq_zero (E := E), ← isStarNormal_iff_norm_eq_adjoint.mp hT]

open ContinuousLinearMap

/--
theorem `IsStarNormal.ker_adjoint_eq_ker` / 定理 `IsStarNormal.ker_adjoint_eq_ker`

English:
theorem IsStarNormal.ker_adjoint_eq_ker
  given: (hT : IsStarNormal T)
  proof: Submodule.ext hT.adjoint_apply_eq_zero_iff

中文:
定理 是StarNormal.ker_adjoint_eq_ker
  条件: (hT : 是StarNormal T)
  证明: Submodule.ext hT.adjoint_apply_eq_zero_iff

Depends on / 依赖: Submodule, Submodule.ext, adjoint_apply_eq_zero_iff, hT.adjoint_apply_eq_zero_iff
-/
theorem IsStarNormal.ker_adjoint_eq_ker (hT : IsStarNormal T) :
    (adjoint T).ker = T.ker :=
  Submodule.ext hT.adjoint_apply_eq_zero_iff

/--
theorem `IsStarNormal.orthogonal_range` / 定理 `IsStarNormal.orthogonal_range`

English:
theorem IsStarNormal.orthogonal_range
  given: (hT : IsStarNormal T)
  statement: T.rangeᗮ = T.ker
  proof: T.orthogonal_range ▸ hT.ker_adjoint_eq_ker

中文:
定理 是StarNormal.orthogonal_range
  条件: (hT : 是StarNormal T)
  结论: T.rangeᗮ = T.ker
  证明: T.orthogonal_range ▸ hT.ker_adjoint_eq_ker

Depends on / 依赖: T.orthogonal_range, hT.ker_adjoint_eq_ker, ker_adjoint_eq_ker, orthogonal_range
-/
theorem IsStarNormal.orthogonal_range (hT : IsStarNormal T) : T.rangeᗮ = T.ker :=
  T.orthogonal_range ▸ hT.ker_adjoint_eq_ker

set_option backward.isDefEq.respectTransparency false in
/- TODO: As we have a more general result of this for elements in non-unital C⋆-algebras
(see `Mathlib/Analysis/CStarAlgebra/Projection.lean`), we will want to simplify the proof
by using the complexification of an inner product space over `𝕜`. -/
/--
theorem `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal` / 定理 `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`

English:
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal
  given: (hT : IsIdempotentElem T)
  proof: by
  refine ⟨fun h => by rw [isStarNormal_iff, h], fun h => ?_⟩
  suffices T = star T * T from this ▸ IsSelfAdjoint.star_mul_self _
  rw [← sub_eq_zero]; rw [ContinuousLinearMap.ext_iff]
  simp_rw [zero_apply, ← norm_eq_zero (E := E)]
  have :=
    calc (forall x : E, ‖(T - star T * T) x‖ = 0) ↔ forall x, ‖(adjoint (1 - T)) (T x)‖ = 0 := by
          simp [star_eq_adjoint, one_def]
      _ ↔ forall x, ‖(1 - T) (T x)‖ = 0 := by
          simp only [isStarNormal_iff_norm_eq_adjoint.mp h.one_sub]
      _ ↔ forall x, ‖(T - T * T) x‖ = 0 := by simp
      _ ↔ T - T * T = 0 := by simp only [norm_eq_zero, ContinuousLinearMap.ext_iff, zero_apply]
      _ ↔ IsIdempotentElem T := by simp only [sub_eq_zero, IsIdempotentElem, eq_comm]
  exact this.mpr hT

中文:
定理 IsIdempotentElem.isSelfAdjoint_iff_isStarNormal
  条件: (hT : IsIdempotentElem T)
  证明: by
  refine ⟨fun h => by rw [isStarNormal_iff, h], fun h => ?_⟩
  suffices T = star T * T from this ▸ IsSelfAdjoint.star_mul_self _
  rw [← sub_eq_zero]; rw [ContinuousLinearMap.ext_iff]
  simp_rw [zero_apply, ← norm_eq_zero (E := E)]
  have :=
    calc (forall x : E, ‖(T - star T * T) x‖ = 0) ↔ forall x, ‖(adjoint (1 - T)) (T x)‖ = 0 := by
          simp [star_eq_adjoint, one_def]
      _ ↔ forall x, ‖(1 - T) (T x)‖ = 0 := by
          simp only [isStarNormal_iff_norm_eq_adjoint.mp h.one_sub]
      _ ↔ forall x, ‖(T - T * T) x‖ = 0 := by simp
      _ ↔ T - T * T = 0 := by simp only [norm_eq_zero, ContinuousLinearMap.ext_iff, zero_apply]
      _ ↔ IsIdempotentElem T := by simp only [sub_eq_zero, IsIdempotentElem, eq_comm]
  exact this.mpr hT
-/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal (hT : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ IsStarNormal T := by
  refine ⟨fun h => by rw [isStarNormal_iff, h], fun h => ?_⟩
  suffices T = star T * T from this ▸ IsSelfAdjoint.star_mul_self _
  rw [← sub_eq_zero]; rw [ContinuousLinearMap.ext_iff]
  simp_rw [zero_apply, ← norm_eq_zero (E := E)]
  have :=
    calc (forall x : E, ‖(T - star T * T) x‖ = 0) ↔ forall x, ‖(adjoint (1 - T)) (T x)‖ = 0 := by
          simp [star_eq_adjoint, one_def]
      _ ↔ forall x, ‖(1 - T) (T x)‖ = 0 := by
          simp only [isStarNormal_iff_norm_eq_adjoint.mp h.one_sub]
      _ ↔ forall x, ‖(T - T * T) x‖ = 0 := by simp
      _ ↔ T - T * T = 0 := by simp only [norm_eq_zero, ContinuousLinearMap.ext_iff, zero_apply]
      _ ↔ IsIdempotentElem T := by simp only [sub_eq_zero, IsIdempotentElem, eq_comm]
  exact this.mpr hT

/--
theorem `isStarProjection_iff_isIdempotentElem_and_isStarNormal` / 定理 `isStarProjection_iff_isIdempotentElem_and_isStarNormal`

English:
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal
  proof: by
  rw [isStarProjection_iff]; rw [and_congr_right_iff]
  exact fun h => IsIdempotentElem.isSelfAdjoint_iff_isStarNormal h

中文:
定理 isStarProjection_iff_isIdempotentElem_and_isStarNormal
  证明: by
  rw [isStarProjection_iff]; rw [and_congr_right_iff]
  exact fun h => IsIdempotentElem.isSelfAdjoint_iff_isStarNormal h

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.isSelfAdjoint_iff_isStarNormal, and_congr_right_iff, isSelfAdjoint_iff_isStarNormal, isStarProjection_iff
-/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal :
    IsStarProjection T ↔ IsIdempotentElem T ∧ IsStarNormal T := by
  rw [isStarProjection_iff]; rw [and_congr_right_iff]
  exact fun h => IsIdempotentElem.isSelfAdjoint_iff_isStarNormal h

/--
theorem `isStarProjection_iff_isSymmetricProjection` / 定理 `isStarProjection_iff_isSymmetricProjection`

English:
theorem isStarProjection_iff_isSymmetricProjection
  proof: by
  simp [isStarProjection_iff, LinearMap.isSymmetricProjection_iff,
    isSelfAdjoint_iff_isSymmetric, IsIdempotentElem, End.mul_eq_comp, ← toLinearMap_comp, mul_def]

alias ⟨IsStarProjection.isSymmetricProjection, LinearMap.IsSymmetricProjection.isStarProjection⟩ :=
  isStarProjection_iff_isSymmetricProjection

中文:
定理 isStarProjection_iff_isSymmetricProjection
  证明: by
  simp [isStarProjection_iff, LinearMap.isSymmetricProjection_iff,
    isSelfAdjoint_iff_isSymmetric, IsIdempotentElem, End.mul_eq_comp, ← toLinearMap_comp, mul_def]

alias ⟨IsStarProjection.isSymmetricProjection, LinearMap.IsSymmetricProjection.isStarProjection⟩ :=
  isStarProjection_iff_isSymmetricProjection

Depends on / 依赖: End.mul_eq_comp, IsIdempotentElem, LinearMap, LinearMap.isSymmetricProjection_iff, isSelfAdjoint_iff_isSymmetric, isStarProjection_iff, isSymmetricProjection_iff, mul_def, mul_eq_comp, toLinearMap_comp
-/
theorem isStarProjection_iff_isSymmetricProjection :
    IsStarProjection T ↔ T.IsSymmetricProjection := by
  simp [isStarProjection_iff, LinearMap.isSymmetricProjection_iff,
    isSelfAdjoint_iff_isSymmetric, IsIdempotentElem, End.mul_eq_comp, ← toLinearMap_comp, mul_def]

alias ⟨IsStarProjection.isSymmetricProjection, LinearMap.IsSymmetricProjection.isStarProjection⟩ :=
  isStarProjection_iff_isSymmetricProjection

/--
theorem `IsStarProjection.ext_iff` / 定理 `IsStarProjection.ext_iff`

English:
theorem IsStarProjection.ext_iff
  statement: {S : E ->L[𝕜] E}
  proof: by
  simpa using hS.isSymmetricProjection.ext_iff hT.isSymmetricProjection

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

中文:
定理 是StarProjection.ext_iff
  结论: {S : E ->L[𝕜] E}
  证明: by
  simpa using hS.isSymmetricProjection.ext_iff hT.isSymmetricProjection

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

Depends on / 依赖: ext_iff, hS.isSymmetricProjection.ext_iff, hT.isSymmetricProjection, isSymmetricProjection
-/
theorem IsStarProjection.ext_iff {S : E ->L[𝕜] E}
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    S = T ↔ S.range = T.range := by
  simpa using hS.isSymmetricProjection.ext_iff hT.isSymmetricProjection

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

/--
theorem `_root_.InnerProductSpace.isStarProjection_rankOne_self` / 定理 `_root_.InnerProductSpace.isStarProjection_rankOne_self`

English:
theorem _root_.InnerProductSpace.isStarProjection_rankOne_self
  given: {x : E} (hx : ‖x‖ = 1)
  proof: (isSymmetricProjection_rankOne_self hx).isStarProjection

中文:
定理 _root_.内积空间.isStarProjection_rankOne_self
  条件: {x : E} (hx : ‖x‖ = 1)
  证明: (isSymmetricProjection_rankOne_self hx).isStarProjection

Depends on / 依赖: isStarProjection, isSymmetricProjection_rankOne_self
-/
theorem _root_.InnerProductSpace.isStarProjection_rankOne_self {x : E} (hx : ‖x‖ = 1) :
    IsStarProjection (rankOne 𝕜 x x) := (isSymmetricProjection_rankOne_self hx).isStarProjection

open Module End Submodule in
/--
theorem `orthogonal_mem_invtSubmodule` / 定理 `orthogonal_mem_invtSubmodule`

English:
theorem orthogonal_mem_invtSubmodule
  statement: {T : E ->L[𝕜] E} {U : Submodule 𝕜 E}
  proof: by
  simp only [mem_invtSubmodule_iff_forall_mem_of_mem, coe_coe, mem_orthogonal] at h ⊢
  grind [T.adjoint_inner_left]

中文:
定理 orthogonal_mem_invtSubmodule
  结论: {T : E ->L[𝕜] E} {U : 子模 𝕜 E}
  证明: by
  simp only [mem_invtSubmodule_iff_forall_mem_of_mem, coe_coe, mem_orthogonal] at h ⊢
  grind [T.adjoint_inner_left]

Depends on / 依赖: T.adjoint_inner_left, adjoint_inner_left, coe_coe, mem_invtSubmodule_iff_forall_mem_of_mem, mem_orthogonal
-/
theorem orthogonal_mem_invtSubmodule {T : E ->L[𝕜] E} {U : Submodule 𝕜 E}
    (h : U in invtSubmodule T.adjoint.toLinearMap) :
    Uᗮ in invtSubmodule T.toLinearMap := by
  simp only [mem_invtSubmodule_iff_forall_mem_of_mem, coe_coe, mem_orthogonal] at h ⊢
  grind [T.adjoint_inner_left]

open Module End in
/--
theorem `mem_invtSubmodule_adjoint_iff` / 定理 `mem_invtSubmodule_adjoint_iff`

English:
theorem mem_invtSubmodule_adjoint_iff
  statement: {T : E ->L[𝕜] E} {U : Submodule 𝕜 E}
  proof: orthogonal_mem_invtSubmodule
  mpr := by simpa using orthogonal_mem_invtSubmodule (T := T.adjoint) (U := Uᗮ)

中文:
定理 mem_invtSubmodule_adjoint_iff
  结论: {T : E ->L[𝕜] E} {U : 子模 𝕜 E}
  证明: orthogonal_mem_invtSubmodule
  mpr := by simpa using orthogonal_mem_invtSubmodule (T := T.adjoint) (U := Uᗮ)

Depends on / 依赖: orthogonal_mem_invtSubmodule
-/
theorem mem_invtSubmodule_adjoint_iff {T : E ->L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] :
    U in invtSubmodule T.adjoint.toLinearMap ↔ Uᗮ in invtSubmodule T.toLinearMap where
  mp := orthogonal_mem_invtSubmodule
  mpr := by simpa using orthogonal_mem_invtSubmodule (T := T.adjoint) (U := Uᗮ)

end ContinuousLinearMap

/-- `U.starProjection` is a star projection. -/
@[simp]
/--
theorem `isStarProjection_starProjection` / 定理 `isStarProjection_starProjection`

English:
theorem isStarProjection_starProjection
  statement: [CompleteSpace E] {U : Submodule 𝕜 E}
  proof: ⟨U.isIdempotentElem_starProjection, isSelfAdjoint_starProjection U⟩

中文:
定理 isStarProjection_starProjection
  结论: [完备空间 E] {U : 子模 𝕜 E}
  证明: ⟨U.isIdempotentElem_starProjection, isSelfAdjoint_starProjection U⟩

Depends on / 依赖: U.isIdempotentElem_starProjection, isIdempotentElem_starProjection, isSelfAdjoint_starProjection
-/
theorem isStarProjection_starProjection [CompleteSpace E] {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : IsStarProjection U.starProjection :=
  ⟨U.isIdempotentElem_starProjection, isSelfAdjoint_starProjection U⟩

open ContinuousLinearMap in
/--
theorem `isStarProjection_iff_eq_starProjection_range` / 定理 `isStarProjection_iff_eq_starProjection_range`

English:
theorem isStarProjection_iff_eq_starProjection_range
  given: [CompleteSpace E] {p : E ->L[𝕜] E}
  proof: by
  simp_rw [p.isStarProjection_iff_isSymmetricProjection.eq,
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, coe_inj]

中文:
定理 isStarProjection_iff_eq_starProjection_range
  条件: [完备空间 E] {p : E ->L[𝕜] E}
  证明: by
  simp_rw [p.isStarProjection_iff_isSymmetricProjection.eq,
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, coe_inj]

Depends on / 依赖: LinearMap, LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, coe_inj, isStarProjection_iff_isSymmetricProjection, isSymmetricProjection_iff_eq_coe_starProjection_range, p.isStarProjection_iff_isSymmetricProjection.eq, simp_rw
-/
theorem isStarProjection_iff_eq_starProjection_range [CompleteSpace E] {p : E ->L[𝕜] E} :
    IsStarProjection p ↔ exists (_ : p.range.HasOrthogonalProjection),
    p = p.range.starProjection := by
  simp_rw [p.isStarProjection_iff_isSymmetricProjection.eq,
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, coe_inj]

/--
lemma `isStarProjection_iff_eq_starProjection` / 引理 `isStarProjection_iff_eq_starProjection`

English:
lemma isStarProjection_iff_eq_starProjection
  given: [CompleteSpace E] {p : E ->L[𝕜] E}
  proof: ⟨fun h => ⟨p.range, isStarProjection_iff_eq_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; simp⟩

中文:
引理 isStarProjection_iff_eq_starProjection
  条件: [完备空间 E] {p : E ->L[𝕜] E}
  证明: ⟨fun h => ⟨p.range, isStarProjection_iff_eq_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; simp⟩

Depends on / 依赖: isStarProjection_iff_eq_starProjection_range, isStarProjection_iff_eq_starProjection_range.mp, p.range
-/
lemma isStarProjection_iff_eq_starProjection [CompleteSpace E] {p : E ->L[𝕜] E} :
    IsStarProjection p
      ↔ exists (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection), p = K.starProjection :=
  ⟨fun h => ⟨p.range, isStarProjection_iff_eq_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; simp⟩

namespace LinearMap

variable [CompleteSpace E]
variable {T : E ->ₗ[𝕜] E}

/--
Definition of `IsSymmetric.toSelfAdjoint` / `IsSymmetric.toSelfAdjoint` 的定义

English:
definition IsSymmetric.toSelfAdjoint
  signature: (hT : IsSymmetric T)
  body: ⟨⟨T, hT.continuous⟩, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT⟩

中文:
定义 IsSymmetric.toSelfAdjoint
  签名: (hT : IsSymmetric T)
  定义体: ⟨⟨T, hT.continuous⟩, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr, continuous, hT.continuous, isSelfAdjoint_iff_isSymmetric
-/
def IsSymmetric.toSelfAdjoint (hT : IsSymmetric T) : selfAdjoint (E ->L[𝕜] E) :=
  ⟨⟨T, hT.continuous⟩, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT⟩

/--
theorem `IsSymmetric.coe_toSelfAdjoint` / 定理 `IsSymmetric.coe_toSelfAdjoint`

English:
theorem IsSymmetric.coe_toSelfAdjoint
  given: (hT : IsSymmetric T)
  statement: (hT.toSelfAdjoint : E ->ₗ[𝕜] E) = T
  proof: rfl

中文:
定理 IsSymmetric.coe_toSelfAdjoint
  条件: (hT : IsSymmetric T)
  结论: (hT.toSelfAdjoint : E ->ₗ[𝕜] E) = T
  证明: rfl
-/
theorem IsSymmetric.coe_toSelfAdjoint (hT : IsSymmetric T) : (hT.toSelfAdjoint : E ->ₗ[𝕜] E) = T :=
  rfl

/--
theorem `IsSymmetric.toSelfAdjoint_apply` / 定理 `IsSymmetric.toSelfAdjoint_apply`

English:
theorem IsSymmetric.toSelfAdjoint_apply
  given: (hT : IsSymmetric T) {x : E}
  proof: rfl

中文:
定理 IsSymmetric.toSelfAdjoint_apply
  条件: (hT : IsSymmetric T) {x : E}
  证明: rfl
-/
theorem IsSymmetric.toSelfAdjoint_apply (hT : IsSymmetric T) {x : E} :
    (hT.toSelfAdjoint : E -> E) x = T x :=
  rfl

end LinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/--
Definition of `adjoint` / `adjoint` 的定义

English:
definition adjoint
  signature: : (E ->ₗ[𝕜] F) ≃ₗ⋆[𝕜] F ->ₗ[𝕜] E
  body: haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  /- Note: Instead of the two instances above, the following works:
    ```
      haveI := FiniteDimensional.complete 𝕜
      haveI := FiniteDimensional.complete 𝕜
    ```
    But removing one of the `have`s makes it fail. The reason is that `E` and `F` don't live
    in the same universe, so the first `have` can no longer be used for `F` after its universe
    metavariable has been assigned to that of `E`!
  -/
  ((LinearMap.toContinuousLinearMap : (E ->ₗ[𝕜] F) ≃ₗ[𝕜] E ->L[𝕜] F).trans
      ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm

中文:
定义 adjoint
  签名: : (E ->ₗ[𝕜] F) ≃ₗ⋆[𝕜] F ->ₗ[𝕜] E
  定义体: haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  /- Note: Instead of the two instances above, the following works:
    ```
      haveI := FiniteDimensional.complete 𝕜
      haveI := FiniteDimensional.complete 𝕜
    ```
    But removing one of the `have`s makes it fail. The reason is that `E` and `F` don't live
    in the same universe, so the first `have` can no longer be used for `F` after its universe
    metavariable has been assigned to that of `E`!
  -/
  ((LinearMap.toContinuousLinearMap : (E ->ₗ[𝕜] F) ≃ₗ[𝕜] E ->L[𝕜] F).trans
      ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
def adjoint : (E ->ₗ[𝕜] F) ≃ₗ⋆[𝕜] F ->ₗ[𝕜] E :=
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  /- Note: Instead of the two instances above, the following works:
    ```
      haveI := FiniteDimensional.complete 𝕜
      haveI := FiniteDimensional.complete 𝕜
    ```
    But removing one of the `have`s makes it fail. The reason is that `E` and `F` don't live
    in the same universe, so the first `have` can no longer be used for `F` after its universe
    metavariable has been assigned to that of `E`!
  -/
  ((LinearMap.toContinuousLinearMap : (E ->ₗ[𝕜] F) ≃ₗ[𝕜] E ->L[𝕜] F).trans
      ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm

/--
theorem `adjoint_toContinuousLinearMap` / 定理 `adjoint_toContinuousLinearMap`

English:
theorem adjoint_toContinuousLinearMap
  given: (A : E ->ₗ[𝕜] F)
  proof: FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl

中文:
定理 adjoint_toContinuousLinearMap
  条件: (A : E ->ₗ[𝕜] F)
  证明: FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem adjoint_toContinuousLinearMap (A : E ->ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl

/--
theorem `adjoint_eq_toCLM_adjoint` / 定理 `adjoint_eq_toCLM_adjoint`

English:
theorem adjoint_eq_toCLM_adjoint
  given: (A : E ->ₗ[𝕜] F)
  proof: FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl

中文:
定理 adjoint_eq_toCLM_adjoint
  条件: (A : E ->ₗ[𝕜] F)
  证明: FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem adjoint_eq_toCLM_adjoint (A : E ->ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl

/--
theorem `_root_.ContinuousLinearMap.adjoint_toLinearMap` / 定理 `_root_.ContinuousLinearMap.adjoint_toLinearMap`

English:
theorem _root_.ContinuousLinearMap.adjoint_toLinearMap
  given: (A : E ->L[𝕜] F)
  proof: FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.toLinearMap.adjoint = A.adjoint.toLinearMap :=
  rfl

中文:
定理 _root_.连续线性映射.adjoint_toLinearMap
  条件: (A : E ->L[𝕜] F)
  证明: FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.toLinearMap.adjoint = A.adjoint.toLinearMap :=
  rfl

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem _root_.ContinuousLinearMap.adjoint_toLinearMap (A : E ->L[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.toLinearMap.adjoint = A.adjoint.toLinearMap :=
  rfl

/--
theorem `adjoint_inner_left` / 定理 `adjoint_inner_left`

English:
theorem adjoint_inner_left
  given: (A : E ->ₗ[𝕜] F) (x : E) (y : F)
  statement: ⟪adjoint A y, x⟫ = ⟪y, A x⟫
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A]; rw [adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y

中文:
定理 adjoint_inner_left
  条件: (A : E ->ₗ[𝕜] F) (x : E) (y : F)
  结论: ⟪adjoint A y, x⟫ = ⟪y, A x⟫
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A]; rw [adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.adjoint_inner_left, FiniteDimensional, FiniteDimensional.complete, adjoint_eq_toCLM_adjoint, adjoint_inner_left, coe_toContinuousLinearMap, complete
-/
theorem adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A]; rw [adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y

/--
theorem `adjoint_inner_right` / 定理 `adjoint_inner_right`

English:
theorem adjoint_inner_right
  given: (A : E ->ₗ[𝕜] F) (x : E) (y : F)
  statement: ⟪x, adjoint A y⟫ = ⟪A x, y⟫
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A]; rw [adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y

中文:
定理 adjoint_inner_right
  条件: (A : E ->ₗ[𝕜] F) (x : E) (y : F)
  结论: ⟪x, adjoint A y⟫ = ⟪A x, y⟫
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A]; rw [adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.adjoint_inner_right, FiniteDimensional, FiniteDimensional.complete, adjoint_eq_toCLM_adjoint, adjoint_inner_right, coe_toContinuousLinearMap, complete
-/
theorem adjoint_inner_right (A : E ->ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A]; rw [adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y

/-- The adjoint is involutive. -/
@[simp]
/--
theorem `adjoint_adjoint` / 定理 `adjoint_adjoint`

English:
theorem adjoint_adjoint
  given: (A : E ->ₗ[𝕜] F)
  statement: A.adjoint.adjoint = A
  proof: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjoint_inner_right]; rw [adjoint_inner_left]

中文:
定理 adjoint_adjoint
  条件: (A : E ->ₗ[𝕜] F)
  结论: A.adjoint.adjoint = A
  证明: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjoint_inner_right]; rw [adjoint_inner_left]

Depends on / 依赖: adjoint_inner_left, adjoint_inner_right, ext_inner_left
-/
theorem adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.adjoint = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjoint_inner_right]; rw [adjoint_inner_left]

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
/--
theorem `adjoint_comp` / 定理 `adjoint_comp`

English:
theorem adjoint_comp
  given: (A : F ->ₗ[𝕜] G) (B : E ->ₗ[𝕜] F)
  proof: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]

中文:
定理 adjoint_comp
  条件: (A : F ->ₗ[𝕜] G) (B : E ->ₗ[𝕜] F)
  证明: by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, adjoint_inner_right, coe_comp, comp_apply, ext_inner_left
-/
theorem adjoint_comp (A : F ->ₗ[𝕜] G) (B : E ->ₗ[𝕜] F) :
    (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]

/--
theorem `eq_adjoint_iff` / 定理 `eq_adjoint_iff`

English:
theorem eq_adjoint_iff
  given: (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
  proof: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]

中文:
定理 eq_adjoint_iff
  条件: (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
  证明: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]

Depends on / 依赖: adjoint_inner_left, ext_inner_right
-/
theorem eq_adjoint_iff (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E) :
    A = B.adjoint ↔ forall x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]
/--
theorem `IsSymmetric.adjoint_eq` / 定理 `IsSymmetric.adjoint_eq`

English:
theorem IsSymmetric.adjoint_eq
  given: {A : E ->ₗ[𝕜] E} (hA : A.IsSymmetric)
  proof: by
  rwa [eq_comm, eq_adjoint_iff A A]

中文:
定理 IsSymmetric.adjoint_eq
  条件: {A : E ->ₗ[𝕜] E} (hA : A.IsSymmetric)
  证明: by
  rwa [eq_comm, eq_adjoint_iff A A]

Depends on / 依赖: eq_adjoint_iff, eq_comm
-/
theorem IsSymmetric.adjoint_eq {A : E ->ₗ[𝕜] E} (hA : A.IsSymmetric) :
    A.adjoint = A := by
  rwa [eq_comm, eq_adjoint_iff A A]

/--
lemma `adjoint_id` / 引理 `adjoint_id`

English:
lemma adjoint_id
  statement: (.id : E ->ₗ[𝕜] E).adjoint = .id
  proof: by simp

中文:
引理 adjoint_id
  结论: (.id : E ->ₗ[𝕜] E).adjoint = .id
  证明: by simp
-/
lemma adjoint_id : (.id : E ->ₗ[𝕜] E).adjoint = .id := by simp
/--
lemma `adjoint_one` / 引理 `adjoint_one`

English:
lemma adjoint_one
  statement: (1 : E ->ₗ[𝕜] E).adjoint = 1
  proof: by simp

中文:
引理 adjoint_one
  结论: (1 : E ->ₗ[𝕜] E).adjoint = 1
  证明: by simp
-/
lemma adjoint_one : (1 : E ->ₗ[𝕜] E).adjoint = 1 := by simp

/--
lemma `orthogonal_ker` / 引理 `orthogonal_ker`

English:
lemma orthogonal_ker
  given: (A : E ->ₗ[𝕜] F)
  statement: A.kerᗮ = A.adjoint.range
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_ker

中文:
引理 orthogonal_ker
  条件: (A : E ->ₗ[𝕜] F)
  结论: A.kerᗮ = A.adjoint.range
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_ker

Depends on / 依赖: A.toContinuousLinearMap.orthogonal_ker, FiniteDimensional, FiniteDimensional.complete, complete, orthogonal_ker, toContinuousLinearMap
-/
lemma orthogonal_ker (A : E ->ₗ[𝕜] F) : A.kerᗮ = A.adjoint.range := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_ker

/--
lemma `orthogonal_range` / 引理 `orthogonal_range`

English:
lemma orthogonal_range
  given: (A : E ->ₗ[𝕜] F)
  statement: A.rangeᗮ = A.adjoint.ker
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_range

中文:
引理 orthogonal_range
  条件: (A : E ->ₗ[𝕜] F)
  结论: A.rangeᗮ = A.adjoint.ker
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_range

Depends on / 依赖: A.toContinuousLinearMap.orthogonal_range, FiniteDimensional, FiniteDimensional.complete, complete, orthogonal_range, toContinuousLinearMap
-/
lemma orthogonal_range (A : E ->ₗ[𝕜] F) : A.rangeᗮ = A.adjoint.ker := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_range

/--
lemma `ker_adjoint_comp_self` / 引理 `ker_adjoint_comp_self`

English:
lemma ker_adjoint_comp_self
  given: (A : E ->ₗ[𝕜] F)
  statement: (A.adjoint ∘ₗ A).ker = A.ker
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.ker_adjoint_comp_self

中文:
引理 ker_adjoint_comp_self
  条件: (A : E ->ₗ[𝕜] F)
  结论: (A.adjoint ∘ₗ A).ker = A.ker
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.ker_adjoint_comp_self

Depends on / 依赖: A.toContinuousLinearMap.ker_adjoint_comp_self, FiniteDimensional, FiniteDimensional.complete, complete, ker_adjoint_comp_self, toContinuousLinearMap
-/
lemma ker_adjoint_comp_self (A : E ->ₗ[𝕜] F) : (A.adjoint ∘ₗ A).ker = A.ker := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.ker_adjoint_comp_self

/--
lemma `ker_self_comp_adjoint` / 引理 `ker_self_comp_adjoint`

English:
lemma ker_self_comp_adjoint
  given: (A : E ->ₗ[𝕜] F)
  statement: (A ∘ₗ A.adjoint).ker = A.adjoint.ker
  proof: by
  simpa using A.adjoint.ker_adjoint_comp_self

中文:
引理 ker_self_comp_adjoint
  条件: (A : E ->ₗ[𝕜] F)
  结论: (A ∘ₗ A.adjoint).ker = A.adjoint.ker
  证明: by
  simpa using A.adjoint.ker_adjoint_comp_self

Depends on / 依赖: A.adjoint.ker_adjoint_comp_self, adjoint, ker_adjoint_comp_self
-/
lemma ker_self_comp_adjoint (A : E ->ₗ[𝕜] F) : (A ∘ₗ A.adjoint).ker = A.adjoint.ker := by
  simpa using A.adjoint.ker_adjoint_comp_self

/--
lemma `adjoint_comp_self_injective_iff` / 引理 `adjoint_comp_self_injective_iff`

English:
lemma adjoint_comp_self_injective_iff
  given: (A : E ->ₗ[𝕜] F)
  proof: by
  rw [← coe_comp]; rw [← ker_eq_bot]; rw [← ker_eq_bot]; rw [ker_adjoint_comp_self]

中文:
引理 adjoint_comp_self_injective_iff
  条件: (A : E ->ₗ[𝕜] F)
  证明: by
  rw [← coe_comp]; rw [← ker_eq_bot]; rw [← ker_eq_bot]; rw [ker_adjoint_comp_self]

Depends on / 依赖: coe_comp, ker_adjoint_comp_self, ker_eq_bot
-/
lemma adjoint_comp_self_injective_iff (A : E ->ₗ[𝕜] F) :
    Function.Injective (A.adjoint ∘ A) ↔ Function.Injective A := by
  rw [← coe_comp]; rw [← ker_eq_bot]; rw [← ker_eq_bot]; rw [ker_adjoint_comp_self]

/--
lemma `self_comp_adjoint_injective_iff` / 引理 `self_comp_adjoint_injective_iff`

English:
lemma self_comp_adjoint_injective_iff
  given: (A : E ->ₗ[𝕜] F)
  proof: by
  simpa using A.adjoint.adjoint_comp_self_injective_iff

中文:
引理 self_comp_adjoint_injective_iff
  条件: (A : E ->ₗ[𝕜] F)
  证明: by
  simpa using A.adjoint.adjoint_comp_self_injective_iff

Depends on / 依赖: A.adjoint.adjoint_comp_self_injective_iff, adjoint, adjoint_comp_self_injective_iff
-/
lemma self_comp_adjoint_injective_iff (A : E ->ₗ[𝕜] F) :
    Function.Injective (A ∘ A.adjoint) ↔ Function.Injective A.adjoint := by
  simpa using A.adjoint.adjoint_comp_self_injective_iff

/--
lemma `range_adjoint_comp_self` / 引理 `range_adjoint_comp_self`

English:
lemma range_adjoint_comp_self
  given: (A : E ->ₗ[𝕜] F)
  statement: (A.adjoint ∘ₗ A).range = A.adjoint.range
  proof: calc
    (A.adjoint ∘ₗ A).range = (A.adjoint ∘ₗ A).kerᗮ := by simp [orthogonal_ker]
    _ = A.adjoint.range := by rw [ker_adjoint_comp_self, orthogonal_ker]

中文:
引理 range_adjoint_comp_self
  条件: (A : E ->ₗ[𝕜] F)
  结论: (A.adjoint ∘ₗ A).range = A.adjoint.range
  证明: calc
    (A.adjoint ∘ₗ A).range = (A.adjoint ∘ₗ A).kerᗮ := by simp [orthogonal_ker]
    _ = A.adjoint.range := by rw [ker_adjoint_comp_self, orthogonal_ker]

Depends on / 依赖: A.adjoint, A.adjoint.range, adjoint, ker_adjoint_comp_self, orthogonal_ker
-/
lemma range_adjoint_comp_self (A : E ->ₗ[𝕜] F) : (A.adjoint ∘ₗ A).range = A.adjoint.range :=
  calc
    (A.adjoint ∘ₗ A).range = (A.adjoint ∘ₗ A).kerᗮ := by simp [orthogonal_ker]
    _ = A.adjoint.range := by rw [ker_adjoint_comp_self, orthogonal_ker]

/--
lemma `range_self_comp_adjoint` / 引理 `range_self_comp_adjoint`

English:
lemma range_self_comp_adjoint
  given: (A : E ->ₗ[𝕜] F)
  statement: (A ∘ₗ A.adjoint).range = A.range
  proof: by
  simpa using A.adjoint.range_adjoint_comp_self

中文:
引理 range_self_comp_adjoint
  条件: (A : E ->ₗ[𝕜] F)
  结论: (A ∘ₗ A.adjoint).range = A.range
  证明: by
  simpa using A.adjoint.range_adjoint_comp_self

Depends on / 依赖: A.adjoint.range_adjoint_comp_self, adjoint, range_adjoint_comp_self
-/
lemma range_self_comp_adjoint (A : E ->ₗ[𝕜] F) : (A ∘ₗ A.adjoint).range = A.range := by
  simpa using A.adjoint.range_adjoint_comp_self

/--
theorem `finrank_range_adjoint` / 定理 `finrank_range_adjoint`

English:
theorem finrank_range_adjoint
  given: (A : E ->ₗ[𝕜] F)
  proof: calc
  _ = Module.finrank 𝕜 F - Module.finrank 𝕜 A.adjoint.ker := by
    simp [← A.adjoint.finrank_range_add_finrank_ker]
  _ = _ := by rw [← A.adjoint.ker.finrank_add_finrank_orthogonal,
    orthogonal_ker, adjoint_adjoint]; simp

中文:
定理 finrank_range_adjoint
  条件: (A : E ->ₗ[𝕜] F)
  证明: calc
  _ = Module.finrank 𝕜 F - Module.finrank 𝕜 A.adjoint.ker := by
    simp [← A.adjoint.finrank_range_add_finrank_ker]
  _ = _ := by rw [← A.adjoint.ker.finrank_add_finrank_orthogonal,
    orthogonal_ker, adjoint_adjoint]; simp
-/
theorem finrank_range_adjoint (A : E ->ₗ[𝕜] F) :
    Module.finrank 𝕜 A.adjoint.range = Module.finrank 𝕜 A.range := calc
  _ = Module.finrank 𝕜 F - Module.finrank 𝕜 A.adjoint.ker := by
    simp [← A.adjoint.finrank_range_add_finrank_ker]
  _ = _ := by rw [← A.adjoint.ker.finrank_add_finrank_orthogonal,
    orthogonal_ker, adjoint_adjoint]; simp

/--
theorem `eq_adjoint_iff_basis` / 定理 `eq_adjoint_iff_basis`

English:
theorem eq_adjoint_iff_basis
  statement: {ι₁ : Type*} {ι₂ : Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F)
  proof: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  refine Basis.ext b₁ fun i₁ => ?_
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]

中文:
定理 eq_adjoint_iff_basis
  结论: {ι₁ : 类型} {ι₂ : 类型} (b₁ : 基 ι₁ 𝕜 E) (b₂ : 基 ι₂ 𝕜 F)
  证明: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  refine Basis.ext b₁ fun i₁ => ?_
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]

Depends on / 依赖: Basis.ext, adjoint_inner_left, ext_inner_right_basis
-/
theorem eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F)
    (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E) :
    A = B.adjoint ↔ forall (i₁ : ι₁) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  refine Basis.ext b₁ fun i₁ => ?_
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]

/--
theorem `eq_adjoint_iff_basis_left` / 定理 `eq_adjoint_iff_basis_left`

English:
theorem eq_adjoint_iff_basis_left
  given: {ι : Type*} (b : Basis ι 𝕜 E) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
  proof: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => ?_⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]

中文:
定理 eq_adjoint_iff_basis_left
  条件: {ι : 类型} (b : 基 ι 𝕜 E) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
  证明: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => ?_⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]

Depends on / 依赖: Basis.ext, adjoint_inner_left, ext_inner_right
-/
theorem eq_adjoint_iff_basis_left {ι : Type*} (b : Basis ι 𝕜 E) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E) :
    A = B.adjoint ↔ forall i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => ?_⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]

/--
theorem `eq_adjoint_iff_basis_right` / 定理 `eq_adjoint_iff_basis_right`

English:
theorem eq_adjoint_iff_basis_right
  given: {ι : Type*} (b : Basis ι 𝕜 F) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
  proof: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]

中文:
定理 eq_adjoint_iff_basis_right
  条件: {ι : 类型} (b : 基 ι 𝕜 F) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
  证明: by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]

Depends on / 依赖: adjoint_inner_left, ext_inner_right_basis
-/
theorem eq_adjoint_iff_basis_right {ι : Type*} (b : Basis ι 𝕜 F) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E) :
    A = B.adjoint ↔ forall i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (E ->ₗ[𝕜] E)
  body: ⟨adjoint⟩

中文:
实例 :
  签名: 对合 (E ->ₗ[𝕜] E)
  定义体: ⟨adjoint⟩

Depends on / 依赖: adjoint
-/
instance : Star (E ->ₗ[𝕜] E) :=
  ⟨adjoint⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar (E ->ₗ[𝕜] E)
  body: ⟨adjoint_adjoint⟩

中文:
实例 :
  签名: InvolutiveStar (E ->ₗ[𝕜] E)
  定义体: ⟨adjoint_adjoint⟩

Depends on / 依赖: adjoint_adjoint
-/
instance : InvolutiveStar (E ->ₗ[𝕜] E) :=
  ⟨adjoint_adjoint⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (E ->ₗ[𝕜] E)
  body: ⟨adjoint_comp⟩

中文:
实例 :
  签名: StarMul (E ->ₗ[𝕜] E)
  定义体: ⟨adjoint_comp⟩

Depends on / 依赖: adjoint_comp
-/
instance : StarMul (E ->ₗ[𝕜] E) :=
  ⟨adjoint_comp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (E ->ₗ[𝕜] E)
  body: ⟨map_add adjoint⟩

中文:
实例 :
  签名: 对合环 (E ->ₗ[𝕜] E)
  定义体: ⟨map_add adjoint⟩

Depends on / 依赖: adjoint, map_add
-/
instance : StarRing (E ->ₗ[𝕜] E) :=
  ⟨map_add adjoint⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule 𝕜 (E ->ₗ[𝕜] E)
  body: ⟨map_smulₛₗ adjoint⟩

中文:
实例 :
  签名: 对合模 𝕜 (E ->ₗ[𝕜] E)
  定义体: ⟨map_smulₛₗ adjoint⟩

Depends on / 依赖: adjoint
-/
instance : StarModule 𝕜 (E ->ₗ[𝕜] E) :=
  ⟨map_smulₛₗ adjoint⟩

/--
theorem `star_eq_adjoint` / 定理 `star_eq_adjoint`

English:
theorem star_eq_adjoint
  given: (A : E ->ₗ[𝕜] E)
  statement: star A = A.adjoint
  proof: rfl

中文:
定理 star_eq_adjoint
  条件: (A : E ->ₗ[𝕜] E)
  结论: star A = A.adjoint
  证明: rfl
-/
theorem star_eq_adjoint (A : E ->ₗ[𝕜] E) : star A = A.adjoint :=
  rfl

/--
theorem `isSelfAdjoint_iff'` / 定理 `isSelfAdjoint_iff'`

English:
theorem isSelfAdjoint_iff'
  given: {A : E ->ₗ[𝕜] E}
  statement: IsSelfAdjoint A ↔ A.adjoint = A
  proof: Iff.rfl

中文:
定理 isSelfAdjoint_iff'
  条件: {A : E ->ₗ[𝕜] E}
  结论: IsSelfAdjoint A ↔ A.adjoint = A
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isSelfAdjoint_iff' {A : E ->ₗ[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl

/--
theorem `isSymmetric_iff_isSelfAdjoint` / 定理 `isSymmetric_iff_isSelfAdjoint`

English:
theorem isSymmetric_iff_isSelfAdjoint
  given: (A : E ->ₗ[𝕜] E)
  statement: IsSymmetric A ↔ IsSelfAdjoint A
  proof: by
  rw [isSelfAdjoint_iff']; rw [IsSymmetric]; rw [← LinearMap.eq_adjoint_iff]
  exact eq_comm

中文:
定理 isSymmetric_iff_isSelfAdjoint
  条件: (A : E ->ₗ[𝕜] E)
  结论: IsSymmetric A ↔ IsSelfAdjoint A
  证明: by
  rw [isSelfAdjoint_iff']; rw [IsSymmetric]; rw [← LinearMap.eq_adjoint_iff]
  exact eq_comm

Depends on / 依赖: IsSymmetric, LinearMap, LinearMap.eq_adjoint_iff, eq_adjoint_iff, eq_comm, isSelfAdjoint_iff
-/
theorem isSymmetric_iff_isSelfAdjoint (A : E ->ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A := by
  rw [isSelfAdjoint_iff']; rw [IsSymmetric]; rw [← LinearMap.eq_adjoint_iff]
  exact eq_comm

/--
lemma `id_mem_unitary` / 引理 `id_mem_unitary`

English:
lemma id_mem_unitary
  statement: .id in unitary (E ->ₗ[𝕜] E)
  proof: one_mem _

中文:
引理 id_mem_unitary
  结论: .id in unitary (E ->ₗ[𝕜] E)
  证明: one_mem _
-/
@[simp] lemma id_mem_unitary : .id in unitary (E ->ₗ[𝕜] E) := one_mem _

/--
theorem `isAdjointPair_inner` / 定理 `isAdjointPair_inner`

English:
theorem isAdjointPair_inner
  given: (A : E ->ₗ[𝕜] F)
  proof: by
  intro x y
  simp [adjoint_inner_left]

中文:
定理 isAdjointPair_inner
  条件: (A : E ->ₗ[𝕜] F)
  证明: by
  intro x y
  simp [adjoint_inner_left]
-/
theorem isAdjointPair_inner (A : E ->ₗ[𝕜] F) :
    IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip
      (innerₛₗ 𝕜 (E := F)).flip A A.adjoint := by
  intro x y
  simp [adjoint_inner_left]

/-! This next batch of lemmas is based on theorems like `LinearMap.IsPositive.conj_adjoint`, which
are in a downstream file but historically existed before these lemmas. We can't put them in the file
where `LinearMap.IsSymmetric` is defined because they depend on the adjoint. -/

@[aesop safe apply]
/--
theorem `IsSymmetric.conj_adjoint` / 定理 `IsSymmetric.conj_adjoint`

English:
theorem IsSymmetric.conj_adjoint
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (S : E ->ₗ[𝕜] F)
  proof: fun _ _ => by simp [← adjoint_inner_right, hT]

中文:
定理 IsSymmetric.conj_adjoint
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (S : E ->ₗ[𝕜] F)
  证明: fun _ _ => by simp [← adjoint_inner_right, hT]

Depends on / 依赖: adjoint_inner_right
-/
theorem IsSymmetric.conj_adjoint {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (S : E ->ₗ[𝕜] F) :
    (S ∘ₗ T ∘ₗ S.adjoint).IsSymmetric := fun _ _ => by simp [← adjoint_inner_right, hT]

/--
theorem `isSymmetric_self_comp_adjoint` / 定理 `isSymmetric_self_comp_adjoint`

English:
theorem isSymmetric_self_comp_adjoint
  given: (T : E ->ₗ[𝕜] F)
  statement: (T ∘ₗ adjoint T).IsSymmetric
  proof: by
  simpa using LinearMap.IsSymmetric.id.conj_adjoint T

@[aesop safe apply]

中文:
定理 isSymmetric_self_comp_adjoint
  条件: (T : E ->ₗ[𝕜] F)
  结论: (T ∘ₗ adjoint T).IsSymmetric
  证明: by
  simpa using LinearMap.IsSymmetric.id.conj_adjoint T

@[aesop safe apply]

Depends on / 依赖: IsSymmetric, LinearMap, LinearMap.IsSymmetric.id.conj_adjoint, conj_adjoint
-/
theorem isSymmetric_self_comp_adjoint (T : E ->ₗ[𝕜] F) : (T ∘ₗ adjoint T).IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.conj_adjoint T

@[aesop safe apply]
/--
theorem `IsSymmetric.adjoint_conj` / 定理 `IsSymmetric.adjoint_conj`

English:
theorem IsSymmetric.adjoint_conj
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (S : F ->ₗ[𝕜] E)
  proof: by
  simpa using hT.conj_adjoint S.adjoint

中文:
定理 IsSymmetric.adjoint_conj
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (S : F ->ₗ[𝕜] E)
  证明: by
  simpa using hT.conj_adjoint S.adjoint

Depends on / 依赖: S.adjoint, adjoint, conj_adjoint, hT.conj_adjoint
-/
theorem IsSymmetric.adjoint_conj {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (S : F ->ₗ[𝕜] E) :
    (S.adjoint ∘ₗ T ∘ₗ S).IsSymmetric := by
  simpa using hT.conj_adjoint S.adjoint

/--
theorem `isSymmetric_adjoint_comp_self` / 定理 `isSymmetric_adjoint_comp_self`

English:
theorem isSymmetric_adjoint_comp_self
  given: (T : E ->ₗ[𝕜] F)
  statement: (adjoint T ∘ₗ T).IsSymmetric
  proof: by
  simpa using LinearMap.IsSymmetric.id.adjoint_conj T

中文:
定理 isSymmetric_adjoint_comp_self
  条件: (T : E ->ₗ[𝕜] F)
  结论: (adjoint T ∘ₗ T).IsSymmetric
  证明: by
  simpa using LinearMap.IsSymmetric.id.adjoint_conj T

Depends on / 依赖: IsSymmetric, LinearMap, LinearMap.IsSymmetric.id.adjoint_conj, adjoint_conj
-/
theorem isSymmetric_adjoint_comp_self (T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.adjoint_conj T

/--
theorem `isSymmetric_adjoint_mul_self` / 定理 `isSymmetric_adjoint_mul_self`

English:
theorem isSymmetric_adjoint_mul_self
  given: (T : E ->ₗ[𝕜] E)
  statement: IsSymmetric (T.adjoint * T)
  proof: by
  intro x y
  simp [adjoint_inner_left, adjoint_inner_right]

中文:
定理 isSymmetric_adjoint_mul_self
  条件: (T : E ->ₗ[𝕜] E)
  结论: IsSymmetric (T.adjoint * T)
  证明: by
  intro x y
  simp [adjoint_inner_left, adjoint_inner_right]

Depends on / 依赖: adjoint_inner_left, adjoint_inner_right
-/
theorem isSymmetric_adjoint_mul_self (T : E ->ₗ[𝕜] E) : IsSymmetric (T.adjoint * T) := by
  intro x y
  simp [adjoint_inner_left, adjoint_inner_right]

/--
theorem `re_inner_adjoint_mul_self_nonneg` / 定理 `re_inner_adjoint_mul_self_nonneg`

English:
theorem re_inner_adjoint_mul_self_nonneg
  given: (T : E ->ₗ[𝕜] E) (x : E)
  proof: by
  simp only [Module.End.mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

@[simp]

中文:
定理 re_inner_adjoint_mul_self_nonneg
  条件: (T : E ->ₗ[𝕜] E) (x : E)
  证明: by
  simp only [Module.End.mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

@[simp]

Depends on / 依赖: Module, Module.End.mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K, mul_apply, sq_nonneg
-/
theorem re_inner_adjoint_mul_self_nonneg (T : E ->ₗ[𝕜] E) (x : E) :
    0 <= re ⟪x, (T.adjoint * T) x⟫ := by
  simp only [Module.End.mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

@[simp]
/--
theorem `im_inner_adjoint_mul_self_eq_zero` / 定理 `im_inner_adjoint_mul_self_eq_zero`

English:
theorem im_inner_adjoint_mul_self_eq_zero
  given: (T : E ->ₗ[𝕜] E) (x : E)
  proof: by
  simp only [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

中文:
定理 im_inner_adjoint_mul_self_eq_zero
  条件: (T : E ->ₗ[𝕜] E) (x : E)
  证明: by
  simp only [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

Depends on / 依赖: adjoint_inner_right, inner_self_eq_norm_sq_to_K
-/
theorem im_inner_adjoint_mul_self_eq_zero (T : E ->ₗ[𝕜] E) (x : E) :
    im ⟪x, T.adjoint (T x)⟫ = 0 := by
  simp only [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/--
theorem `isSelfAdjoint_toContinuousLinearMap_iff` / 定理 `isSelfAdjoint_toContinuousLinearMap_iff`

English:
theorem isSelfAdjoint_toContinuousLinearMap_iff
  given: (T : E ->ₗ[𝕜] E)
  proof: FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toContinuousLinearMap ↔ IsSelfAdjoint T := by
  simp [IsSelfAdjoint, star, adjoint,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]

中文:
定理 isSelfAdjoint_toContinuousLinearMap_iff
  条件: (T : E ->ₗ[𝕜] E)
  证明: FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toContinuousLinearMap ↔ IsSelfAdjoint T := by
  simp [IsSelfAdjoint, star, adjoint,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem isSelfAdjoint_toContinuousLinearMap_iff (T : E ->ₗ[𝕜] E) :
    have := FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toContinuousLinearMap ↔ IsSelfAdjoint T := by
  simp [IsSelfAdjoint, star, adjoint,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]

/--
theorem `_root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff` / 定理 `_root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff`

English:
theorem _root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff
  given: (T : E ->L[𝕜] E)
  proof: FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toLinearMap ↔ IsSelfAdjoint T := by
  simp only [IsSelfAdjoint, star, adjoint, LinearEquiv.trans_apply,
    coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
  rfl

中文:
定理 _root_.连续线性映射.isSelfAdjoint_toLinearMap_iff
  条件: (T : E ->L[𝕜] E)
  证明: FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toLinearMap ↔ IsSelfAdjoint T := by
  simp only [IsSelfAdjoint, star, adjoint, LinearEquiv.trans_apply,
    coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
  rfl

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem _root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff (T : E ->L[𝕜] E) :
    have := FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toLinearMap ↔ IsSelfAdjoint T := by
  simp only [IsSelfAdjoint, star, adjoint, LinearEquiv.trans_apply,
    coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
  rfl

/--
theorem `isStarProjection_toContinuousLinearMap_iff` / 定理 `isStarProjection_toContinuousLinearMap_iff`

English:
theorem isStarProjection_toContinuousLinearMap_iff
  given: {T : E ->ₗ[𝕜] E}
  proof: FiniteDimensional.complete 𝕜 E
    IsStarProjection (toContinuousLinearMap T) ↔ IsStarProjection T := by
  simp [isStarProjection_iff, isSelfAdjoint_toContinuousLinearMap_iff,
    ← ContinuousLinearMap.isIdempotentElem_toLinearMap_iff]

中文:
定理 isStarProjection_toContinuousLinearMap_iff
  条件: {T : E ->ₗ[𝕜] E}
  证明: FiniteDimensional.complete 𝕜 E
    IsStarProjection (toContinuousLinearMap T) ↔ IsStarProjection T := by
  simp [isStarProjection_iff, isSelfAdjoint_toContinuousLinearMap_iff,
    ← ContinuousLinearMap.isIdempotentElem_toLinearMap_iff]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, complete
-/
theorem isStarProjection_toContinuousLinearMap_iff {T : E ->ₗ[𝕜] E} :
    have := FiniteDimensional.complete 𝕜 E
    IsStarProjection (toContinuousLinearMap T) ↔ IsStarProjection T := by
  simp [isStarProjection_iff, isSelfAdjoint_toContinuousLinearMap_iff,
    ← ContinuousLinearMap.isIdempotentElem_toLinearMap_iff]

/--
theorem `isStarProjection_iff_isSymmetricProjection` / 定理 `isStarProjection_iff_isSymmetricProjection`

English:
theorem isStarProjection_iff_isSymmetricProjection
  given: {T : E ->ₗ[𝕜] E}
  proof: by
  simp [← isStarProjection_toContinuousLinearMap_iff,
    ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]

中文:
定理 isStarProjection_iff_isSymmetricProjection
  条件: {T : E ->ₗ[𝕜] E}
  证明: by
  simp [← isStarProjection_toContinuousLinearMap_iff,
    ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection, isStarProjection_iff_isSymmetricProjection, isStarProjection_toContinuousLinearMap_iff
-/
theorem isStarProjection_iff_isSymmetricProjection {T : E ->ₗ[𝕜] E} :
    IsStarProjection T ↔ T.IsSymmetricProjection := by
  simp [← isStarProjection_toContinuousLinearMap_iff,
    ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]

open LinearMap in
/--
theorem `IsStarProjection.ext_iff` / 定理 `IsStarProjection.ext_iff`

English:
theorem IsStarProjection.ext_iff
  statement: {S T : E ->ₗ[𝕜] E}
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  simpa using ContinuousLinearMap.IsStarProjection.ext_iff
    (S.isStarProjection_toContinuousLinearMap_iff.mpr hS)
    (T.isStarProjection_toContinuousLinearMap_iff.mpr hT)

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

中文:
定理 是StarProjection.ext_iff
  结论: {S T : E ->ₗ[𝕜] E}
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  simpa using ContinuousLinearMap.IsStarProjection.ext_iff
    (S.isStarProjection_toContinuousLinearMap_iff.mpr hS)
    (T.isStarProjection_toContinuousLinearMap_iff.mpr hT)

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff
-/
theorem IsStarProjection.ext_iff {S T : E ->ₗ[𝕜] E}
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    S = T ↔ LinearMap.range S = LinearMap.range T := by
  have := FiniteDimensional.complete 𝕜 E
  simpa using ContinuousLinearMap.IsStarProjection.ext_iff
    (S.isStarProjection_toContinuousLinearMap_iff.mpr hS)
    (T.isStarProjection_toContinuousLinearMap_iff.mpr hT)

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff

/--
theorem `adjoint_innerₛₗ_apply` / 定理 `adjoint_innerₛₗ_apply`

English:
theorem adjoint_innerₛₗ_apply
  given: (x : E)
  proof: have := FiniteDimensional.complete 𝕜 E
  ext fun _ => congr($(ContinuousLinearMap.adjoint_innerSL_apply x) _)

中文:
定理 adjoint_innerₛₗ_apply
  条件: (x : E)
  证明: have := FiniteDimensional.complete 𝕜 E
  ext fun _ => congr($(ContinuousLinearMap.adjoint_innerSL_apply x) _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.adjoint_innerSL_apply, FiniteDimensional, FiniteDimensional.complete, adjoint_innerSL_apply, complete
-/
theorem adjoint_innerₛₗ_apply (x : E) :
    adjoint (innerₛₗ 𝕜 x) = toSpanSingleton 𝕜 E x :=
  have := FiniteDimensional.complete 𝕜 E
  ext fun _ => congr($(ContinuousLinearMap.adjoint_innerSL_apply x) _)

/--
theorem `adjoint_toSpanSingleton` / 定理 `adjoint_toSpanSingleton`

English:
theorem adjoint_toSpanSingleton
  given: (x : E)
  proof: by
  simp [← adjoint_innerₛₗ_apply]

中文:
定理 adjoint_toSpanSingleton
  条件: (x : E)
  证明: by
  simp [← adjoint_innerₛₗ_apply]
-/
theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 E x) = innerₛₗ 𝕜 x := by
  simp [← adjoint_innerₛₗ_apply]

open Module End in
/--
theorem `_root_.Module.End.mem_invtSubmodule_adjoint_iff` / 定理 `_root_.Module.End.mem_invtSubmodule_adjoint_iff`

English:
theorem _root_.Module.End.mem_invtSubmodule_adjoint_iff
  given: {T : E ->ₗ[𝕜] E} {U : Submodule 𝕜 E}
  proof: have := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.mem_invtSubmodule_adjoint_iff

中文:
定理 _root_.模.End.mem_invtSubmodule_adjoint_iff
  条件: {T : E ->ₗ[𝕜] E} {U : 子模 𝕜 E}
  证明: have := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.mem_invtSubmodule_adjoint_iff

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mem_invtSubmodule_adjoint_iff, FiniteDimensional, FiniteDimensional.complete, complete, mem_invtSubmodule_adjoint_iff
-/
theorem _root_.Module.End.mem_invtSubmodule_adjoint_iff {T : E ->ₗ[𝕜] E} {U : Submodule 𝕜 E} :
    U in invtSubmodule T.adjoint ↔ Uᗮ in invtSubmodule T :=
  have := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.mem_invtSubmodule_adjoint_iff

end LinearMap

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

section linearIsometryEquiv
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

namespace ContinuousLinearMap

/--
theorem `inner_map_map_iff_adjoint_comp_self` / 定理 `inner_map_map_iff_adjoint_comp_self`

English:
theorem inner_map_map_iff_adjoint_comp_self
  given: (u : H ->L[𝕜] K)
  proof: by
  refine ⟨fun h => ext fun x => ?_, fun h => ?_⟩
  · refine ext_inner_right 𝕜 fun y => ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]

中文:
定理 inner_map_map_iff_adjoint_comp_self
  条件: (u : H ->L[𝕜] K)
  证明: by
  refine ⟨fun h => ext fun x => ?_, fun h => ?_⟩
  · refine ext_inner_right 𝕜 fun y => ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]

Depends on / 依赖: adjoint_inner_left, comp_apply, ext_inner_right, star_eq_adjoint
-/
theorem inner_map_map_iff_adjoint_comp_self (u : H ->L[𝕜] K) :
    (forall x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜) ↔ adjoint u ∘L u = 1 := by
  refine ⟨fun h => ext fun x => ?_, fun h => ?_⟩
  · refine ext_inner_right 𝕜 fun y => ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]

/--
theorem `norm_map_iff_adjoint_comp_self` / 定理 `norm_map_iff_adjoint_comp_self`

English:
theorem norm_map_iff_adjoint_comp_self
  given: (u : H ->L[𝕜] K)
  proof: by
  rw [LinearMap.norm_map_iff_inner_map_map u]; rw [u.inner_map_map_iff_adjoint_comp_self]

中文:
定理 norm_map_iff_adjoint_comp_self
  条件: (u : H ->L[𝕜] K)
  证明: by
  rw [LinearMap.norm_map_iff_inner_map_map u]; rw [u.inner_map_map_iff_adjoint_comp_self]

Depends on / 依赖: LinearMap, LinearMap.norm_map_iff_inner_map_map, inner_map_map_iff_adjoint_comp_self, norm_map_iff_inner_map_map, u.inner_map_map_iff_adjoint_comp_self
-/
theorem norm_map_iff_adjoint_comp_self (u : H ->L[𝕜] K) :
    (forall x : H, ‖u x‖ = ‖x‖) ↔ adjoint u ∘L u = 1 := by
  rw [LinearMap.norm_map_iff_inner_map_map u]; rw [u.inner_map_map_iff_adjoint_comp_self]

/--
theorem `isometry_iff_adjoint_comp_self` / 定理 `isometry_iff_adjoint_comp_self`

English:
theorem isometry_iff_adjoint_comp_self
  given: (u : H ->L[𝕜] K)
  proof: by
  rw [AddMonoidHomClass.isometry_iff_norm]; rw [norm_map_iff_adjoint_comp_self]

@[simp]

中文:
定理 isometry_iff_adjoint_comp_self
  条件: (u : H ->L[𝕜] K)
  证明: by
  rw [AddMonoidHomClass.isometry_iff_norm]; rw [norm_map_iff_adjoint_comp_self]

@[simp]

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_iff_norm, isometry_iff_norm, norm_map_iff_adjoint_comp_self
-/
theorem isometry_iff_adjoint_comp_self (u : H ->L[𝕜] K) :
    Isometry u ↔ adjoint u ∘L u = 1 := by
  rw [AddMonoidHomClass.isometry_iff_norm]; rw [norm_map_iff_adjoint_comp_self]

@[simp]
/--
lemma `_root_.LinearIsometryEquiv.adjoint_eq_symm` / 引理 `_root_.LinearIsometryEquiv.adjoint_eq_symm`

English:
lemma _root_.LinearIsometryEquiv.adjoint_eq_symm
  given: (e : H ≃ₗᵢ[𝕜] K)
  proof: calc
    _ = adjoint (e : H ->L[𝕜] K) ∘L e ∘L (e.symm : K ->L[𝕜] H) := by simp
    _ = e.symm := by
      rw [← comp_assoc]; rw [norm_map_iff_adjoint_comp_self _ |>.mp e.norm_map]; rw [one_def]; rw [id_comp]

omit [CompleteSpace H] [CompleteSpace K] in

中文:
引理 _root_.线性等距等价.adjoint_eq_symm
  条件: (e : H ≃ₗᵢ[𝕜] K)
  证明: calc
    _ = adjoint (e : H ->L[𝕜] K) ∘L e ∘L (e.symm : K ->L[𝕜] H) := by simp
    _ = e.symm := by
      rw [← comp_assoc]; rw [norm_map_iff_adjoint_comp_self _ |>.mp e.norm_map]; rw [one_def]; rw [id_comp]

omit [CompleteSpace H] [CompleteSpace K] in

Depends on / 依赖: adjoint, comp_assoc, e.norm_map, e.symm, id_comp, norm_map, norm_map_iff_adjoint_comp_self, one_def
-/
lemma _root_.LinearIsometryEquiv.adjoint_eq_symm (e : H ≃ₗᵢ[𝕜] K) :
    adjoint (e : H ->L[𝕜] K) = e.symm :=
  calc
    _ = adjoint (e : H ->L[𝕜] K) ∘L e ∘L (e.symm : K ->L[𝕜] H) := by simp
    _ = e.symm := by
      rw [← comp_assoc]; rw [norm_map_iff_adjoint_comp_self _ |>.mp e.norm_map]; rw [one_def]; rw [id_comp]

omit [CompleteSpace H] [CompleteSpace K] in
/--
theorem `_root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm` / 定理 `_root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm`

English:
theorem _root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
  proof: have := FiniteDimensional.complete 𝕜 H
  have := FiniteDimensional.complete 𝕜 K
  congr($e.adjoint_eq_symm)

@[simp]

中文:
定理 _root_.线性等距等价.adjoint_toLinearMap_eq_symm
  证明: have := FiniteDimensional.complete 𝕜 H
  have := FiniteDimensional.complete 𝕜 K
  congr($e.adjoint_eq_symm)

@[simp]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, adjoint_eq_symm, complete, e.adjoint_eq_symm
-/
theorem _root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
    [FiniteDimensional 𝕜 H] [FiniteDimensional 𝕜 K] (e : H ≃ₗᵢ[𝕜] K) :
    LinearMap.adjoint e.toLinearMap = e.symm.toLinearMap :=
  have := FiniteDimensional.complete 𝕜 H
  have := FiniteDimensional.complete 𝕜 K
  congr($e.adjoint_eq_symm)

@[simp]
/--
lemma `_root_.LinearIsometryEquiv.star_eq_symm` / 引理 `_root_.LinearIsometryEquiv.star_eq_symm`

English:
lemma _root_.LinearIsometryEquiv.star_eq_symm
  given: (e : H ≃ₗᵢ[𝕜] H)
  proof: e.adjoint_eq_symm

中文:
引理 _root_.线性等距等价.star_eq_symm
  条件: (e : H ≃ₗᵢ[𝕜] H)
  证明: e.adjoint_eq_symm

Depends on / 依赖: adjoint_eq_symm, e.adjoint_eq_symm
-/
lemma _root_.LinearIsometryEquiv.star_eq_symm (e : H ≃ₗᵢ[𝕜] H) :
    star (e : H ->L[𝕜] H) = e.symm :=
  e.adjoint_eq_symm

/--
theorem `norm_map_of_mem_unitary` / 定理 `norm_map_of_mem_unitary`

English:
theorem norm_map_of_mem_unitary
  given: {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x : H)
  proof: -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.norm_map_iff_adjoint_comp_self.mpr this x

中文:
定理 norm_map_of_mem_unitary
  条件: {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x : H)
  证明: -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.norm_map_iff_adjoint_comp_self.mpr this x
-/
theorem norm_map_of_mem_unitary {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x : H) :
    ‖u x‖ = ‖x‖ :=
  -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.norm_map_iff_adjoint_comp_self.mpr this x

/--
theorem `inner_map_map_of_mem_unitary` / 定理 `inner_map_map_of_mem_unitary`

English:
theorem inner_map_map_of_mem_unitary
  given: {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x y : H)
  proof: -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.inner_map_map_iff_adjoint_comp_self.mpr this x y

中文:
定理 inner_map_map_of_mem_unitary
  条件: {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x y : H)
  证明: -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.inner_map_map_iff_adjoint_comp_self.mpr this x y
-/
theorem inner_map_map_of_mem_unitary {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x y : H) :
    ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.inner_map_map_iff_adjoint_comp_self.mpr this x y

end ContinuousLinearMap

namespace LinearIsometryEquiv

open ContinuousLinearMap ContinuousLinearEquiv in
/--
Definition of `conjStarAlgEquiv` / `conjStarAlgEquiv` 的定义

English:
definition conjStarAlgEquiv
  signature: (e : H ≃ₗᵢ[𝕜] K)
  body: .ofAlgEquiv e.toContinuousLinearEquiv.conjContinuousAlgEquiv fun x => by
    simp [star_eq_adjoint, conjContinuousAlgEquiv_apply, ← toContinuousLinearEquiv_symm, comp_assoc]

中文:
定义 conjStarAlgEquiv
  签名: (e : H ≃ₗᵢ[𝕜] K)
  定义体: .ofAlgEquiv e.toContinuousLinearEquiv.conjContinuousAlgEquiv fun x => by
    simp [star_eq_adjoint, conjContinuousAlgEquiv_apply, ← toContinuousLinearEquiv_symm, comp_assoc]

Depends on / 依赖: comp_assoc, conjContinuousAlgEquiv, conjContinuousAlgEquiv_apply, e.toContinuousLinearEquiv.conjContinuousAlgEquiv, ofAlgEquiv, star_eq_adjoint, toContinuousLinearEquiv, toContinuousLinearEquiv_symm
-/
def conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) : (H ->L[𝕜] H) ≃⋆ₐ[𝕜] (K ->L[𝕜] K) :=
  .ofAlgEquiv e.toContinuousLinearEquiv.conjContinuousAlgEquiv fun x => by
    simp [star_eq_adjoint, conjContinuousAlgEquiv_apply, ← toContinuousLinearEquiv_symm, comp_assoc]

/--
lemma `conjStarAlgEquiv_apply_apply` / 引理 `conjStarAlgEquiv_apply_apply`

English:
lemma conjStarAlgEquiv_apply_apply
  given: (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H) (y : K)
  proof: rfl

中文:
引理 conjStarAlgEquiv_apply_apply
  条件: (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H) (y : K)
  证明: rfl
-/
@[simp] lemma conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H) (y : K) :
    e.conjStarAlgEquiv x y = e (x (e.symm y)) := rfl

/--
theorem `symm_conjStarAlgEquiv_apply_apply` / 定理 `symm_conjStarAlgEquiv_apply_apply`

English:
theorem symm_conjStarAlgEquiv_apply_apply
  given: (e : H ≃ₗᵢ[𝕜] K) (f : K ->L[𝕜] K) (x : H)
  proof: rfl

中文:
定理 symm_conjStarAlgEquiv_apply_apply
  条件: (e : H ≃ₗᵢ[𝕜] K) (f : K ->L[𝕜] K) (x : H)
  证明: rfl
-/
theorem symm_conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (f : K ->L[𝕜] K) (x : H) :
    e.conjStarAlgEquiv.symm f x = e.symm (f (e x)) := rfl

/--
lemma `conjStarAlgEquiv_apply` / 引理 `conjStarAlgEquiv_apply`

English:
lemma conjStarAlgEquiv_apply
  given: (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H)
  proof: rfl

中文:
引理 conjStarAlgEquiv_apply
  条件: (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H)
  证明: rfl
-/
lemma conjStarAlgEquiv_apply (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H) :
    e.conjStarAlgEquiv x = e ∘L x ∘L e.symm := rfl

/--
lemma `symm_conjStarAlgEquiv` / 引理 `symm_conjStarAlgEquiv`

English:
lemma symm_conjStarAlgEquiv
  given: (e : H ≃ₗᵢ[𝕜] K)
  proof: rfl

中文:
引理 symm_conjStarAlgEquiv
  条件: (e : H ≃ₗᵢ[𝕜] K)
  证明: rfl
-/
@[simp] lemma symm_conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) :
    e.conjStarAlgEquiv.symm = e.symm.conjStarAlgEquiv := rfl

/--
theorem `conjStarAlgEquiv_refl` / 定理 `conjStarAlgEquiv_refl`

English:
theorem conjStarAlgEquiv_refl
  statement: conjStarAlgEquiv (.refl 𝕜 H) = .refl _ _
  proof: rfl

中文:
定理 conjStarAlgEquiv_refl
  结论: conjStarAlgEquiv (.refl 𝕜 H) = .refl _ _
  证明: rfl
-/
@[simp] theorem conjStarAlgEquiv_refl : conjStarAlgEquiv (.refl 𝕜 H) = .refl _ _ := rfl

/--
theorem `conjStarAlgEquiv_trans` / 定理 `conjStarAlgEquiv_trans`

English:
theorem conjStarAlgEquiv_trans
  statement: {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  proof: rfl

中文:
定理 conjStarAlgEquiv_trans
  结论: {G : 类型} [赋范交换加群 G] [内积空间 𝕜 G]
  证明: rfl
-/
theorem conjStarAlgEquiv_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (e : H ≃ₗᵢ[𝕜] K) (f : K ≃ₗᵢ[𝕜] G) :
    (e.trans f).conjStarAlgEquiv = e.conjStarAlgEquiv.trans f.conjStarAlgEquiv := rfl

set_option backward.isDefEq.respectTransparency false in
open ContinuousLinearEquiv ContinuousLinearMap in
/--
theorem `conjStarAlgEquiv_ext_iff` / 定理 `conjStarAlgEquiv_ext_iff`

English:
theorem conjStarAlgEquiv_ext_iff
  given: (f g : H ≃ₗᵢ[𝕜] K)
  proof: by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, LinearIsometryEquiv.ext_iff, conjStarAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← comp_assoc, toContinuousLinearEquiv_symm,
    eq_comp_toContinuousLinearMap_symm,
    comp_assoc, ← comp_assoc _ (f : H ->L[𝕜] K), comp_coe, ← ContinuousLinearMap.mul_def,
    ← Subalgebra.mem_center_iff (R := 𝕜), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : 𝕜), by ext; simp [h]⟩⟩
  by_cases! hy : y = 0
  · exact ⟨1, fun x => by simp [by simpa [hy] using congr($h x).symm]⟩
  have hfg : (f : H ->L[𝕜] K) = y • g := by ext; simpa using congr(g ($h _)).symm
  have hgf : (g : H ->L[𝕜] K) = star y • f := by
    ext x
    have := by simpa [map_smulₛₗ, ← ContinuousLinearEquiv.comp_coe, ← toContinuousLinearEquiv_symm,
      ← adjoint_eq_symm, ContinuousLinearMap.one_def] using congr(f (adjoint $h x)).symm
    simpa
  have : (g : H ->L[𝕜] K) = (starRingEnd 𝕜 y * y) • g := by
    simp [← smul_smul, ← hfg, ← star_def, ← hgf]
  nth_rw 1 [← one_smul 𝕜 (g : H ->L[𝕜] K)] at this
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [eq_comm] at this
  obtain (this | this) := this
  · exact ⟨⟨y, by simp [Unitary.mem_iff, this, mul_comm y]⟩, fun x => congr($hfg x)⟩
  · exact ⟨1, fun x => by simp [by simpa using congr($this x)]⟩

中文:
定理 conjStarAlgEquiv_ext_iff
  条件: (f g : H ≃ₗᵢ[𝕜] K)
  证明: by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, LinearIsometryEquiv.ext_iff, conjStarAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← comp_assoc, toContinuousLinearEquiv_symm,
    eq_comp_toContinuousLinearMap_symm,
    comp_assoc, ← comp_assoc _ (f : H ->L[𝕜] K), comp_coe, ← ContinuousLinearMap.mul_def,
    ← Subalgebra.mem_center_iff (R := 𝕜), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : 𝕜), by ext; simp [h]⟩⟩
  by_cases! hy : y = 0
  · exact ⟨1, fun x => by simp [by simpa [hy] using congr($h x).symm]⟩
  have hfg : (f : H ->L[𝕜] K) = y • g := by ext; simpa using congr(g ($h _)).symm
  have hgf : (g : H ->L[𝕜] K) = star y • f := by
    ext x
    have := by simpa [map_smulₛₗ, ← ContinuousLinearEquiv.comp_coe, ← toContinuousLinearEquiv_symm,
      ← adjoint_eq_symm, ContinuousLinearMap.one_def] using congr(f (adjoint $h x)).symm
    simpa
  have : (g : H ->L[𝕜] K) = (starRingEnd 𝕜 y * y) • g := by
    simp [← smul_smul, ← hfg, ← star_def, ← hgf]
  nth_rw 1 [← one_smul 𝕜 (g : H ->L[𝕜] K)] at this
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [eq_comm] at this
  obtain (this | this) := this
  · exact ⟨⟨y, by simp [Unitary.mem_iff, this, mul_comm y]⟩, fun x => congr($hfg x)⟩
  · exact ⟨1, fun x => by simp [by simpa using congr($this x)]⟩

Depends on / 依赖: Algebra, Algebra.IsCentral.center_eq_bot, Algebra.algebraMap_eq_smul_one, Algebra.mem_bot, ContinuousLinearMap, ContinuousLinearMap.mul_def, IsCentral, LinearIsometryEquiv, LinearIsometryEquiv.ext_iff, Set.mem_range, StarAlgEquiv, StarAlgEquiv.ext_iff, Subalgebra, Subalgebra.mem_center_iff, algebraMap_eq_smul_one, center_eq_bot, comp_assoc, comp_coe, conjStarAlgEquiv_apply, conv_lhs
-/
theorem conjStarAlgEquiv_ext_iff (f g : H ≃ₗᵢ[𝕜] K) :
    f.conjStarAlgEquiv = g.conjStarAlgEquiv ↔ exists α : unitary 𝕜, f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, LinearIsometryEquiv.ext_iff, conjStarAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← comp_assoc, toContinuousLinearEquiv_symm,
    eq_comp_toContinuousLinearMap_symm,
    comp_assoc, ← comp_assoc _ (f : H ->L[𝕜] K), comp_coe, ← ContinuousLinearMap.mul_def,
    ← Subalgebra.mem_center_iff (R := 𝕜), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : 𝕜), by ext; simp [h]⟩⟩
  by_cases! hy : y = 0
  · exact ⟨1, fun x => by simp [by simpa [hy] using congr($h x).symm]⟩
  have hfg : (f : H ->L[𝕜] K) = y • g := by ext; simpa using congr(g ($h _)).symm
  have hgf : (g : H ->L[𝕜] K) = star y • f := by
    ext x
    have := by simpa [map_smulₛₗ, ← ContinuousLinearEquiv.comp_coe, ← toContinuousLinearEquiv_symm,
      ← adjoint_eq_symm, ContinuousLinearMap.one_def] using congr(f (adjoint $h x)).symm
    simpa
  have : (g : H ->L[𝕜] K) = (starRingEnd 𝕜 y * y) • g := by
    simp [← smul_smul, ← hfg, ← star_def, ← hgf]
  nth_rw 1 [← one_smul 𝕜 (g : H ->L[𝕜] K)] at this
  rw [← sub_eq_zero]; rw [← sub_smul]; rw [smul_eq_zero]; rw [sub_eq_zero]; rw [eq_comm] at this
  obtain (this | this) := this
  · exact ⟨⟨y, by simp [Unitary.mem_iff, this, mul_comm y]⟩, fun x => congr($hfg x)⟩
  · exact ⟨1, fun x => by simp [by simpa using congr($this x)]⟩

end LinearIsometryEquiv
end linearIsometryEquiv

namespace Unitary

/--
theorem `norm_map` / 定理 `norm_map`

English:
theorem norm_map
  given: (u : unitary (H ->L[𝕜] H)) (x : H)
  statement: ‖(u : H ->L[𝕜] H) x‖ = ‖x‖
  proof: u.val.norm_map_of_mem_unitary u.property x

中文:
定理 norm_map
  条件: (u : unitary (H ->L[𝕜] H)) (x : H)
  结论: ‖(u : H ->L[𝕜] H) x‖ = ‖x‖
  证明: u.val.norm_map_of_mem_unitary u.property x

Depends on / 依赖: norm_map_of_mem_unitary, property, u.property, u.val.norm_map_of_mem_unitary
-/
theorem norm_map (u : unitary (H ->L[𝕜] H)) (x : H) : ‖(u : H ->L[𝕜] H) x‖ = ‖x‖ :=
  u.val.norm_map_of_mem_unitary u.property x

/--
theorem `inner_map_map` / 定理 `inner_map_map`

English:
theorem inner_map_map
  given: (u : unitary (H ->L[𝕜] H)) (x y : H)
  proof: u.val.inner_map_map_of_mem_unitary u.property x y

中文:
定理 inner_map_map
  条件: (u : unitary (H ->L[𝕜] H)) (x y : H)
  证明: u.val.inner_map_map_of_mem_unitary u.property x y

Depends on / 依赖: inner_map_map_of_mem_unitary, property, u.property, u.val.inner_map_map_of_mem_unitary
-/
theorem inner_map_map (u : unitary (H ->L[𝕜] H)) (x y : H) :
    ⟪(u : H ->L[𝕜] H) x, (u : H ->L[𝕜] H) y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  u.val.inner_map_map_of_mem_unitary u.property x y

/--
Definition of `linearIsometryEquiv` / `linearIsometryEquiv` 的定义

English:
definition linearIsometryEquiv
  signature: : unitary (H ->L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H) where
  body: { (u : H ->L[𝕜] H) with
      norm_map' := norm_map u
      invFun := ↑(star u)
      left_inv := fun x => congr($(star_mul_self u).val x)
      right_inv := fun x => congr($(mul_star_self u).val x) }
  invFun e :=
    { val := e
      property := by
        let e' : (H ->L[𝕜] H)ˣ :=
          { val := (e : H ->L[𝕜] H)
            inv := (e.symm : H ->L[𝕜] H)
            val_inv := by ext; simp
            inv_val := by ext; simp }
exact IsUnit.mem_unitary_of_star_mul_self ⟨e', rfl⟩
          (e : H ->L[𝕜] H).norm_map_iff_adjoint_comp_self.mp e.norm_map }
  map_mul' u v := by ext; rfl

@[simp]

中文:
定义 linearIsometryEquiv
  签名: : unitary (H ->L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H) where
  定义体: { (u : H ->L[𝕜] H) with
      norm_map' := norm_map u
      invFun := ↑(star u)
      left_inv := fun x => congr($(star_mul_self u).val x)
      right_inv := fun x => congr($(mul_star_self u).val x) }
  invFun e :=
    { val := e
      property := by
        let e' : (H ->L[𝕜] H)ˣ :=
          { val := (e : H ->L[𝕜] H)
            inv := (e.symm : H ->L[𝕜] H)
            val_inv := by ext; simp
            inv_val := by ext; simp }
exact IsUnit.mem_unitary_of_star_mul_self ⟨e', rfl⟩
          (e : H ->L[𝕜] H).norm_map_iff_adjoint_comp_self.mp e.norm_map }
  map_mul' u v := by ext; rfl

@[simp]

Depends on / 依赖: IsUnit, IsUnit.mem_unitary_of_star_mul_self, e.norm_map, e.symm, invFun, inv_val, left_inv, map_mul, mem_unitary_of_star_mul_self, mul_star_self, norm_map, norm_map_iff_adjoint_comp_self, norm_map_iff_adjoint_comp_self.mp, property, right_inv, star_mul_self, val_inv
-/
noncomputable def linearIsometryEquiv : unitary (H ->L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H) where
  toFun u :=
    { (u : H ->L[𝕜] H) with
      norm_map' := norm_map u
      invFun := ↑(star u)
      left_inv := fun x => congr($(star_mul_self u).val x)
      right_inv := fun x => congr($(mul_star_self u).val x) }
  invFun e :=
    { val := e
      property := by
        let e' : (H ->L[𝕜] H)ˣ :=
          { val := (e : H ->L[𝕜] H)
            inv := (e.symm : H ->L[𝕜] H)
            val_inv := by ext; simp
            inv_val := by ext; simp }
exact IsUnit.mem_unitary_of_star_mul_self ⟨e', rfl⟩
          (e : H ->L[𝕜] H).norm_map_iff_adjoint_comp_self.mp e.norm_map }
  map_mul' u v := by ext; rfl

@[simp]
/--
lemma `coe_linearIsometryEquiv_apply` / 引理 `coe_linearIsometryEquiv_apply`

English:
lemma coe_linearIsometryEquiv_apply
  given: (u : unitary (H ->L[𝕜] H))
  proof: rfl

@[simp]

中文:
引理 coe_linearIsometryEquiv_apply
  条件: (u : unitary (H ->L[𝕜] H))
  证明: rfl

@[simp]
-/
lemma coe_linearIsometryEquiv_apply (u : unitary (H ->L[𝕜] H)) :
    linearIsometryEquiv u = (u : H ->L[𝕜] H) :=
  rfl

@[simp]
/--
lemma `coe_symm_linearIsometryEquiv_apply` / 引理 `coe_symm_linearIsometryEquiv_apply`

English:
lemma coe_symm_linearIsometryEquiv_apply
  given: (e : H ≃ₗᵢ[𝕜] H)
  proof: rfl

中文:
引理 coe_symm_linearIsometryEquiv_apply
  条件: (e : H ≃ₗᵢ[𝕜] H)
  证明: rfl
-/
lemma coe_symm_linearIsometryEquiv_apply (e : H ≃ₗᵢ[𝕜] H) :
    linearIsometryEquiv.symm e = (e : H ->L[𝕜] H) :=
  rfl

/--
theorem `conjStarAlgEquiv_unitaryLinearIsometryEquiv` / 定理 `conjStarAlgEquiv_unitaryLinearIsometryEquiv`

English:
theorem conjStarAlgEquiv_unitaryLinearIsometryEquiv
  given: (u : unitary (H ->L[𝕜] H))
  proof: rfl

中文:
定理 conjStarAlgEquiv_unitaryLinearIsometryEquiv
  条件: (u : unitary (H ->L[𝕜] H))
  证明: rfl
-/
theorem conjStarAlgEquiv_unitaryLinearIsometryEquiv (u : unitary (H ->L[𝕜] H)) :
    (linearIsometryEquiv u).conjStarAlgEquiv = conjStarAlgAut 𝕜 _ u := rfl

/--
theorem `conjStarAlgAut_symm_unitaryLinearIsometryEquiv` / 定理 `conjStarAlgAut_symm_unitaryLinearIsometryEquiv`

English:
theorem conjStarAlgAut_symm_unitaryLinearIsometryEquiv
  given: (u : H ≃ₗᵢ[𝕜] H)
  proof: by
  simp [← conjStarAlgEquiv_unitaryLinearIsometryEquiv]

中文:
定理 conjStarAlgAut_symm_unitaryLinearIsometryEquiv
  条件: (u : H ≃ₗᵢ[𝕜] H)
  证明: by
  simp [← conjStarAlgEquiv_unitaryLinearIsometryEquiv]

Depends on / 依赖: conjStarAlgEquiv_unitaryLinearIsometryEquiv
-/
theorem conjStarAlgAut_symm_unitaryLinearIsometryEquiv (u : H ≃ₗᵢ[𝕜] H) :
    conjStarAlgAut 𝕜 (H ->L[𝕜] H) (linearIsometryEquiv.symm u) = u.conjStarAlgEquiv := by
  simp [← conjStarAlgEquiv_unitaryLinearIsometryEquiv]

end Unitary

end Unitary

section Matrix

open Matrix LinearMap

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
variable (v₁ : OrthonormalBasis n 𝕜 E) (v₂ : OrthonormalBasis m 𝕜 F)

/--
lemma `Matrix.toLin_conjTranspose` / 引理 `Matrix.toLin_conjTranspose`

English:
lemma Matrix.toLin_conjTranspose
  given: (A : Matrix m n 𝕜)
  proof: by
.mpr fun i j => ?_ refine eq_adjoint_iff_basis v₂.toBasis v₁.toBasis _ _
  simp_rw [toLin_self]
  simp [sum_inner, inner_smul_left, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp v₁.orthonormal, orthonormal_iff_ite.mp v₂.orthonormal]

中文:
引理 矩阵.toLin_conjTranspose
  条件: (A : 矩阵 m n 𝕜)
  证明: by
.mpr fun i j => ?_ refine eq_adjoint_iff_basis v₂.toBasis v₁.toBasis _ _
  simp_rw [toLin_self]
  simp [sum_inner, inner_smul_left, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp v₁.orthonormal, orthonormal_iff_ite.mp v₂.orthonormal]

Depends on / 依赖: eq_adjoint_iff_basis, inner_smul_left, inner_smul_right, inner_sum, orthonormal, orthonormal_iff_ite, orthonormal_iff_ite.mp, simp_rw, sum_inner, toBasis, toLin_self
-/
lemma Matrix.toLin_conjTranspose (A : Matrix m n 𝕜) :
    toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A) := by
.mpr fun i j => ?_ refine eq_adjoint_iff_basis v₂.toBasis v₁.toBasis _ _
  simp_rw [toLin_self]
  simp [sum_inner, inner_smul_left, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp v₁.orthonormal, orthonormal_iff_ite.mp v₂.orthonormal]

/--
lemma `LinearMap.toMatrix_adjoint` / 引理 `LinearMap.toMatrix_adjoint`

English:
lemma LinearMap.toMatrix_adjoint
  given: (f : E ->ₗ[𝕜] F)
  proof: .injective by simp [toLin_conjTranspose] toLin v₂.toBasis v₁.toBasis

中文:
引理 线性映射.toMatrix_adjoint
  条件: (f : E ->ₗ[𝕜] F)
  证明: .injective by simp [toLin_conjTranspose] toLin v₂.toBasis v₁.toBasis

Depends on / 依赖: injective, toBasis, toLin_conjTranspose
-/
lemma LinearMap.toMatrix_adjoint (f : E ->ₗ[𝕜] F) :
    toMatrix v₂.toBasis v₁.toBasis (adjoint f) = (toMatrix v₁.toBasis v₂.toBasis f)ᴴ :=
.injective by simp [toLin_conjTranspose] toLin v₂.toBasis v₁.toBasis

/-- The star algebra equivalence between the linear endomorphisms of finite-dimensional inner
product space and square matrices induced by the choice of an orthonormal basis. -/
@[simps]
/--
Definition of `LinearMap.toMatrixOrthonormal` / `LinearMap.toMatrixOrthonormal` 的定义

English:
definition LinearMap.toMatrixOrthonormal
  signature: : (E ->ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜
  body: { LinearMap.toMatrix v₁.toBasis v₁.toBasis with
    map_mul' := LinearMap.toMatrix_mul v₁.toBasis
    map_star' := LinearMap.toMatrix_adjoint v₁ v₁ }

中文:
定义 线性映射.toMatrixOrthonormal
  签名: : (E ->ₗ[𝕜] E) ≃⋆ₐ[𝕜] 矩阵 n n 𝕜
  定义体: { LinearMap.toMatrix v₁.toBasis v₁.toBasis with
    map_mul' := LinearMap.toMatrix_mul v₁.toBasis
    map_star' := LinearMap.toMatrix_adjoint v₁ v₁ }

Depends on / 依赖: LinearMap, LinearMap.toMatrix, LinearMap.toMatrix_adjoint, LinearMap.toMatrix_mul, map_mul, map_star, toBasis, toMatrix, toMatrix_adjoint, toMatrix_mul
-/
def LinearMap.toMatrixOrthonormal : (E ->ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  { LinearMap.toMatrix v₁.toBasis v₁.toBasis with
    map_mul' := LinearMap.toMatrix_mul v₁.toBasis
    map_star' := LinearMap.toMatrix_adjoint v₁ v₁ }

/--
lemma `LinearMap.toMatrixOrthonormal_apply_apply` / 引理 `LinearMap.toMatrixOrthonormal_apply_apply`

English:
lemma LinearMap.toMatrixOrthonormal_apply_apply
  given: (f : E ->ₗ[𝕜] E) (i j : n)
  proof: calc
    _ = v₁.repr (f (v₁ j)) i := f.toMatrix_apply ..
    _ = ⟪v₁ i, f (v₁ j)⟫_𝕜 := v₁.repr_apply_apply ..

中文:
引理 线性映射.toMatrixOrthonormal_apply_apply
  条件: (f : E ->ₗ[𝕜] E) (i j : n)
  证明: calc
    _ = v₁.repr (f (v₁ j)) i := f.toMatrix_apply ..
    _ = ⟪v₁ i, f (v₁ j)⟫_𝕜 := v₁.repr_apply_apply ..

Depends on / 依赖: f.toMatrix_apply, repr_apply_apply, toMatrix_apply
-/
lemma LinearMap.toMatrixOrthonormal_apply_apply (f : E ->ₗ[𝕜] E) (i j : n) :
    toMatrixOrthonormal v₁ f i j = ⟪v₁ i, f (v₁ j)⟫_𝕜 :=
  calc
    _ = v₁.repr (f (v₁ j)) i := f.toMatrix_apply ..
    _ = ⟪v₁ i, f (v₁ j)⟫_𝕜 := v₁.repr_apply_apply ..

/--
lemma `LinearMap.toMatrixOrthonormal_reindex` / 引理 `LinearMap.toMatrixOrthonormal_reindex`

English:
lemma LinearMap.toMatrixOrthonormal_reindex
  given: (e : n ≃ m) (f : E ->ₗ[𝕜] E)
  proof: Matrix.ext fun i j =>
    calc toMatrixOrthonormal (v₁.reindex e) f i j
      _ = (v₁.reindex e).repr (f (v₁.reindex e j)) i := f.toMatrix_apply ..
      _ = v₁.repr (f (v₁ (e.symm j))) (e.symm i) := by simp
      _ = toMatrixOrthonormal v₁ f (e.symm i) (e.symm j) := Eq.symm (f.toMatrix_apply ..)

中文:
引理 线性映射.toMatrixOrthonormal_reindex
  条件: (e : n ≃ m) (f : E ->ₗ[𝕜] E)
  证明: Matrix.ext fun i j =>
    calc toMatrixOrthonormal (v₁.reindex e) f i j
      _ = (v₁.reindex e).repr (f (v₁.reindex e j)) i := f.toMatrix_apply ..
      _ = v₁.repr (f (v₁ (e.symm j))) (e.symm i) := by simp
      _ = toMatrixOrthonormal v₁ f (e.symm i) (e.symm j) := Eq.symm (f.toMatrix_apply ..)

Depends on / 依赖: Eq.symm, Matrix, Matrix.ext, e.symm, f.toMatrix_apply, reindex, toMatrixOrthonormal, toMatrix_apply
-/
lemma LinearMap.toMatrixOrthonormal_reindex (e : n ≃ m) (f : E ->ₗ[𝕜] E) :
    toMatrixOrthonormal (v₁.reindex e) f = (toMatrixOrthonormal v₁ f).reindex e e :=
  Matrix.ext fun i j =>
    calc toMatrixOrthonormal (v₁.reindex e) f i j
      _ = (v₁.reindex e).repr (f (v₁.reindex e j)) i := f.toMatrix_apply ..
      _ = v₁.repr (f (v₁ (e.symm j))) (e.symm i) := by simp
      _ = toMatrixOrthonormal v₁ f (e.symm i) (e.symm j) := Eq.symm (f.toMatrix_apply ..)

open scoped ComplexConjugate

/--
theorem `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` / 定理 `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

English:
theorem Matrix.toEuclideanLin_conjTranspose_eq_adjoint
  given: (A : Matrix m n 𝕜)
  proof: A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)

中文:
定理 矩阵.toEuclideanLin_conjTranspose_eq_adjoint
  条件: (A : 矩阵 m n 𝕜)
  证明: A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)

Depends on / 依赖: A.toLin_conjTranspose, EuclideanSpace, EuclideanSpace.basisFun, basisFun, toLin_conjTranspose
-/
theorem Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = A.toEuclideanLin.adjoint :=
  A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)

end Matrix

@[simp]
/--
theorem `LinearIsometry.adjoint_comp_self` / 定理 `LinearIsometry.adjoint_comp_self`

English:
theorem LinearIsometry.adjoint_comp_self
  statement: {E E' : Type*}
  proof: f.toContinuousLinearMap.isometry_iff_adjoint_comp_self.mp f.isometry

中文:
定理 线性等距.adjoint_comp_self
  结论: {E E' : 类型}
  证明: f.toContinuousLinearMap.isometry_iff_adjoint_comp_self.mp f.isometry

Depends on / 依赖: f.isometry, f.toContinuousLinearMap.isometry_iff_adjoint_comp_self.mp, isometry, isometry_iff_adjoint_comp_self, toContinuousLinearMap
-/
theorem LinearIsometry.adjoint_comp_self {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E'] (f : E ->ₗᵢ[𝕜] E') :
    f.toContinuousLinearMap.adjoint ∘L f.toContinuousLinearMap = 1 :=
  f.toContinuousLinearMap.isometry_iff_adjoint_comp_self.mp f.isometry

/-- A version of `LinearIsometry.adjoint_comp_self` in terms of `LinearMap.adjoint`. -/
@[simp]
/--
theorem `LinearIsometry.adjoint_comp_self'` / 定理 `LinearIsometry.adjoint_comp_self'`

English:
theorem LinearIsometry.adjoint_comp_self'
  statement: {E E' : Type*}
  proof: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 E'
  ext x
  exact congr($(f.adjoint_comp_self) x)

中文:
定理 线性等距.adjoint_comp_self'
  结论: {E E' : 类型}
  证明: by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 E'
  ext x
  exact congr($(f.adjoint_comp_self) x)

Depends on / 依赖: FiniteDimensional, FiniteDimensional.complete, adjoint_comp_self, complete, f.adjoint_comp_self
-/
theorem LinearIsometry.adjoint_comp_self' {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] (f : E ->ₗᵢ[𝕜] E') :
    f.adjoint ∘ₗ f.toLinearMap = LinearMap.id := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 E'
  ext x
  exact congr($(f.adjoint_comp_self) x)
