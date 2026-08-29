/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The span of a single vector

The equivalence of `𝕜` and `𝕜 • x` for `x ≠ 0` are defined as continuous linear equivalence and
isometry.

## Main definitions

* `ContinuousLinearEquiv.toSpanNonzeroSingleton`: The continuous linear equivalence between `𝕜` and
  `𝕜 • x` for `x ≠ 0`.
* `LinearIsometryEquiv.toSpanUnitSingleton`: For `‖x‖ = 1` the continuous linear equivalence is a
  linear isometry equivalence.

-/

@[expose] public section

variable {𝕜 E : Type*}

namespace LinearMap

variable (𝕜)

section Seminormed

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/--
theorem `toSpanSingleton_homothety` / 定理 `toSpanSingleton_homothety`

English:
theorem toSpanSingleton_homothety
  given: (x : E) (c : 𝕜)
  proof: by
  rw [mul_comm]
  exact norm_smul _ _

中文:
定理 toSpanSingleton_homothety
  条件: (x : E) (c : 𝕜)
  证明: by
  rw [mul_comm]
  exact norm_smul _ _

Depends on / 依赖: mul_comm, norm_smul
-/
theorem toSpanSingleton_homothety (x : E) (c : 𝕜) :
    ‖LinearMap.toSpanSingleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ := by
  rw [mul_comm]
  exact norm_smul _ _

end Seminormed

end LinearMap

namespace ContinuousLinearEquiv

variable (𝕜)

section Seminormed
variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/--
theorem `_root_.LinearEquiv.toSpanNonzeroSingleton_homothety` / 定理 `_root_.LinearEquiv.toSpanNonzeroSingleton_homothety`

English:
theorem _root_.LinearEquiv.toSpanNonzeroSingleton_homothety
  given: (x : E) (h : x != 0) (c : 𝕜)
  proof: LinearMap.toSpanSingleton_homothety _ _ _

中文:
定理 _root_.LinearEquiv.toSpanNonzeroSingleton_homothety
  条件: (x : E) (h : x != 0) (c : 𝕜)
  证明: LinearMap.toSpanSingleton_homothety _ _ _

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton_homothety, toSpanSingleton_homothety
-/
theorem _root_.LinearEquiv.toSpanNonzeroSingleton_homothety (x : E) (h : x != 0) (c : 𝕜) :
    ‖LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
  LinearMap.toSpanSingleton_homothety _ _ _

end Seminormed

section Normed
variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
continuous linear equivalence from `𝕜` to the span of `x`. -/
@[simps!]
/--
Definition of `toSpanNonzeroSingleton` / `toSpanNonzeroSingleton` 的定义

English:
definition toSpanNonzeroSingleton
  signature: (x : E) (h : x != 0)
  body: ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h)

中文:
定义 toSpanNonzeroSingleton
  签名: (x : E) (h : x != 0)
  定义体: ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h)

Depends on / 依赖: LinearEquiv, LinearEquiv.toSpanNonzeroSingleton, LinearEquiv.toSpanNonzeroSingleton_homothety, norm_pos_iff, norm_pos_iff.mpr, ofHomothety, toSpanNonzeroSingleton, toSpanNonzeroSingleton_homothety
-/
noncomputable def toSpanNonzeroSingleton (x : E) (h : x != 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
  ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h)

/--
Definition of `coord` / `coord` 的定义

English:
definition coord
  signature: (x : E) (h : x != 0)
  body: (toSpanNonzeroSingleton 𝕜 x h).symm

@[simp]

中文:
定义 coord
  签名: (x : E) (h : x != 0)
  定义体: (toSpanNonzeroSingleton 𝕜 x h).symm

@[simp]

Depends on / 依赖: toSpanNonzeroSingleton
-/
noncomputable def coord (x : E) (h : x != 0) : StrongDual 𝕜 (𝕜 ∙ x) :=
  (toSpanNonzeroSingleton 𝕜 x h).symm

@[simp]
/--
theorem `coe_toSpanNonzeroSingleton_symm` / 定理 `coe_toSpanNonzeroSingleton_symm`

English:
theorem coe_toSpanNonzeroSingleton_symm
  given: {x : E} (h : x != 0)
  proof: rfl

@[simp]

中文:
定理 coe_toSpanNonzeroSingleton_symm
  条件: {x : E} (h : x != 0)
  证明: rfl

@[simp]
-/
theorem coe_toSpanNonzeroSingleton_symm {x : E} (h : x != 0) :
    ⇑(toSpanNonzeroSingleton 𝕜 x h).symm = coord 𝕜 x h :=
  rfl

@[simp]
/--
theorem `coord_toSpanNonzeroSingleton` / 定理 `coord_toSpanNonzeroSingleton`

English:
theorem coord_toSpanNonzeroSingleton
  given: {x : E} (h : x != 0) (c : 𝕜)
  proof: (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c

@[simp]

中文:
定理 coord_toSpanNonzeroSingleton
  条件: {x : E} (h : x != 0) (c : 𝕜)
  证明: (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c

@[simp]

Depends on / 依赖: symm_apply_apply, toSpanNonzeroSingleton
-/
theorem coord_toSpanNonzeroSingleton {x : E} (h : x != 0) (c : 𝕜) :
    coord 𝕜 x h (toSpanNonzeroSingleton 𝕜 x h c) = c :=
  (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c

@[simp]
/--
theorem `toSpanNonzeroSingleton_coord` / 定理 `toSpanNonzeroSingleton_coord`

English:
theorem toSpanNonzeroSingleton_coord
  given: {x : E} (h : x != 0) (y : 𝕜 ∙ x)
  proof: (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y

@[simp]

中文:
定理 toSpanNonzeroSingleton_coord
  条件: {x : E} (h : x != 0) (y : 𝕜 ∙ x)
  证明: (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y

@[simp]

Depends on / 依赖: apply_symm_apply, toSpanNonzeroSingleton
-/
theorem toSpanNonzeroSingleton_coord {x : E} (h : x != 0) (y : 𝕜 ∙ x) :
    toSpanNonzeroSingleton 𝕜 x h (coord 𝕜 x h y) = y :=
  (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y

@[simp]
/--
theorem `coord_self` / 定理 `coord_self`

English:
theorem coord_self
  given: (x : E) (h : x != 0)
  proof: LinearEquiv.coord_self 𝕜 E x h

中文:
定理 coord_self
  条件: (x : E) (h : x != 0)
  证明: LinearEquiv.coord_self 𝕜 E x h

Depends on / 依赖: LinearEquiv, LinearEquiv.coord_self, coord_self
-/
theorem coord_self (x : E) (h : x != 0) :
    (coord 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
  LinearEquiv.coord_self 𝕜 E x h

end Normed

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/--
Definition of `toSpanUnitSingleton` / `toSpanUnitSingleton` 的定义

English:
definition toSpanUnitSingleton
  signature: (x : E) (hx : ‖x‖ = 1)
  body: LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)
  norm_map' := by
    intro
    rw [LinearEquiv.toSpanNonzeroSingleton_homothety]; rw [hx]; rw [one_mul]

中文:
定义 toSpanUnitSingleton
  签名: (x : E) (hx : ‖x‖ = 1)
  定义体: LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)
  norm_map' := by
    intro
    rw [LinearEquiv.toSpanNonzeroSingleton_homothety]; rw [hx]; rw [one_mul]

Depends on / 依赖: LinearEquiv, LinearEquiv.toSpanNonzeroSingleton, toSpanNonzeroSingleton
-/
noncomputable def toSpanUnitSingleton (x : E) (hx : ‖x‖ = 1) :
    𝕜 ≃ₗᵢ[𝕜] 𝕜 ∙ x where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)
  norm_map' := by
    intro
    rw [LinearEquiv.toSpanNonzeroSingleton_homothety]; rw [hx]; rw [one_mul]

/--
theorem `toSpanUnitSingleton_apply` / 定理 `toSpanUnitSingleton_apply`

English:
theorem toSpanUnitSingleton_apply
  given: (x : E) (hx : ‖x‖ = 1) (r : 𝕜)
  proof: by
  rfl

中文:
定理 toSpanUnitSingleton_apply
  条件: (x : E) (hx : ‖x‖ = 1) (r : 𝕜)
  证明: by
  rfl
-/
@[simp] theorem toSpanUnitSingleton_apply (x : E) (hx : ‖x‖ = 1) (r : 𝕜) :
    toSpanUnitSingleton x hx r = (⟨r • x, by aesop⟩ : 𝕜 ∙ x) := by
  rfl

end LinearIsometryEquiv
