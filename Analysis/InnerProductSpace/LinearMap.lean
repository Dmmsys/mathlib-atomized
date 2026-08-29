/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Linear maps on inner product spaces

This file studies linear maps on inner product spaces.

## Main results

- We define `innerSL` as the inner product bundled as a continuous sesquilinear map
- We prove a general polarization identity for linear maps (`inner_map_polarization`)
- We show that a linear map preserving the inner product is an isometry
  (`LinearMap.isometryOfInner`) and conversely an isometry preserves the inner product
  (`LinearIsometry.inner_map_map`).

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Complex_Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace Complex V]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inner_map_polarization` / 定理 `inner_map_polarization`

English:
theorem inner_map_polarization
  given: (T : V ->ₗ[Complex] V) (x y : V)
  proof: by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

中文:
定理 inner_map_polarization
  条件: (T : V ->ₗ[复形] V) (x y : V)
  证明: by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

Depends on / 依赖: Complex.I_sq, Complex.conj_I, I_sq, conj_I, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, map_add, map_smul, map_sub, mul_add, mul_assoc, mul_neg, mul_sub, neg_neg, neg_one_mul, one_mul
-/
theorem inner_map_polarization (T : V ->ₗ[Complex] V) (x y : V) :
    ⟪T y, x⟫_Complex =
      (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_Complex +
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_Complex -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_Complex) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inner_map_polarization'` / 定理 `inner_map_polarization'`

English:
theorem inner_map_polarization'
  given: (T : V ->ₗ[Complex] V) (x y : V)
  proof: by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

中文:
定理 inner_map_polarization'
  条件: (T : V ->ₗ[复形] V) (x y : V)
  证明: by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

Depends on / 依赖: Complex.I_sq, Complex.conj_I, I_sq, conj_I, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, map_add, map_smul, map_sub, mul_add, mul_assoc, mul_neg, mul_sub, neg_neg, neg_one_mul, one_mul
-/
theorem inner_map_polarization' (T : V ->ₗ[Complex] V) (x y : V) :
    ⟪T x, y⟫_Complex =
      (⟪T (x + y), x + y⟫_Complex - ⟪T (x - y), x - y⟫_Complex -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_Complex +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_Complex) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

end Complex_Seminormed

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Complex V]

/--
theorem `inner_map_self_eq_zero` / 定理 `inner_map_self_eq_zero`

English:
theorem inner_map_self_eq_zero
  given: (T : V ->ₗ[Complex] V)
  statement: (forall x : V, ⟪T x, x⟫_Complex = 0) ↔ T = 0
  proof: by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply]; rw [← @inner_self_eq_zero Complex V]; rw [inner_map_polarization]
    simp only [hT]
    simp
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

中文:
定理 inner_map_self_eq_zero
  条件: (T : V ->ₗ[复形] V)
  结论: (对任意 x : V, ⟪T x, x⟫_Complex = 0) ↔ T = 0
  证明: by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply]; rw [← @inner_self_eq_zero Complex V]; rw [inner_map_polarization]
    simp only [hT]
    simp
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, inner_map_polarization, inner_self_eq_zero, inner_zero_left, zero_apply
-/
theorem inner_map_self_eq_zero (T : V ->ₗ[Complex] V) : (forall x : V, ⟪T x, x⟫_Complex = 0) ↔ T = 0 := by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply]; rw [← @inner_self_eq_zero Complex V]; rw [inner_map_polarization]
    simp only [hT]
    simp
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

/--
theorem `ext_inner_map` / 定理 `ext_inner_map`

English:
theorem ext_inner_map
  given: (S T : V ->ₗ[Complex] V)
  statement: (forall x : V, ⟪S x, x⟫_Complex = ⟪T x, x⟫_Complex) ↔ S = T
  proof: by
  rw [← sub_eq_zero]; rw [← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply]; rw [inner_sub_left]; rw [sub_eq_zero]

中文:
定理 ext_inner_map
  条件: (S T : V ->ₗ[复形] V)
  结论: (对任意 x : V, ⟪S x, x⟫_Complex = ⟪T x, x⟫_Complex) ↔ S = T
  证明: by
  rw [← sub_eq_zero]; rw [← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply]; rw [inner_sub_left]; rw [sub_eq_zero]

Depends on / 依赖: LinearMap, LinearMap.sub_apply, forall_congr, inner_map_self_eq_zero, inner_sub_left, sub_apply, sub_eq_zero
-/
theorem ext_inner_map (S T : V ->ₗ[Complex] V) : (forall x : V, ⟪S x, x⟫_Complex = ⟪T x, x⟫_Complex) ↔ S = T := by
  rw [← sub_eq_zero]; rw [← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply]; rw [inner_sub_left]; rw [sub_eq_zero]

end Complex

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']

set_option backward.isDefEq.respectTransparency false in
/-- A linear isometry preserves the inner product. -/
@[simp]
/--
theorem `LinearIsometry.inner_map_map` / 定理 `LinearIsometry.inner_map_map`

English:
theorem LinearIsometry.inner_map_map
  given: (f : E ->ₗᵢ[𝕜] E') (x y : E)
  statement: ⟪f x, f y⟫ = ⟪x, y⟫
  proof: by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

中文:
定理 线性等距.inner_map_map
  条件: (f : E ->ₗᵢ[𝕜] E') (x y : E)
  结论: ⟪f x, f y⟫ = ⟪x, y⟫
  证明: by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

Depends on / 依赖: f.norm_map, inner_eq_sum_norm_sq_div_four, norm_map
-/
theorem LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
/--
theorem `LinearIsometryEquiv.inner_map_map` / 定理 `LinearIsometryEquiv.inner_map_map`

English:
theorem LinearIsometryEquiv.inner_map_map
  given: (f : E ≃ₗᵢ[𝕜] E') (x y : E)
  statement: ⟪f x, f y⟫ = ⟪x, y⟫
  proof: f.toLinearIsometry.inner_map_map x y

中文:
定理 线性等距等价.inner_map_map
  条件: (f : E ≃ₗᵢ[𝕜] E') (x y : E)
  结论: ⟪f x, f y⟫ = ⟪x, y⟫
  证明: f.toLinearIsometry.inner_map_map x y

Depends on / 依赖: f.toLinearIsometry.inner_map_map, inner_map_map, toLinearIsometry
-/
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y

/--
theorem `LinearIsometryEquiv.inner_map_eq_flip` / 定理 `LinearIsometryEquiv.inner_map_eq_flip`

English:
theorem LinearIsometryEquiv.inner_map_eq_flip
  given: (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E')
  proof: by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]

中文:
定理 线性等距等价.inner_map_eq_flip
  条件: (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E')
  证明: by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]

Depends on / 依赖: apply_symm_apply, conv_lhs, f.apply_symm_apply, f.inner_map_map, inner_map_map
-/
theorem LinearIsometryEquiv.inner_map_eq_flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') :
    ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜 := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]

/--
Definition of `LinearMap.isometryOfInner` / `LinearMap.isometryOfInner` 的定义

English:
definition LinearMap.isometryOfInner
  signature: (f : E ->ₗ[𝕜] E') (h : forall x y, ⟪f x, f y⟫ = ⟪x, y⟫)
  body: ⟨f, fun x => by simp only [@norm_eq_sqrt_re_inner 𝕜, h]⟩

@[simp]

中文:
定义 线性映射.isometryOfInner
  签名: (f : E ->ₗ[𝕜] E') (h : 对任意 x y, ⟪f x, f y⟫ = ⟪x, y⟫)
  定义体: ⟨f, fun x => by simp only [@norm_eq_sqrt_re_inner 𝕜, h]⟩

@[simp]

Depends on / 依赖: norm_eq_sqrt_re_inner
-/
def LinearMap.isometryOfInner (f : E ->ₗ[𝕜] E') (h : forall x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ->ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by simp only [@norm_eq_sqrt_re_inner 𝕜, h]⟩

@[simp]
/--
theorem `LinearMap.coe_isometryOfInner` / 定理 `LinearMap.coe_isometryOfInner`

English:
theorem LinearMap.coe_isometryOfInner
  given: (f : E ->ₗ[𝕜] E') (h)
  statement: ⇑(f.isometryOfInner h) = f
  proof: rfl

@[simp]

中文:
定理 线性映射.coe_isometryOfInner
  条件: (f : E ->ₗ[𝕜] E') (h)
  结论: ⇑(f.isometryOfInner h) = f
  证明: rfl

@[simp]
-/
theorem LinearMap.coe_isometryOfInner (f : E ->ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
/--
theorem `LinearMap.isometryOfInner_toLinearMap` / 定理 `LinearMap.isometryOfInner_toLinearMap`

English:
theorem LinearMap.isometryOfInner_toLinearMap
  given: (f : E ->ₗ[𝕜] E') (h)
  proof: rfl

中文:
定理 线性映射.isometryOfInner_toLinearMap
  条件: (f : E ->ₗ[𝕜] E') (h)
  证明: rfl
-/
theorem LinearMap.isometryOfInner_toLinearMap (f : E ->ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearMap = f :=
  rfl

/--
Definition of `LinearEquiv.isometryOfInner` / `LinearEquiv.isometryOfInner` 的定义

English:
definition LinearEquiv.isometryOfInner
  signature: (f : E ≃ₗ[𝕜] E') (h : forall x y, ⟪f x, f y⟫ = ⟪x, y⟫)
  body: ⟨f, ((f : E ->ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]

中文:
定义 线性等价.isometryOfInner
  签名: (f : E ≃ₗ[𝕜] E') (h : 对任意 x y, ⟪f x, f y⟫ = ⟪x, y⟫)
  定义体: ⟨f, ((f : E ->ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]

Depends on / 依赖: isometryOfInner, norm_map
-/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : forall x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E ->ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]
/--
theorem `LinearEquiv.coe_isometryOfInner` / 定理 `LinearEquiv.coe_isometryOfInner`

English:
theorem LinearEquiv.coe_isometryOfInner
  given: (f : E ≃ₗ[𝕜] E') (h)
  statement: ⇑(f.isometryOfInner h) = f
  proof: rfl

@[simp]

中文:
定理 线性等价.coe_isometryOfInner
  条件: (f : E ≃ₗ[𝕜] E') (h)
  结论: ⇑(f.isometryOfInner h) = f
  证明: rfl

@[simp]
-/
theorem LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
/--
theorem `LinearEquiv.isometryOfInner_toLinearEquiv` / 定理 `LinearEquiv.isometryOfInner_toLinearEquiv`

English:
theorem LinearEquiv.isometryOfInner_toLinearEquiv
  given: (f : E ≃ₗ[𝕜] E') (h)
  proof: rfl

中文:
定理 线性等价.isometryOfInner_toLinearEquiv
  条件: (f : E ≃ₗ[𝕜] E') (h)
  证明: rfl
-/
theorem LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearEquiv = f :=
  rfl

/--
theorem `LinearMap.norm_map_iff_inner_map_map` / 定理 `LinearMap.norm_map_iff_inner_map_map`

English:
theorem LinearMap.norm_map_iff_inner_map_map
  statement: {F : Type*} [FunLike F E E'] [LinearMapClass F 𝕜 E E']
  proof: ⟨({ toLinearMap := LinearMapClass.linearMap f, norm_map' := · : E ->ₗᵢ[𝕜] E' }.inner_map_map),
    (LinearMapClass.linearMap f |>.isometryOfInner · |>.norm_map)⟩

中文:
定理 线性映射.norm_map_iff_inner_map_map
  结论: {F : 类型} [函数状 F E E'] [线性映射类 F 𝕜 E E']
  证明: ⟨({ toLinearMap := LinearMapClass.linearMap f, norm_map' := · : E ->ₗᵢ[𝕜] E' }.inner_map_map),
    (LinearMapClass.linearMap f |>.isometryOfInner · |>.norm_map)⟩

Depends on / 依赖: LinearMapClass, LinearMapClass.linearMap, inner_map_map, isometryOfInner, linearMap, norm_map, toLinearMap
-/
theorem LinearMap.norm_map_iff_inner_map_map {F : Type*} [FunLike F E E'] [LinearMapClass F 𝕜 E E']
    (f : F) : (forall x, ‖f x‖ = ‖x‖) ↔ (forall x y, ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜) :=
  ⟨({ toLinearMap := LinearMapClass.linearMap f, norm_map' := · : E ->ₗᵢ[𝕜] E' }.inner_map_map),
    (LinearMapClass.linearMap f |>.isometryOfInner · |>.norm_map)⟩

end

variable (𝕜)

/--
Definition of `innerSL` / `innerSL` 的定义

English:
definition innerSL
  signature: : E ->L⋆[𝕜] E ->L[𝕜] 𝕜
  body: LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply_apply]

@[simp]

中文:
定义 innerSL
  签名: : E ->L⋆[𝕜] E ->L[𝕜] 𝕜
  定义体: LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, norm_inner_le_norm, one_mul
-/
def innerSL : E ->L⋆[𝕜] E ->L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply_apply]

@[simp]
/--
theorem `coe_innerSL_apply` / 定理 `coe_innerSL_apply`

English:
theorem coe_innerSL_apply
  given: (v : E)
  statement: ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫
  proof: rfl

中文:
定理 coe_innerSL_apply
  条件: (v : E)
  结论: ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫
  证明: rfl
-/
theorem coe_innerSL_apply (v : E) : ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

/--
theorem `innerSL_apply_apply` / 定理 `innerSL_apply_apply`

English:
theorem innerSL_apply_apply
  given: (v w : E)
  statement: innerSL 𝕜 v w = ⟪v, w⟫
  proof: rfl

中文:
定理 innerSL_apply_apply
  条件: (v w : E)
  结论: innerSL 𝕜 v w = ⟪v, w⟫
  证明: rfl
-/
theorem innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫ :=
  rfl

/--
theorem `ContinuousLinearMap.toLinearMap_innerSL_apply` / 定理 `ContinuousLinearMap.toLinearMap_innerSL_apply`

English:
theorem ContinuousLinearMap.toLinearMap_innerSL_apply
  given: (v : E)
  proof: rfl

中文:
定理 连续线性映射.toLinearMap_innerSL_apply
  条件: (v : E)
  证明: rfl
-/
@[simp] theorem ContinuousLinearMap.toLinearMap_innerSL_apply (v : E) :
    (innerSL 𝕜 v).toLinearMap = innerₛₗ 𝕜 v := rfl

/--
Definition of `innerSLFlip` / `innerSLFlip` 的定义

English:
definition innerSLFlip
  signature: : E ->L[𝕜] E ->L⋆[𝕜] 𝕜
  body: @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)

@[simp]

中文:
定义 innerSLFlip
  签名: : E ->L[𝕜] E ->L⋆[𝕜] 𝕜
  定义体: @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip, RingHom, RingHom.id, innerSL, starRingEnd
-/
def innerSLFlip : E ->L[𝕜] E ->L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)

@[simp]
/--
theorem `innerSLFlip_apply_apply` / 定理 `innerSLFlip_apply_apply`

English:
theorem innerSLFlip_apply_apply
  given: (x y : E)
  statement: innerSLFlip 𝕜 x y = ⟪y, x⟫
  proof: rfl

中文:
定理 innerSLFlip_apply_apply
  条件: (x y : E)
  结论: innerSLFlip 𝕜 x y = ⟪y, x⟫
  证明: rfl
-/
theorem innerSLFlip_apply_apply (x y : E) : innerSLFlip 𝕜 x y = ⟪y, x⟫ :=
  rfl

variable (F) in
/--
lemma `flip_innerSL_real` / 引理 `flip_innerSL_real`

English:
lemma flip_innerSL_real
  statement: (innerSL Real (E := F)).flip = innerSL Real (E := F)
  proof: by
  ext v w
  exact real_inner_comm _ _

中文:
引理 flip_innerSL_real
  结论: (innerSL 实数 (E := F)).flip = innerSL 实数 (E := F)
  证明: by
  ext v w
  exact real_inner_comm _ _
-/
@[simp] lemma flip_innerSL_real : (innerSL Real (E := F)).flip = innerSL Real (E := F) := by
  ext v w
  exact real_inner_comm _ _

variable {𝕜}

namespace ContinuousLinearMap

variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

-- Note: odd and expensive build behavior is explicitly turned off using `noncomputable`
/--
Definition of `toSesqForm` / `toSesqForm` 的定义

English:
definition toSesqForm
  signature: : (E ->L[𝕜] E') ->L[𝕜] E' ->L⋆[𝕜] E ->L[𝕜] 𝕜
  body: (ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' ->L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)

@[simp]

中文:
定义 toSesqForm
  签名: : (E ->L[𝕜] E') ->L[𝕜] E' ->L⋆[𝕜] E ->L[𝕜] 𝕜
  定义体: (ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' ->L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compSL, ContinuousLinearMap.flip, RingHom, RingHom.id, compSL, innerSLFlip, starRingEnd, toContinuousLinearEquiv
-/
noncomputable def toSesqForm : (E ->L[𝕜] E') ->L[𝕜] E' ->L⋆[𝕜] E ->L[𝕜] 𝕜 :=
  (ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' ->L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)

@[simp]
/--
theorem `toSesqForm_apply_coe` / 定理 `toSesqForm_apply_coe`

English:
theorem toSesqForm_apply_coe
  given: (f : E ->L[𝕜] E') (x : E')
  statement: toSesqForm f x = (innerSL 𝕜 x).comp f
  proof: rfl

中文:
定理 toSesqForm_apply_coe
  条件: (f : E ->L[𝕜] E') (x : E')
  结论: toSesqForm f x = (innerSL 𝕜 x).comp f
  证明: rfl
-/
theorem toSesqForm_apply_coe (f : E ->L[𝕜] E') (x : E') : toSesqForm f x = (innerSL 𝕜 x).comp f :=
  rfl

/--
theorem `toSesqForm_apply_norm_le` / 定理 `toSesqForm_apply_norm_le`

English:
theorem toSesqForm_apply_norm_le
  given: {f : E ->L[𝕜] E'} {v : E'}
  statement: ‖toSesqForm f v‖ <= ‖f‖ * ‖v‖
  proof: by
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  have h₁ : ‖f x‖ <= ‖f‖ * ‖x‖ := le_opNorm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ <= ‖v‖ * ‖f x‖ := h₂
    _ <= ‖v‖ * (‖f‖ * ‖x‖) := by gcongr
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring

中文:
定理 toSesqForm_apply_norm_le
  条件: {f : E ->L[𝕜] E'} {v : E'}
  结论: ‖toSesqForm f v‖ <= ‖f‖ * ‖v‖
  证明: by
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  have h₁ : ‖f x‖ <= ‖f‖ * ‖x‖ := le_opNorm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ <= ‖v‖ * ‖f x‖ := h₂
    _ <= ‖v‖ * (‖f‖ * ‖x‖) := by gcongr
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring

Depends on / 依赖: le_opNorm, norm_inner_le_norm, opNorm_le_bound
-/
theorem toSesqForm_apply_norm_le {f : E ->L[𝕜] E'} {v : E'} : ‖toSesqForm f v‖ <= ‖f‖ * ‖v‖ := by
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  have h₁ : ‖f x‖ <= ‖f‖ * ‖x‖ := le_opNorm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ <= ‖v‖ * ‖f x‖ := h₂
    _ <= ‖v‖ * (‖f‖ * ‖x‖) := by gcongr
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring

end ContinuousLinearMap

variable (𝕜)

/-- `innerSL` is an isometry. Note that the associated `LinearIsometry` is defined in
`InnerProductSpace.Dual` as `toDualMap`. -/
@[simp]
/--
theorem `innerSL_apply_norm` / 定理 `innerSL_apply_norm`

English:
theorem innerSL_apply_norm
  given: (x : E)
  statement: ‖innerSL 𝕜 x‖ = ‖x‖
  proof: by
  refine
    le_antisymm ((innerSL 𝕜 x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) ?_
  rcases (norm_nonneg x).eq_or_lt' with (h | h)
  · simp [h]
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : 𝕜)‖ := by
        rw [← sq]; rw [inner_self_eq_norm_sq_to_K]; rw [norm_pow]; rw [norm_ofReal]; rw [abs_norm]
      _ <= ‖innerSL 𝕜 x‖ * ‖x‖ := (innerSL 𝕜 x).le_opNorm _

中文:
定理 innerSL_apply_norm
  条件: (x : E)
  结论: ‖innerSL 𝕜 x‖ = ‖x‖
  证明: by
  refine
    le_antisymm ((innerSL 𝕜 x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) ?_
  rcases (norm_nonneg x).eq_or_lt' with (h | h)
  · simp [h]
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : 𝕜)‖ := by
        rw [← sq]; rw [inner_self_eq_norm_sq_to_K]; rw [norm_pow]; rw [norm_ofReal]; rw [abs_norm]
      _ <= ‖innerSL 𝕜 x‖ * ‖x‖ := (innerSL 𝕜 x).le_opNorm _

Depends on / 依赖: abs_norm, eq_or_lt, innerSL, inner_self_eq_norm_sq_to_K, le_antisymm, le_opNorm, norm_inner_le_norm, norm_nonneg, norm_ofReal, norm_pow, opNorm_le_bound
-/
theorem innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖ := by
  refine
    le_antisymm ((innerSL 𝕜 x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) ?_
  rcases (norm_nonneg x).eq_or_lt' with (h | h)
  · simp [h]
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : 𝕜)‖ := by
        rw [← sq]; rw [inner_self_eq_norm_sq_to_K]; rw [norm_pow]; rw [norm_ofReal]; rw [abs_norm]
      _ <= ‖innerSL 𝕜 x‖ * ‖x‖ := (innerSL 𝕜 x).le_opNorm _

/--
lemma `norm_innerSL_le` / 引理 `norm_innerSL_le`

English:
lemma norm_innerSL_le
  statement: ‖innerSL 𝕜 (E := E)‖ <= 1
  proof: ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

中文:
引理 norm_innerSL_le
  结论: ‖innerSL 𝕜 (E := E)‖ <= 1
  证明: ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)
-/
lemma norm_innerSL_le : ‖innerSL 𝕜 (E := E)‖ <= 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

end Norm_Seminormed

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}

/--
theorem `inner_map_complex` / 定理 `inner_map_complex`

English:
theorem inner_map_complex
  statement: [SeminormedAddCommGroup G] [InnerProductSpace Real G] (f : G ≃ₗᵢ[Real] Complex)
  proof: by rw [← Complex.inner, f.inner_map_map]

中文:
定理 inner_map_complex
  结论: [SeminormedAddComm群 G] [内积空间 实数 G] (f : G ≃ₗᵢ[实数] 复形)
  证明: by rw [← Complex.inner, f.inner_map_map]

Depends on / 依赖: Complex.inner, FiniteDimensional, FiniteDimensional.proper_real, NormedAddCommGroup, f.inner_map_map, inner_map_map, proper_real
-/
theorem inner_map_complex [SeminormedAddCommGroup G] [InnerProductSpace Real G] (f : G ≃ₗᵢ[Real] Complex)
    (x y : G) : ⟪x, y⟫_Real = (f y * conj (f x)).re := by rw [← Complex.inner, f.inner_map_map]

end RCLikeToReal

section ReApplyInnerSelf

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
Definition of `ContinuousLinearMap.reApplyInnerSelf` / `ContinuousLinearMap.reApplyInnerSelf` 的定义

English:
definition ContinuousLinearMap.reApplyInnerSelf
  signature: (T : E ->L[𝕜] E) (x : E)
  body: re ⟪T x, x⟫

中文:
定义 连续线性映射.reApplyInnerSelf
  签名: (T : E ->L[𝕜] E) (x : E)
  定义体: re ⟪T x, x⟫

Depends on / 依赖: FiniteDimensional, FiniteDimensional.proper, ProperSpace, nontriviality, of_locallyCompactSpace, of_locallyCompact_module, proper
-/
def ContinuousLinearMap.reApplyInnerSelf (T : E ->L[𝕜] E) (x : E) : Real :=
  re ⟪T x, x⟫

/--
theorem `ContinuousLinearMap.reApplyInnerSelf_apply` / 定理 `ContinuousLinearMap.reApplyInnerSelf_apply`

English:
theorem ContinuousLinearMap.reApplyInnerSelf_apply
  given: (T : E ->L[𝕜] E) (x : E)
  proof: rfl

中文:
定理 连续线性映射.reApplyInnerSelf_apply
  条件: (T : E ->L[𝕜] E) (x : E)
  证明: rfl
-/
theorem ContinuousLinearMap.reApplyInnerSelf_apply (T : E ->L[𝕜] E) (x : E) :
    T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl

end ReApplyInnerSelf

section ReApplyInnerSelf_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `ContinuousLinearMap.reApplyInnerSelf_continuous` / 定理 `ContinuousLinearMap.reApplyInnerSelf_continuous`

English:
theorem ContinuousLinearMap.reApplyInnerSelf_continuous
  given: (T : E ->L[𝕜] E)
  proof: reCLM.continuous.comp T.continuous.inner continuous_id

中文:
定理 连续线性映射.reApplyInnerSelf_continuous
  条件: (T : E ->L[𝕜] E)
  证明: reCLM.continuous.comp T.continuous.inner continuous_id

Depends on / 依赖: T.continuous.inner, continuous, continuous_id, reCLM.continuous.comp
-/
theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E ->L[𝕜] E) :
    Continuous T.reApplyInnerSelf :=
reCLM.continuous.comp T.continuous.inner continuous_id

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ContinuousLinearMap.reApplyInnerSelf_smul` / 定理 `ContinuousLinearMap.reApplyInnerSelf_smul`

English:
theorem ContinuousLinearMap.reApplyInnerSelf_smul
  given: (T : E ->L[𝕜] E) (x : E) {c : 𝕜}
  proof: by
  simp only [map_smul, ContinuousLinearMap.reApplyInnerSelf_apply, inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

中文:
定理 连续线性映射.reApplyInnerSelf_smul
  条件: (T : E ->L[𝕜] E) (x : E) {c : 𝕜}
  证明: by
  simp only [map_smul, ContinuousLinearMap.reApplyInnerSelf_apply, inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

Depends on / 依赖: Algebra, Algebra.smul_def, ContinuousLinearMap, ContinuousLinearMap.reApplyInnerSelf_apply, algebraMap_eq_ofReal, inner_smul_left, inner_smul_right, map_smul, mul_assoc, mul_conj, ofReal_pow, reApplyInnerSelf_apply, smul_def, smul_re
-/
theorem ContinuousLinearMap.reApplyInnerSelf_smul (T : E ->L[𝕜] E) (x : E) {c : 𝕜} :
    T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
  simp only [map_smul, ContinuousLinearMap.reApplyInnerSelf_apply, inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

end ReApplyInnerSelf_Seminormed

namespace InnerProductSpace
variable {𝕜 E F G : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [SeminormedAddCommGroup G] [InnerProductSpace 𝕜 G]

open ContinuousLinearMap

variable (𝕜) in
/--
Definition of `rankOne` / `rankOne` 的定义

English:
definition rankOne
  signature: : E ->L[𝕜] F ->L⋆[𝕜] F ->L[𝕜] E
  body: .flip .comp (.smulRightL 𝕜 _ _) (innerSL 𝕜)

中文:
定义 rankOne
  签名: : E ->L[𝕜] F ->L⋆[𝕜] F ->L[𝕜] E
  定义体: .flip .comp (.smulRightL 𝕜 _ _) (innerSL 𝕜)

Depends on / 依赖: innerSL, smulRightL
-/
noncomputable def rankOne : E ->L[𝕜] F ->L⋆[𝕜] F ->L[𝕜] E :=
.flip .comp (.smulRightL 𝕜 _ _) (innerSL 𝕜)

/--
lemma `rankOne_def` / 引理 `rankOne_def`

English:
lemma rankOne_def
  given: (x : E) (y : F)
  statement: rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x
  proof: rfl

中文:
引理 rankOne_def
  条件: (x : E) (y : F)
  结论: rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x
  证明: rfl
-/
lemma rankOne_def (x : E) (y : F) : rankOne 𝕜 x y = (innerSL 𝕜 y).smulRight x := rfl

/--
lemma `rankOne_def'` / 引理 `rankOne_def'`

English:
lemma rankOne_def'
  given: (x : E) (y : F)
  statement: rankOne 𝕜 x y = .toSpanSingleton 𝕜 x ∘L innerSL 𝕜 y
  proof: rfl

中文:
引理 rankOne_def'
  条件: (x : E) (y : F)
  结论: rankOne 𝕜 x y = .toSpanSingleton 𝕜 x ∘L innerSL 𝕜 y
  证明: rfl
-/
lemma rankOne_def' (x : E) (y : F) : rankOne 𝕜 x y = .toSpanSingleton 𝕜 x ∘L innerSL 𝕜 y := rfl

/--
lemma `toLinearMap_rankOne` / 引理 `toLinearMap_rankOne`

English:
lemma toLinearMap_rankOne
  given: (x : E) (y : F)
  proof: rfl

中文:
引理 toLinearMap_rankOne
  条件: (x : E) (y : F)
  证明: rfl
-/
lemma toLinearMap_rankOne (x : E) (y : F) :
    (rankOne 𝕜 x y).toLinearMap = (innerₛₗ 𝕜 y).smulRight x := rfl

/--
theorem `norm_rankOne` / 定理 `norm_rankOne`

English:
theorem norm_rankOne
  given: (x : E) (y : F)
  statement: ‖rankOne 𝕜 x y‖ = ‖x‖ * ‖y‖
  proof: by
  rw [rankOne_def]; rw [norm_smulRight_apply]; rw [innerSL_apply_norm]; rw [mul_comm]

中文:
定理 norm_rankOne
  条件: (x : E) (y : F)
  结论: ‖rankOne 𝕜 x y‖ = ‖x‖ * ‖y‖
  证明: by
  rw [rankOne_def]; rw [norm_smulRight_apply]; rw [innerSL_apply_norm]; rw [mul_comm]
-/
@[simp] theorem norm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖ = ‖x‖ * ‖y‖ := by
  rw [rankOne_def]; rw [norm_smulRight_apply]; rw [innerSL_apply_norm]; rw [mul_comm]

/--
theorem `nnnorm_rankOne` / 定理 `nnnorm_rankOne`

English:
theorem nnnorm_rankOne
  given: (x : E) (y : F)
  statement: ‖rankOne 𝕜 x y‖₊ = ‖x‖₊ * ‖y‖₊
  proof: NNReal.eq norm_rankOne _ _

中文:
定理 nnnorm_rankOne
  条件: (x : E) (y : F)
  结论: ‖rankOne 𝕜 x y‖₊ = ‖x‖₊ * ‖y‖₊
  证明: NNReal.eq norm_rankOne _ _
-/
@[simp] theorem nnnorm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖₊ = ‖x‖₊ * ‖y‖₊ :=
NNReal.eq norm_rankOne _ _

/--
theorem `enorm_rankOne` / 定理 `enorm_rankOne`

English:
theorem enorm_rankOne
  given: (x : E) (y : F)
  statement: ‖rankOne 𝕜 x y‖ₑ = ‖x‖ₑ * ‖y‖ₑ
  proof: ENNReal.coe_inj.mpr nnnorm_rankOne _ _

中文:
定理 enorm_rankOne
  条件: (x : E) (y : F)
  结论: ‖rankOne 𝕜 x y‖ₑ = ‖x‖ₑ * ‖y‖ₑ
  证明: ENNReal.coe_inj.mpr nnnorm_rankOne _ _
-/
@[simp] theorem enorm_rankOne (x : E) (y : F) : ‖rankOne 𝕜 x y‖ₑ = ‖x‖ₑ * ‖y‖ₑ :=
ENNReal.coe_inj.mpr nnnorm_rankOne _ _

/--
lemma `rankOne_apply` / 引理 `rankOne_apply`

English:
lemma rankOne_apply
  given: (x : E) (y z : F)
  statement: rankOne 𝕜 x y z = inner 𝕜 y z • x
  proof: rfl

中文:
引理 rankOne_apply
  条件: (x : E) (y z : F)
  结论: rankOne 𝕜 x y z = inner 𝕜 y z • x
  证明: rfl
-/
@[simp] lemma rankOne_apply (x : E) (y z : F) : rankOne 𝕜 x y z = inner 𝕜 y z • x := rfl

/--
lemma `comp_rankOne` / 引理 `comp_rankOne`

English:
lemma comp_rankOne
  statement: {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  proof: by
  simp_rw [rankOne_def', ← comp_assoc, comp_toSpanSingleton]

中文:
引理 comp_rankOne
  结论: {G : 类型} [SeminormedAddComm群 G] [赋范空间 𝕜 G]
  证明: by
  simp_rw [rankOne_def', ← comp_assoc, comp_toSpanSingleton]

Depends on / 依赖: comp_assoc, comp_toSpanSingleton, rankOne_def, simp_rw
-/
lemma comp_rankOne {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (x : E) (y : F) (f : E ->L[𝕜] G) : f ∘L rankOne 𝕜 x y = rankOne 𝕜 (f x) y := by
  simp_rw [rankOne_def', ← comp_assoc, comp_toSpanSingleton]

/--
theorem `isIdempotentElem_rankOne_self` / 定理 `isIdempotentElem_rankOne_self`

English:
theorem isIdempotentElem_rankOne_self
  given: {x : F} (hx : ‖x‖ = 1)
  proof: by simp [IsIdempotentElem, mul_def, comp_rankOne, hx]

中文:
定理 isIdempotentElem_rankOne_self
  条件: {x : F} (hx : ‖x‖ = 1)
  证明: by simp [IsIdempotentElem, mul_def, comp_rankOne, hx]

Depends on / 依赖: IsIdempotentElem, comp_rankOne, mul_def
-/
theorem isIdempotentElem_rankOne_self {x : F} (hx : ‖x‖ = 1) :
    IsIdempotentElem (rankOne 𝕜 x x) := by simp [IsIdempotentElem, mul_def, comp_rankOne, hx]

/--
theorem `rankOne_one_right_eq_toSpanSingleton` / 定理 `rankOne_one_right_eq_toSpanSingleton`

English:
theorem rankOne_one_right_eq_toSpanSingleton
  given: (x : F)
  proof: by ext; simp

中文:
定理 rankOne_one_right_eq_toSpanSingleton
  条件: (x : F)
  证明: by ext; simp
-/
@[simp] theorem rankOne_one_right_eq_toSpanSingleton (x : F) :
    rankOne 𝕜 x 1 = toSpanSingleton 𝕜 x := by ext; simp

/--
theorem `rankOne_one_left_eq_innerSL` / 定理 `rankOne_one_left_eq_innerSL`

English:
theorem rankOne_one_left_eq_innerSL
  given: (x : F)
  statement: rankOne 𝕜 1 x = innerSL 𝕜 x
  proof: by ext; simp

中文:
定理 rankOne_one_left_eq_innerSL
  条件: (x : F)
  结论: rankOne 𝕜 1 x = innerSL 𝕜 x
  证明: by ext; simp
-/
@[simp] theorem rankOne_one_left_eq_innerSL (x : F) : rankOne 𝕜 1 x = innerSL 𝕜 x := by ext; simp

/--
lemma `rankOne_comp_rankOne` / 引理 `rankOne_comp_rankOne`

English:
lemma rankOne_comp_rankOne
  given: (x : E) (y z : F) (w : G)
  proof: by
  simp [comp_rankOne]

中文:
引理 rankOne_comp_rankOne
  条件: (x : E) (y z : F) (w : G)
  证明: by
  simp [comp_rankOne]

Depends on / 依赖: comp_rankOne
-/
lemma rankOne_comp_rankOne (x : E) (y z : F) (w : G) :
    rankOne 𝕜 x y ∘L rankOne 𝕜 z w = inner 𝕜 y z • rankOne 𝕜 x w := by
  simp [comp_rankOne]

/--
lemma `inner_left_rankOne_apply` / 引理 `inner_left_rankOne_apply`

English:
lemma inner_left_rankOne_apply
  given: (x : F) (y z : G) (w : F)
  proof: by
  simp [inner_smul_left, inner_conj_symm]

中文:
引理 inner_left_rankOne_apply
  条件: (x : F) (y z : G) (w : F)
  证明: by
  simp [inner_smul_left, inner_conj_symm]

Depends on / 依赖: inner_conj_symm, inner_smul_left
-/
lemma inner_left_rankOne_apply (x : F) (y z : G) (w : F) :
    inner 𝕜 (rankOne 𝕜 x y z) w = inner 𝕜 z y * inner 𝕜 x w := by
  simp [inner_smul_left, inner_conj_symm]

/--
lemma `inner_right_rankOne_apply` / 引理 `inner_right_rankOne_apply`

English:
lemma inner_right_rankOne_apply
  given: (x y : F) (z w : G)
  proof: by
  simp [inner_smul_right, mul_comm]

中文:
引理 inner_right_rankOne_apply
  条件: (x y : F) (z w : G)
  证明: by
  simp [inner_smul_right, mul_comm]

Depends on / 依赖: inner_smul_right, mul_comm
-/
lemma inner_right_rankOne_apply (x y : F) (z w : G) :
    inner 𝕜 x (rankOne 𝕜 y z w) = inner 𝕜 x y * inner 𝕜 z w := by
  simp [inner_smul_right, mul_comm]

section Normed
variable {F H : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/--
theorem `rankOne_eq_zero` / 定理 `rankOne_eq_zero`

English:
theorem rankOne_eq_zero
  given: {x : E} {y : F}
  statement: rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0
  proof: by
  simp [ContinuousLinearMap.ext_iff, rankOne_apply, forall_or_right, or_comm,
    ext_iff_inner_right 𝕜 (E := F)]

中文:
定理 rankOne_eq_zero
  条件: {x : E} {y : F}
  结论: rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0
  证明: by
  simp [ContinuousLinearMap.ext_iff, rankOne_apply, forall_or_right, or_comm,
    ext_iff_inner_right 𝕜 (E := F)]
-/
@[simp] theorem rankOne_eq_zero {x : E} {y : F} : rankOne 𝕜 x y = 0 ↔ x = 0 ∨ y = 0 := by
  simp [ContinuousLinearMap.ext_iff, rankOne_apply, forall_or_right, or_comm,
    ext_iff_inner_right 𝕜 (E := F)]

/--
lemma `rankOne_ne_zero` / 引理 `rankOne_ne_zero`

English:
lemma rankOne_ne_zero
  given: {x : E} {y : F} (hx : x != 0) (hy : y != 0)
  statement: rankOne 𝕜 x y != 0
  proof: by
  grind [rankOne_eq_zero]

中文:
引理 rankOne_ne_zero
  条件: {x : E} {y : F} (hx : x != 0) (hy : y != 0)
  结论: rankOne 𝕜 x y != 0
  证明: by
  grind [rankOne_eq_zero]

Depends on / 依赖: rankOne_eq_zero
-/
lemma rankOne_ne_zero {x : E} {y : F} (hx : x != 0) (hy : y != 0) : rankOne 𝕜 x y != 0 := by
  grind [rankOne_eq_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIdempotentElem_rankOne_self_iff` / 定理 `isIdempotentElem_rankOne_self_iff`

English:
theorem isIdempotentElem_rankOne_self_iff
  given: {x : F} (hx : x != 0)
  proof: by
  refine ⟨?_, isIdempotentElem_rankOne_self⟩
  simp only [IsIdempotentElem, mul_def, comp_rankOne, rankOne_apply, inner_self_eq_norm_sq_to_K,
    map_smul, _root_.smul_apply]
  nth_rw 2 [← one_smul 𝕜 (rankOne 𝕜 x x)]
  rw [← sub_eq_zero]; rw [← sub_smul]
  simp only [smul_eq_zero, rankOne_eq_zero, hx, or_self, or_false, sub_eq_zero, sq_eq_one_iff,
    FaithfulSMul.algebraMap_eq_one_iff, ← show ((-(1 : Real) : Real) : 𝕜) = -1 by grind, ofReal_inj]
  grind [norm_nonneg]

中文:
定理 isIdempotentElem_rankOne_self_iff
  条件: {x : F} (hx : x != 0)
  证明: by
  refine ⟨?_, isIdempotentElem_rankOne_self⟩
  simp only [IsIdempotentElem, mul_def, comp_rankOne, rankOne_apply, inner_self_eq_norm_sq_to_K,
    map_smul, _root_.smul_apply]
  nth_rw 2 [← one_smul 𝕜 (rankOne 𝕜 x x)]
  rw [← sub_eq_zero]; rw [← sub_smul]
  simp only [smul_eq_zero, rankOne_eq_zero, hx, or_self, or_false, sub_eq_zero, sq_eq_one_iff,
    FaithfulSMul.algebraMap_eq_one_iff, ← show ((-(1 : Real) : Real) : 𝕜) = -1 by grind, ofReal_inj]
  grind [norm_nonneg]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_one_iff, IsIdempotentElem, _root_, _root_.smul_apply, algebraMap_eq_one_iff, comp_rankOne, inner_self_eq_norm_sq_to_K, isIdempotentElem_rankOne_self, map_smul, mul_def, norm_nonneg, nth_rw, ofReal_inj, one_smul, or_false, or_self, rankOne, rankOne_apply, rankOne_eq_zero
-/
theorem isIdempotentElem_rankOne_self_iff {x : F} (hx : x != 0) :
    IsIdempotentElem (rankOne 𝕜 x x) ↔ ‖x‖ = 1 := by
  refine ⟨?_, isIdempotentElem_rankOne_self⟩
  simp only [IsIdempotentElem, mul_def, comp_rankOne, rankOne_apply, inner_self_eq_norm_sq_to_K,
    map_smul, _root_.smul_apply]
  nth_rw 2 [← one_smul 𝕜 (rankOne 𝕜 x x)]
  rw [← sub_eq_zero]; rw [← sub_smul]
  simp only [smul_eq_zero, rankOne_eq_zero, hx, or_self, or_false, sub_eq_zero, sq_eq_one_iff,
    FaithfulSMul.algebraMap_eq_one_iff, ← show ((-(1 : Real) : Real) : 𝕜) = -1 by grind, ofReal_inj]
  grind [norm_nonneg]

/--
theorem `rankOne_eq_rankOne_iff_comm` / 定理 `rankOne_eq_rankOne_iff_comm`

English:
theorem rankOne_eq_rankOne_iff_comm
  given: {a c : F} {b d : H}
  proof: by
  simp_rw [ContinuousLinearMap.ext_iff, ext_iff_inner_left 𝕜 (E := F),
    ext_iff_inner_right 𝕜 (E := H)]
  rw [forall_comm]
  simp [inner_smul_left, inner_smul_right, mul_comm]

中文:
定理 rankOne_eq_rankOne_iff_comm
  条件: {a c : F} {b d : H}
  证明: by
  simp_rw [ContinuousLinearMap.ext_iff, ext_iff_inner_left 𝕜 (E := F),
    ext_iff_inner_right 𝕜 (E := H)]
  rw [forall_comm]
  simp [inner_smul_left, inner_smul_right, mul_comm]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, ext_iff, ext_iff_inner_left, ext_iff_inner_right, forall_comm, inner_smul_left, inner_smul_right, mul_comm, simp_rw
-/
theorem rankOne_eq_rankOne_iff_comm {a c : F} {b d : H} :
    rankOne 𝕜 a b = rankOne 𝕜 c d ↔ rankOne 𝕜 b a = rankOne 𝕜 d c := by
  simp_rw [ContinuousLinearMap.ext_iff, ext_iff_inner_left 𝕜 (E := F),
    ext_iff_inner_right 𝕜 (E := H)]
  rw [forall_comm]
  simp [inner_smul_left, inner_smul_right, mul_comm]

open ComplexOrder in
/--
theorem `exists_of_rankOne_eq_rankOne` / 定理 `exists_of_rankOne_eq_rankOne`

English:
theorem exists_of_rankOne_eq_rankOne
  statement: {a c : F} {b d : H}
  proof: by
  have h₂ := rankOne_eq_rankOne_iff_comm.mp h
  simp only [ContinuousLinearMap.ext_iff, rankOne_apply] at h h₂
  have h₃ := calc
    a = (⟪b, b⟫_𝕜 / ⟪b, b⟫_𝕜) • a := by simp_all
    _ = (1 / ⟪b, b⟫_𝕜) • (⟪b, b⟫_𝕜 • a) := by simp only [smul_smul]; ring_nf
    _ = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by simp only [h, smul_smul]; ring_nf
  have h₄ := calc
    b = (⟪a, a⟫_𝕜 / ⟪a, a⟫_𝕜) • b := by simp_all
    _ = (1 / ⟪a, a⟫_𝕜) • (⟪a, a⟫_𝕜 • b) := by simp only [smul_smul]; ring_nf
    _ = ((⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) * (⟪c, c⟫_𝕜 / ⟪a, a⟫_𝕜)) • d := by
      simp_rw [h₂, h₃, inner_smul_right, smul_smul]; ring_nf
  have h₅ : ⟪d, b⟫_𝕜 != 0 := fun h => by simp [h, hb] at h₄
  have h₆ : c != 0 := fun h => by simp [h, ha] at h₃
refine ⟨_, ‖c‖ ^ 2 / ‖a‖ ^ 2, div_ne_zero h₅ by simpa, ?_, h₃, by simpa using h₄⟩
  simp_rw [← ofReal_pow, ← ofReal_div, pos_iff (K := 𝕜), ofReal_re, ofReal_im, and_true]
  exact div_pos (by simpa [sq_pos_iff]) (by simpa [sq_pos_iff])

中文:
定理 存在_of_rankOne_eq_rankOne
  结论: {a c : F} {b d : H}
  证明: by
  have h₂ := rankOne_eq_rankOne_iff_comm.mp h
  simp only [ContinuousLinearMap.ext_iff, rankOne_apply] at h h₂
  have h₃ := calc
    a = (⟪b, b⟫_𝕜 / ⟪b, b⟫_𝕜) • a := by simp_all
    _ = (1 / ⟪b, b⟫_𝕜) • (⟪b, b⟫_𝕜 • a) := by simp only [smul_smul]; ring_nf
    _ = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by simp only [h, smul_smul]; ring_nf
  have h₄ := calc
    b = (⟪a, a⟫_𝕜 / ⟪a, a⟫_𝕜) • b := by simp_all
    _ = (1 / ⟪a, a⟫_𝕜) • (⟪a, a⟫_𝕜 • b) := by simp only [smul_smul]; ring_nf
    _ = ((⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) * (⟪c, c⟫_𝕜 / ⟪a, a⟫_𝕜)) • d := by
      simp_rw [h₂, h₃, inner_smul_right, smul_smul]; ring_nf
  have h₅ : ⟪d, b⟫_𝕜 != 0 := fun h => by simp [h, hb] at h₄
  have h₆ : c != 0 := fun h => by simp [h, ha] at h₃
refine ⟨_, ‖c‖ ^ 2 / ‖a‖ ^ 2, div_ne_zero h₅ by simpa, ?_, h₃, by simpa using h₄⟩
  simp_rw [← ofReal_pow, ← ofReal_div, pos_iff (K := 𝕜), ofReal_re, ofReal_im, and_true]
  exact div_pos (by simpa [sq_pos_iff]) (by simpa [sq_pos_iff])

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_iff, ext_iff, rankOne_apply, rankOne_eq_rankOne_iff_comm, rankOne_eq_rankOne_iff_comm.mp, ring_nf, smul_smul
-/
theorem exists_of_rankOne_eq_rankOne {a c : F} {b d : H}
    (ha : a != 0) (hb : b != 0) (h : rankOne 𝕜 a b = rankOne 𝕜 c d) :
    exists (α β : 𝕜) (_ : α != 0) (_ : 0 < β), a = α • c ∧ b = (α * β) • d := by
  have h₂ := rankOne_eq_rankOne_iff_comm.mp h
  simp only [ContinuousLinearMap.ext_iff, rankOne_apply] at h h₂
  have h₃ := calc
    a = (⟪b, b⟫_𝕜 / ⟪b, b⟫_𝕜) • a := by simp_all
    _ = (1 / ⟪b, b⟫_𝕜) • (⟪b, b⟫_𝕜 • a) := by simp only [smul_smul]; ring_nf
    _ = (⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) • c := by simp only [h, smul_smul]; ring_nf
  have h₄ := calc
    b = (⟪a, a⟫_𝕜 / ⟪a, a⟫_𝕜) • b := by simp_all
    _ = (1 / ⟪a, a⟫_𝕜) • (⟪a, a⟫_𝕜 • b) := by simp only [smul_smul]; ring_nf
    _ = ((⟪d, b⟫_𝕜 / ⟪b, b⟫_𝕜) * (⟪c, c⟫_𝕜 / ⟪a, a⟫_𝕜)) • d := by
      simp_rw [h₂, h₃, inner_smul_right, smul_smul]; ring_nf
  have h₅ : ⟪d, b⟫_𝕜 != 0 := fun h => by simp [h, hb] at h₄
  have h₆ : c != 0 := fun h => by simp [h, ha] at h₃
refine ⟨_, ‖c‖ ^ 2 / ‖a‖ ^ 2, div_ne_zero h₅ by simpa, ?_, h₃, by simpa using h₄⟩
  simp_rw [← ofReal_pow, ← ofReal_div, pos_iff (K := 𝕜), ofReal_re, ofReal_im, and_true]
  exact div_pos (by simpa [sq_pos_iff]) (by simpa [sq_pos_iff])

end Normed

end InnerProductSpace

namespace ContinuousLinearMap

open InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/--
theorem `opNorm_le_of_re_inner_le` / 定理 `opNorm_le_of_re_inner_le`

English:
theorem opNorm_le_of_re_inner_le
  statement: {T : E ->L[𝕜] F} {C : Real} (hC : 0 <= C)
  proof: by
  refine opNorm_le_of_unit_norm hC fun x hx => ?_
  by_cases hTx : ‖T x‖ = 0
  · rwa [hTx]
  · specialize h x (((‖T x‖⁻¹ : Real) : 𝕜) • T x) hx (by simp [norm_smul, hTx])
    rwa [inner_smul_right, re_ofReal_mul, ← norm_sq_eq_re_inner,
      inv_mul_eq_div, sq, mul_self_div_self] at h

中文:
定理 opNorm_le_of_re_inner_le
  结论: {T : E ->L[𝕜] F} {C : 实数} (hC : 0 <= C)
  证明: by
  refine opNorm_le_of_unit_norm hC fun x hx => ?_
  by_cases hTx : ‖T x‖ = 0
  · rwa [hTx]
  · specialize h x (((‖T x‖⁻¹ : Real) : 𝕜) • T x) hx (by simp [norm_smul, hTx])
    rwa [inner_smul_right, re_ofReal_mul, ← norm_sq_eq_re_inner,
      inv_mul_eq_div, sq, mul_self_div_self] at h

Depends on / 依赖: inner_smul_right, inv_mul_eq_div, mul_self_div_self, norm_smul, norm_sq_eq_re_inner, opNorm_le_of_unit_norm, re_ofReal_mul, specialize
-/
theorem opNorm_le_of_re_inner_le {T : E ->L[𝕜] F} {C : Real} (hC : 0 <= C)
    (h : forall x y, ‖x‖ = 1 -> ‖y‖ = 1 -> re ⟪T x, y⟫_𝕜 <= C) : ‖T‖ <= C := by
  refine opNorm_le_of_unit_norm hC fun x hx => ?_
  by_cases hTx : ‖T x‖ = 0
  · rwa [hTx]
  · specialize h x (((‖T x‖⁻¹ : Real) : 𝕜) • T x) hx (by simp [norm_smul, hTx])
    rwa [inner_smul_right, re_ofReal_mul, ← norm_sq_eq_re_inner,
      inv_mul_eq_div, sq, mul_self_div_self] at h

end ContinuousLinearMap
