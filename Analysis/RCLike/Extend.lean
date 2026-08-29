/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Extending an `ℝ`-linear functional to a `𝕜`-linear functional

In this file we provide a way to extend a (optionally, continuous) `ℝ`-linear map to a (continuous)
`𝕜`-linear map in a way that bounds the norm by the norm of the original map, when `𝕜` is either
`ℝ` (the extension is trivial) or `ℂ`. We formulate the extension uniformly, by assuming `RCLike 𝕜`.

We motivate the form of the extension as follows. Note that `fc : F →ₗ[𝕜] 𝕜` is determined fully by
`re fc`: for all `x : F`, `fc (I • x) = I * fc x`, so `im (fc x) = -re (fc (I • x))`. Therefore,
given an `fr : F →ₗ[ℝ] ℝ`, we define `fc x = fr x - fr (I • x) * I`.

In `Mathlib/Analysis/Normed/Module/RCLike/Extend.lean` we show that this extension is isometric.
This is separate to avoid importing material about the operator norm into files about more
elementary properties, like locally convex spaces.

## Main definitions

* `LinearMap.extendRCLike`
* `ContinuousLinearMap.extendRCLike`

-/

@[expose] public section

open RCLike

open ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
namespace Module.Dual

variable [AddCommGroup F] [Module Real F] [Module 𝕜 F] [IsScalarTower Real 𝕜 F]

/--
Definition of `extendRCLike` / `extendRCLike` 的定义

English:
definition extendRCLike
  signature: (fr : Dual Real F)
  body: letI fc : F -> 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add (x y) : fc (x + y) = fc x + fc y := by
    simp only [fc, smul_add, map_add, mul_add]
    abel
  have A (c : Real) (x : F) : (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by simp
  have smul_Real (c : Real) (x : F) : fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    simp only [fc, A, smul_comm I, mul_comm I, mul_sub, mul_assoc]
  have smul_I (x : F) : fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    obtain (h | h) := @I_mul_I_ax 𝕜 _
    · simp [fc, h]
    · simp [fc, mul_sub, ← mul_assoc, smul_smul, h, add_comm]
  have smul_𝕜 (c : 𝕜) (x : F) : fc (c • x) = c • fc x := by
    rw [← re_add_im c]
    simp only [add_smul, ← smul_smul, add, smul_Real, smul_I, ← mul_assoc, smul_eq_mul, add_mul]
  { toFun := fc
    map_add' := add
    map_smul' := smul_𝕜 }

中文:
定义 extendRCLike
  签名: (fr : 对偶 实数 F)
  定义体: letI fc : F -> 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add (x y) : fc (x + y) = fc x + fc y := by
    simp only [fc, smul_add, map_add, mul_add]
    abel
  have A (c : Real) (x : F) : (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by simp
  have smul_Real (c : Real) (x : F) : fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    simp only [fc, A, smul_comm I, mul_comm I, mul_sub, mul_assoc]
  have smul_I (x : F) : fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    obtain (h | h) := @I_mul_I_ax 𝕜 _
    · simp [fc, h]
    · simp [fc, mul_sub, ← mul_assoc, smul_smul, h, add_comm]
  have smul_𝕜 (c : 𝕜) (x : F) : fc (c • x) = c • fc x := by
    rw [← re_add_im c]
    simp only [add_smul, ← smul_smul, add, smul_Real, smul_I, ← mul_assoc, smul_eq_mul, add_mul]
  { toFun := fc
    map_add' := add
    map_smul' := smul_𝕜 }

Depends on / 依赖: I_mul_I_ax, map_add, mul_add, mul_assoc, mul_comm, mul_sub, smul_I, smul_Real, smul_add, smul_comm
-/
noncomputable def extendRCLike (fr : Dual Real F) : Dual 𝕜 F :=
  letI fc : F -> 𝕜 := fun x => (fr x : 𝕜) - (I : 𝕜) * fr ((I : 𝕜) • x)
  have add (x y) : fc (x + y) = fc x + fc y := by
    simp only [fc, smul_add, map_add, mul_add]
    abel
  have A (c : Real) (x : F) : (fr ((c : 𝕜) • x) : 𝕜) = (c : 𝕜) * (fr x : 𝕜) := by simp
  have smul_Real (c : Real) (x : F) : fc ((c : 𝕜) • x) = (c : 𝕜) * fc x := by
    simp only [fc, A, smul_comm I, mul_comm I, mul_sub, mul_assoc]
  have smul_I (x : F) : fc ((I : 𝕜) • x) = (I : 𝕜) * fc x := by
    obtain (h | h) := @I_mul_I_ax 𝕜 _
    · simp [fc, h]
    · simp [fc, mul_sub, ← mul_assoc, smul_smul, h, add_comm]
  have smul_𝕜 (c : 𝕜) (x : F) : fc (c • x) = c • fc x := by
    rw [← re_add_im c]
    simp only [add_smul, ← smul_smul, add, smul_Real, smul_I, ← mul_assoc, smul_eq_mul, add_mul]
  { toFun := fc
    map_add' := add
    map_smul' := smul_𝕜 }

/--
theorem `extendRCLike_apply` / 定理 `extendRCLike_apply`

English:
theorem extendRCLike_apply
  given: (fr : Dual Real F) (x : F)
  proof: rfl

@[simp]

中文:
定理 extendRCLike_apply
  条件: (fr : 对偶 实数 F) (x : F)
  证明: rfl

@[simp]
-/
theorem extendRCLike_apply (fr : Dual Real F) (x : F) :
    fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
/--
theorem `re_extendRCLike_apply` / 定理 `re_extendRCLike_apply`

English:
theorem re_extendRCLike_apply
  given: (fr : Dual Real F) (x : F)
  statement: re (fr.extendRCLike x : 𝕜) = fr x
  proof: by
  simp only [extendRCLike_apply, map_sub, zero_mul, mul_zero, sub_zero, rclike_simps]

@[simp]

中文:
定理 re_extendRCLike_apply
  条件: (fr : 对偶 实数 F) (x : F)
  结论: re (fr.extendRCLike x : 𝕜) = fr x
  证明: by
  simp only [extendRCLike_apply, map_sub, zero_mul, mul_zero, sub_zero, rclike_simps]

@[simp]

Depends on / 依赖: extendRCLike_apply, map_sub, mul_zero, rclike_simps, sub_zero, zero_mul
-/
theorem re_extendRCLike_apply (fr : Dual Real F) (x : F) : re (fr.extendRCLike x : 𝕜) = fr x := by
  simp only [extendRCLike_apply, map_sub, zero_mul, mul_zero, sub_zero, rclike_simps]

@[simp]
/--
lemma `im_extendRCLike_apply` / 引理 `im_extendRCLike_apply`

English:
lemma im_extendRCLike_apply
  given: (g : Dual Real F) (x : F)
  proof: by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

中文:
引理 im_extendRCLike_apply
  条件: (g : 对偶 实数 F) (x : F)
  证明: by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

Depends on / 依赖: I_eq_zero_or_im_I_eq_one, RCLike, RCLike.I_eq_zero_or_im_I_eq_one, all_goals, extendRCLike_apply
-/
lemma im_extendRCLike_apply (g : Dual Real F) (x : F) :
    im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x) := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

/--
theorem `norm_extendRCLike_apply_sq` / 定理 `norm_extendRCLike_apply_sq`

English:
theorem norm_extendRCLike_apply_sq
  given: (fr : Dual Real F) (x : F)
  proof: calc
  ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = re (conj (fr.extendRCLike x) * fr.extendRCLike x : 𝕜) := by
    rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [ofReal_re]
  _ = fr (conj (fr.extendRCLike x : 𝕜) • x) := by
    rw [← smul_eq_mul]; rw [← map_smul]; rw [re_extendRCLike_apply]

中文:
定理 norm_extendRCLike_apply_sq
  条件: (fr : 对偶 实数 F) (x : F)
  证明: calc
  ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = re (conj (fr.extendRCLike x) * fr.extendRCLike x : 𝕜) := by
    rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [ofReal_re]
  _ = fr (conj (fr.extendRCLike x : 𝕜) • x) := by
    rw [← smul_eq_mul]; rw [← map_smul]; rw [re_extendRCLike_apply]
-/
theorem norm_extendRCLike_apply_sq (fr : Dual Real F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = fr (conj (fr.extendRCLike x : 𝕜) • x) := calc
  ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = re (conj (fr.extendRCLike x) * fr.extendRCLike x : 𝕜) := by
    rw [RCLike.conj_mul]; rw [← ofReal_pow]; rw [ofReal_re]
  _ = fr (conj (fr.extendRCLike x : 𝕜) • x) := by
    rw [← smul_eq_mul]; rw [← map_smul]; rw [re_extendRCLike_apply]

/-- The extension `Module.Dual.extendRCLike` as a linear equivalence between the algebraic duals. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `extendRCLikeₗ` / `extendRCLikeₗ` 的定义

English:
definition extendRCLikeₗ
  signature: : Dual Real F ≃ₗ[Real] Dual 𝕜 F where
  body: extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reLm.comp (f.restrictScalars Real)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

中文:
定义 extendRCLikeₗ
  签名: : 对偶 实数 F ≃ₗ[实数] 对偶 𝕜 F where
  定义体: extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reLm.comp (f.restrictScalars Real)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

Depends on / 依赖: extendRCLike
-/
noncomputable def extendRCLikeₗ : Dual Real F ≃ₗ[Real] Dual 𝕜 F where
  toFun := extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reLm.comp (f.restrictScalars Real)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

end Module.Dual

namespace StrongDual

variable [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [ContinuousConstSMul 𝕜 F]
variable [Module Real F] [IsScalarTower Real 𝕜 F]

/--
Definition of `extendRCLike` / `extendRCLike` 的定义

English:
definition extendRCLike
  signature: (fr : StrongDual Real F)
  body: Module.Dual.extendRCLike fr.toLinearMap
  cont := show Continuous fun x => (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop

中文:
定义 extendRCLike
  签名: (fr : StrongDual 实数 F)
  定义体: Module.Dual.extendRCLike fr.toLinearMap
  cont := show Continuous fun x => (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop

Depends on / 依赖: Module, Module.Dual.extendRCLike, extendRCLike, fr.toLinearMap, toLinearMap
-/
noncomputable def extendRCLike (fr : StrongDual Real F) : StrongDual 𝕜 F where
  __ := Module.Dual.extendRCLike fr.toLinearMap
  cont := show Continuous fun x => (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) by fun_prop

/--
theorem `extendRCLike_apply` / 定理 `extendRCLike_apply`

English:
theorem extendRCLike_apply
  given: (fr : StrongDual Real F) (x : F)
  proof: rfl

@[simp]

中文:
定理 extendRCLike_apply
  条件: (fr : StrongDual 实数 F) (x : F)
  证明: rfl

@[simp]
-/
theorem extendRCLike_apply (fr : StrongDual Real F) (x : F) :
    fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜) := rfl

@[simp]
/--
lemma `re_extendRCLike_apply` / 引理 `re_extendRCLike_apply`

English:
lemma re_extendRCLike_apply
  given: (g : StrongDual Real F) (x : F)
  proof: by
  simp [extendRCLike_apply]

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.re_extendTo𝕜ₗ := re_extendRCLike_apply

@[simp]

中文:
引理 re_extendRCLike_apply
  条件: (g : StrongDual 实数 F) (x : F)
  证明: by
  simp [extendRCLike_apply]

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.re_extendTo𝕜ₗ := re_extendRCLike_apply

@[simp]

Depends on / 依赖: extendRCLike_apply
-/
lemma re_extendRCLike_apply (g : StrongDual Real F) (x : F) :
    re ((extendRCLike g) x : 𝕜) = g x := by
  simp [extendRCLike_apply]

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.re_extendTo𝕜ₗ := re_extendRCLike_apply

@[simp]
/--
lemma `im_extendRCLike_apply` / 引理 `im_extendRCLike_apply`

English:
lemma im_extendRCLike_apply
  given: (g : StrongDual Real F) (x : F)
  proof: by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

中文:
引理 im_extendRCLike_apply
  条件: (g : StrongDual 实数 F) (x : F)
  证明: by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

Depends on / 依赖: I_eq_zero_or_im_I_eq_one, RCLike, RCLike.I_eq_zero_or_im_I_eq_one, all_goals, extendRCLike_apply
-/
lemma im_extendRCLike_apply (g : StrongDual Real F) (x : F) :
    im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x) := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  all_goals simp [h, extendRCLike_apply]

/-- The extension `StrongDual.extendRCLike` as a linear equivalence between the algebraic duals.

When `F` is a normed space, this can be upgraded to an *isometric* linear equivalence, see
`StrongDual.extendRCLikeₗᵢ`. -/
@[simps -isSimp apply symm_apply]
/--
Definition of `extendRCLikeₗ` / `extendRCLikeₗ` 的定义

English:
definition extendRCLikeₗ
  signature: : StrongDual Real F ≃ₗ[Real] StrongDual 𝕜 F where
  body: StrongDual.extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reCLM.comp (f.restrictScalars Real)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp [extendRCLike_apply]
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.extendTo𝕜ₗ := extendRCLikeₗ

中文:
定义 extendRCLikeₗ
  签名: : StrongDual 实数 F ≃ₗ[实数] StrongDual 𝕜 F where
  定义体: StrongDual.extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reCLM.comp (f.restrictScalars Real)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp [extendRCLike_apply]
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.extendTo𝕜ₗ := extendRCLikeₗ

Depends on / 依赖: StrongDual, StrongDual.extendRCLike, extendRCLike
-/
noncomputable def extendRCLikeₗ : StrongDual Real F ≃ₗ[Real] StrongDual 𝕜 F where
  toFun := StrongDual.extendRCLike (𝕜 := 𝕜)
  invFun f := RCLike.reCLM.comp (f.restrictScalars Real)
  left_inv f := by ext; simp
  right_inv f := by ext; apply RCLike.ext <;> simp [extendRCLike_apply]
  map_add' := by intros; ext; simp [extendRCLike_apply]; ring
  map_smul' := by intros; ext; simp [extendRCLike_apply, real_smul_eq_coe_mul]; ring

@[deprecated (since := "2026-02-24")] alias _root_.RCLike.extendTo𝕜ₗ := extendRCLikeₗ

end StrongDual

namespace LinearMap

open Module.Dual

@[deprecated (since := "2026-02-24")] alias extendTo𝕜' := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply := extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply_re := re_extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_apply_sq := norm_extendRCLike_apply_sq
@[deprecated (since := "2026-02-24")] alias extendTo𝕜 := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜_apply := extendRCLike_apply

end LinearMap

namespace ContinuousLinearMap

open StrongDual

@[deprecated (since := "2026-02-24")] alias extendTo𝕜' := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜'_apply := extendRCLike_apply
@[deprecated (since := "2026-02-24")] alias extendTo𝕜 := extendRCLike
@[deprecated (since := "2026-02-24")] alias extendTo𝕜_apply := extendRCLike_apply

end ContinuousLinearMap
