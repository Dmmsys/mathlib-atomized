/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Basis.MulOpposite

/-!
# Inner product space on `Hᵐᵒᵖ`

This file defines the inner product space structure on `Hᵐᵒᵖ` where we define
the inner product naturally. We also define `OrthonormalBasis.mulOpposite`.
-/

@[expose] public section

namespace MulOpposite
variable {𝕜 H : Type*}

open MulOpposite

/-- The inner product of `Hᵐᵒᵖ` is given by `⟪x, y⟫ ↦ ⟪x.unop, y.unop⟫`. -/
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inner product of `Hᵐᵒᵖ` is given by `⟪x, y⟫ ↦ ⟪x.unop, y.unop⟫`.
-/
instance [Inner 𝕜 H] : Inner 𝕜 Hᵐᵒᵖ where inner x y := inner 𝕜 x.unop y.unop
/-
**MulOpposite.inner_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {𝕜 : Type u_1} {H : Type u_2} [inst : Inner 𝕜 H] (x y : Hᵐᵒᵖ),   inner 𝕜
 (MulOpposite.unop x) (MulOpposite.unop y) = inner 𝕜 x y
参数：x y : Hᵐᵒᵖ；MulOpposite.unop x；MulOpposite.unop y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem inner_unop [Inner 𝕜 H] (x y : Hᵐᵒᵖ) : inner 𝕜 x.unop y.unop = inner 𝕜 x y := rfl
/-
**MulOpposite.inner_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {𝕜 : Type u_1} {H : Type u_2} [inst : Inner 𝕜 H] (x y : H),   inner 𝕜 (M
ulOpposite.op x) (MulOpposite.op y) = inner 𝕜 x y
参数：x y : H；MulOpposite.op x；MulOpposite.op y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem inner_op [Inner 𝕜 H] (x y : H) : inner 𝕜 (op x) (op y) = inner 𝕜 x y := rfl

section InnerProductSpace
variable [RCLike 𝕜] [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InnerProductSpace 𝕜 Hᵐᵒᵖ where
  norm_sq_eq_re_inner x := (inner_self_eq_norm_sq x.unop).symm
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.unop y.unop
  add_left x y z := InnerProductSpace.add_left x.unop y.unop z.unop
  smul_left x y r := InnerProductSpace.smul_left x.unop y.unop r

section orthonormal

/-
**MulOpposite._root_.Module.Basis.mulOpposite_is_orthonormal_iff** 是 Mathlib 中的一
个定理，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Basis.mulOpposite_is_orthonormal_iff {ι : Type*} (b : Module.Basis ι 𝕜 H) :
    Orthonormal 𝕜 b.mulOpposite ↔ Orthonormal 𝕜 b := Iff.rfl

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Fintype ι]

/-- The multiplicative opposite of an orthonormal basis `b`, i.e., `b i ↦ op (b i)`. -/
/-
**MulOpposite._root_.OrthonormalBasis.mulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Mul
Opposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative opposite of an orthonormal basis `b`, i.e., `b i ↦ op (b i)`.
-/
noncomputable def _root_.OrthonormalBasis.mulOpposite (b : OrthonormalBasis ι 𝕜 H) :
    OrthonormalBasis ι 𝕜 Hᵐᵒᵖ := b.toBasis.mulOpposite.toOrthonormalBasis b.orthonormal
/-
**MulOpposite._root_.OrthonormalBasis.toBasis_mulOpposite** 是 Mathlib 中的一个引理，位于命
名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.OrthonormalBasis.toBasis_mulOpposite (b : OrthonormalBasis ι 𝕜 H) :
    b.mulOpposite.toBasis = b.toBasis.mulOpposite := rfl

end orthonormal

end InnerProductSpace

end MulOpposite

