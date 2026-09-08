/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Algebra

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the Euclidean norm of its components.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/

@[expose] public noncomputable section


@[inherit_doc] scoped[Quaternion] notation "ℍ" => Quaternion ℝ

open scoped RealInnerProductSpace

namespace Quaternion

/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inner ℝ ℍ :=
  ⟨fun a b => (a * star b).re⟩
/-
**Quaternion.inner_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：inner_self (a : ℍ) : ⟪a, a⟫ = normSq a
参数：a : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl
/-
**Quaternion.inner_def** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：inner_def (a b : ℍ) : ⟪a, b⟫ = (a * star b).re
参数：a b : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * star b).re :=
  rfl
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedAddCommGroup ℍ :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ ℍ _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun _ => normSq_nonneg
      definite := fun _ => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_def, add_mul, re_add]
      smul_left := fun x y r => by simp [inner_def] }
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InnerProductSpace ℝ ℍ :=
  InnerProductSpace.ofCore _
/-
**Quaternion.normSq_eq_norm_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_eq_norm_mul_self (a : ℍ) : normSq a = ‖a‖ * ‖a‖
参数：a : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.inner_self`：inner_self (a : ℍ) : ⟪a, a⟫ = normSq a
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
-/
theorem normSq_eq_norm_mul_self (a : ℍ) : normSq a = ‖a‖ * ‖a‖ := by
  rw [← inner_self, real_inner_self_eq_norm_mul_norm]
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormOneClass ℍ :=
  ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]
/-
**Quaternion.norm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：norm_coe (a : Real) : ‖(a : ℍ)‖ = ‖a‖
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_real_inner`：norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫
_Real
· 使用定理 `Quaternion.inner_self`：inner_self (a : ℍ) : ⟪a, a⟫ = normSq a
· 使用定理 `Quaternion.normSq_coe`：normSq_coe : normSq (x : ℍ[R]) = x ^ 2
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
-/
theorem norm_coe (a : ℝ) : ‖(a : ℍ)‖ = ‖a‖ := by
  rw [norm_eq_sqrt_real_inner, inner_self, normSq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

@[simp, norm_cast]
/-
**Quaternion.nnnorm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：nnnorm_coe (a : Real) : ‖(a : ℍ)‖₊ = ‖a‖₊
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Quaternion.norm_coe`：norm_coe (a : Real) : ‖(a : ℍ)‖ = ‖a‖
-/
theorem nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_coe a

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
/-
**Quaternion.norm_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：norm_star (a : ℍ) : ‖star a‖ = ‖a‖
参数：a : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_real_inner`：norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫
_Real
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Quaternion.normSq_star`：normSq_star : normSq (star a) = normSq a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_star (a : ℍ) : ‖star a‖ = ‖a‖ := by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
/-
**Quaternion.nnnorm_star** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：nnnorm_star (a : ℍ) : ‖star a‖₊ = ‖a‖₊
参数：a : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Quaternion.norm_star`：norm_star (a : ℍ) : ‖star a‖ = ‖a‖
-/
theorem nnnorm_star (a : ℍ) : ‖star a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_star a
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedDivisionRing ℍ where
  dist_eq _ _ := rfl
  norm_mul _ _ := by simp_rw [norm_eq_sqrt_real_inner, inner_self]; simp
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedAlgebra ℝ ℍ where
  norm_smul_le := norm_smul_le
  toAlgebra := Quaternion.algebra
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CStarRing ℍ where
  norm_mul_self_le x :=
    le_of_eq <| Eq.symm <| (norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_star x)

/-- Coercion from `ℂ` to `ℍ`. -/
/-
**Quaternion.coeComplex** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：ℂ → Quaternion ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℂ` to `ℍ`.
-/
@[coe] def coeComplex (z : ℂ) : ℍ := ⟨z.re, z.im, 0, 0⟩
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℂ` to `ℍ`.
-/
instance : Coe ℂ ℍ := ⟨coeComplex⟩

@[simp, norm_cast]
/-
**Quaternion.re_coeComplex** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_coeComplex (z : Complex) : (z : ℍ).re = z.re
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem re_coeComplex (z : ℂ) : (z : ℍ).re = z.re :=
  rfl

@[simp, norm_cast]
/-
**Quaternion.imI_coeComplex** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imI_coeComplex (z : Complex) : (z : ℍ).imI = z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imI_coeComplex (z : ℂ) : (z : ℍ).imI = z.im :=
  rfl

@[simp, norm_cast]
/-
**Quaternion.imJ_coeComplex** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imJ_coeComplex (z : Complex) : (z : ℍ).imJ = 0
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imJ_coeComplex (z : ℂ) : (z : ℍ).imJ = 0 :=
  rfl

@[simp, norm_cast]
/-
**Quaternion.imK_coeComplex** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：imK_coeComplex (z : Complex) : (z : ℍ).imK = 0
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imK_coeComplex (z : ℂ) : (z : ℍ).imK = 0 :=
  rfl

@[simp, norm_cast]
/-
**Quaternion.coeComplex_add** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coeComplex_add (z w : Complex) : ↑(z + w) = (z + w : ℍ)
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quaternion.ext`：ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a
.imK = b.imK -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem coeComplex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by ext <;> simp

@[simp, norm_cast]
/-
**Quaternion.coeComplex_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coeComplex_mul (z w : Complex) : ↑(z * w) = (z * w : ℍ)
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quaternion.ext`：ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a
.imK = b.imK -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Quaternion.re_mul`：re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a
.imJ * b.imJ - a.imK * b.imK
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `Quaternion.imI_mul`：imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re 
+ a.imJ * b.imK - a.imK * b.imJ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Quaternion.imJ_mul`：imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK
 + a.imJ * b.re + a.imK * b.imI
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Quaternion.imK_mul`：imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ
 - a.imJ * b.imI + a.imK * b.re
-/
theorem coeComplex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by ext <;> simp

@[simp, norm_cast]
/-
**Quaternion.coeComplex_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coeComplex_zero : ((0 : Complex) : ℍ) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeComplex_zero : ((0 : ℂ) : ℍ) = 0 :=
  rfl

@[simp, norm_cast]
/-
**Quaternion.coeComplex_one** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coeComplex_one : ((1 : Complex) : ℍ) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeComplex_one : ((1 : ℂ) : ℍ) = 1 :=
  rfl

@[simp, norm_cast]
/-
**Quaternion.coe_real_complex_mul** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_real_complex_mul (r : Real) (z : Complex) : (r • z : ℍ) = ↑r * ↑z
参数：r : Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quaternion.ext`：ext : a.re = b.re -> a.imI = b.imI -> a.imJ = b.imJ -> a
.imK = b.imK -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.re_mul`：re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a
.imJ * b.imJ - a.imK * b.imK
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Quaternion.imI_mul`：imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re 
+ a.imJ * b.imK - a.imK * b.imJ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Quaternion.imJ_mul`：imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK
 + a.imJ * b.re + a.imK * b.imI
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Quaternion.imK_mul`：imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ
 - a.imJ * b.imI + a.imK * b.re
-/
theorem coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z := by ext <;> simp

@[simp, norm_cast]
/-
**Quaternion.coeComplex_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coeComplex_coe (r : Real) : ((r : Complex) : ℍ) = r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeComplex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r :=
  rfl

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
/-
**Quaternion.ofComplex** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：ofComplex : Complex ->ₐ[Real] ℍ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quaternion.coeComplex_mul`：coeComplex_mul (z w : Complex) : ↑(z * w) = (
z * w : ℍ)
· 使用定理 `Quaternion.coeComplex_add`：coeComplex_add (z w : Complex) : ↑(z + w) = (
z + w : ℍ)

--- 原说明 ---
Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism.
-/
def ofComplex : ℂ →ₐ[ℝ] ℍ where
  toFun := (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl

@[simp]
/-
**Quaternion.coe_ofComplex** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：coe_ofComplex : ⇑ofComplex = coeComplex
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofComplex : ⇑ofComplex = coeComplex := rfl

/-- The norm of the components as a Euclidean vector equals the norm of the quaternion. -/
/-
**Quaternion.norm_toLp_equivTuple** 是 Mathlib 中的一个引理，位于命名空间 `Quaternion`。
形式化陈述：norm_toLp_equivTuple (x : ℍ) : ‖WithLp.toLp 2 (equivTuple Real x)‖ = ‖x‖
参数：x : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_real_inner`：norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫
_Real
· 使用定理 `Quaternion.inner_self`：inner_self (a : ℍ) : ⟪a, a⟫ = normSq a
· 使用定理 `Quaternion.normSq_def'`：normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3
 ^ 2 + a.4 ^ 2
· 使用定理 `PiLp.inner_apply`：PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι -> Typ
e*} [forall i, NormedAddCommGroup (f i)] [forall i, InnerProductSpace 𝕜 (f i)] (
x y : …
· 使用定理 `Fin.sum_univ_four`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 4 
→ M), ∑ i, f i = f 0 + f 1 + f 2 + f 3
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ

--- 原说明 ---
The norm of the components as a Euclidean vector equals the norm of the quaterni
on.
-/
lemma norm_toLp_equivTuple (x : ℍ) : ‖WithLp.toLp 2 (equivTuple ℝ x)‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_self, normSq_def', PiLp.inner_apply,
    Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl

/-- `QuaternionAlgebra.linearEquivTuple` as a `LinearIsometryEquiv`. -/
@[simps apply symm_apply]
/-
**Quaternion.linearIsometryEquivTuple** 是 Mathlib 中的一个定义，位于命名空间 `Quaternion`。
形式化陈述：linearIsometryEquivTuple : ℍ ≃ₗᵢ[Real] EuclideanSpace Real (Fin 4)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `Quaternion.norm_toLp_equivTuple`：norm_toLp_equivTuple (x : ℍ) : ‖WithLp.
toLp 2 (equivTuple Real x)‖ = ‖x‖

--- 原说明 ---
`QuaternionAlgebra.linearEquivTuple` as a `LinearIsometryEquiv`.
-/
def linearIsometryEquivTuple : ℍ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) (0 : ℝ) (-1 : ℝ)).trans
      (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm with
    toFun := fun a => !₂[a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_toLp_equivTuple }

@[continuity]
/-
**Quaternion.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_coe : Continuous (coe : Real -> ℍ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem continuous_coe : Continuous (coe : ℝ → ℍ) :=
  continuous_algebraMap ℝ ℍ

@[continuity]
/-
**Quaternion.continuous_normSq** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_normSq : Continuous (normSq : ℍ -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g 
: X → M}…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
-/
theorem continuous_normSq : Continuous (normSq : ℍ → ℝ) := by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.fun_mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)

@[continuity]
/-
**Quaternion.continuous_re** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_re : Continuous fun q : ℍ => q.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
theorem continuous_re : Continuous fun q : ℍ => q.re :=
  (PiLp.continuous_apply 2 _ 0).comp linearIsometryEquivTuple.continuous

@[continuity]
/-
**Quaternion.continuous_imI** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_imI : Continuous fun q : ℍ => q.imI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
theorem continuous_imI : Continuous fun q : ℍ => q.imI :=
  (PiLp.continuous_apply 2 _ 1).comp linearIsometryEquivTuple.continuous

@[continuity]
/-
**Quaternion.continuous_imJ** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_imJ : Continuous fun q : ℍ => q.imJ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
theorem continuous_imJ : Continuous fun q : ℍ => q.imJ :=
  (PiLp.continuous_apply 2 _ 2).comp linearIsometryEquivTuple.continuous

@[continuity]
/-
**Quaternion.continuous_imK** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_imK : Continuous fun q : ℍ => q.imK
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `PiLp.continuous_apply`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4)
 [inst : (i : ι) → TopologicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp
 i
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
theorem continuous_imK : Continuous fun q : ℍ => q.imK :=
  (PiLp.continuous_apply 2 _ 3).comp linearIsometryEquivTuple.continuous

@[continuity]
/-
**Quaternion.continuous_im** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：continuous_im : Continuous fun q : ℍ => q.im
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Quaternion.continuous_coe`：continuous_coe : Continuous (coe : Real -> ℍ)
· 使用定理 `Quaternion.continuous_re`：continuous_re : Continuous fun q : ℍ => q.re
-/
theorem continuous_im : Continuous fun q : ℍ => q.im := by
  simpa only [← sub_re_self] using! continuous_id.sub (continuous_coe.comp continuous_re)
/-
**Quaternion.** 是 Mathlib 中的一个实例，位于命名空间 `Quaternion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace ℍ :=
  haveI : IsUniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding
  (completeSpace_congr this).1 inferInstance

section infinite_sum

variable {α : Type*} {L : SummationFilter α}

@[simp, norm_cast]
/-
**Quaternion.hasSum_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：hasSum_coe {f : α -> Real} {r : Real} : HasSum (fun a => (f a : ℍ)) (↑r : 
ℍ) L ↔ HasSum f r L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Quaternion.continuous_re`：continuous_re : Continuous fun q : ℍ => q.re
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasSum_coe {f : α → ℝ} {r : ℝ} : HasSum (fun a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L :=
  ⟨fun h => by
    simpa only using!
    h.map (show ℍ →ₗ[ℝ] ℝ from QuaternionAlgebra.reₗ _ _ _) continuous_re,
    fun h => by simpa only using! h.map (algebraMap ℝ ℍ) (continuous_algebraMap _ _)⟩

@[simp, norm_cast]
/-
**Quaternion.summable_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：summable_coe {f : α -> Real} : (Summable (fun a => (f a : ℍ)) L) ↔ Summabl
e f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.map_iff_of_leftInverse`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L 
: SummationFilter β} …
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Quaternion.continuous_re`：continuous_re : Continuous fun q : ℍ => q.re
· 使用定理 `Quaternion.re_coe`：re_coe : (x : ℍ[R]).re = x
-/
theorem summable_coe {f : α → ℝ} : (Summable (fun a => (f a : ℍ)) L) ↔ Summable f L := by
  simpa only using!
    Summable.map_iff_of_leftInverse (algebraMap ℝ ℍ) (show ℍ →ₗ[ℝ] ℝ from
      QuaternionAlgebra.reₗ _ _ _)
      (continuous_algebraMap _ _) continuous_re re_coe

@[norm_cast]
/-
**Quaternion.tsum_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：tsum_coe (f : α -> Real) : (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a)
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Quaternion.continuous_re`：continuous_re : Continuous fun q : ℍ => q.re
· 使用定理 `Quaternion.re_coe`：re_coe : (x : ℍ[R]).re = x
-/
theorem tsum_coe (f : α → ℝ) : (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a) :=
  (Function.LeftInverse.map_tsum f (continuous_algebraMap _ _) continuous_re re_coe).symm

end infinite_sum

end Quaternion

