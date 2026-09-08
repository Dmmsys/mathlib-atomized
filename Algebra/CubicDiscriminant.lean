/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.IntervalCases

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

* `Cubic`: the structure representing a cubic polynomial.
* `Cubic.discr`: the discriminant of a cubic polynomial.

## Main statements

* `Cubic.discr_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
  the cubic has no duplicate roots.

## References

* https://en.wikipedia.org/wiki/Cubic_equation
* https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/

@[expose] public section


noncomputable section

/-- The structure representing a cubic polynomial. -/
@[ext]
/-
**Cubic** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure representing a cubic polynomial.
-/
structure Cubic (R : Type*) where
  /-- The degree-3 coefficient -/
  a : R
  /-- The degree-2 coefficient -/
  b : R
  /-- The degree-1 coefficient -/
  c : R
  /-- The degree-0 coefficient -/
  d : R

namespace Cubic

open Polynomial

variable {R S F K : Type*}

/-
**Cubic.** 是 Mathlib 中的一个实例，位于命名空间 `Cubic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited R] : Inhabited (Cubic R) :=
  ⟨⟨default, default, default, default⟩⟩
/-
**Cubic.** 是 Mathlib 中的一个实例，位于命名空间 `Cubic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] : Zero (Cubic R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

section Basic

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

/-- Convert a cubic polynomial to a polynomial. -/
/-
**Cubic.toPoly** 是 Mathlib 中的一个定义，位于命名空间 `Cubic`。
形式化陈述：toPoly (P : Cubic R) : R[X]
参数：P : Cubic R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a cubic polynomial to a polynomial.
-/
def toPoly (P : Cubic R) : R[X] :=
  C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d
/-
**Cubic.C_mul_prod_X_sub_C_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} : C w * (X - C x) * (X - 
C y) * (X - C z) = toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w *
 -(x * y * z)⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.C_add`：C_add : C (a + b) = C a + C b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 47 条，此处仅展示前 30 条）
-/
theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    C w * (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  simp only [toPoly, C_neg, C_add, C_mul]
  ring1
/-
**Cubic.prod_X_sub_C_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：prod_X_sub_C_eq [CommRing S] {x y z : S} : (X - C x) * (X - C y) * (X - C 
z) = toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Cubic.C_mul_prod_X_sub_C_eq`：C_mul_prod_X_sub_C_eq [CommRing S] {w x y z
 : S} : C w * (X - C x) * (X - C y) * (X - C z) = toPoly ⟨w, w * -(x + y + z), w
 * (x * y + x * z…
-/
theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  rw [← one_mul <| X - C x, ← C_1, C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul]

/-! ### Coefficients -/


section Coeff

/-
**Cubic.coeffs** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]

@[simp]
/-
**Cubic.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：coeff_eq_zero {n : Nat} (hn : 3 < n) : P.toPoly.coeff n = 0
参数：hn : 3 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.coeffs`：∀ {R : Type u
_1} {P : Cubic R} [inst : Semiring R],   (∀ n > 3, P.toPoly.coeff n = 0) ∧     P
.toPoly.coeff 3 = P.a ∧ P.toPoly.coeff 2 = P.b …
-/
theorem coeff_eq_zero {n : ℕ} (hn : 3 < n) : P.toPoly.coeff n = 0 :=
  coeffs.1 n hn

@[simp]
/-
**Cubic.coeff_eq_a** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：coeff_eq_a : P.toPoly.coeff 3 = P.a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.coeffs`：∀ {R : Type u
_1} {P : Cubic R} [inst : Semiring R],   (∀ n > 3, P.toPoly.coeff n = 0) ∧     P
.toPoly.coeff 3 = P.a ∧ P.toPoly.coeff 2 = P.b …
-/
theorem coeff_eq_a : P.toPoly.coeff 3 = P.a :=
  coeffs.2.1

@[simp]
/-
**Cubic.coeff_eq_b** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：coeff_eq_b : P.toPoly.coeff 2 = P.b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.coeffs`：∀ {R : Type u
_1} {P : Cubic R} [inst : Semiring R],   (∀ n > 3, P.toPoly.coeff n = 0) ∧     P
.toPoly.coeff 3 = P.a ∧ P.toPoly.coeff 2 = P.b …
-/
theorem coeff_eq_b : P.toPoly.coeff 2 = P.b :=
  coeffs.2.2.1

@[simp]
/-
**Cubic.coeff_eq_c** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：coeff_eq_c : P.toPoly.coeff 1 = P.c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.coeffs`：∀ {R : Type u
_1} {P : Cubic R} [inst : Semiring R],   (∀ n > 3, P.toPoly.coeff n = 0) ∧     P
.toPoly.coeff 3 = P.a ∧ P.toPoly.coeff 2 = P.b …
-/
theorem coeff_eq_c : P.toPoly.coeff 1 = P.c :=
  coeffs.2.2.2.1

@[simp]
/-
**Cubic.coeff_eq_d** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：coeff_eq_d : P.toPoly.coeff 0 = P.d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.coeffs`：∀ {R : Type u
_1} {P : Cubic R} [inst : Semiring R],   (∀ n > 3, P.toPoly.coeff n = 0) ∧     P
.toPoly.coeff 3 = P.a ∧ P.toPoly.coeff 2 = P.b …
-/
theorem coeff_eq_d : P.toPoly.coeff 0 = P.d :=
  coeffs.2.2.2.2
/-
**Cubic.a_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a
参数：h : P.toPoly = Q.toPoly。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.coeff_eq_a`：coeff_eq_a : P.toPoly.coeff 3 = P.a
-/
theorem a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]
/-
**Cubic.b_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b
参数：h : P.toPoly = Q.toPoly。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.coeff_eq_b`：coeff_eq_b : P.toPoly.coeff 2 = P.b
-/
theorem b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]
/-
**Cubic.c_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c
参数：h : P.toPoly = Q.toPoly。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.coeff_eq_c`：coeff_eq_c : P.toPoly.coeff 1 = P.c
-/
theorem c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]
/-
**Cubic.d_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d
参数：h : P.toPoly = Q.toPoly。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.coeff_eq_d`：coeff_eq_d : P.toPoly.coeff 0 = P.d
-/
theorem d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]
/-
**Cubic.toPoly_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q
参数：P Q : Cubic R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.ext`：∀ {R : Type u_1} {x y : Cubic R}, x.a = y.a → x.b = y.b → x.c
 = y.c → x.d = y.d → x = y
· 使用定理 `Cubic.a_of_eq`：a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a
· 使用定理 `Cubic.b_of_eq`：b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b
· 使用定理 `Cubic.c_of_eq`：c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c
· 使用定理 `Cubic.d_of_eq`：d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q :=
  ⟨fun h ↦ Cubic.ext (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩
/-
**Cubic.of_a_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d
参数：ha : P.a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.toPoly.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (P : Cubic R),  
 P.toPoly =     Polynomial.C P.a * Polynomial.X ^ 3 + Polynomial.C P.b * Polynom
ial.X ^…
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d := by
  rw [toPoly, ha, C_0, zero_mul, zero_add]
/-
**Cubic.of_a_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
-/
theorem of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d :=
  of_a_eq_zero rfl
/-
**Cubic.of_b_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d
参数：ha : P.a = 0；hb : P.b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d := by
  rw [of_a_eq_zero ha, hb, C_0, zero_mul, zero_add]
/-
**Cubic.of_b_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
-/
theorem of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d :=
  of_b_eq_zero rfl rfl
/-
**Cubic.of_c_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P
.d
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P.d := by
  rw [of_b_eq_zero ha hb, hc, C_0, zero_mul, zero_add]
/-
**Cubic.of_c_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.of_c_eq_zero`：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) : P.toPoly = C P.d
-/
theorem of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d :=
  of_c_eq_zero rfl rfl rfl
/-
**Cubic.of_d_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
 P.toPoly = 0
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0；hd : P.d = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_c_eq_zero`：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) : P.toPoly = C P.d
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
-/
theorem of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly = 0 := by
  rw [of_c_eq_zero ha hb hc, hd, C_0]
/-
**Cubic.of_d_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.of_d_eq_zero`：of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) (hd : P.d = 0) : P.toPoly = 0
-/
theorem of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0 :=
  of_d_eq_zero rfl rfl rfl rfl
/-
**Cubic.zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：zero : (0 : Cubic R).toPoly = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.of_d_eq_zero'`：of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0
-/
theorem zero : (0 : Cubic R).toPoly = 0 :=
  of_d_eq_zero'
/-
**Cubic.toPoly_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0
参数：P : Cubic R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.zero`：zero : (0 : Cubic R).toPoly = 0
· 使用定理 `Cubic.toPoly_injective`：toPoly_injective (P Q : Cubic R) : P.toPoly = Q.
toPoly ↔ P = Q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero, toPoly_injective]
/-
**Cubic.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  rw [(toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩
/-
**Cubic.ne_zero_of_a_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：ne_zero_of_a_ne_zero (ha : P.a != 0) : P.toPoly != 0
参数：ha : P.a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.ne_zero`：∀ {R : Type 
u_1} {P : Cubic R} [inst : Semiring R], P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0 → 
P.toPoly ≠ 0
-/
theorem ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp ne_zero).1 ha
/-
**Cubic.ne_zero_of_b_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：ne_zero_of_b_ne_zero (hb : P.b != 0) : P.toPoly != 0
参数：hb : P.b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.ne_zero`：∀ {R : Type 
u_1} {P : Cubic R} [inst : Semiring R], P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0 → 
P.toPoly ≠ 0
-/
theorem ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp ne_zero).2).1 hb
/-
**Cubic.ne_zero_of_c_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：ne_zero_of_c_ne_zero (hc : P.c != 0) : P.toPoly != 0
参数：hc : P.c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.ne_zero`：∀ {R : Type 
u_1} {P : Cubic R} [inst : Semiring R], P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0 → 
P.toPoly ≠ 0
-/
theorem ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).1 hc
/-
**Cubic.ne_zero_of_d_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：ne_zero_of_d_ne_zero (hd : P.d != 0) : P.toPoly != 0
参数：hd : P.d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用定理 `_private.Mathlib.Algebra.CubicDiscriminant.0.Cubic.ne_zero`：∀ {R : Type 
u_1} {P : Cubic R} [inst : Semiring R], P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0 → 
P.toPoly ≠ 0
-/
theorem ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).2 hd

@[simp]
/-
**Cubic.leadingCoeff_of_a_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_a_ne_zero (ha : P.a != 0) : P.toPoly.leadingCoeff = P.a
参数：ha : P.a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_cubic`：leadingCoeff_cubic (ha : a != 0) : leadin
gCoeff (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = a
-/
theorem leadingCoeff_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.leadingCoeff = P.a :=
  leadingCoeff_cubic ha
/-
**Cubic.leadingCoeff_of_a_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_a_ne_zero' (ha : a != 0) : (toPoly ⟨a, b, c, d⟩).leadingCo
eff = a
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.leadingCoeff_of_a_ne_zero`：leadingCoeff_of_a_ne_zero (ha : P.a != 
0) : P.toPoly.leadingCoeff = P.a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).leadingCoeff = a := by
  simp [ha]

@[simp]
/-
**Cubic.leadingCoeff_of_b_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b != 0) : P.toPoly.leadin
gCoeff = P.b
参数：ha : P.a = 0；hb : P.b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
· 使用定理 `Polynomial.leadingCoeff_quadratic`：leadingCoeff_quadratic (ha : a != 0) 
: leadingCoeff (C a * X ^ 2 + C b * X + C c) = a
-/
theorem leadingCoeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.leadingCoeff = P.b := by
  rw [of_a_eq_zero ha, leadingCoeff_quadratic hb]
/-
**Cubic.leadingCoeff_of_b_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_b_ne_zero' (hb : b != 0) : (toPoly ⟨0, b, c, d⟩).leadingCo
eff = b
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.leadingCoeff_of_b_ne_zero`：leadingCoeff_of_b_ne_zero (ha : P.a = 0
) (hb : P.b != 0) : P.toPoly.leadingCoeff = P.b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem leadingCoeff_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).leadingCoeff = b := by
  simp [hb]

@[simp]
/-
**Cubic.leadingCoeff_of_c_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0) : 
P.toPoly.leadingCoeff = P.c
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
· 使用定理 `Polynomial.leadingCoeff_linear`：leadingCoeff_linear (ha : a != 0) : lead
ingCoeff (C a * X + C b) = a
-/
theorem leadingCoeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.leadingCoeff = P.c := by
  rw [of_b_eq_zero ha hb, leadingCoeff_linear hc]
/-
**Cubic.leadingCoeff_of_c_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_c_ne_zero' (hc : c != 0) : (toPoly ⟨0, 0, c, d⟩).leadingCo
eff = c
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.leadingCoeff_of_c_ne_zero`：leadingCoeff_of_c_ne_zero (ha : P.a = 0
) (hb : P.b = 0) (hc : P.c != 0) : P.toPoly.leadingCoeff = P.c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem leadingCoeff_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c := by
  simp [hc]

@[simp]
/-
**Cubic.leadingCoeff_of_c_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P
.toPoly.leadingCoeff = P.d
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_c_eq_zero`：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) : P.toPoly = C P.d
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
theorem leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.leadingCoeff = P.d := by
  rw [of_c_eq_zero ha hb hc, leadingCoeff_C]
/-
**Cubic.leadingCoeff_of_c_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.leadingCoeff_of_c_eq_zero`：leadingCoeff_of_c_eq_zero (ha : P.a = 0
) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.leadingCoeff = P.d
-/
theorem leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d :=
  leadingCoeff_of_c_eq_zero rfl rfl rfl
/-
**Cubic.monic_of_a_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic
参数：ha : P.a = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Cubic.leadingCoeff_of_a_ne_zero`：leadingCoeff_of_a_ne_zero (ha : P.a != 
0) : P.toPoly.leadingCoeff = P.a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero), ha]
/-
**Cubic.monic_of_a_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.monic_of_a_eq_one`：monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Mon
ic
-/
theorem monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic :=
  monic_of_a_eq_one rfl
/-
**Cubic.monic_of_b_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic
参数：ha : P.a = 0；hb : P.b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Cubic.leadingCoeff_of_b_ne_zero`：leadingCoeff_of_b_ne_zero (ha : P.a = 0
) (hb : P.b != 0) : P.toPoly.leadingCoeff = P.b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero), hb]
/-
**Cubic.monic_of_b_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.monic_of_b_eq_one`：monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1)
 : P.toPoly.Monic
-/
theorem monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic :=
  monic_of_b_eq_one rfl rfl
/-
**Cubic.monic_of_c_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.
Monic
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Cubic.leadingCoeff_of_c_ne_zero`：leadingCoeff_of_c_ne_zero (ha : P.a = 0
) (hb : P.b = 0) (hc : P.c != 0) : P.toPoly.leadingCoeff = P.c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero), hc]
/-
**Cubic.monic_of_c_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.monic_of_c_eq_one`：monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0)
 (hc : P.c = 1) : P.toPoly.Monic
-/
theorem monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic :=
  monic_of_c_eq_one rfl rfl rfl
/-
**Cubic.monic_of_d_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d =
 1) : P.toPoly.Monic
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0；hd : P.d = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用定理 `Cubic.leadingCoeff_of_c_eq_zero`：leadingCoeff_of_c_eq_zero (ha : P.a = 0
) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.leadingCoeff = P.d
-/
theorem monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
    P.toPoly.Monic := by
  rw [Monic, leadingCoeff_of_c_eq_zero ha hb hc, hd]
/-
**Cubic.monic_of_d_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.monic_of_d_eq_one`：monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0)
 (hc : P.c = 0) (hd : P.d = 1) : P.toPoly.Monic
-/
theorem monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic :=
  monic_of_d_eq_one rfl rfl rfl rfl

end Coeff

/-! ### Degrees -/


section Degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
@[simps]
/-
**Cubic.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Cubic`。
形式化陈述：equiv : Cubic R ≃ { p : R[X] // p.degree <= 3 } where toFun P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between cubic polynomials and polynomials of degree at most thre
e.
-/
def equiv : Cubic R ≃ { p : R[X] // p.degree ≤ 3 } where
  toFun P := ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [coeffs]
  right_inv f := by
    ext n
    obtain hn | hn := le_or_gt n 3
    · interval_cases n <;> simp only <;> ring_nf <;> try simp only [coeffs]
    · rw [coeff_eq_zero hn, (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2]
      simpa using hn

@[simp]
/-
**Cubic.degree_of_a_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_a_ne_zero (ha : P.a != 0) : P.toPoly.degree = 3
参数：ha : P.a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_cubic`：degree_cubic (ha : a != 0) : degree (C a * X ^ 
3 + C b * X ^ 2 + C c * X + C d) = 3
-/
theorem degree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.degree = 3 :=
  degree_cubic ha
/-
**Cubic.degree_of_a_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_a_ne_zero' (ha : a != 0) : (toPoly ⟨a, b, c, d⟩).degree = 3
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.degree_of_a_ne_zero`：degree_of_a_ne_zero (ha : P.a != 0) : P.toPol
y.degree = 3
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).degree = 3 := by
  simp [ha]
/-
**Cubic.degree_of_a_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree <= 2
参数：ha : P.a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
· 使用定理 `Polynomial.degree_quadratic_le`：degree_quadratic_le : degree (C a * X ^ 
2 + C b * X + C c) <= 2
-/
theorem degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le
/-
**Cubic.degree_of_a_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.degree_of_a_eq_zero`：degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly
.degree <= 2
-/
theorem degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree ≤ 2 :=
  degree_of_a_eq_zero rfl

@[simp]
/-
**Cubic.degree_of_b_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b != 0) : P.toPoly.degree = 2
参数：ha : P.a = 0；hb : P.b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
· 使用定理 `Polynomial.degree_quadratic`：degree_quadratic (ha : a != 0) : degree (C 
a * X ^ 2 + C b * X + C c) = 2
-/
theorem degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.degree = 2 := by
  rw [of_a_eq_zero ha, degree_quadratic hb]
/-
**Cubic.degree_of_b_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_b_ne_zero' (hb : b != 0) : (toPoly ⟨0, b, c, d⟩).degree = 2
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.degree_of_b_ne_zero`：degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b 
!= 0) : P.toPoly.degree = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem degree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).degree = 2 := by
  simp [hb]
/-
**Cubic.degree_of_b_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree <= 1
参数：ha : P.a = 0；hb : P.b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
· 使用定理 `Polynomial.degree_linear_le`：degree_linear_le : degree (C a * X + C b) <
= 1
-/
theorem degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le
/-
**Cubic.degree_of_b_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.degree_of_b_eq_zero`：degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b 
= 0) : P.toPoly.degree <= 1
-/
theorem degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree ≤ 1 :=
  degree_of_b_eq_zero rfl rfl

@[simp]
/-
**Cubic.degree_of_c_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0) : P.toPo
ly.degree = 1
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
· 使用定理 `Polynomial.degree_linear`：degree_linear (ha : a != 0) : degree (C a * X 
+ C b) = 1
-/
theorem degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.toPoly.degree = 1 := by
  rw [of_b_eq_zero ha hb, degree_linear hc]
/-
**Cubic.degree_of_c_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_c_ne_zero' (hc : c != 0) : (toPoly ⟨0, 0, c, d⟩).degree = 1
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.degree_of_c_ne_zero`：degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b 
= 0) (hc : P.c != 0) : P.toPoly.degree = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem degree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).degree = 1 := by
  simp [hc]
/-
**Cubic.degree_of_c_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPol
y.degree <= 0
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_c_eq_zero`：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) : P.toPoly = C P.d
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
-/
theorem degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.degree ≤ 0 := by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le
/-
**Cubic.degree_of_c_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.degree_of_c_eq_zero`：degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b 
= 0) (hc : P.c = 0) : P.toPoly.degree <= 0
-/
theorem degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree ≤ 0 :=
  degree_of_c_eq_zero rfl rfl rfl

@[simp]
/-
**Cubic.degree_of_d_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d
 != 0) : P.toPoly.degree = 0
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0；hd : P.d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_c_eq_zero`：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) : P.toPoly = C P.d
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
-/
theorem degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
    P.toPoly.degree = 0 := by
  rw [of_c_eq_zero ha hb hc, degree_C hd]
/-
**Cubic.degree_of_d_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_d_ne_zero' (hd : d != 0) : (toPoly ⟨0, 0, 0, d⟩).degree = 0
参数：hd : d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.degree_of_d_ne_zero`：degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b 
= 0) (hc : P.c = 0) (hd : P.d != 0) : P.toPoly.degree = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem degree_of_d_ne_zero' (hd : d ≠ 0) : (toPoly ⟨0, 0, 0, d⟩).degree = 0 := by
  simp [hd]

@[simp]
/-
**Cubic.degree_of_d_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d
 = 0) : P.toPoly.degree = ⊥
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0；hd : P.d = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_d_eq_zero`：of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) (hd : P.d = 0) : P.toPoly = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
-/
theorem degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly.degree = ⊥ := by
  rw [of_d_eq_zero ha hb hc hd, degree_zero]
/-
**Cubic.degree_of_d_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.degree_of_d_eq_zero`：degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b 
= 0) (hc : P.c = 0) (hd : P.d = 0) : P.toPoly.degree = ⊥
-/
theorem degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero rfl rfl rfl rfl

@[simp]
/-
**Cubic.degree_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.degree_of_d_eq_zero'`：degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic
 R).toPoly.degree = ⊥
-/
theorem degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero'

@[simp]
/-
**Cubic.natDegree_of_a_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_a_ne_zero (ha : P.a != 0) : P.toPoly.natDegree = 3
参数：ha : P.a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_cubic`：natDegree_cubic (ha : a != 0) : natDegree (C
 a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3
-/
theorem natDegree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.natDegree = 3 :=
  natDegree_cubic ha
/-
**Cubic.natDegree_of_a_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_a_ne_zero' (ha : a != 0) : (toPoly ⟨a, b, c, d⟩).natDegree = 
3
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.natDegree_of_a_ne_zero`：natDegree_of_a_ne_zero (ha : P.a != 0) : P
.toPoly.natDegree = 3
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).natDegree = 3 := by
  simp [ha]
/-
**Cubic.natDegree_of_a_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree <= 2
参数：ha : P.a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
· 使用定理 `Polynomial.natDegree_quadratic_le`：natDegree_quadratic_le : natDegree (C
 a * X ^ 2 + C b * X + C c) <= 2
-/
theorem natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le
/-
**Cubic.natDegree_of_a_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.natDegree_of_a_eq_zero`：natDegree_of_a_eq_zero (ha : P.a = 0) : P.
toPoly.natDegree <= 2
-/
theorem natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree ≤ 2 :=
  natDegree_of_a_eq_zero rfl

@[simp]
/-
**Cubic.natDegree_of_b_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_b_ne_zero (ha : P.a = 0) (hb : P.b != 0) : P.toPoly.natDegree
 = 2
参数：ha : P.a = 0；hb : P.b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_a_eq_zero`：of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^
 2 + C P.c * X + C P.d
· 使用定理 `Polynomial.natDegree_quadratic`：natDegree_quadratic (ha : a != 0) : natD
egree (C a * X ^ 2 + C b * X + C c) = 2
-/
theorem natDegree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.natDegree = 2 := by
  rw [of_a_eq_zero ha, natDegree_quadratic hb]
/-
**Cubic.natDegree_of_b_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_b_ne_zero' (hb : b != 0) : (toPoly ⟨0, b, c, d⟩).natDegree = 
2
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.natDegree_of_b_ne_zero`：natDegree_of_b_ne_zero (ha : P.a = 0) (hb 
: P.b != 0) : P.toPoly.natDegree = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem natDegree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).natDegree = 2 := by
  simp [hb]
/-
**Cubic.natDegree_of_b_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree 
<= 1
参数：ha : P.a = 0；hb : P.b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
· 使用定理 `Polynomial.natDegree_linear_le`：natDegree_linear_le : natDegree (C a * X
 + C b) <= 1
-/
theorem natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le
/-
**Cubic.natDegree_of_b_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.natDegree_of_b_eq_zero`：natDegree_of_b_eq_zero (ha : P.a = 0) (hb 
: P.b = 0) : P.toPoly.natDegree <= 1
-/
theorem natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree ≤ 1 :=
  natDegree_of_b_eq_zero rfl rfl

@[simp]
/-
**Cubic.natDegree_of_c_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0) : P.t
oPoly.natDegree = 1
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_b_eq_zero`：of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPol
y = C P.c * X + C P.d
· 使用定理 `Polynomial.natDegree_linear`：natDegree_linear (ha : a != 0) : natDegree 
(C a * X + C b) = 1
-/
theorem natDegree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.natDegree = 1 := by
  rw [of_b_eq_zero ha hb, natDegree_linear hc]
/-
**Cubic.natDegree_of_c_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_c_ne_zero' (hc : c != 0) : (toPoly ⟨0, 0, c, d⟩).natDegree = 
1
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.natDegree_of_c_ne_zero`：natDegree_of_c_ne_zero (ha : P.a = 0) (hb 
: P.b = 0) (hc : P.c != 0) : P.toPoly.natDegree = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem natDegree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).natDegree = 1 := by
  simp [hc]

@[simp]
/-
**Cubic.natDegree_of_c_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.to
Poly.natDegree = 0
参数：ha : P.a = 0；hb : P.b = 0；hc : P.c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.of_c_eq_zero`：of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c
 = 0) : P.toPoly = C P.d
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
-/
theorem natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.natDegree = 0 := by
  rw [of_c_eq_zero ha hb hc, natDegree_C]
/-
**Cubic.natDegree_of_c_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.natDegree_of_c_eq_zero`：natDegree_of_c_eq_zero (ha : P.a = 0) (hb 
: P.b = 0) (hc : P.c = 0) : P.toPoly.natDegree = 0
-/
theorem natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0 :=
  natDegree_of_c_eq_zero rfl rfl rfl

@[simp]
/-
**Cubic.natDegree_of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cubic.natDegree_of_c_eq_zero'`：natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 
0, d⟩).natDegree = 0
-/
theorem natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0 :=
  natDegree_of_c_eq_zero'

end Degree

/-! ### Map across a homomorphism -/


section Map

variable [Semiring S] {φ : R →+* S}

/-- Map a cubic polynomial across a semiring homomorphism. -/
/-
**Cubic.map** 是 Mathlib 中的一个定义，位于命名空间 `Cubic`。
形式化陈述：map (φ : R ->+* S) (P : Cubic R) : Cubic S
参数：φ : R ->+* S；P : Cubic R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a cubic polynomial across a semiring homomorphism.
-/
def map (φ : R →+* S) (P : Cubic R) : Cubic S :=
  ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩
/-
**Cubic.map_toPoly** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

end Map

end Basic

section Roots

open Multiset

/-! ### Roots over an extension -/


section Extension

variable {P : Cubic R} [CommRing R] [CommRing S] {φ : R →+* S}

/-- The roots of a cubic polynomial. -/
/-
**Cubic.roots** 是 Mathlib 中的一个定义，位于命名空间 `Cubic`。
形式化陈述：roots [IsDomain R] (P : Cubic R) : Multiset R
参数：P : Cubic R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The roots of a cubic polynomial.
-/
def roots [IsDomain R] (P : Cubic R) : Multiset R :=
  P.toPoly.roots
/-
**Cubic.map_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roo
ts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.roots.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomai
n R] (P : Cubic R), P.roots = P.toPoly.roots
· 使用定理 `Cubic.map_toPoly`：map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toP
oly
-/
theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  rw [roots, map_toPoly]
/-
**Cubic.mem_roots_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：mem_roots_iff [IsDomain R] (h0 : P.toPoly != 0) (x : R) : x in P.roots ↔ P
.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0
参数：h0 : P.toPoly != 0；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.roots.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomai
n R] (P : Cubic R), P.roots = P.toPoly.roots
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Cubic.toPoly.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (P : Cubic R),  
 P.toPoly =     Polynomial.C P.a * Polynomial.X ^ 3 + Polynomial.C P.b * Polynom
ial.X ^…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_roots_iff [IsDomain R] (h0 : P.toPoly ≠ 0) (x : R) :
    x ∈ P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [roots, mem_roots h0, IsRoot, toPoly]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
/-
**Cubic.card_roots_le** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card <= 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Polynomial.card_roots`：card_roots (hp0 : p != 0) : (Multiset.card (roots
 p) : WithBot Nat) <= degree p
· 使用定理 `Polynomial.degree_cubic_le`：degree_cubic_le : degree (C a * X ^ 3 + C b 
* X ^ 2 + C c * X + C d) <= 3
-/
theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · simp [hP]
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/


section Split

/-
**Cubic.splits_iff_card_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：splits_iff_card_roots (ha : P.a != 0) : Splits (P.toPoly.map φ) ↔ (map φ P
).roots.card = 3
参数：ha : P.a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.roots.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomai
n R] (P : Cubic R), P.roots = P.toPoly.roots
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.map_toPoly`：map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toP
oly
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq`：degree_eq_iff_natDegree_eq {p : R
[X]} {n : Nat} (hp : p != 0) : p.degree = n ↔ p.natDegree = n
· 使用定理 `Cubic.ne_zero_of_a_ne_zero`：ne_zero_of_a_ne_zero (ha : P.a != 0) : P.toP
oly != 0
· 使用定理 `Cubic.degree_of_a_ne_zero`：degree_of_a_ne_zero (ha : P.a != 0) : P.toPol
y.degree = 3
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem splits_iff_card_roots (ha : P.a ≠ 0) :
    Splits (P.toPoly.map φ) ↔ (map φ P).roots.card = 3 := by
  replace ha : (map φ P).a ≠ 0 := (map_ne_zero φ).mpr ha
  rw [roots, ← map_toPoly, Polynomial.splits_iff_card_roots,
    ← ((degree_eq_iff_natDegree_eq <| ne_zero_of_a_ne_zero ha).1 <| degree_of_a_ne_zero ha : _ = 3)]
/-
**Cubic.splits_iff_roots_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：splits_iff_roots_eq_three (ha : P.a != 0) : Splits (P.toPoly.map φ) ↔ exis
ts x y z : K, (map φ P).roots = {x, y, z}
参数：ha : P.a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.splits_iff_card_roots`：splits_iff_card_roots (ha : P.a != 0) : Spl
its (P.toPoly.map φ) ↔ (map φ P).roots.card = 3
· 使用定理 `Multiset.card_eq_three`：card_eq_three {s : Multiset α} : card s = 3 ↔ ex
ists x y z, s = {x, y, z}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) :
    Splits (P.toPoly.map φ) ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} := by
  rw [splits_iff_card_roots ha, card_eq_three]
/-
**Cubic.eq_prod_three_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：eq_prod_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) : (
map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z)
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.map_toPoly`：map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toP
oly
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cubic.splits_iff_roots_eq_three`：splits_iff_roots_eq_three (ha : P.a != 
0) : Splits (P.toPoly.map φ) ↔ exists x y z : K, (map φ P).roots = {x, y, z}
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Cubic.leadingCoeff_of_a_ne_zero`：leadingCoeff_of_a_ne_zero (ha : P.a != 
0) : P.toPoly.leadingCoeff = P.a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.map_roots`：map_roots [IsDomain S] : (map φ P).roots = (Polynomial.
map φ P.toPoly).roots
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    (map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) := by
  rw [map_toPoly,
    Splits.eq_prod_roots <|
      (splits_iff_roots_eq_three ha).mpr <| Exists.intro x <| Exists.intro y <| Exists.intro z h3,
    leadingCoeff_map, leadingCoeff_of_a_ne_zero ha, ← map_roots, h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
/-
**Cubic.eq_sum_three_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：eq_sum_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) : ma
p φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -
(x * y * z)⟩
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cubic.toPoly_injective`：toPoly_injective (P Q : Cubic R) : P.toPoly = Q.
toPoly ↔ P = Q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.eq_prod_three_roots`：eq_prod_three_roots (ha : P.a != 0) (h3 : (ma
p φ P).roots = {x, y, z}) : (map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y)
 * (X - C z)
· 使用定理 `Cubic.C_mul_prod_X_sub_C_eq`：C_mul_prod_X_sub_C_eq [CommRing S] {w x y z
 : S} : C w * (X - C x) * (X - C y) * (X - C z) = toPoly ⟨w, w * -(x + y + z), w
 * (x * y + x * z…
-/
theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    map φ P =
      ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ := by
  apply_fun toPoly
  · rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
  · exact fun P Q ↦ (toPoly_injective P Q).mp
/-
**Cubic.b_eq_three_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：b_eq_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) : φ P.
b = φ P.a * -(x + y + z)
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Cubic.eq_sum_three_roots`：eq_sum_three_roots (ha : P.a != 0) (h3 : (map 
φ P).roots = {x, y, z}) : map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y
 + x * z + y *…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem b_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.b = φ P.a * -(x + y + z) := by
  injection eq_sum_three_roots ha h3
/-
**Cubic.c_eq_three_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：c_eq_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) : φ P.
c = φ P.a * (x * y + x * z + y * z)
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Cubic.eq_sum_three_roots`：eq_sum_three_roots (ha : P.a != 0) (h3 : (map 
φ P).roots = {x, y, z}) : map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y
 + x * z + y *…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem c_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.c = φ P.a * (x * y + x * z + y * z) := by
  injection eq_sum_three_roots ha h3
/-
**Cubic.d_eq_three_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：d_eq_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) : φ P.
d = φ P.a * -(x * y * z)
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Cubic.eq_sum_three_roots`：eq_sum_three_roots (ha : P.a != 0) (h3 : (map 
φ P).roots = {x, y, z}) : map φ P = ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y
 + x * z + y *…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem d_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.d = φ P.a * -(x * y * z) := by
  injection eq_sum_three_roots ha h3

end Split

/-! ### Discriminant over a splitting field -/


section Discriminant

/-- The discriminant of a cubic polynomial. -/
/-
**Cubic.discr** 是 Mathlib 中的一个定义，位于命名空间 `Cubic`。
形式化陈述：discr {R : Type*} [Ring R] (P : Cubic R) : R
参数：P : Cubic R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discriminant of a cubic polynomial.
-/
def discr {R : Type*} [Ring R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d
/-
**Cubic.discr_eq_prod_three_roots** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：discr_eq_prod_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z
}) : φ P.discr = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Cubic.b_eq_three_roots`：b_eq_three_roots (ha : P.a != 0) (h3 : (map φ P)
.roots = {x, y, z}) : φ P.b = φ P.a * -(x + y + z)
· 使用定理 `Cubic.c_eq_three_roots`：c_eq_three_roots (ha : P.a != 0) (h3 : (map φ P)
.roots = {x, y, z}) : φ P.c = φ P.a * (x * y + x * z + y * z)
· 使用定理 `Cubic.d_eq_three_roots`：d_eq_three_roots (ha : P.a != 0) (h3 : (map φ P)
.roots = {x, y, z}) : φ P.d = φ P.a * -(x * y * z)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 74 条，此处仅展示前 30 条）
-/
theorem discr_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.discr = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
  simp only [discr, RingHom.map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3]
  ring1
/-
**Cubic.discr_ne_zero_iff_roots_ne** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：discr_ne_zero_iff_roots_ne (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, 
z}) : P.discr != 0 ↔ x != y ∧ x != z ∧ y != z
参数：ha : P.a != 0；h3 : (map φ P).roots = {x, y, z}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Cubic.discr_eq_prod_three_roots`：discr_eq_prod_three_roots (ha : P.a != 
0) (h3 : (map φ P).roots = {x, y, z}) : φ P.discr = (φ P.a * φ P.a * (x - y) * (
x - z) * (y - z)) ^ 2
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem discr_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.discr ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  rw [← map_ne_zero φ, discr_eq_prod_three_roots ha h3, pow_two]
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self_iff, and_iff_right ha,
    and_assoc]
/-
**Cubic.discr_ne_zero_iff_roots_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：discr_ne_zero_iff_roots_nodup (ha : P.a != 0) (hP : (P.toPoly.map φ).Split
s) : P.discr != 0 ↔ (map φ P).roots.Nodup
参数：ha : P.a != 0；hP : (P.toPoly.map φ).Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cubic.splits_iff_roots_eq_three`：splits_iff_roots_eq_three (ha : P.a != 
0) : Splits (P.toPoly.map φ) ↔ exists x y z : K, (map φ P).roots = {x, y, z}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cubic.discr_ne_zero_iff_roots_ne`：discr_ne_zero_iff_roots_ne (ha : P.a !
= 0) (h3 : (map φ P).roots = {x, y, z}) : P.discr != 0 ↔ x != y ∧ x != z ∧ y != 
z
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem discr_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (hP : (P.toPoly.map φ).Splits) :
    P.discr ≠ 0 ↔ (map φ P).roots.Nodup := by
  have ⟨x, y, z, h3⟩ := (splits_iff_roots_eq_three ha).mp hP
  rw [discr_ne_zero_iff_roots_ne ha h3, h3]
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton]
  simp only [nodup_singleton]
  tauto
/-
**Cubic.card_roots_of_discr_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cubic`。
形式化陈述：card_roots_of_discr_ne_zero [DecidableEq K] (ha : P.a != 0) (h3 : (P.toPol
y.map φ).Splits) (hd : P.discr != 0) : (map φ P).roots.toFinset.card = 3
参数：ha : P.a != 0；h3 : (P.toPoly.map φ).Splits；hd : P.discr != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.toFinset_card_of_nodup`：Multiset.toFinset_card_of_nodup {m : Mu
ltiset α} (h : m.Nodup) : #m.toFinset = Multiset.card m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cubic.discr_ne_zero_iff_roots_nodup`：discr_ne_zero_iff_roots_nodup (ha :
 P.a != 0) (hP : (P.toPoly.map φ).Splits) : P.discr != 0 ↔ (map φ P).roots.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cubic.splits_iff_card_roots`：splits_iff_card_roots (ha : P.a != 0) : Spl
its (P.toPoly.map φ) ↔ (map φ P).roots.card = 3
-/
theorem card_roots_of_discr_ne_zero [DecidableEq K] (ha : P.a ≠ 0) (h3 : (P.toPoly.map φ).Splits)
    (hd : P.discr ≠ 0) : (map φ P).roots.toFinset.card = 3 := by
  rwa [toFinset_card_of_nodup <| (discr_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← splits_iff_card_roots ha]

end Discriminant

end Roots

end Cubic

