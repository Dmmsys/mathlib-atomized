/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Group action on the upper half-plane

We equip the upper half-plane with the structure of a `GL (Fin 2) ℝ` action by fractional linear
transformations (composing with complex conjugation when needed to extend the action from the
positive-determinant subgroup, so that `!![-1, 0; 0, 1]` acts as `z ↦ -conj z`.)
-/

@[expose] public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace UpperHalfPlane

/-- Numerator of the formula for a fractional linear transformation -/
/-
**UpperHalfPlane.num** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：num (g : GL (Fin 2) Real) (z : Complex) : Complex
参数：g : GL (Fin 2) Real；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Numerator of the formula for a fractional linear transformation
-/
def num (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := g 0 0 * z + g 0 1

/-- Denominator of the formula for a fractional linear transformation -/
/-
**UpperHalfPlane.denom** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom (g : GL (Fin 2) Real) (z : Complex) : Complex
参数：g : GL (Fin 2) Real；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Denominator of the formula for a fractional linear transformation
-/
def denom (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := g 1 0 * z + g 1 1

@[simp]
/-
**UpperHalfPlane.num_neg** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：num_neg (g : GL (Fin 2) Real) (z : Complex) : num (-g) z = -(num g z)
参数：g : GL (Fin 2) Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 32 条，此处仅展示前 30 条）
-/
lemma num_neg (g : GL (Fin 2) ℝ) (z : ℂ) : num (-g) z = -(num g z) := by
  simp [num]; ring

@[simp]
/-
**UpperHalfPlane.denom_neg** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_neg (g : GL (Fin 2) Real) (z : Complex) : denom (-g) z = -(denom g z
)
参数：g : GL (Fin 2) Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 32 条，此处仅展示前 30 条）
-/
lemma denom_neg (g : GL (Fin 2) ℝ) (z : ℂ) : denom (-g) z = -(denom g z) := by
  simp [denom]; ring
/-
**UpperHalfPlane.linear_ne_zero_of_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`
。
形式化陈述：linear_ne_zero_of_im {cd : Fin 2 -> Real} {z : Complex} (hz : z.im != 0) (
h : cd != 0) : (cd 0 : Complex) * z + cd 1 != 0
参数：hz : z.im != 0；h : cd != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem linear_ne_zero_of_im {cd : Fin 2 → ℝ} {z : ℂ} (hz : z.im ≠ 0) (h : cd ≠ 0) :
    (cd 0 : ℂ) * z + cd 1 ≠ 0 := by
  contrapose h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, mul_eq_zero, hz, or_false] using! h
  simp only [this, zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_eq_zero] at h
  ext i
  fin_cases i <;> assumption
/-
**UpperHalfPlane.linear_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：linear_ne_zero {cd : Fin 2 -> Real} (τ : ℍ) (h : cd != 0) : (cd 0 : Comple
x) * τ + cd 1 != 0
参数：τ : ℍ；h : cd != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.linear_ne_zero_of_im`：linear_ne_zero_of_im {cd : Fin 2 ->
 Real} {z : Complex} (hz : z.im != 0) (h : cd != 0) : (cd 0 : Complex) * z + cd 
1 != 0
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
-/
theorem linear_ne_zero {cd : Fin 2 → ℝ} (τ : ℍ) (h : cd ≠ 0) :
    (cd 0 : ℂ) * τ + cd 1 ≠ 0 :=
  linear_ne_zero_of_im τ.im_ne_zero h
/-
**UpperHalfPlane.denom_ne_zero_of_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_ne_zero_of_im (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) :
 denom g z != 0
参数：g : GL (Fin 2) Real；hz : z.im != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.linear_ne_zero_of_im`：linear_ne_zero_of_im {cd : Fin 2 ->
 Real} {z : Complex} (hz : z.im != 0) (h : cd != 0) : (cd 0 : Complex) * z + cd 
1 != 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem denom_ne_zero_of_im (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : denom g z ≠ 0 := by
  refine linear_ne_zero_of_im hz fun H ↦ g.det.ne_zero ?_
  simp [Matrix.det_fin_two, H]

@[simp]
/-
**UpperHalfPlane.denom_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ) : denom g z != 0
参数：g : GL (Fin 2) Real；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.denom_ne_zero_of_im`：denom_ne_zero_of_im (g : GL (Fin 2) 
Real) {z : Complex} (hz : z.im != 0) : denom g z != 0
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
-/
theorem denom_ne_zero (g : GL (Fin 2) ℝ) (z : ℍ) : denom g z ≠ 0 :=
  denom_ne_zero_of_im g z.im_ne_zero
/-
**UpperHalfPlane.normSq_denom_pos** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：normSq_denom_pos (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) : 0 
< Complex.normSq (denom g z)
参数：g : GL (Fin 2) Real；hz : z.im != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.normSq_pos`：normSq_pos {z : Complex} : 0 < normSq z ↔ z != 0
· 使用定理 `UpperHalfPlane.denom_ne_zero_of_im`：denom_ne_zero_of_im (g : GL (Fin 2) 
Real) {z : Complex} (hz : z.im != 0) : denom g z != 0
-/
theorem normSq_denom_pos (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)
/-
**UpperHalfPlane.normSq_denom_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`
。
形式化陈述：normSq_denom_ne_zero (g : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) 
: Complex.normSq (denom g z) != 0
参数：g : GL (Fin 2) Real；hz : z.im != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `UpperHalfPlane.normSq_denom_pos`：normSq_denom_pos (g : GL (Fin 2) Real) 
{z : Complex} (hz : z.im != 0) : 0 < Complex.normSq (denom g z)
-/
theorem normSq_denom_ne_zero (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gt (normSq_denom_pos g hz)
/-
**UpperHalfPlane.denom_cocycle** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_cocycle (g h : GL (Fin 2) Real) {z : Complex} (hz : z.im != 0) : den
om (g * h) z = denom g (num h z / denom h z) * denom h z
参数：g h : GL (Fin 2) Real；hz : z.im != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `UpperHalfPlane.denom_ne_zero_of_im`：denom_ne_zero_of_im (g : GL (Fin 2) 
Real) {z : Complex} (hz : z.im != 0) : denom g z != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
（共 63 条，此处仅展示前 30 条）
-/
lemma denom_cocycle (g h : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    denom (g * h) z = denom g (num h z / denom h z) * denom h z := by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero_of_im h hz]
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring
/-
**UpperHalfPlane.moebius_im** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：moebius_im (g : GL (Fin 2) Real) (z : Complex) : (num g z / denom g z).im 
= g.det.val * z.im / Complex.normSq (denom g z)
参数：g : GL (Fin 2) Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.div_im`：div_im (z w : Complex) : (z / w).im = z.im * w.re / norm
Sq w - z.re * w.im / normSq w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 52 条，此处仅展示前 30 条）
-/
lemma moebius_im (g : GL (Fin 2) ℝ) (z : ℂ) :
    (num g z / denom g z).im = g.det.val * z.im / Complex.normSq (denom g z) := by
  simp only [num, denom, Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    GeneralLinearGroup.val_det_apply, g.1.det_fin_two]
  ring

/-- Automorphism of `ℂ`: the identity if `0 < det g` and conjugation otherwise. -/
/-
**UpperHalfPlane.** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Automorphism of `ℂ`: the identity if `0 < det g` and conjugation otherwise.
-/
noncomputable def σ (g : GL (Fin 2) ℝ) : ℂ ≃A[ℝ] ℂ :=
  if 0 < g.det.val then .refl ℝ ℂ else Complex.conjCAE
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_conj (g : GL (Fin 2) ℝ) (z : ℂ) : σ g (conj z) = conj (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

@[simp]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_ofReal (g : GL (Fin 2) ℝ) (y : ℝ) : σ g y = y := by
  simp only [σ]
  split_ifs <;> simp
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_num (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (num h z) = num h (σ g z) := by
  simp [num]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_denom (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (denom h z) = denom h (σ g z) := by
  simp [denom]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_neg (g : GL (Fin 2) ℝ) : σ (-g) = σ g := by
  simp [σ, det_neg]

@[simp]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_sq (g : GL (Fin 2) ℝ) (z : ℂ) : σ g (σ g z) = z := by
  simp only [σ]
  split_ifs <;> simp
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_im_ne_zero {g z} : (σ g z).im ≠ 0 ↔ z.im ≠ 0 := by
  simp only [σ]
  split_ifs <;> simp
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_mul (g g' : GL (Fin 2) ℝ) (z : ℂ) : σ (g * g') z = σ g (σ g' z) := by
  simp only [σ, map_mul, Units.val_mul]
  rcases g.det_ne_zero.lt_or_gt with (h | h) <;>
  rcases g'.det_ne_zero.lt_or_gt with (h' | h')
  · simp [mul_pos_of_neg_of_neg h h', h.not_gt, h'.not_gt]
  · simp [(mul_neg_of_neg_of_pos h h').not_gt, h.not_gt, h']
  · simp [(mul_neg_of_pos_of_neg h h').not_gt, h, h'.not_gt]
  · simp [mul_pos h h', h, h']
/-
**UpperHalfPlane.** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_mul_comm (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (σ h z) = σ h (σ g z) := by
  simp only [σ]
  split_ifs <;> simp
/-
**UpperHalfPlane.norm_** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_σ (g : GL (Fin 2) ℝ) (z : ℂ) : ‖σ g z‖ = ‖z‖ := by
  simp only [σ]
  split_ifs <;> simp

/-- Fractional linear transformation, also known as the Moebius transformation -/
/-
**UpperHalfPlane.smulAux'** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：smulAux' (g : GL (Fin 2) Real) (z : Complex) : Complex
参数：g : GL (Fin 2) Real；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional linear transformation, also known as the Moebius transformation
-/
def smulAux' (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := σ g (num g z / denom g z)
/-
**UpperHalfPlane.smulAux'_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (g : GL (Fin 2) ℝ) (z : ℂ),   (UpperHalfPlane.smulAux' g z).im =     |↑(
Matrix.GeneralLinearGroup.det g)| * z.im / Complex.normSq (UpperHalfPlane.denom 
g z)
参数：g : GL (Fin 2) ℝ；z : ℂ；UpperHalfPlane.smulAux' g z；Matrix.GeneralLinearGroup.
det g；UpperHalfPlane.denom g z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `UpperHalfPlane.moebius_im`：moebius_im (g : GL (Fin 2) Real) (z : Complex
) : (num g z / denom g z).im = g.det.val * z.im / Complex.normSq (denom g z)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
-/
lemma smulAux'_im (g : GL (Fin 2) ℝ) (z : ℂ) :
    (smulAux' g z).im = |g.det.val| * z.im / Complex.normSq (denom g z) := by
  simp only [smulAux', σ]
  split_ifs with h <;>
  [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]] <;>
  simpa only [Complex.conjCAE_apply, Complex.star_def, Complex.conj_im,
    neg_mul, neg_div, neg_inj] using! moebius_im g z

/-- Fractional linear transformation, also known as the Moebius transformation -/
/-
**UpperHalfPlane.smulAux** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：smulAux (g : GL (Fin 2) Real) (z : ℍ) : ℍ
参数：g : GL (Fin 2) Real；z : ℍ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fractional linear transformation, also known as the Moebius transformation
-/
def smulAux (g : GL (Fin 2) ℝ) (z : ℍ) : ℍ :=
  mk (smulAux' g z) <| by
    rw [smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) z.im_pos) (normSq_denom_pos _ z.im_ne_zero)
/-
**UpperHalfPlane.denom_cocycle'** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_cocycle' (g h : GL (Fin 2) Real) (z : ℍ) : denom (g * h) z = σ h (de
nom g (smulAux h z)) * denom h z
参数：g h : GL (Fin 2) Real；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `UpperHalfPlane.σ_ofReal`：σ_ofReal (g : GL (Fin 2) Real) (y : Real) : σ g
 y = y
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用引理 `UpperHalfPlane.σ_sq`：σ_sq (g : GL (Fin 2) Real) (z : Complex) : σ g (σ g
 z) = z
· 使用引理 `UpperHalfPlane.denom_cocycle`：denom_cocycle (g h : GL (Fin 2) Real) {z :
 Complex} (hz : z.im != 0) : denom (g * h) z = denom g (num h z / denom h z) * d
enom h z
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
-/
lemma denom_cocycle' (g h : GL (Fin 2) ℝ) (z : ℍ) :
    denom (g * h) z = σ h (denom g (smulAux h z)) * denom h z := by
  simpa [smulAux, smulAux', denom, σ_sq] using denom_cocycle g h z.im_ne_zero
/-
**UpperHalfPlane.mul_smul'** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mul_smul' (g h : GL (Fin 2) Real) (z : ℍ) : smulAux (g * h) z = smulAux g 
(smulAux h z)
参数：g h : GL (Fin 2) Real；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用引理 `UpperHalfPlane.σ_num`：σ_num (g h : GL (Fin 2) Real) (z : Complex) : σ g 
(num h z) = num h (σ g z)
· 使用引理 `UpperHalfPlane.σ_mul`：σ_mul (g g' : GL (Fin 2) Real) (z : Complex) : σ (
g * g') z = σ g (σ g' z)
· 使用引理 `UpperHalfPlane.σ_denom`：σ_denom (g h : GL (Fin 2) Real) (z : Complex) : 
σ g (denom h z) = denom h (σ g z)
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用引理 `UpperHalfPlane.moebius_im`：moebius_im (g : GL (Fin 2) Real) (z : Complex
) : (num g z / denom g z).im = g.det.val * z.im / Complex.normSq (denom g z)
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `UpperHalfPlane.normSq_denom_ne_zero`：normSq_denom_ne_zero (g : GL (Fin 2
) Real) {z : Complex} (hz : z.im != 0) : Complex.normSq (denom g z) != 0
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `UpperHalfPlane.denom_ne_zero_of_im`：denom_ne_zero_of_im (g : GL (Fin 2) 
Real) {z : Complex} (hz : z.im != 0) : denom g z != 0
· 使用定理 `UpperHalfPlane.denom.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), UpperHalfPlane.
denom g z = ↑(↑g 1 0) * z + ↑(↑g 1 1)
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `div_add'`：div_add' (a b c : K) (hc : c != 0) : a / c + b = (a + b * c) /
 c
· 使用定理 `UpperHalfPlane.num.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), UpperHalfPlane.nu
m g z = ↑(↑g 0 0) * z + ↑(↑g 0 1)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
（共 59 条，此处仅展示前 30 条）
-/
theorem mul_smul' (g h : GL (Fin 2) ℝ) (z : ℍ) :
    smulAux (g * h) z = smulAux g (smulAux h z) := by
  ext : 1
  simp only [smulAux, coe_mk, smulAux', map_div₀, σ_num, σ_denom, σ_mul]
  generalize hu : σ g (σ h z) = u
  have hu : u.im ≠ 0 := by simpa only [← hu, σ_im_ne_zero] using! z.im_ne_zero
  have hu' : (num h u / denom h u).im ≠ 0 := by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_zero h.det_ne_zero hu) (normSq_denom_ne_zero _ hu)
  rw [div_eq_div_iff (denom_ne_zero_of_im _ hu) (denom_ne_zero_of_im _ hu'),
    denom, mul_div, div_add' _ _ _ (denom_ne_zero_of_im _ hu), mul_div]
  conv_rhs => rw [num]
  rw [mul_div, div_add' _ _ _ (denom_ne_zero_of_im _ hu), div_mul_eq_mul_div]
  congr 1
  simp only [num, denom, Units.val_mul, mul_apply, Fin.sum_univ_succ,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- Action of `GL (Fin 2) ℝ` on the upper half-plane, with `GL(2, ℝ)⁺` acting by Moebius
transformations in the usual way, extended to all of `GL (Fin 2) ℝ` using complex conjugation. -/
/-
**UpperHalfPlane.glAction** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：glAction : MulAction (GL (Fin 2) Real) ℍ where smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.mul_smul'`：mul_smul' (g h : GL (Fin 2) Real) (z : ℍ) : sm
ulAux (g * h) z = smulAux g (smulAux h z)

--- 原说明 ---
Action of `GL (Fin 2) ℝ` on the upper half-plane, with `GL(2, ℝ)⁺` acting by Moe
bius
transformations in the usual way, extended to all of `GL (Fin 2) ℝ` using comple
x conjugation.
-/
instance glAction : MulAction (GL (Fin 2) ℝ) ℍ where
  smul := smulAux
  one_smul z := by
    change smulAux 1 z = z
    simp [smulAux, smulAux', num, denom, σ]
  mul_smul := mul_smul'
/-
**UpperHalfPlane.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_smul (g : GL (Fin 2) Real) (z : ℍ) : ↑(g • z) = σ g (num g z / denom g
 z)
参数：g : GL (Fin 2) Real；z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (g : GL (Fin 2) ℝ) (z : ℍ) :
    ↑(g • z) = σ g (num g z / denom g z) := rfl
/-
**UpperHalfPlane.coe_smul_of_det_pos** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_smul_of_det_pos {g : GL (Fin 2) Real} (hg : 0 < g.det.val) (z : ℍ) : ↑
(g • z) = num g z / denom g z
参数：Fin 2；hg : 0 < g.det.val；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.smulAux'.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ),   UpperHalfP
lane.smulAux' g z = (UpperHalfPlane.σ g) (UpperHalfPlane.num g z / UpperHalfPlan
e.denom g z)
· 使用定理 `UpperHalfPlane.σ.eq_1`：∀ (g : GL (Fin 2) ℝ),   UpperHalfPlane.σ g = if 0
 < ↑(Matrix.GeneralLinearGroup.det g) then ContinuousAlgEquiv.refl ℝ ℂ else Comp
lex.conjCAE
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ContinuousAlgEquiv.refl_apply`：refl_apply (a : A) : refl R A a = a
· 使用定理 `UpperHalfPlane.num.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), UpperHalfPlane.nu
m g z = ↑(↑g 0 0) * z + ↑(↑g 0 1)
· 使用定理 `UpperHalfPlane.denom.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), UpperHalfPlane.
denom g z = ↑(↑g 1 0) * z + ↑(↑g 1 1)
-/
lemma coe_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    ↑(g • z) = num g z / denom g z := by
  change smulAux' g z = _
  rw [smulAux', σ, if_pos hg, ContinuousAlgEquiv.refl_apply, num, denom]
/-
**UpperHalfPlane.denom_cocycle_** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma denom_cocycle_σ (g h : GL (Fin 2) ℝ) (z : ℍ) :
    denom (g * h) z = σ h (denom g ↑(h • z)) * denom h z :=
  denom_cocycle' g h z
/-
**UpperHalfPlane.glPos_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：glPos_smul_def {g : GL (Fin 2) Real} (hg : 0 < g.det.val) (z : ℍ) : g • z 
= ⟨num g z / denom g z, coe_smul_of_det_pos hg z ▸ (g • z).im_pos⟩
参数：Fin 2；hg : 0 < g.det.val；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `UpperHalfPlane.coe_smul_of_det_pos`：coe_smul_of_det_pos {g : GL (Fin 2) 
Real} (hg : 0 < g.det.val) (z : ℍ) : ↑(g • z) = num g z / denom g z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma glPos_smul_def {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    g • z = ⟨num g z / denom g z, coe_smul_of_det_pos hg z ▸ (g • z).im_pos⟩ := by
  ext; simp [coe_smul_of_det_pos hg]

section GLAction
variable (g : GL (Fin 2) ℝ) (z : ℍ)

set_option backward.isDefEq.respectTransparency false in
/-
**UpperHalfPlane.re_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：re_smul : (g • z).re = (num g z / denom g z).re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用定理 `DFunLike.ite_apply`：ite_apply {P : Prop} [Decidable P] (f g : F) (x : α)
 : (if P then f else g) x = if P then f x else g x
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Complex.div_re`：div_re (z w : Complex) : (z / w).re = z.re * w.re / norm
Sq w + z.im * w.im / normSq w
· 使用定理 `Complex.normSq_conj`：normSq_conj (z : Complex) : normSq (conj z) = normS
q z
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_smul : (g • z).re = (num g z / denom g z).re := by
  change (smulAux' g z).re = _
  simp +contextual [smulAux', σ, DFunLike.ite_apply, apply_ite, Complex.div_re]
/-
**UpperHalfPlane.im_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：im_smul : (g • z).im = |(num g z / denom g z).im|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFunLike.ite_apply`：ite_apply {P : Prop} [Decidable P] (f g : F) (x : α)
 : (if P then f else g) x = if P then f x else g x
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `UpperHalfPlane.moebius_im`：moebius_im (g : GL (Fin 2) Real) (z : Complex
) : (num g z / denom g z).im = g.det.val * z.im / Complex.normSq (denom g z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.coe_im`：coe_im (z : ℍ) : (z : Complex).im = z.im
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem im_smul : (g • z).im = |(num g z / denom g z).im| := by
  change (smulAux' g z).im = _
  simp only [smulAux', σ, DFunLike.ite_apply, ContinuousAlgEquiv.refl_apply, apply_ite, moebius_im,
    Complex.conjCAE_apply, Complex.conj_im, ← neg_div, ← neg_mul, abs_div, abs_mul,
    abs_of_pos (show 0 < (z : ℂ).im from z.coe_im ▸ z.im_pos),
    abs_of_nonneg <| Complex.normSq_nonneg _]
  split_ifs with h <;> [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]]
/-
**UpperHalfPlane.im_smul_eq_div_normSq** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：im_smul_eq_div_normSq : (g • z).im = |g.det.val| * z.im / Complex.normSq (
denom g z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.smulAux'_im`：∀ (g : GL (Fin 2) ℝ) (z : ℂ),   (UpperHalfPl
ane.smulAux' g z).im =     |↑(Matrix.GeneralLinearGroup.det g)| * z.im / Complex
.normSq (UpperHa…
-/
lemma im_smul_eq_div_normSq : (g • z).im = |g.det.val| * z.im / Complex.normSq (denom g z) :=
  smulAux'_im g z
/-
**UpperHalfPlane.c_mul_im_sq_le_normSq_denom** 是 Mathlib 中的一个定理，位于命名空间 `UpperHal
fPlane`。
形式化陈述：c_mul_im_sq_le_normSq_denom : (g 1 0 * z.im) ^ 2 <= Complex.normSq (denom 
g z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
（共 69 条，此处仅展示前 30 条）
-/
theorem c_mul_im_sq_le_normSq_denom : (g 1 0 * z.im) ^ 2 ≤ Complex.normSq (denom g z) := by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 ≤ (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [denom, Complex.normSq]; ring

@[simp]
/-
**UpperHalfPlane.neg_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：neg_smul : -g • z = g • z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.σ_neg`：σ_neg (g : GL (Fin 2) Real) : σ (-g) = σ g
· 使用引理 `UpperHalfPlane.num_neg`：num_neg (g : GL (Fin 2) Real) (z : Complex) : nu
m (-g) z = -(num g z)
· 使用引理 `UpperHalfPlane.denom_neg`：denom_neg (g : GL (Fin 2) Real) (z : Complex) 
: denom (-g) z = -(denom g z)
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_smul : -g • z = g • z := by
  ext1
  simp [coe_smul]

@[simp]
/-
**UpperHalfPlane.num_one** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：num_one : num 1 z = z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma num_one : num 1 z = z := by simp [num]

@[simp]
/-
**UpperHalfPlane.denom_one** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_one : denom 1 z = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma denom_one : denom 1 z = 1 := by
  simp [denom]

@[simp]
/-
**UpperHalfPlane.num_scalar** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：num_scalar (u : Realˣ) (z : ℍ) : num (.scalar (Fin 2) u) z = u * z
参数：u : Realˣ；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem num_scalar (u : ℝˣ) (z : ℍ) : num (.scalar (Fin 2) u) z = u * z := by
  simp [num]

@[simp]
/-
**UpperHalfPlane.denom_scalar** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_scalar (u : Realˣ) (z : ℍ) : denom (.scalar (Fin 2) u) z = u
参数：u : Realˣ；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem denom_scalar (u : ℝˣ) (z : ℍ) : denom (.scalar (Fin 2) u) z = u := by
  simp [denom]

@[simp]
/-
**UpperHalfPlane.glScalar_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：glScalar_smul (u : Realˣ) (z : ℍ) : GeneralLinearGroup.scalar (Fin 2) u • 
z = z
参数：u : Realˣ；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `UpperHalfPlane.coe_smul_of_det_pos`：coe_smul_of_det_pos {g : GL (Fin 2) 
Real} (hg : 0 < g.det.val) (z : ℍ) : ↑(g • z) = num g z / denom g z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.det_scalar`：det_scalar (u : Rˣ) : det (scalar 
n u) = u ^ Fintype.card n
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `UpperHalfPlane.glPos_smul_def`：glPos_smul_def {g : GL (Fin 2) Real} (hg 
: 0 < g.det.val) (z : ℍ) : g • z = ⟨num g z / denom g z, coe_smul_of_det_pos hg 
z ▸ (g • z).im_pos⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.num_scalar`：num_scalar (u : Realˣ) (z : ℍ) : num (.scalar
 (Fin 2) u) z = u * z
· 使用定理 `UpperHalfPlane.denom_scalar`：denom_scalar (u : Realˣ) (z : ℍ) : denom (.
scalar (Fin 2) u) z = u
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem glScalar_smul (u : ℝˣ) (z : ℍ) :
    GeneralLinearGroup.scalar (Fin 2) u • z = z := by
  rw [glPos_smul_def]
  · simp
  · simp [sq_pos_iff]
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction.IsPretransitive (GL (Fin 2) ℝ) ℍ where
  exists_smul_eq z w := by
    set m : Matrix (Fin 2) (Fin 2) ℝ := !![w.im, z.im * w.re - w.im * z.re; 0, z.im]
    refine ⟨.mkOfDetNeZero m <| by simp [m, im_ne_zero], ?_⟩
    ext
    simp [coe_smul_of_det_pos, im_pos, num, denom, m, Complex.ext_iff, im_ne_zero]

end GLAction

section PGLAction

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction PGL(2, ℝ) ℍ :=
  Matrix.ProjGenLinGroup.mulActionOfGL glScalar_smul

@[simp]
/-
**UpperHalfPlane.pglMk_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：pglMk_smul (g : GL (Fin 2) Real) (z : ℍ) : ProjGenLinGroup.mk g • z = g • 
z
参数：g : GL (Fin 2) Real；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ProjGenLinGroup.mk_smul`：mk_smul {α : Type*} [MulAction (GL n R) 
α] (h) (g : GL n R) (a : α) : letI : MulAction (PGL(n, R)) α
· 使用定理 `UpperHalfPlane.glScalar_smul`：glScalar_smul (u : Realˣ) (z : ℍ) : Genera
lLinearGroup.scalar (Fin 2) u • z = z
-/
theorem pglMk_smul (g : GL (Fin 2) ℝ) (z : ℍ) :
    ProjGenLinGroup.mk g • z = g • z :=
  ProjGenLinGroup.mk_smul ..
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction.IsPretransitive PGL(2, ℝ) ℍ :=
  .of_smul_eq .mk <| pglMk_smul _ _

end PGLAction

section SLAction

/-
**UpperHalfPlane.SLAction** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：SLAction {R : Type*} [CommRing R] [Algebra R Real] : MulAction SL(2, R) ℍ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance SLAction {R : Type*} [CommRing R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.mapGL ℝ
/-
**UpperHalfPlane.coe_specialLinearGroup_apply** 是 Mathlib 中的一个定理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：coe_specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R Real] (g 
: SL(2, R)) (z : ℍ) : ↑(g • z) = (((algebraMap R Real (g 0 0) : Complex) * z + (
algebraMap R Real (g 0 1) : Complex)) / ((algebraMap R Real (g 1 0) : Complex) *
 z + (algebraMap R Real (g 1 1) : Complex)))
参数：g : SL(2, R)；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.compHom_smul_def`：compHom_smul_def {E F G : Type*} [Monoid E] 
[Monoid F] [MulAction F G] (f : E ->* F) (a : E) (x : G) : letI : MulAction E G
· 使用引理 `UpperHalfPlane.coe_smul_of_det_pos`：coe_smul_of_det_pos {g : GL (Fin 2) 
Real} (hg : 0 < g.det.val) (z : ℍ) : ↑(g • z) = num g z / denom g z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matrix.SpecialLinearGroup.det_mapGL`：det_mapGL (g : SpecialLinearGroup n
 R) : (mapGL S g).det = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem coe_specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    ↑(g • z) =
      (((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ)) /
      ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ))) := by
  rw [MulAction.compHom_smul_def, coe_smul_of_det_pos (by simp)]
  rfl
/-
**UpperHalfPlane.specialLinearGroup_apply** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPl
ane`。
形式化陈述：specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R Real] (g : SL
(2, R)) (z : ℍ) : g • z = mk (((algebraMap R Real (g 0 0) : Complex) * z + (alge
braMap R Real (g 0 1) : Complex)) / ((algebraMap R Real (g 1 0) : Complex) * z +
 (algebraMap R Real (g 1 1) : Complex))) (coe_specialLinearGroup_apply g z ▸ (g 
• z).im_pos)
参数：g : SL(2, R)；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    g • z = mk
      (((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ)) /
      ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ)))
      (coe_specialLinearGroup_apply g z ▸ (g • z).im_pos) := by
  ext; simp [coe_specialLinearGroup_apply]

/-! these next few lemmas are *not* flagged `@simp` because of the constructors on the RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead. -/

/-
**UpperHalfPlane.modular_S_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：modular_S_smul (z : ℍ) : ModularGroup.S • z = mk (-z : Complex)⁻¹ z.im_inv
_neg_coe_pos
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.im_inv_neg_coe_pos`：im_inv_neg_coe_pos (z : ℍ) : 0 < (-z 
: Complex)⁻¹.im
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.specialLinearGroup_apply`：specialLinearGroup_apply {R : T
ype*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : g • z = mk (((algeb
raMap R Real (g 0 0) : Comple…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
these next few lemmas are *not* flagged `@simp` because of the constructors on t
he RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead.
-/
theorem modular_S_smul (z : ℍ) :
    ModularGroup.S • z = mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos := by
  rw [specialLinearGroup_apply]
  simp [ModularGroup.S, neg_div, inv_neg]
/-
**UpperHalfPlane.modular_T_zpow_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：modular_T_zpow_smul (z : ℍ) (n : Int) : ModularGroup.T ^ n • z = (n : Real
) +ᵥ z
参数：z : ℍ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.ext_iff`：∀ {x y : UpperHalfPlane}, x = y ↔ ↑x = ↑y
· 使用定理 `UpperHalfPlane.coe_vadd`：coe_vadd : ↑(x +ᵥ z) = (x + z : Complex)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modular_T_zpow_smul (z : ℍ) (n : ℤ) : ModularGroup.T ^ n • z = (n : ℝ) +ᵥ z := by
  rw [UpperHalfPlane.ext_iff, coe_vadd, add_comm, coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, Complex.ofReal_one, one_mul, cons_val_one,
    zero_mul, zero_add, div_one]
/-
**UpperHalfPlane.modular_T_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：modular_T_smul (z : ℍ) : ModularGroup.T • z = (1 : Real) +ᵥ z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `UpperHalfPlane.modular_T_zpow_smul`：modular_T_zpow_smul (z : ℍ) (n : Int
) : ModularGroup.T ^ n • z = (n : Real) +ᵥ z
-/
theorem modular_T_smul (z : ℍ) : ModularGroup.T • z = (1 : ℝ) +ᵥ z := by
  simpa only [zpow_one, Int.cast_one] using modular_T_zpow_smul z 1

set_option backward.isDefEq.respectTransparency false in
/-
**UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `UpperHalfPlane`。
形式化陈述：exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, Real)) (hc : g 1 0
 = 0) : exists (u : { x : Real // 0 < x }) (v : Real), (g • · : ℍ -> ℍ) = (v +ᵥ 
·) ∘ (u • ·)
参数：g : SL(2, Real)；hc : g 1 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero
`：fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type*} [Field R] (g : SL(2
, R)) (hg : g 1 0 = 0) : exists (a b : R) (h : a != 0), g = (⟨…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
（共 52 条，此处仅展示前 30 条）
-/
theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v : ℝ), (g • · : ℍ → ℍ) = (v +ᵥ ·) ∘ (u • ·) := by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices ↑a * z * a + b * a = b * a + a * a * z by simpa [specialLinearGroup_apply, add_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
/-
**UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_ne_zero** 是 Mathlib 中的一个定理
，位于命名空间 `UpperHalfPlane`。
形式化陈述：exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, Real)) (hc : g 1 0
 != 0) : exists (u : { x : Real // 0 < x }) (v w : Real), (g • · : ℍ -> ℍ) = (w 
+ᵥ ·) ∘ (ModularGroup.S • · : ℍ -> ℍ) ∘ (v +ᵥ · : ℍ -> ℍ) ∘ (u • · : ℍ -> ℍ)
参数：g : SL(2, Real)；hc : g 1 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `Matrix.SpecialLinearGroup.fin_two_induction`：fin_two_induction (P : SL(2
, R) -> Prop) (h : forall (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; 
c, d], by rwa [det_fin_two_of]⟩) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用定理 `UpperHalfPlane.im_inv_neg_coe_pos`：im_inv_neg_coe_pos (z : ℍ) : 0 < (-z 
: Complex)⁻¹.im
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `UpperHalfPlane.modular_S_smul`：modular_S_smul (z : ℍ) : ModularGroup.S •
 z = mk (-z : Complex)⁻¹ z.im_inv_neg_coe_pos
· 使用定理 `UpperHalfPlane.mk.congr_simp`：∀ (coe coe_1 : ℂ) (e_coe : coe = coe_1) (c
oe_im_pos : 0 < coe.im),   { coe := coe, coe_im_pos := coe_im_pos } = { coe := c
oe_1, coe_im_pos :…
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
-/
theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : g 1 0 ≠ 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v w : ℝ),
      (g • · : ℍ → ℍ) =
        (w +ᵥ ·) ∘ (ModularGroup.S • · : ℍ → ℍ) ∘ (v +ᵥ · : ℍ → ℍ) ∘ (u • · : ℍ → ℍ) := by
  have h_denom (z : ℍ) := denom_ne_zero g z
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | _ a b c d h => ?_
  replace hc : c ≠ 0 := by simpa using! hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  suffices (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹ by
    simpa [modular_S_smul, coe_specialLinearGroup_apply]
  replace hc : (c : ℂ) ≠ 0 := by norm_cast
  replace h_denom : ↑c * z + d ≠ 0 := by simpa using! h_denom ⟨z, hz⟩
  replace h : (a * d - b * c : ℂ) = (1 : ℂ) := by norm_cast
  grind

end SLAction

section toSL2R

/-- Map from `ℍ` to `SL(2, ℝ)`, giving a continuous section of the map `g ↦ g • I`. -/
/-
**UpperHalfPlane.toSL2R** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：toSL2R (z : ℍ) : SL(2, Real)
参数：z : ℍ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map from `ℍ` to `SL(2, ℝ)`, giving a continuous section of the map `g ↦ g • I`.
-/
noncomputable def toSL2R (z : ℍ) : SL(2, ℝ) :=
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩
/-
**UpperHalfPlane.toSL2R_apply** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：toSL2R_apply (z : ℍ) : z.toSL2R = ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], 
by simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSL2R_apply (z : ℍ) : z.toSL2R =
  ⟨!![√z.im, z.re / √z.im; 0, 1 / √z.im], by
    simp [mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr z.im_pos)]⟩ := (rfl)
/-
**UpperHalfPlane.coe_toSL2R** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (z : UpperHalfPlane), ↑z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im]
参数：z : UpperHalfPlane。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toSL2R (z : ℍ) : z.toSL2R = !![√z.im, z.re / √z.im; 0, 1 / √z.im] := (rfl)
/-
**UpperHalfPlane.toSL2R_smul_I** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (z : UpperHalfPlane), z.toSL2R • UpperHalfPlane.I = z
参数：z : UpperHalfPlane。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `div_add'`：div_add' (a b c : K) (hc : c != 0) : a / c + b = (a + b * c) /
 c
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `UpperHalfPlane.re_add_im`：re_add_im (z : ℍ) : (z.re + z.im * Complex.I :
 Complex) = z
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.coe_specialLinearGroup_apply`：coe_specialLinearGroup_appl
y {R : Type*} [CommRing R] [Algebra R Real] (g : SL(2, R)) (z : ℍ) : ↑(g • z) = 
(((algebraMap R Real (g 0 0) : Co…
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.coe_toSL2R`：∀ (z : UpperHalfPlane), ↑z.toSL2R = !![√z.im,
 z.re / √z.im; 0, 1 / √z.im]
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
（共 33 条，此处仅展示前 30 条）
-/
@[simp] lemma toSL2R_smul_I (z : ℍ) : z.toSL2R • I = z := by
  have : √z.im ≠ (0 : ℂ) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply, div_eq_iff (mod_cast denom_ne_zero z.toSL2R I)]
    simpa [add_comm]
  rw [div_add' (hc := this), mul_right_comm, ← Complex.ofReal_mul, ← Real.sqrt_mul z.im_pos.le,
    Real.sqrt_mul_self z.im_pos.le, re_add_im, div_eq_mul_inv]

/-- `SL(2, ℝ)` acts transitively on the upper half-plane. -/
/-
**UpperHalfPlane.isPretransitiveSL2R** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：isPretransitiveSL2R : MulAction.IsPretransitive SL(2, Real) ℍ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_orbit`：∀ {G : Type u_2} {X : Type u_5} [ins
t : Group G] [inst_1 : MulAction G X] {x₀ : X},   (∀ (x : X), ∃ g, g • x₀ = x) →
 MulAction.IsPretransiti…
· 使用定理 `UpperHalfPlane.toSL2R_smul_I`：∀ (z : UpperHalfPlane), z.toSL2R • UpperHa
lfPlane.I = z

--- 原说明 ---
`SL(2, ℝ)` acts transitively on the upper half-plane.
-/
instance isPretransitiveSL2R : MulAction.IsPretransitive SL(2, ℝ) ℍ :=
  .of_orbit fun z ↦ ⟨_, toSL2R_smul_I z⟩

/-- `GL(2, ℝ)` acts transitively on the upper half-plane. -/
/-
**UpperHalfPlane.isPretransitiveGL2R** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
形式化陈述：isPretransitiveGL2R : MulAction.IsPretransitive (GL (Fin 2) Real) ℍ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_smul_eq`：∀ {M : Type u_5} {N : Type u_6} {α
 : Type u_7} [inst : SMul M α] [inst_1 : SMul N α] [MulAction.IsPretransitive M 
α]   (f : M → N), (∀ {c : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MulAction.compHom_smul_def`：compHom_smul_def {E F G : Type*} [Monoid E] 
[Monoid F] [MulAction F G] (f : E ->* F) (a : E) (x : G) : letI : MulAction E G

--- 原说明 ---
`GL(2, ℝ)` acts transitively on the upper half-plane.
-/
instance isPretransitiveGL2R : MulAction.IsPretransitive (GL (Fin 2) ℝ) ℍ :=
  .of_smul_eq ((↑) : SL(2, ℝ) → _) fun {g z} ↦ (MulAction.compHom_smul_def _ g z).symm

end toSL2R

section J

/-- The matrix `[-1, 0; 0, 1]`, which defines an anti-holomorphic involution of `ℍ` via
`τ ↦ -conj τ`. -/
/-
**UpperHalfPlane.J** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：J : GL (Fin 2) Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix `[-1, 0; 0, 1]`, which defines an anti-holomorphic involution of `ℍ` 
via
`τ ↦ -conj τ`.
-/
def J : GL (Fin 2) ℝ := .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)
/-
**UpperHalfPlane.coe_J_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：coe_J_smul (τ : ℍ) : (↑(J • τ) : Complex) = -conj ↑τ
参数：τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.GeneralLinearGroup.val_mkOfDetNeZero`：∀ {n : Type u} [inst : Deci
dableEq n] [inst_1 : Fintype n] {K : Type u_1} [inst_2 : Field K] (A : Matrix n 
n K)   (h : A.det ≠ 0), ↑(Matrix.…
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
（共 34 条，此处仅展示前 30 条）
-/
lemma coe_J_smul (τ : ℍ) : (↑(J • τ) : ℂ) = -conj ↑τ := by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : ℝ) < 0 by simp, num, denom]
/-
**UpperHalfPlane.val_J** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：↑UpperHalfPlane.J = !![-1, 0; 0, 1]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_J : J.val = !![-1, 0; 0, 1] := rfl
/-
**UpperHalfPlane.J_sq** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：UpperHalfPlane.J ^ 2 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.GeneralLinearGroup.val_mkOfDetNeZero`：∀ {n : Type u} [inst : Deci
dableEq n] [inst_1 : Fintype n] {K : Type u_1} [inst_2 : Field K] (A : Matrix n 
n K)   (h : A.det ≠ 0), ↑(Matrix.…
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `Matrix.vecMul_cons`：vecMul_cons (v : Fin n.succ -> α) (w : o' -> α) (B :
 Fin n -> o' -> α) : v ᵥ* of (vecCons w B) = vecHead v • w + vecTail v ᵥ* of B
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.neg_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Neg α] (x : α) (v : Fi
n n → α), -Matrix.vecCons x v = Matrix.vecCons (-x) (-v)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Matrix.neg_empty`：∀ {α : Type u_1} [inst : Neg α] (v : Fin 0 → α), -v = 
![]
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.one_fin_two`：one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1,
 0; 0, 1]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma J_sq : J ^ 2 = 1 := by ext; simp [J, sq, Matrix.one_fin_two]
/-
**UpperHalfPlane.det_J** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：Matrix.GeneralLinearGroup.det UpperHalfPlane.J = -1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.GeneralLinearGroup.val_mkOfDetNeZero`：∀ {n : Type u} [inst : Deci
dableEq n] [inst_1 : Fintype n] {K : Type u_1} [inst_2 : Field K] (A : Matrix n 
n K)   (h : A.det ≠ 0), ↑(Matrix.…
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma det_J : J.det = -1 := by ext; simp [J]
/-
**UpperHalfPlane.sigma_J** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：UpperHalfPlane.σ UpperHalfPlane.J = Complex.conjCAE
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.GeneralLinearGroup.val_mkOfDetNeZero`：∀ {n : Type u} [inst : Deci
dableEq n] [inst_1 : Fintype n] {K : Type u_1} [inst_2 : Field K] (A : Matrix n 
n K)   (h : A.det ≠ 0), ↑(Matrix.…
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
@[simp] lemma sigma_J : σ J = Complex.conjCAE := by simp [σ, J]
/-
**UpperHalfPlane.denom_J** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (τ : ℂ), UpperHalfPlane.denom UpperHalfPlane.J τ = 1
参数：τ : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_mkOfDetNeZero`：∀ {n : Type u} [inst : Deci
dableEq n] [inst_1 : Fintype n] {K : Type u_1} [inst_2 : Field K] (A : Matrix n 
n K)   (h : A.det ≠ 0), ↑(Matrix.…
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma denom_J (τ : ℂ) : denom J τ = 1 := by simp [J, denom]

@[simp]
/-
**UpperHalfPlane.denom_J_mul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：denom_J_mul (g : GL (Fin 2) Real) (τ : Complex) : denom (J * g) τ = denom 
g τ
参数：g : GL (Fin 2) Real；τ : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.cons_mul`：cons_mul [Fintype n'] (v : n' -> α) (A : Fin m -> n' ->
 α) (B : Matrix n' o' α) : of (vecCons v A) * B = of (vecCons (v ᵥ* B) (of.symm 
(of A…
· 使用定理 `Matrix.empty_mul`：empty_mul [Fintype n'] (A : Matrix (Fin 0) n' α) (B : 
Matrix n' o' α) : A * B = of ![]
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `Matrix.cons_dotProduct`：cons_dotProduct (x : α) (v : Fin n -> α) (w : Fi
n n.succ -> α) : vecCons x v ⬝ᵥ w = x * vecHead w + v ⬝ᵥ vecTail w
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Matrix.dotProduct_of_isEmpty`：dotProduct_of_isEmpty [Fintype n'] [IsEmpt
y n'] (v w : n' -> α) : v ⬝ᵥ w = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma denom_J_mul (g : GL (Fin 2) ℝ) (τ : ℂ) : denom (J * g) τ = denom g τ := by
  simp [denom, vecMul, vecHead, vecTail]

end J

end UpperHalfPlane

namespace ModularGroup -- results specific to `SL(2, ℤ)`
-- TODO: Move these elsewhere, maybe somewhere in the algebra or number theory hierarchies?

section ModularScalarTowers

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`. -/
@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.coe** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：coe (g : SL(2, Int)) : GL(2, Real)⁺
参数：g : SL(2, Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`.
-/
def coe (g : SL(2, ℤ)) : GL(2, ℝ)⁺ := ((g : SL(2, ℝ)) : GL(2, ℝ)⁺)

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：coe_inj (a b : SL(2, Int)) : coe a = coe b ↔ a = b
参数：a b : SL(2, Int)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.SpecialLinearGroup.ext`：ext (A B : SpecialLinearGroup n R) : (for
all i j, A i j = B i j) -> A = B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma coe_inj (a b : SL(2, ℤ)) : coe a = coe b ↔ a = b := by
  refine ⟨fun h ↦ a.ext b fun i j ↦ ?_, congr_arg _⟩
  simp only [Subtype.ext_iff, GeneralLinearGroup.ext_iff] at h
  simpa [coe] using h i j

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`, bundled as a group hom. -/
@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：coeHom : SL(2, Int) ->* GL(2, Real)⁺
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`, bundled as a group hom.
-/
def coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺ := toGLPos.comp <| map <| Int.castRingHom _

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.coeHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：coeHom_apply (g : SL(2, Int)) : coeHom g = coe g
参数：g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeHom_apply (g : SL(2, ℤ)) : coeHom g = coe g := rfl

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.coe_apply_complex** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：coe_apply_complex {g : SL(2, Int)} {i j : Fin 2} : (Units.val <| Subtype.v
al <| coe g) i j = (Subtype.val g i j : Complex)
参数：2, Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_apply_complex {g : SL(2, ℤ)} {i j : Fin 2} :
    (Units.val <| Subtype.val <| coe g) i j = (Subtype.val g i j : ℂ) :=
  rfl

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.det_coe** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：det_coe {g : SL(2, Int)} : det (Units.val <| Subtype.val <| coe g) = 1
参数：2, Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.det_coe`：det_coe : det ↑ₘA = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_coe {g : SL(2, ℤ)} : det (Units.val <| Subtype.val <| coe g) = 1 := by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.coe_one** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：coe_one : coe 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_one : coe 1 = 1 := by
  simp only [coe, map_one]

/-- Multiplication action of `SL(2, ℤ)` on `GL(2, ℝ)⁺`. -/
@[reducible, deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.SLOnGLPos** 是 Mathlib 中的一个定义，位于命名空间 `ModularGroup`。
形式化陈述：SLOnGLPos : SMul SL(2, Int) GL(2, Real)⁺
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication action of `SL(2, ℤ)` on `GL(2, ℝ)⁺`.
-/
def SLOnGLPos : SMul SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩

attribute [local instance] SLOnGLPos

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.SLOnGLPos_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：SLOnGLPos_smul_apply (s : SL(2, Int)) (g : GL(2, Real)⁺) (z : ℍ) : (s • g)
 • z = ((s : GL(2, Real)⁺) * g) • z
参数：s : SL(2, Int)；g : GL(2, Real)⁺；z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SLOnGLPos_smul_apply (s : SL(2, ℤ)) (g : GL(2, ℝ)⁺) (z : ℍ) :
    (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
/-
**ModularGroup.SL_to_GL_tower** 是 Mathlib 中的一个引理，位于命名空间 `ModularGroup`。
形式化陈述：SL_to_GL_tower : IsScalarTower SL(2, Int) GL(2, Real)⁺ ℍ where smul_assoc 
s g z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.mul_smul'`：mul_smul' (g h : GL (Fin 2) Real) (z : ℍ) : sm
ulAux (g * h) z = smulAux g (smulAux h z)
-/
lemma SL_to_GL_tower : IsScalarTower SL(2, ℤ) GL(2, ℝ)⁺ ℍ where
  smul_assoc s g z := by
    simp only [SLOnGLPos_smul_apply]
    apply mul_smul'

end ModularScalarTowers

section SLModularAction

variable (g : SL(2, ℤ)) (z : ℍ)

@[simp]
/-
**ModularGroup.sl_moeb** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：sl_moeb : g • z = (g : GL (Fin 2) Real) • z
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sl_moeb : g • z = (g : GL (Fin 2) ℝ) • z := rfl

@[simp high]
/-
**ModularGroup.SL_neg_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：SL_neg_smul : -g • z = g • z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularGroup.sl_moeb`：sl_moeb : g • z = (g : GL (Fin 2) Real) • z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.neg_smul`：neg_smul : -g • z = g • z
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.SpecialLinearGroup.coe_int_neg`：coe_int_neg (g : SpecialLinearGro
up n Int) : ↑(-g) = (-↑g : SpecialLinearGroup n R)
· 使用定理 `Units.mk.congr_simp`：∀ {α : Type u} [inst : Monoid α] (val val_1 : α) (e
_val : val = val_1) (inv inv_1 : α) (e_inv : inv = inv_1)   (val_inv : val * inv
 = 1) (in…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SL_neg_smul : -g • z = g • z := by
  rw [sl_moeb, ← z.neg_smul]
  congr 1 with i j
  simp [toGL]
/-
**ModularGroup.im_smul_eq_div_normSq** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `UpperHalfPlane.im_smul_eq_div_normSq`：im_smul_eq_div_normSq : (g • z).im
 = |g.det.val| * z.im / Complex.normSq (denom g z)
-/
theorem im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z) := by
  simpa using z.im_smul_eq_div_normSq g
/-
**ModularGroup.denom_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：denom_apply : denom g z = g 1 0 * z + g 1 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem denom_apply : denom g z = g 1 0 * z + g 1 1 := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ModularGroup.denom_S** 是 Mathlib 中的一个定理，位于命名空间 `ModularGroup`。
形式化陈述：∀ (z : UpperHalfPlane),   UpperHalfPlane.denom       (Matrix.SpecialLinear
Group.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S))
 ↑z =     ↑z
参数：z : UpperHalfPlane；Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup
.map (Int.castRingHom ℝ)) ModularGroup.S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma denom_S : denom S z = z := by simp [S, denom_apply]

end SLModularAction

end ModularGroup

