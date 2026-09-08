/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
In particular, we prove that
`π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n`
as well as the infinite sum representation of cotangent (also known as the Mittag-Leffler
expansion): `π * cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))`.
-/

public section

open Real Complex

open scoped UpperHalfPlane

local notation "ℂ_ℤ" => integerComplement

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

/-
**Complex.cot_eq_exp_ratio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.cot_eq_exp_ratio (z : Complex) : cot z = (Complex.exp (2 * I * z) 
+ 1) / (I * (1 - Complex.exp (2 * I * z)))
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cot.eq_1`：∀ (z : ℂ), z.cot = Complex.cos z / Complex.sin z
· 使用定理 `Complex.sin.eq_1`：∀ (z : ℂ), Complex.sin z = (Complex.exp (-z * Complex.
I) - Complex.exp (z * Complex.I)) * Complex.I / 2
· 使用定理 `Complex.cos.eq_1`：∀ (z : ℂ), Complex.cos z = (Complex.exp (z * Complex.I
) + Complex.exp (-z * Complex.I)) / 2
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 100 条，此处仅展示前 30 条）
-/
lemma Complex.cot_eq_exp_ratio (z : ℂ) :
    cot z = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z))) := by
  rw [Complex.cot, Complex.sin, Complex.cos]
  have h1 : exp (z * I) + exp (-z * I) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    ring_nf
  have h2 : (exp (-z * I) - exp (z * I)) = exp (-(z * I)) * ((1 - exp (2 * I * z))) := by
    ring_nf
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h1, h2]
  field

/-- The version one probably wants to use more. -/
/-
**Complex.cot_pi_eq_exp_ratio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.cot_pi_eq_exp_ratio (z : Complex) : cot (π * z) = (Complex.exp (2 
* π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z)))
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.cot_eq_exp_ratio`：Complex.cot_eq_exp_ratio (z : Complex) : cot z
 = (Complex.exp (2 * I * z) + 1) / (I * (1 - Complex.exp (2 * I * z)))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The version one probably wants to use more.
-/
lemma Complex.cot_pi_eq_exp_ratio (z : ℂ) :
    cot (π * z) = (Complex.exp (2 * π * I * z) + 1) / (I * (1 - Complex.exp (2 * π * I * z))) := by
  rw [cot_eq_exp_ratio (π * z)]
  ring_nf

/-- This is the version one probably wants, which is why the pi's are there. -/
/-
**pi_mul_cot_pi_q_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_mul_cot_pi_q_exp (z : ℍ) : π * cot (π * z) = π * I - 2 * π * I * ∑' n :
 Nat, Complex.exp (2 * π * I * z) ^ n
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_div_mul_one_div`：div_mul_eq_div_mul_one_div : a / (b * c) = a
 / b * (1 / c)
· 使用定理 `Complex.div_I`：div_I (z : Complex) : z / I = -(z * I)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
This is the version one probably wants, which is why the pi's are there.
-/
theorem pi_mul_cot_pi_q_exp (z : ℍ) :
    π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n := by
  have h1 : π * ((exp (2 * π * I * z) + 1) / (I * (1 - exp (2 * π * I * z)))) =
      -π * I * ((exp (2 * π * I * z) + 1) * (1 / (1 - exp (2 * π * I * z)))) := by
    simp only [div_mul_eq_div_mul_one_div, div_I, one_div, neg_mul, mul_neg, neg_inj]
    ring
  rw [cot_pi_eq_exp_ratio, h1, one_div, (tsum_geometric_of_norm_lt_one
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one z)).symm, add_comm, geom_series_mul_one_add
      (Complex.exp (2 * π * I * (z : ℂ))) (UpperHalfPlane.norm_exp_two_pi_I_lt_one _)]
  ring

section MittagLeffler

open Filter Function

open scoped Topology Nat Complex

variable {x : ℂ} {Z : Set ℂ}

/-- The main term in the infinite product for sine. -/
/-
**sineTerm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：sineTerm (x : Complex) (n : Nat) : Complex
参数：x : Complex；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main term in the infinite product for sine.
-/
noncomputable abbrev sineTerm (x : ℂ) (n : ℕ) : ℂ := -x ^ 2 / (n + 1) ^ 2
/-
**sineTerm_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sineTerm_ne_zero {x : Complex} (hx : x in Complex_Int) (n : Nat) : 1 + sin
eTerm x n != 0
参数：hx : x in Complex_Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用引理 `neg_div'`：neg_div' (a b : R) : -(b / a) = -b / a
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.cast_add_one_ne_zero`：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) !
= 0
· 使用引理 `Complex.integerComplement_pow_two_ne_pow_two`：integerComplement_pow_two_
ne_pow_two {x : Complex} (hx : x in Complex_Int) (n : Int) : x ^ 2 != n ^ 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
lemma sineTerm_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℕ) : 1 + sineTerm x n ≠ 0 := by
  simp only [sineTerm, ne_eq]
  rw [add_eq_zero_iff_eq_neg, neg_div', eq_div_iff]
  · have := (integerComplement_pow_two_ne_pow_two hx (n + 1 : ℤ))
    aesop
  · simp [Nat.cast_add_one_ne_zero n]
/-
**tendsto_euler_sin_prod'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_euler_sin_prod' (h0 : x != 0) : Tendsto (fun n : Nat => ∏ i in Fin
set.range n, (1 + sineTerm x i)) atTop (𝓝 (sin (π * x) / (π * x)))
参数：h0 : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 76 条，此处仅展示前 30 条）
-/
lemma tendsto_euler_sin_prod' (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ ↦ ∏ i ∈ Finset.range n, (1 + sineTerm x i)) atTop
    (𝓝 (sin (π * x) / (π * x))) := by
  rw [show (sin (π * x) / (π * x)) = sin (π * x) * (1 / (π * x)) by ring]
  apply (Filter.Tendsto.mul_const (b := 1 / (π * x)) (tendsto_euler_sin_prod x)).congr
  exact fun n ↦ by field_simp; rfl
/-
**multipliable_sineTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_sineTerm (x : Complex) : Multipliable fun i => (1 + sineTerm 
x i)
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `multipliable_one_add_of_summable`：multipliable_one_add_of_summable [Comp
leteSpace R] (hf : Summable fun i => ‖f i‖) : Multipliable fun i => (1 + f i)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `summable_pow_div_add`：summable_pow_div_add {α : Type*} (x : α) [RCLike α
] (q k : Nat) (hq : 1 < q) : Summable fun n : Nat => ‖(x / (↑n + k) ^ q)‖
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_div`：∀ (z w : ℂ), ‖z / w‖ = ‖z‖ / ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma multipliable_sineTerm (x : ℂ) : Multipliable fun i ↦ (1 + sineTerm x i) := by
  apply multipliable_one_add_of_summable
  have := summable_pow_div_add (x ^ 2) 2 1 Nat.one_lt_two
  simpa [sineTerm] using this
/-
**euler_sineTerm_tprod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：euler_sineTerm_tprod (hx : x in Complex_Int) : ∏' i : Nat, (1 + sineTerm x
 i) = Complex.sin (π * x) / (π * x)
参数：hx : x in Complex_Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multipliable.hasProd_iff`：Multipliable.hasProd_iff (h : Multipliable f L
) : HasProd f a L ↔ ∏'[L] b, f b = a
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `multipliable_sineTerm`：multipliable_sineTerm (x : Complex) : Multipliabl
e fun i => (1 + sineTerm x i)
· 使用定理 `Multipliable.hasProd_iff_tendsto_nat`：hasProd_iff_tendsto_nat [T2Space M
] {f : Nat -> M} (hf : Multipliable f) : HasProd f m ↔ Tendsto (fun n : Nat => ∏
 i in range n, f i) atTop …
· 使用引理 `tendsto_euler_sin_prod'`：tendsto_euler_sin_prod' (h0 : x != 0) : Tendsto
 (fun n : Nat => ∏ i in Finset.range n, (1 + sineTerm x i)) atTop (𝓝 (sin (π * x
) / (π * x)))
· 使用定理 `Complex.integerComplement.ne_zero`：∀ {x : ℂ}, x ∈ Complex.integerComplem
ent → x ≠ 0
-/
lemma euler_sineTerm_tprod (hx : x ∈ ℂ_ℤ) :
    ∏' i : ℕ, (1 + sineTerm x i) = Complex.sin (π * x) / (π * x) := by
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x),
    Multipliable.hasProd_iff_tendsto_nat (multipliable_sineTerm x)]
  exact tendsto_euler_sin_prod' (integerComplement.ne_zero hx)
/-
**sineTerm_bound_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sineTerm_bound_aux (hZ : IsCompact Z) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ j z, z ∈ Z → ‖sineTerm z j‖ ≤ u j := by
  have hf : ContinuousOn (fun x : ℂ => ‖-x ^ 2‖) Z := by
    fun_prop
  obtain ⟨s, hs⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  refine ⟨fun n : ℕ => ‖(s : ℂ) / (n + 1) ^ 2‖, ?_, ?_⟩
  · simpa using summable_pow_div_add (s : ℂ) 2 1 (Nat.one_lt_two)
  · simp only [norm_neg, norm_pow, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, sineTerm, norm_div, norm_real, norm_eq_abs] at *
    intro n x hx
    gcongr
    apply le_trans (hs x hx) (le_abs_self s)
/-
**multipliableUniformlyOn_euler_sin_prod_on_compact** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：multipliableUniformlyOn_euler_sin_prod_on_compact (hZC : IsCompact Z) : Mu
ltipliableUniformlyOn (fun n : Nat => fun z : Complex => (1 + sineTerm z n)) Z
参数：hZC : IsCompact Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent.0.sin
eTerm_bound_aux`：∀ {Z : Set ℂ}, IsCompact Z → ∃ u, Summable u ∧ ∀ (j : ℕ), ∀ z ∈
 Z, ‖sineTerm z j‖ ≤ u j
· 使用引理 `Summable.multipliableUniformlyOn_nat_one_add`：multipliableUniformlyOn_na
t_one_add {f : Nat -> α -> R} (hK : IsCompact K) {u : Nat -> Real} (hu : Summabl
e u) (h : forallᶠ n in atTop, fora…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma multipliableUniformlyOn_euler_sin_prod_on_compact (hZC : IsCompact Z) :
    MultipliableUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n)) Z := by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop
/-
**HasProdUniformlyOn_sineTerm_prod_on_compact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdUniformlyOn_sineTerm_prod_on_compact (hZ2 : Z subseteq Complex_Int)
 (hZC : IsCompact Z) : HasProdUniformlyOn (fun n : Nat => fun z : Complex => (1 
+ sineTerm z n)) (fun x => (Complex.sin (↑π * x) / (↑π * x))) Z
参数：hZ2 : Z subseteq Complex_Int；hZC : IsCompact Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HasProdUniformlyOn.congr_right`：HasProdUniformlyOn.congr_right {g' : β -
> α} (h : HasProdUniformlyOn f g s) (hgg' : s.EqOn g g') : HasProdUniformlyOn f 
g' s
· 使用定理 `MultipliableUniformlyOn.hasProdUniformlyOn`：MultipliableUniformlyOn.hasP
rodUniformlyOn (h : MultipliableUniformlyOn f s) : HasProdUniformlyOn f (∏' i, f
 i ·) s
· 使用引理 `multipliableUniformlyOn_euler_sin_prod_on_compact`：multipliableUniformly
On_euler_sin_prod_on_compact (hZC : IsCompact Z) : MultipliableUniformlyOn (fun 
n : Nat => fun z : Complex => (1 + sine…
· 使用引理 `euler_sineTerm_tprod`：euler_sineTerm_tprod (hx : x in Complex_Int) : ∏' 
i : Nat, (1 + sineTerm x i) = Complex.sin (π * x) / (π * x)
-/
lemma HasProdUniformlyOn_sineTerm_prod_on_compact (hZ2 : Z ⊆ ℂ_ℤ)
    (hZC : IsCompact Z) :
    HasProdUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
    (fun x => (Complex.sin (↑π * x) / (↑π * x))) Z := by
  apply (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn.congr_right
  exact fun x hx => euler_sineTerm_tprod (by aesop)
/-
**HasProdLocallyUniformlyOn_euler_sin_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasProdLocallyUniformlyOn_euler_sin_prod : HasProdLocallyUniformlyOn (fun 
n : Nat => fun z : Complex => (1 + sineTerm z n)) (fun x => (Complex.sin (π * x)
 / (π * x))) Complex_Int
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProdLocallyUniformlyOn_of_forall_compact`：hasProdLocallyUniformlyOn_o
f_forall_compact (hs : IsOpen s) [LocallyCompactSpace β] (h : forall K subseteq 
s, IsCompact K -> HasProdUniforml…
· 使用定理 `Complex.isOpen_compl_range_intCast`：IsOpen (Set.range Int.cast)ᶜ
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用引理 `HasProdUniformlyOn_sineTerm_prod_on_compact`：HasProdUniformlyOn_sineTerm
_prod_on_compact (hZ2 : Z subseteq Complex_Int) (hZC : IsCompact Z) : HasProdUni
formlyOn (fun n : Nat => fun z : …
-/
lemma HasProdLocallyUniformlyOn_euler_sin_prod :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
    (fun x => (Complex.sin (π * x) / (π * x))) ℂ_ℤ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact Complex.isOpen_compl_range_intCast
  exact fun _ hZ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZ hZC

/-- `sin π z` is non vanishing on the complement of the integers in `ℂ`. -/
/-
**sin_pi_mul_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sin_pi_mul_ne_zero (hx : x in Complex_Int) : Complex.sin (π * x) != 0
参数：hx : x in Complex_Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.sin_ne_zero_iff`：sin_ne_zero_iff {θ : Complex} : sin θ != 0 ↔ fo
rall k : Int, θ != k * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`sin π z` is non vanishing on the complement of the integers in `ℂ`.
-/
theorem sin_pi_mul_ne_zero (hx : x ∈ ℂ_ℤ) : Complex.sin (π * x) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k
  nth_rw 2 [mul_comm]
  exact Injective.ne (mul_right_injective₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by aesop)
/-
**cot_pi_mul_contDiffWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cot_pi_mul_contDiffWithinAt (k : Nat∞) (hx : x in Complex_Int) : ContDiffW
ithinAt Complex k (fun x => (↑π * x).cot) ℍₒ x
参数：k : Nat∞；hx : x in Complex_Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.div`：ContDiffWithinAt.div {f g : E -> 𝕜} {n} (hf : Cont
DiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x != 0) : Cont
DiffWithin…
· 使用定理 `ContDiffWithinAt.div_const`：ContDiffWithinAt.div_const {f : E -> 𝕜'} {n}
 (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') : ContDiffWithinAt 𝕜 n (fun x => f x
 / c) s x
· 使用定理 `ContDiffWithinAt.add`：ContDiffWithinAt.add {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `ContDiffWithinAt.cexp`：ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt 
𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => Complex.exp (f x)) s x
· 使用定理 `ContDiffWithinAt.mul`：ContDiffWithinAt.mul {s : Set E} {f g : E -> 𝔸} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
· 使用定理 `contDiffWithinAt_id`：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (i
d : E -> E) s x
· 使用定理 `ContDiffWithinAt.neg`：ContDiffWithinAt.neg {s : Set E} {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun x => -f x) s x
· 使用定理 `ContDiffWithinAt.sub`：ContDiffWithinAt.sub {s : Set E} {f g : E -> F} (h
f : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWith
inAt 𝕜 n (…
· 使用定理 `sin_pi_mul_ne_zero`：sin_pi_mul_ne_zero (hx : x in Complex_Int) : Complex
.sin (π * x) != 0
-/
lemma cot_pi_mul_contDiffWithinAt (k : ℕ∞) (hx : x ∈ ℂ_ℤ) :
    ContDiffWithinAt ℂ k (fun x ↦ (↑π * x).cot) ℍₒ x := by
  simp_rw [Complex.cot, Complex.cos, Complex.sin]
  exact ContDiffWithinAt.div (by fun_prop) (by fun_prop) (sin_pi_mul_ne_zero hx)
/-
**tendsto_logDeriv_euler_sin_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_logDeriv_euler_sin_div (hx : x in Complex_Int) : Tendsto (fun n : 
Nat => logDeriv (fun z => ∏ j in Finset.range n, (1 + sineTerm z j)) x) atTop (𝓝
 <| logDeriv (fun t => (Complex.sin (π * t) / (π * t))) x)
参数：hx : x in Complex_Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.logDeriv_tendsto`：logDeriv_tendsto {ι : Type*} {p : Filter ι} {f
 : ι -> Complex -> Complex} {g : Complex -> Complex} {s : Set Complex} (hs : IsO
pen s) {x : Co…
· 使用定理 `Complex.isOpen_compl_range_intCast`：IsOpen (Set.range Int.cast)ᶜ
· 使用引理 `HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange`：HasProd
LocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange {f : Nat -> β -> α} (h 
: HasProdLocallyUniformlyOn f g s) : TendstoLocallyUn…
· 使用引理 `HasProdLocallyUniformlyOn_euler_sin_prod`：HasProdLocallyUniformlyOn_eule
r_sin_prod : HasProdLocallyUniformlyOn (fun n : Nat => fun z : Complex => (1 + s
ineTerm z n)) (fun x => (Compl…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableOn.fun_finsetProd`：DifferentiableOn.fun_finsetProd (hd : f
orall i in u, DifferentiableOn 𝕜 (f i) s) : DifferentiableOn 𝕜 (∏ i in u, f i ·)
 s
· 使用定理 `DifferentiableOn.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `DifferentiableOn.div_const`：DifferentiableOn.div_const (hc : Differentia
bleOn 𝕜 c s) (d : 𝕜') : DifferentiableOn 𝕜 (fun x => c x / d) s
· 使用定理 `DifferentiableOn.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableOn.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sin_pi_mul_ne_zero`：sin_pi_mul_ne_zero (hx : x in Complex_Int) : Complex
.sin (π * x) != 0
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用定理 `Complex.integerComplement.ne_zero`：∀ {x : ℂ}, x ∈ Complex.integerComplem
ent → x ≠ 0
-/
lemma tendsto_logDeriv_euler_sin_div (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ ↦ logDeriv (fun z ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x)
        atTop (𝓝 <| logDeriv (fun t ↦ (Complex.sin (π * t) / (π * t))) x) := by
  refine logDeriv_tendsto isOpen_compl_range_intCast hx
      HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange ?_ ?_
  · filter_upwards with n using by fun_prop
  · simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨sin_pi_mul_ne_zero hx, Real.pi_ne_zero, integerComplement.ne_zero hx⟩
/-
**logDeriv_sin_div_eq_cot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_sin_div_eq_cot (hz : x in Complex_Int) : logDeriv (fun t => (Comp
lex.sin (π * t) / (π * t))) x = π * cot (π * x) - 1 / x
参数：hz : x in Complex_Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv_div`：logDeriv_div {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg :
 g x != 0) (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) : logDe
ri…
· 使用定理 `sin_pi_mul_ne_zero`：sin_pi_mul_ne_zero (hx : x in Complex_Int) : Complex
.sin (π * x) != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用定理 `Complex.integerComplement.ne_zero`：∀ {x : ℂ}, x ∈ Complex.integerComplem
ent → x ≠ 0
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Complex.differentiableAt_sin`：differentiableAt_sin {x : Complex} : Diffe
rentiableAt Complex sin x
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `logDeriv_comp`：logDeriv_comp {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : 
DifferentiableAt 𝕜' f (g x)) (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x 
= l…
· 使用定理 `Complex.logDeriv_sin`：Complex.logDeriv_sin : logDeriv (Complex.sin) = Co
mplex.cot
· 使用定理 `deriv_const_mul_id`：deriv_const_mul_id (c : 𝕜) : deriv (fun y => c * y) 
x = c
· 使用定理 `logDeriv_const_mul`：logDeriv_const_mul {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (h
a : a != 0) : logDeriv (fun z => a * f z) x = logDeriv f x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `logDeriv_id'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (x : 𝕜
), logDeriv (fun x => x) x = 1 / x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
（共 54 条，此处仅展示前 30 条）
-/
lemma logDeriv_sin_div_eq_cot (hz : x ∈ ℂ_ℤ) :
    logDeriv (fun t ↦ (Complex.sin (π * t) / (π * t))) x = π * cot (π * x) - 1 / x := by
  have : (fun t ↦ (Complex.sin (π * t) / (π * t))) = fun z ↦
    (Complex.sin ∘ fun t ↦ π * t) z / (π * z) := by simp
  rw [this, logDeriv_div _ (by apply sin_pi_mul_ne_zero hz) ?_
    (DifferentiableAt.comp _ (Complex.differentiableAt_sin) (by fun_prop)) (by fun_prop),
    logDeriv_comp (Complex.differentiableAt_sin) (by fun_prop), Complex.logDeriv_sin,
    deriv_const_mul_id, logDeriv_const_mul, logDeriv_id']
  · ring
  · simp
  · simp only [ne_eq, mul_eq_zero, ofReal_eq_zero, not_or]
    exact ⟨Real.pi_ne_zero, integerComplement.ne_zero hz⟩

/-- The term in the infinite sum expansion of cot. -/
/-
**cotTerm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：cotTerm (x : Complex) (n : Nat) : Complex
参数：x : Complex；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The term in the infinite sum expansion of cot.
-/
noncomputable abbrev cotTerm (x : ℂ) (n : ℕ) : ℂ := 1 / (x - (n + 1)) + 1 / (x + (n + 1))
/-
**logDeriv_sineTerm_eq_cotTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_sineTerm_eq_cotTerm (hx : x in Complex_Int) (i : Nat) : logDeriv 
(fun (z : Complex) => 1 + sineTerm z i) x = cotTerm x i
参数：hx : x in Complex_Int；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.integerComplement_add_ne_zero`：integerComplement_add_ne_zero {x 
: Complex} (hx : x in Complex_Int) (a : Int) : x + (a : Complex) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Complex.integerComplement_pow_two_ne_pow_two`：integerComplement_pow_two_
ne_pow_two {x : Complex} (hx : x in Complex_Int) (n : Int) : x ^ 2 != n ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const_add'`：deriv_const_add' (c : F) : (deriv (c + f ·)) = deriv f
· 使用定理 `deriv_div_const`：deriv_div_const (d : 𝕜') : deriv (fun x => c x / d) x =
 deriv c x / d
· 使用定理 `deriv.fun_neg'`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : T
ype v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F},
 (de…
· 使用定理 `deriv_fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} [inst : NontriviallyNorme
dField 𝕜] [inst_1 : NormedCommRing 𝔸]   [inst_2 : NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸}
 {x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
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
（共 116 条，此处仅展示前 30 条）
-/
lemma logDeriv_sineTerm_eq_cotTerm (hx : x ∈ ℂ_ℤ) (i : ℕ) :
    logDeriv (fun (z : ℂ) ↦ 1 + sineTerm z i) x = cotTerm x i := by
  have h1 := integerComplement_add_ne_zero hx (i + 1)
  have h2 : ((x : ℂ) - (i + 1)) ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hx (-(i + 1))
  have h3 : (i + 1) ^ 2 + - x ^ 2 ≠ 0 := by
      have := (integerComplement_pow_two_ne_pow_two hx ((i + 1) : ℤ))
      rw [← sub_eq_add_neg, sub_ne_zero]
      aesop
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, ne_eq, sineTerm, logDeriv_apply,
    deriv_const_add', deriv_div_const, deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow,
    Nat.cast_ofNat, deriv_id'', cotTerm] at *
  field
/-
**logDeriv_prod_sineTerm_eq_sum_cotTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_prod_sineTerm_eq_sum_cotTerm (hx : x in Complex_Int) (n : Nat) : 
logDeriv (fun (z : Complex) => ∏ j in Finset.range n, (1 + sineTerm z j)) x = ∑ 
j in Finset.range n, cotTerm x j
参数：hx : x in Complex_Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv_prod`：logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜
'} {x : 𝕜} (hf : forall i in s, f i x != 0) (hd : forall i in s, DifferentiableA
t 𝕜…
· 使用引理 `sineTerm_ne_zero`：sineTerm_ne_zero {x : Complex} (hx : x in Complex_Int)
 (n : Nat) : 1 + sineTerm x n != 0
· 使用定理 `DifferentiableAt.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `DifferentiableAt.div_const`：DifferentiableAt.div_const (hc : Differentia
bleAt 𝕜 c x) (d : 𝕜') : DifferentiableAt 𝕜 (fun x => c x / d) x
· 使用定理 `DifferentiableAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableAt.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `logDeriv_sineTerm_eq_cotTerm`：logDeriv_sineTerm_eq_cotTerm (hx : x in Co
mplex_Int) (i : Nat) : logDeriv (fun (z : Complex) => 1 + sineTerm z i) x = cotT
erm x i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logDeriv_prod_sineTerm_eq_sum_cotTerm (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x =
    ∑ j ∈ Finset.range n, cotTerm x j := by
  rw [logDeriv_prod]
  · simp_rw [logDeriv_sineTerm_eq_cotTerm hx]
  · exact fun i _ ↦ sineTerm_ne_zero hx i
  · fun_prop
/-
**tendsto_logDeriv_euler_cot_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_logDeriv_euler_cot_sub (hx : x in Complex_Int) : Tendsto (fun n : 
Nat => ∑ j in Finset.range n, cotTerm x j) atTop (𝓝 <| π * cot (π * x) - 1 / x)
参数：hx : x in Complex_Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `logDeriv_sin_div_eq_cot`：logDeriv_sin_div_eq_cot (hz : x in Complex_Int)
 : logDeriv (fun t => (Complex.sin (π * t) / (π * t))) x = π * cot (π * x) - 1 /
 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `logDeriv_prod_sineTerm_eq_sum_cotTerm`：logDeriv_prod_sineTerm_eq_sum_cot
Term (hx : x in Complex_Int) (n : Nat) : logDeriv (fun (z : Complex) => ∏ j in F
inset.range n, (1 + sineTer…
· 使用引理 `tendsto_logDeriv_euler_sin_div`：tendsto_logDeriv_euler_sin_div (hx : x i
n Complex_Int) : Tendsto (fun n : Nat => logDeriv (fun z => ∏ j in Finset.range 
n, (1 + sineTerm z j…
-/
lemma tendsto_logDeriv_euler_cot_sub (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, cotTerm x j) atTop
    (𝓝 <| π * cot (π * x) - 1 / x) := by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx
/-
**cotTerm_identity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cotTerm_identity (hz : x in Complex_Int) (n : Nat) : cotTerm x n = 2 * x *
 (1 / ((x + (n + 1)) * (x - (n + 1))))
参数：hz : x in Complex_Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div_add_one_div`：one_div_add_one_div (ha : a != 0) (hb : b != 0) : 1
 / a + 1 / b = (a + b) / (a * b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Complex.integerComplement_add_ne_zero`：integerComplement_add_ne_zero {x 
: Complex} (hx : x in Complex_Int) (a : Int) : x + (a : Complex) != 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 57 条，此处仅展示前 30 条）
-/
lemma cotTerm_identity (hz : x ∈ ℂ_ℤ) (n : ℕ) :
    cotTerm x n = 2 * x * (1 / ((x + (n + 1)) * (x - (n + 1)))) := by
  simp only [cotTerm]
  rw [one_div_add_one_div]
  · ring
  · simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1) : ℤ)
  · simpa using (integerComplement_add_ne_zero hz ((n : ℤ) + 1))
/-
**summable_cotTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_cotTerm (hz : x in Complex_Int) : Summable fun n => cotTerm x n
参数：hz : x in Complex_Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `cotTerm_identity`：cotTerm_identity (hz : x in Complex_Int) (n : Nat) : c
otTerm x n = 2 * x * (1 / ((x + (n + 1)) * (x - (n + 1))))
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `EisensteinSeries.summable_linear_sub_mul_linear_add`：summable_linear_sub
_mul_linear_add (z : Complex) (c₁ c₂ : Int) : Summable fun n : Int => ((c₁ * z -
 n) * (c₂ * z + n))⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 32 条，此处仅展示前 30 条）
-/
lemma summable_cotTerm (hz : x ∈ ℂ_ℤ) : Summable fun n ↦ cotTerm x n := by
  rw [funext fun n ↦ cotTerm_identity hz n]
  apply Summable.mul_left
  suffices Summable fun i : ℕ ↦ (x - (↑i : ℂ))⁻¹ * (x + (↑i : ℂ))⁻¹ by
    rw [← summable_nat_add_iff 1] at this
    simpa using this
  suffices Summable fun i : ℤ ↦ (x - (↑i : ℂ))⁻¹ * (x + (↑i : ℂ))⁻¹ by
    apply this.comp_injective CharZero.cast_injective
  apply (EisensteinSeries.summable_linear_sub_mul_linear_add x 1 1).congr
  simp [mul_comm]

@[deprecated (since := "2026-01-28")] alias Summable_cotTerm := summable_cotTerm
/-
**cot_series_rep'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cot_series_rep' (hz : x in Complex_Int) : π * cot (π * x) - 1 / x = ∑' n :
 Nat, (1 / (x - (n + 1)) + 1 / (x + (n + 1)))
参数：hz : x in Complex_Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Summable.hasSum_iff_tendsto_nat`：∀ {M : Type u_1} [inst : AddCommMonoid 
M] [inst_1 : TopologicalSpace M] {m : M} [T2Space M] {f : ℕ → M},   Summable f →
 (HasSum f m ↔ Filter…
· 使用引理 `summable_cotTerm`：summable_cotTerm (hz : x in Complex_Int) : Summable fu
n n => cotTerm x n
· 使用引理 `tendsto_logDeriv_euler_cot_sub`：tendsto_logDeriv_euler_cot_sub (hx : x i
n Complex_Int) : Tendsto (fun n : Nat => ∑ j in Finset.range n, cotTerm x j) atT
op (𝓝 <| π * cot (π …
-/
lemma cot_series_rep' (hz : x ∈ ℂ_ℤ) : π * cot (π * x) - 1 / x =
    ∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

/-- The cotangent infinite sum representation. -/
/-
**cot_series_rep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cot_series_rep (hz : x in Complex_Int) : π * cot (π * x) = 1 / x + ∑' n : 
Nat+, (1 / (x - n) + 1 / (x + n))
参数：hz : x in Complex_Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_pnat_eq_tsum_succ`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {f : ℕ → M},   ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1)
· 使用引理 `cot_series_rep'`：cot_series_rep' (hz : x in Complex_Int) : π * cot (π * 
x) - 1 / x = ∑' n : Nat, (1 / (x - (n + 1)) + 1 / (x + (n + 1)))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The cotangent infinite sum representation.
-/
theorem cot_series_rep (hz : x ∈ ℂ_ℤ) :
    π * cot (π * x) = 1 / x + ∑' n : ℕ+, (1 / (x - n) + 1 / (x + n)) := by
  have h0 := tsum_pnat_eq_tsum_succ (f := fun n ↦ 1 / (x - n) + 1 / (x + n))
  have h1 := cot_series_rep' hz
  simp only [one_div, Nat.cast_add, Nat.cast_one] at *
  rw [h0, ← h1]
  ring

end MittagLeffler

section iteratedDeriv

open Set UpperHalfPlane

open scoped Nat

variable (k : ℕ)

/-
**contDiffOn_inv_linear** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma contDiffOn_inv_linear (d : ℤ) : ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z + d)) ℂ_ℤ := by
  simpa using ContDiffOn.fun_inv (by fun_prop) (fun x hx ↦ integerComplement_add_ne_zero hx d)
/-
**eqOn_iteratedDeriv_cotTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eqOn_iteratedDeriv_cotTerm (d : Nat) : EqOn (iteratedDeriv k (fun z => cot
Term z d)) (fun z => (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : Int) + (z - (d 
+ 1)) ^ (-1 - k : Int))) Complex_Int
参数：d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.add_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add (M
 i)] (f g : (i : ι) → M i), f + g = fun i => f i + g i
· 使用引理 `iteratedDeriv_add`：iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : Con
tDiffAt 𝕜 n g x) : iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDer
iv n g …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ContDiffOn.contDiffAt`：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (h
x : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent.0.con
tDiffOn_inv_linear`：∀ (k : ℕ) (d : ℤ), ContDiffOn ℂ (↑k) (fun z => 1 / (z + ↑d))
 Complex.integerComplement
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Complex.isOpen_compl_range_intCast`：IsOpen (Set.range Int.cast)ᶜ
· 使用定理 `iter_deriv_inv_linear_sub`：iter_deriv_inv_linear_sub (k : Nat) (c d : 𝕜)
 : deriv^[k] (fun x => (c * x - d)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (
c * x - d) ^ (-…
· 使用定理 `iter_deriv_inv_linear`：iter_deriv_inv_linear (k : Nat) (c d : 𝕜) : deriv
^[k] (fun x => (c * x + d)⁻¹) = (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (c * x + 
d) ^ (-1 - …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 57 条，此处仅展示前 30 条）
-/
lemma eqOn_iteratedDeriv_cotTerm (d : ℕ) :
    EqOn (iteratedDeriv k (fun z ↦ cotTerm z d))
    (fun z ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
    ℂ_ℤ := by
  intro z hz
  rw [← Pi.add_def, iteratedDeriv_add]
  · have h2 := iter_deriv_inv_linear_sub k 1 ((d + 1 : ℂ))
    have h3 := iter_deriv_inv_linear k 1 (d + 1 : ℂ)
    simp only [one_div, one_mul, one_pow, mul_one, Int.reduceNeg, iteratedDeriv_eq_iterate] at *
    rw [h2, h3]
    ring
  · simpa [sub_eq_add_neg] using (contDiffOn_inv_linear k (-(d + 1))).contDiffAt
      (isOpen_compl_range_intCast.mem_nhds hz)
  · simpa using (contDiffOn_inv_linear k (d + 1)).contDiffAt
      (isOpen_compl_range_intCast.mem_nhds hz)
/-
**eqOn_iteratedDerivWithin_cotTerm_integerComplement** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：eqOn_iteratedDerivWithin_cotTerm_integerComplement (d : Nat) : EqOn (itera
tedDerivWithin k (fun z => cotTerm z d) Complex_Int) (fun z => (-1) ^ k * k ! * 
((z + (d + 1)) ^ (-1 - k : Int) + (z - (d + 1)) ^ (-1 - k : Int))) Complex_Int
参数：d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `iteratedDerivWithin_of_isOpen`：iteratedDerivWithin_of_isOpen (hs : IsOpe
n s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s
· 使用定理 `Complex.isOpen_compl_range_intCast`：IsOpen (Set.range Int.cast)ᶜ
· 使用引理 `eqOn_iteratedDeriv_cotTerm`：eqOn_iteratedDeriv_cotTerm (d : Nat) : EqOn 
(iteratedDeriv k (fun z => cotTerm z d)) (fun z => (-1) ^ k * k ! * ((z + (d + 1
)) ^ (-1 - k : I…
-/
lemma eqOn_iteratedDerivWithin_cotTerm_integerComplement (d : ℕ) :
    EqOn
      (iteratedDerivWithin k (fun z ↦ cotTerm z d) ℂ_ℤ)
      (fun z ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
      ℂ_ℤ := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen Complex.isOpen_compl_range_intCast)
  exact eqOn_iteratedDeriv_cotTerm ..
/-
**eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet (d : Nat) : EqOn (itera
tedDerivWithin k (fun z => cotTerm z d) ℍₒ) (fun z => (-1) ^ k * k ! * ((z + (d 
+ 1)) ^ (-1 - k : Int) + (z - (d + 1)) ^ (-1 - k : Int))) ℍₒ
参数：d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `iteratedDerivWithin_congr_right_of_isOpen`：iteratedDerivWithin_congr_rig
ht_of_isOpen (f : 𝕜 -> F) (n : Nat) {s t : Set 𝕜} (hs : IsOpen s) (ht : IsOpen t
) : (s inter t).EqOn (iteratedD…
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `Complex.isOpen_compl_range_intCast`：IsOpen (Set.range Int.cast)ᶜ
· 使用引理 `Complex.upperHalfPlane_inter_integerComplement`：upperHalfPlane_inter_int
egerComplement : {z : Complex | 0 < z.im} inter Complex_Int = {z : Complex | 0 <
 z.im}
· 使用引理 `eqOn_iteratedDerivWithin_cotTerm_integerComplement`：eqOn_iteratedDerivWi
thin_cotTerm_integerComplement (d : Nat) : EqOn (iteratedDerivWithin k (fun z =>
 cotTerm z d) Complex_Int) (fun z => (-1…
· 使用定理 `UpperHalfPlane.coe_mem_integerComplement`：∀ (z : UpperHalfPlane), ↑z ∈ C
omplex.integerComplement
-/
lemma eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet (d : ℕ) :
    EqOn
      (iteratedDerivWithin k (fun z ↦ cotTerm z d) ℍₒ)
      (fun z ↦ (-1) ^ k * k ! * ((z + (d + 1)) ^ (-1 - k : ℤ) + (z - (d + 1)) ^ (-1 - k : ℤ)))
      ℍₒ := by
  apply Set.EqOn.trans (upperHalfPlane_inter_integerComplement ▸
    iteratedDerivWithin_congr_right_of_isOpen (fun z ↦ cotTerm z d) k
    isOpen_upperHalfPlaneSet (isOpen_compl_range_intCast))
  intro z hz
  simpa using! eqOn_iteratedDerivWithin_cotTerm_integerComplement k d
    (coe_mem_integerComplement ⟨z, hz⟩)

open EisensteinSeries in
/-
**cotTermUpperBound** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable abbrev cotTermUpperBound (A B : ℝ) (hB : 0 < B) (a : ℕ) :=
  k ! * (2 * (r (⟨⟨A, B⟩, hB⟩) ^ (-1 - k : ℤ)) * ‖((a + 1) ^ (-1 - k : ℤ) : ℝ)‖)
/-
**summable_cotTermUpperBound** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma summable_cotTermUpperBound (A B : ℝ) (hB : 0 < B) {k : ℕ} (hk : 1 ≤ k) :
    Summable fun a : ℕ ↦ cotTermUpperBound k A B hB a := by
  simp_rw [← mul_assoc]
  apply Summable.mul_left
  conv => enter [1, n]; rw [show (-1 - k : ℤ) = -(1 + k :) by lia, zpow_neg, zpow_natCast];
          enter [1, 1, 1]; norm_cast
  rw [summable_norm_iff, summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ (1 + k))⁻¹)]
  exact summable_nat_pow_inv.mpr <| by lia

open EisensteinSeries in
/-
**iteratedDerivWithin_cotTerm_bounded_uniformly** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iteratedDerivWithin_cotTerm_bounded_uniformly
    {k : ℕ} {K : Set ℂ} (A B : ℝ) (hB : 0 < B)
    (hKAB : K ⊆ (↑) '' verticalStrip A B) (n : ℕ) {a : ℂ} (ha : a ∈ K) :
    ‖iteratedDerivWithin k (fun z ↦ cotTerm z n) ℍₒ a‖ ≤ cotTermUpperBound k A B hB n := by
  rcases hKAB ha with ⟨a, haAB, rfl⟩
  simp only [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n a.im_pos, Complex.norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul, cotTermUpperBound,
    Int.reduceNeg, norm_zpow, Real.norm_eq_abs, two_mul, add_mul]
  gcongr
  have h1 := summand_bound_of_mem_verticalStrip (k := k + 1) (by positivity) ![1, n + 1] hB haAB
  have h2 := abs_norm_eq_max_natAbs_neg n ▸ summand_bound_of_mem_verticalStrip (k := k + 1)
    (by positivity) ![1, -(n + 1)] hB haAB
  apply norm_add_le_of_le
  · simpa (disch := positivity) [sub_eq_add_neg, ← Real.rpow_intCast, abs_norm_eq_max_natAbs,
      abs_of_nonneg] using h1
  · simpa (disch := positivity) [sub_eq_add_neg, ← Real.rpow_intCast, abs_norm_eq_max_natAbs,
      abs_of_nonneg] using h2
/-
**summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm {k : Nat} (hk : 1 <
= k) : SummableLocallyUniformlyOn (fun n => iteratedDerivWithin k (fun z => cotT
erm z n) ℍₒ) ℍₒ
参数：hk : 1 <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SummableLocallyUniformlyOn_of_locally_bounded`：SummableLocallyUniformlyO
n_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β] {f : α -> β ->
 F} {s : Set β} (hs : IsOpen s) (hu…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `UpperHalfPlane.subset_verticalStrip_of_isCompact`：subset_verticalStrip_o
f_isCompact {K : Set ℍ} (hK : IsCompact K) : exists A B : Real, 0 < B ∧ K subset
eq verticalStrip A B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `UpperHalfPlane.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : ℍ -
> Complex)
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent.0.sum
mable_cotTermUpperBound`：∀ (A B : ℝ) (hB : 0 < B) {k : ℕ}, 1 ≤ k → Summable fun 
a => cotTermUpperBound✝ k A B hB a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent.0.ite
ratedDerivWithin_cotTerm_bounded_uniformly`：∀ {k : ℕ} {K : Set ℂ} (A B : ℝ) (hB 
: 0 < B),   K ⊆ UpperHalfPlane.coe '' UpperHalfPlane.verticalStrip A B →     ∀ (
n : ℕ) {a : ℂ},       a …
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm {k : ℕ} (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn (fun n ↦ iteratedDerivWithin k (fun z ↦ cotTerm z n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  lift K to Set ℍ using hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact
    (isEmbedding_coe.isCompact_iff.mpr hKc)
  exact ⟨cotTermUpperBound k A B hB, summable_cotTermUpperBound A B hB hk,
    iteratedDerivWithin_cotTerm_bounded_uniformly A B hB <| by gcongr⟩
/-
**differentiableOn_iteratedDerivWithin_cotTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableOn_iteratedDerivWithin_cotTerm (n l : Nat) : DifferentiableO
n Complex (iteratedDerivWithin l (fun z => cotTerm z n) ℍₒ) ℍₒ
参数：n l : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.const_mul`：DifferentiableOn.const_mul (ha : Differentia
bleOn 𝕜 a s) (b : 𝔸) : DifferentiableOn 𝕜 (fun y => b * a y) s
· 使用定理 `DifferentiableOn.add`：DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f + g) s
· 使用定理 `DifferentiableOn.zpow`：DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f 
t) (h : (forall x in t, f x != 0) ∨ 0 <= m) : DifferentiableOn 𝕜 (fun x => f x ^
 m) t
· 使用定理 `DifferentiableOn.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `UpperHalfPlane.ne_intCast`：ne_intCast (z : ℍ) (n : Int) : (z : Complex) 
!= n
· 使用定理 `DifferentiableOn.sub_const`：DifferentiableOn.sub_const (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => f y - c) s
· 使用定理 `DifferentiableOn.congr`：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f
 s) (h' : forall x in s, f₁ x = f x) : DifferentiableOn 𝕜 f₁ s
· 使用引理 `eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet`：eqOn_iteratedDerivWi
thin_cotTerm_upperHalfPlaneSet (d : Nat) : EqOn (iteratedDerivWithin k (fun z =>
 cotTerm z d) ℍₒ) (fun z => (-1) ^ k * k…
-/
lemma differentiableOn_iteratedDerivWithin_cotTerm (n l : ℕ) :
    DifferentiableOn ℂ (iteratedDerivWithin l (fun z ↦ cotTerm z n) ℍₒ) ℍₒ := by
  suffices DifferentiableOn ℂ (fun z : ℂ ↦ (-1) ^ l * l ! * ((z + (n + 1)) ^ (-1 - l : ℤ) +
    (z - (n + 1)) ^ (-1 - l : ℤ))) ℍₒ by
    exact this.congr fun z hz ↦ eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet l n hz
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.add <;> refine DifferentiableOn.zpow (by fun_prop) <| .inl fun x hx ↦ ?_
  · simpa [add_eq_zero_iff_neg_eq'] using (UpperHalfPlane.ne_intCast (.mk x hx) (-(n + 1))).symm
  · simpa [sub_eq_zero] using (UpperHalfPlane.ne_intCast (.mk x hx) (n + 1))
/-
**aux_summable_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_summable_add {k : ℕ} (hk : 1 ≤ k) (x : ℂ) :
  Summable fun (n : ℕ) ↦ (x + (n + 1)) ^ (-1 - k : ℤ) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).1).congr
  simp [← zpow_neg, sub_eq_add_neg]
/-
**aux_summable_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_summable_sub {k : ℕ} (hk : 1 ≤ k) (x : ℂ) :
  Summable fun (n : ℕ) ↦ (x - (n + 1)) ^ (-1 - k : ℤ) := by
  apply ((summable_nat_add_iff 1).mpr (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.linear_right_summable x 1 (k := k + 1) (by lia))).2).congr
  simp [← zpow_neg, sub_eq_add_neg]

variable {z : ℂ}

-- We have this auxiliary ugly version on the lhs so the rhs looks nicer.
/-
**aux_iteratedDeriv_tsum_cotTerm** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_iteratedDeriv_tsum_cotTerm {k : ℕ} (hk : 1 ≤ k) (hz : z ∈ ℍₒ) :
    (-1) ^ k * (k !) * z ^ (-1 - k : ℤ) +
      iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, cotTerm z n) ℍₒ z =
    (-1) ^ k * k ! * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet hz
    (fun t ht ↦ summable_cotTerm (coe_mem_integerComplement ⟨t, ht⟩))
    (fun l hl hl2 ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cotTerm hl)
    (fun n l z hl hz ↦ (differentiableOn_iteratedDerivWithin_cotTerm n l).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz))]
  conv =>
    enter [1, 2, 1, n]
    rw [eqOn_iteratedDerivWithin_cotTerm_upperHalfPlaneSet k n (by simp [hz])]
  rw [tsum_of_add_one_of_neg_add_one (by simpa using aux_summable_add hk z)
    (by simpa [sub_eq_add_neg] using aux_summable_sub hk z),
    tsum_mul_left, Summable.tsum_add (aux_summable_add hk z) (aux_summable_sub hk z)]
  push_cast
  ring_nf
/-
**iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum {k : Nat} (hk : 1 <= k) (h
z : z in ℍₒ) : iteratedDerivWithin k (fun x : Complex => π * cot (π * x) - 1 / x
) ℍₒ z = -(-1) ^ k * k ! * (z ^ (-1 - k : Int)) + (-1) ^ k * k ! * ∑' n : Int, (
z + n) ^ (-1 - k : Int)
参数：hk : 1 <= k；hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent.0.aux
_iteratedDeriv_tsum_cotTerm`：∀ {z : ℂ} {k : ℕ},   1 ≤ k →     z ∈ UpperHalfPlane
.upperHalfPlaneSet →       (-1) ^ k * ↑k.factorial * z ^ (-1 - ↑k) +           i
teratedDe…
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `iteratedDerivWithin_congr`：iteratedDerivWithin_congr (hfg : Set.EqOn f g
 s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s
· 使用引理 `cot_series_rep'`：cot_series_rep' (hz : x in Complex_Int) : π * cot (π * 
x) - 1 / x = ∑' n : Nat, (1 / (x - (n + 1)) + 1 / (x + (n + 1)))
· 使用定理 `UpperHalfPlane.coe_mem_integerComplement`：∀ (z : UpperHalfPlane), ↑z ∈ C
omplex.integerComplement
-/
lemma iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum {k : ℕ} (hk : 1 ≤ k) (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x) - 1 / x) ℍₒ z =
    -(-1) ^ k * k ! * (z ^ (-1 - k : ℤ)) + (-1) ^ k * k ! * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
  simp only [← aux_iteratedDeriv_tsum_cotTerm hk hz, one_div, neg_mul, neg_add_cancel_left]
  refine iteratedDerivWithin_congr (fun z hz ↦ ?_) hz
  simpa [cotTerm] using (cot_series_rep' (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))
/-
**iteratedDerivWithin_cot_pi_mul_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iteratedDerivWithin_cot_pi_mul_sub_inv {z : ℂ} (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x) - 1 / x) ℍₒ z =
    (iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x)) ℍₒ z) -
    (-1) ^ k * k ! * (z ^ (-1 - k : ℤ)) := by
  simp_rw [sub_eq_add_neg]
  rw [iteratedDerivWithin_fun_add hz isOpen_upperHalfPlaneSet.uniqueDiffOn]
  · simpa [iteratedDerivWithin_fun_neg] using! iteratedDerivWithin_one_div k
      isOpen_upperHalfPlaneSet hz
  · exact ContDiffWithinAt.mul (by fun_prop) (cot_pi_mul_contDiffWithinAt k
      (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩))
  · simp only [one_div]
    apply ContDiffWithinAt.neg
    exact ContDiffWithinAt.inv (by fun_prop) (ne_zero ⟨z, hz⟩)
/-
**iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow {k : Nat} (hk : 1 <= k) {z
 : Complex} (hz : z in ℍₒ) : iteratedDerivWithin k (fun x : Complex => π * cot (
π * x)) ℍₒ z = (-1) ^ k * k ! * ∑' n : Int, (z + n) ^ (-1 - k : Int)
参数：hk : 1 <= k；hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent.0.ite
ratedDerivWithin_cot_pi_mul_sub_inv`：∀ (k : ℕ) {z : ℂ},   z ∈ UpperHalfPlane.upp
erHalfPlaneSet →     iteratedDerivWithin k (fun x => ↑Real.pi * (↑Real.pi * x).c
ot - 1 / x) Upper…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum`：iteratedDerivWithin_cot
_sub_inv_eq_add_mul_tsum {k : Nat} (hk : 1 <= k) (hz : z in ℍₒ) : iteratedDerivW
ithin k (fun x : Complex => π * cot (…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_prod_atom`：∀ {R : Type u_1} [inst : CommS
emiring R] (a : R) (b : ℕ) {e : R}, (a + 0) ^ b * Nat.rawCast 1 = e → a ^ b = e
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 42 条，此处仅展示前 30 条）
-/
lemma iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x)) ℍₒ z =
    (-1) ^ k * k ! * ∑' n : ℤ, (z + n) ^ (-1 - k : ℤ) := by
  have h0 := iteratedDerivWithin_cot_pi_mul_sub_inv k hz
  rw [iteratedDerivWithin_cot_sub_inv_eq_add_mul_tsum hk hz, add_comm] at h0
  rw [← add_left_inj (-(-1) ^ k * k ! * z ^ (-1 - k : ℤ)), h0]
  ring

/-- The series expansion of the iterated derivative of `π cot (π z)`. -/
/-
**iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow {k : Nat} (hk : 1 <= k)
 {z : Complex} (hz : z in ℍₒ) : iteratedDerivWithin k (fun x : Complex => π * co
t (π * x)) ℍₒ z = (-1) ^ k * k ! * ∑' n : Int, 1 / (z + n) ^ (k + 1)
参数：hk : 1 <= k；hz : z in ℍₒ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg_coe_of_pos`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G) {n
 : ℕ}, 0 < n → a ^ (-↑n) = (a ^ n)⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow`：iteratedDerivWithin_cot
_pi_mul_eq_mul_tsum_zpow {k : Nat} (hk : 1 <= k) {z : Complex} (hz : z in ℍₒ) : 
iteratedDerivWithin k (fun x : Comple…

--- 原说明 ---
The series expansion of the iterated derivative of `π cot (π z)`.
-/
theorem iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow {k : ℕ} (hk : 1 ≤ k) {z : ℂ}
    (hz : z ∈ ℍₒ) :
    iteratedDerivWithin k (fun x : ℂ ↦ π * cot (π * x)) ℍₒ z =
      (-1) ^ k * k ! * ∑' n : ℤ, 1 / (z + n) ^ (k + 1) := by
  convert! iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_zpow hk hz with n
  rw [show (-1 - k : ℤ) = -(k + 1 :) by norm_cast; lia, zpow_neg_coe_of_pos _ (by lia),
    one_div]

end iteratedDeriv

