/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Complex arctangent

This file defines the complex arctangent `Complex.arctan` as
$$\arctan z = -\frac i2 \log \frac{1 + zi}{1 - zi}$$
and shows that it extends `Real.arctan` to the complex plane. Its Taylor series expansion
$$\arctan z = \frac{(-1)^n}{2n + 1} z^{2n + 1},\ |z|<1$$
is proved in `Complex.hasSum_arctan`.
-/

@[expose] public section


namespace Complex

open scoped Real

/-- The complex arctangent, defined via the complex logarithm. -/
/-
**Complex.arctan** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：arctan (z : Complex) : Complex
参数：z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex arctangent, defined via the complex logarithm.
-/
noncomputable def arctan (z : ℂ) : ℂ := -I / 2 * log ((1 + z * I) / (1 - z * I))
/-
**Complex.tan_arctan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tan_arctan {z : Complex} (h₁ : z != I) (h₂ : z != -I) : tan (arctan z) = z
参数：h₁ : z != I；h₂ : z != -I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `Complex.div_I`：div_I (z : Complex) : z / I = -(z * I)
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Complex.arctan.eq_1`：∀ (z : ℂ), z.arctan = -Complex.I / 2 * Complex.log 
((1 + z * Complex.I) / (1 - z * Complex.I))
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 118 条，此处仅展示前 30 条）
-/
theorem tan_arctan {z : ℂ} (h₁ : z ≠ I) (h₂ : z ≠ -I) : tan (arctan z) = z := by
  unfold tan sin cos
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ two_ne_zero, ← div_mul_eq_mul_div,
    -- multiply top and bottom by `exp (arctan z * I)`
    ← mul_div_mul_right _ _ (exp_ne_zero (arctan z * I)), sub_mul, add_mul,
    ← exp_add, neg_mul, neg_add_cancel, exp_zero, ← exp_add, ← two_mul]
  have z₁ : 1 + z * I ≠ 0 := by
    contrapose h₁
    rw [add_eq_zero_iff_neg_eq, ← div_eq_iff I_ne_zero, div_I, neg_one_mul, neg_neg] at h₁
    exact h₁.symm
  have z₂ : 1 - z * I ≠ 0 := by
    contrapose h₂
    rw [sub_eq_zero, ← div_eq_iff I_ne_zero, div_I, one_mul] at h₂
    exact h₂.symm
  have key : exp (2 * (arctan z * I)) = (1 + z * I) / (1 - z * I) := by
    rw [arctan, ← mul_rotate, ← mul_assoc,
      show 2 * (I * (-I / 2)) = 1 by simp [field], one_mul, exp_log]
    · exact div_ne_zero z₁ z₂
  -- multiply top and bottom by `1 - z * I`
  rw [key, ← mul_div_mul_right _ _ z₂, sub_mul, add_mul, div_mul_cancel₀ _ z₂, one_mul,
    show _ / _ * I = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]

/-- `cos z` is nonzero when the bounds in `arctan_tan` are met (`z` lies in the vertical strip
`-π / 2 < z.re < π / 2` and `z ≠ π / 2`). -/
/-
**Complex.cos_ne_zero_of_arctan_bounds** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cos_ne_zero_of_arctan_bounds {z : Complex} (h₀ : z != π / 2) (h₁ : -(π / 2
) < z.re) (h₂ : z.re <= π / 2) : cos z != 0
参数：h₀ : z != π / 2；h₁ : -(π / 2) < z.re；h₂ : z.re <= π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.cos_ne_zero_iff`：cos_ne_zero_iff {θ : Complex} : cos θ != 0 ↔ fo
rall k : Int, θ != (2 * k + 1) * π / 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_le_mul_iff_of_pos_right`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Z
ero α] [inst_2 : Preorder α] {a b c : α} [MulPosMono α] [MulPosReflectLE α],   0
 < a → (b * a ≤ c…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
`cos z` is nonzero when the bounds in `arctan_tan` are met (`z` lies in the vert
ical strip
`-π / 2 < z.re < π / 2` and `z ≠ π / 2`).
-/
lemma cos_ne_zero_of_arctan_bounds {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re)
    (h₂ : z.re ≤ π / 2) : cos z ≠ 0 := by
  refine cos_ne_zero_iff.mpr (fun k ↦ ?_)
  rw [ne_eq, Complex.ext_iff, not_and_or] at h₀ ⊢
  norm_cast at h₀ ⊢
  rcases h₀ with nr | ni
  · left; contrapose nr
    rw [nr, mul_div_assoc, neg_eq_neg_one_mul, mul_lt_mul_iff_of_pos_right (by positivity)] at h₁
    rw [nr, ← one_mul (π / 2), mul_div_assoc, mul_le_mul_iff_of_pos_right (by positivity)] at h₂
    norm_cast at h₁ h₂
    change -1 < _ at h₁
    rwa [show 2 * k + 1 = 1 by lia, Int.cast_one, one_mul] at nr
  · exact Or.inr ni

set_option linter.flexible false in -- TODO: fix non-terminal simp
/-
**Complex.arctan_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arctan_tan {z : Complex} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.
re <= π / 2) : arctan (tan z) = z
参数：h₀ : z != π / 2；h₁ : -(π / 2) < z.re；h₂ : z.re <= π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.cos_ne_zero_of_arctan_bounds`：cos_ne_zero_of_arctan_bounds {z : 
Complex} (h₀ : z != π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re <= π / 2) : cos z !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Complex.cos_neg`：cos_neg : cos (-x) = cos x
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `Complex.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
（共 89 条，此处仅展示前 30 条）
-/
theorem arctan_tan {z : ℂ} (h₀ : z ≠ π / 2) (h₁ : -(π / 2) < z.re) (h₂ : z.re ≤ π / 2) :
    arctan (tan z) = z := by
  have h := cos_ne_zero_of_arctan_bounds h₀ h₁ h₂
  unfold arctan tan
  -- multiply top and bottom by `cos z`
  rw [← mul_div_mul_right (1 + _) _ h, add_mul, sub_mul, one_mul, ← mul_rotate, mul_div_cancel₀ _ h]
  conv_lhs =>
    enter [2, 1, 2]
    rw [sub_eq_add_neg, ← neg_mul, ← sin_neg, ← cos_neg]
  rw [← exp_mul_I, ← exp_mul_I, ← exp_sub, show z * I - -z * I = 2 * (I * z) by ring, log_exp,
    show -I / 2 * (2 * (I * z)) = -(I * I) * z by ring, I_mul_I, neg_neg, one_mul]
  all_goals simp
  · rwa [← div_lt_iff₀' two_pos, neg_div]
  · rwa [← le_div_iff₀' two_pos]

@[simp, norm_cast]
/-
**Complex.ofReal_arctan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_arctan (x : Real) : (Real.arctan x : Complex) = arctan x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.tan_arctan`：tan_arctan (x : Real) : tan (arctan x) = x
· 使用定理 `Complex.ofReal_tan`：ofReal_tan (x : Real) : (Real.tan x : Complex) = tan
 x
· 使用定理 `Complex.arctan_tan`：arctan_tan {z : Complex} (h₀ : z != π / 2) (h₁ : -(π
 / 2) < z.re) (h₂ : z.re <= π / 2) : arctan (tan z) = z
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Real.arctan_lt_pi_div_two`：arctan_lt_pi_div_two (x : Real) : arctan x < 
π / 2
· 使用定理 `Real.neg_pi_div_two_lt_arctan`：neg_pi_div_two_lt_arctan (x : Real) : -(π
 / 2) < arctan x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ofReal_arctan (x : ℝ) : (Real.arctan x : ℂ) = arctan x := by
  conv_rhs => rw [← Real.tan_arctan x]
  rw [ofReal_tan, arctan_tan]
  all_goals norm_cast
  · rw [← ne_eq]; exact (Real.arctan_lt_pi_div_two _).ne
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact (Real.arctan_lt_pi_div_two _).le

/-- The argument of `1 + z` for `z` in the open unit disc is always in `(-π / 2, π / 2)`. -/
/-
**Complex.arg_one_add_mem_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：arg_one_add_mem_Ioo {z : Complex} (hz : ‖z‖ < 1) : (1 + z).arg in Set.Ioo 
(-(π / 2)) (π / 2)
参数：hz : ‖z‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Complex.abs_arg_lt_pi_div_two_iff`：abs_arg_lt_pi_div_two_iff {z : Comple
x} : |arg z| < π / 2 ↔ 0 < re z ∨ z = 0
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
· 使用定理 `neg_lt_iff_pos_add'`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] 
[AddLeftStrictMono α] {a b : α}, -a < b ↔ 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Complex.abs_re_le_norm`：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖

--- 原说明 ---
The argument of `1 + z` for `z` in the open unit disc is always in `(-π / 2, π /
 2)`.
-/
lemma arg_one_add_mem_Ioo {z : ℂ} (hz : ‖z‖ < 1) : (1 + z).arg ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [Set.mem_Ioo, ← abs_lt, abs_arg_lt_pi_div_two_iff, add_re, one_re, ← neg_lt_iff_pos_add']
  exact Or.inl (abs_lt.mp ((abs_re_le_norm z).trans_lt hz)).1

/-- We can combine the logs in `log (1 + z * I) + -log (1 - z * I)` into one.
This is only used in `hasSum_arctan`. -/
/-
**Complex.hasSum_arctan_aux** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasSum_arctan_aux {z : Complex} (hz : ‖z‖ < 1) : log (1 + z * I) + -log (1
 - z * I) = log ((1 + z * I) / (1 - z * I))
参数：hz : ‖z‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Complex.mem_slitPlane_iff_arg`：mem_slitPlane_iff_arg {z : Complex} : z i
n slitPlane ↔ z.arg != π ∧ z != 0
· 使用定理 `Complex.mem_slitPlane_of_norm_lt_one`：∀ {z : ℂ}, ‖z‖ < 1 → 1 + z ∈ Compl
ex.slitPlane
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.log_inv`：log_inv (x : Complex) (hx : x.arg != π) : log x⁻¹ = -lo
g x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Complex.log_mul_eq_add_log_iff`：log_mul_eq_add_log_iff {x y : Complex} (
hx₀ : x != 0) (hy₀ : y != 0) : log (x * y) = log x + log y ↔ arg x + arg y in Se
t.Ioc (-π) π
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.arg_one_add_mem_Ioo`：arg_one_add_mem_Ioo {z : Complex} (hz : ‖z‖
 < 1) : (1 + z).arg in Set.Ioo (-(π / 2)) (π / 2)
· 使用定理 `Complex.arg_inv`：arg_inv (x : Complex) : arg x⁻¹ = if arg x = π then π e
lse -arg x
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
We can combine the logs in `log (1 + z * I) + -log (1 - z * I)` into one.
This is only used in `hasSum_arctan`.
-/
lemma hasSum_arctan_aux {z : ℂ} (hz : ‖z‖ < 1) :
    log (1 + z * I) + -log (1 - z * I) = log ((1 + z * I) / (1 - z * I)) := by
  have z₁ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := z * I) (by simpa))
  have z₂ := mem_slitPlane_iff_arg.mp (mem_slitPlane_of_norm_lt_one (z := -(z * I)) (by simpa))
  rw [← sub_eq_add_neg] at z₂
  rw [← log_inv _ z₂.1, ← (log_mul_eq_add_log_iff z₁.2 (inv_eq_zero.ne.mpr z₂.2)).mpr,
    div_eq_mul_inv]
  -- `log_mul_eq_add_log_iff` requires a bound on `arg (1 + z * I) + arg (1 - z * I)⁻¹`.
  -- `arg_one_add_mem_Ioo` provides sufficiently tight bounds on both terms
  have b₁ := arg_one_add_mem_Ioo (z := z * I) (by simpa)
  have b₂ : arg (1 - z * I)⁻¹ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    simp_rw [arg_inv, z₂.1, ite_false, Set.neg_mem_Ioo_iff, neg_neg, sub_eq_add_neg]
    exact arg_one_add_mem_Ioo (by simpa)
  have c₁ := add_lt_add b₁.1 b₂.1
  have c₂ := add_lt_add b₁.2 b₂.2
  rw [show -(π / 2) + -(π / 2) = -π by ring] at c₁
  rw [show π / 2 + π / 2 = π by ring] at c₂
  exact ⟨c₁, c₂.le⟩

set_option backward.defeqAttrib.useBackward true in
/-- The power series expansion of `Complex.arctan`, valid on the open unit disc. -/
/-
**Complex.hasSum_arctan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasSum_arctan {z : Complex} (hz : ‖z‖ < 1) : HasSum (fun n : Nat => (-1) ^
 n * z ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan z)
参数：hz : ‖z‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `Complex.hasSum_taylorSeries_log`：hasSum_taylorSeries_log {z : Complex} (
hz : ‖z‖ < 1) : HasSum (fun n : Nat => (-1) ^ (n + 1) * z ^ n / n) (log (1 + z))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Complex.hasSum_taylorSeries_neg_log`：hasSum_taylorSeries_neg_log {z : Co
mplex} (hz : ‖z‖ < 1) : HasSum (fun n : Nat => z ^ n / n) (-log (1 - z))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} (e : γ ≃ β
), Has…
· 使用引理 `Complex.hasSum_arctan_aux`：hasSum_arctan_aux {z : Complex} (hz : ‖z‖ < 1
) : log (1 + z * I) + -log (1 - z * I) = log ((1 + z * I) / (1 - z * I))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `HasSum.prod_fiberwise`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [Regula
rSpace α] {…
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
The power series expansion of `Complex.arctan`, valid on the open unit disc.
-/
theorem hasSum_arctan {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan z) := by
  have := ((hasSum_taylorSeries_log (z := z * I) (by simpa)).add
    (hasSum_taylorSeries_neg_log (z := z * I) (by simpa))).mul_left (-I / 2)
  simp_rw [← add_div, ← add_one_mul, hasSum_arctan_aux hz] at this
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Odd.neg_one_pow (n := 2 * k + 0 + 1) (by simp),
    neg_add_cancel, zero_mul, zero_div, mul_zero, zero_add,
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Even.neg_one_pow (n := 2 * (k + 1)) (by simp),
    ← mul_div_assoc (_ / _), ← mul_assoc, show -I / 2 * (1 + 1) = -I by ring]
  congr 1
  rw [mul_pow, pow_succ' I, pow_mul, I_sq,
    show -I * _ = -(I * I) * (-1) ^ k * z ^ (2 * k + 1) by ring, I_mul_I, neg_neg, one_mul]

end Complex

/-- The power series expansion of `Real.arctan`, valid on `-1 < x < 1`. -/
/-
**Real.hasSum_arctan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.hasSum_arctan {x : Real} (hx : ‖x‖ < 1) : HasSum (fun n : Nat => (-1)
 ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan x)
参数：hx : ‖x‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.hasSum_arctan`：hasSum_arctan {z : Complex} (hz : ‖z‖ < 1) : HasS
um (fun n : Nat => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan z)
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖

--- 原说明 ---
The power series expansion of `Real.arctan`, valid on `-1 < x < 1`.
-/
theorem Real.hasSum_arctan {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) (arctan x) :=
  mod_cast Complex.hasSum_arctan (z := x) (by simpa)
