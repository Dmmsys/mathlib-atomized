/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Sinc function

This file contains the definition of the sinc function and some of its properties.

## Main definitions

* `Real.sinc`: the (unnormalized) sinc function, defined as `sinc x = sin x / x` for `x ≠ 0`
  and `1` for `x = 0`.

## Main statements

* `continuous_sinc`: the sinc function is continuous.

-/

@[expose] public section

open Filter
open scoped Topology

namespace Real

variable {x : ℝ}

/-- The function `sin x / x` modified to take the value 1 at 0, which makes it continuous. -/
@[pp_nodot]
/-
**Real.sinc** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sinc (x : Real) : Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `sin x / x` modified to take the value 1 at 0, which makes it conti
nuous.
-/
noncomputable def sinc (x : ℝ) : ℝ := if x = 0 then 1 else sin x / x
/-
**Real.sinc_apply** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_apply : sinc x = if x = 0 then 1 else sin x / x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sinc_apply : sinc x = if x = 0 then 1 else sin x / x := rfl

@[simp]
/-
**Real.sinc_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_zero : sinc 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]
/-
**Real.sinc_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_of_ne_zero (hx : x != 0) : sinc x = sin x / x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sinc_of_ne_zero (hx : x ≠ 0) : sinc x = sin x / x := by simp [sinc, hx]
/-
**Real.sinc_eq_dslope** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_eq_dslope : sinc = dslope sin 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_sin`：deriv_sin : deriv sin = cos
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sinc_eq_dslope : sinc = dslope sin 0 := by
  ext
  simp [dslope, Function.update_apply, sinc, slope, div_eq_inv_mul]

@[simp]
/-
**Real.sinc_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_neg (x : Real) : sinc (-x) = sinc x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `Real.sinc_zero`：sinc_zero : sinc 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Real.sinc_of_ne_zero`：sinc_of_ne_zero (hx : x != 0) : sinc x = sin x / x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
-/
lemma sinc_neg (x : ℝ) : sinc (-x) = sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero hx, sinc_of_ne_zero (neg_ne_zero.mpr hx)]
/-
**Real.abs_sinc_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：abs_sinc_le_one (x : Real) : |sinc x| <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.sinc_zero`：sinc_zero : sinc 0 = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `Real.sinc_of_ne_zero`：sinc_of_ne_zero (hx : x != 0) : sinc x = sin x / x
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Real.abs_sin_le_abs`：abs_sin_le_abs : |sin x| <= |x|
-/
lemma abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx, abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact abs_sin_le_abs
/-
**Real.sinc_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_le_one (x : Real) : sinc x <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用引理 `Real.abs_sinc_le_one`：abs_sinc_le_one (x : Real) : |sinc x| <= 1
-/
lemma sinc_le_one (x : ℝ) : sinc x ≤ 1 := (abs_le.mp (abs_sinc_le_one x)).2
/-
**Real.neg_one_le_sinc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：neg_one_le_sinc (x : Real) : -1 <= sinc x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用引理 `Real.abs_sinc_le_one`：abs_sinc_le_one (x : Real) : |sinc x| <= 1
-/
lemma neg_one_le_sinc (x : ℝ) : -1 ≤ sinc x := (abs_le.mp (abs_sinc_le_one x)).1
/-
**Real.sin_div_le_inv_abs** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sin_div_le_inv_abs (x : Real) : sin x / x <= |x|⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
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
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 69 条，此处仅展示前 30 条）
-/
lemma sin_div_le_inv_abs (x : ℝ) : sin x / x ≤ |x|⁻¹ := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_nonpos hx.le, ← one_div, le_div_iff₀, div_eq_mul_inv]
    · ring_nf
      rw [mul_assoc, mul_inv_cancel₀ hx.ne, mul_one, neg_le]
      exact neg_one_le_sin x
    · simpa using hx
  · simp
  · rw [abs_of_nonneg hx.le, div_eq_mul_inv, mul_inv_le_iff₀ hx, inv_mul_cancel₀ hx.ne']
    exact sin_le_one x
/-
**Real.sinc_le_inv_abs** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinc_le_inv_abs (hx : x != 0) : sinc x <= |x|⁻¹
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.sinc_of_ne_zero`：sinc_of_ne_zero (hx : x != 0) : sinc x = sin x / x
· 使用引理 `Real.sin_div_le_inv_abs`：sin_div_le_inv_abs (x : Real) : sin x / x <= |x
|⁻¹
-/
lemma sinc_le_inv_abs (hx : x ≠ 0) : sinc x ≤ |x|⁻¹ := by
  rw [sinc_of_ne_zero hx]
  exact sin_div_le_inv_abs x

/-- The function `sinc` is continuous. -/
@[fun_prop]
/-
**Real.continuous_sinc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：continuous_sinc : Continuous sinc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.sinc_eq_dslope`：sinc_eq_dslope : sinc = dslope sin 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `continuousAt_dslope_of_ne`：continuousAt_dslope_of_ne (h : b != a) : Cont
inuousAt (dslope f a) b ↔ ContinuousAt f b
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Real.continuous_sin`：continuous_sin : Continuous sin

--- 原说明 ---
The function `sinc` is continuous.
-/
lemma continuous_sinc : Continuous sinc := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  rw [sinc_eq_dslope]
  by_cases hx : x = 0
  · simp [hx]
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

end Real

