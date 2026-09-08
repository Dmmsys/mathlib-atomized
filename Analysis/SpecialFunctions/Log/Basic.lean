/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Real logarithm

In this file we define `Real.log` to be the logarithm of a real number. As usual, we extend it from
its domain `(0, +∞)` to a globally defined function. We choose to do it so that `log 0 = 0` and
`log (-x) = log x`.

We prove some basic properties of this function and show that it is continuous.

## Tags

logarithm, continuity
-/

@[expose] public section

open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {x y : ℝ}

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot, wikidata Q11197]
/-
**Real.log** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：log (x : Real) : Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real logarithm function, equal to the inverse of the exponential for `x > 0`
,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extensi
on to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero 
`x` and `y`, and
the derivative of `log` is `1/x` away from `0`.
-/
noncomputable def log (x : ℝ) : ℝ :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
/-
**Real.log_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_of_ne_zero (hx : x != 0) : log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx
⟩
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem log_of_ne_zero (hx : x ≠ 0) : log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩ :=
  dif_neg hx
/-
**Real.log_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_of_pos (hx : 0 < x) : log x = expOrderIso.symm ⟨x, hx⟩
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_of_ne_zero`：log_of_ne_zero (hx : x != 0) : log x = expOrderIso.
symm ⟨|x|, abs_pos.2 hx⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
-/
theorem log_of_pos (hx : 0 < x) : log x = expOrderIso.symm ⟨x, hx⟩ := by
  rw [log_of_ne_zero hx.ne']
  congr
  exact abs_of_pos hx

set_option backward.isDefEq.respectTransparency false in
/-
**Real.exp_log_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_of_ne_zero`：log_of_ne_zero (hx : x != 0) : log x = expOrderIso.
symm ⟨|x|, abs_pos.2 hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_expOrderIso_apply`：coe_expOrderIso_apply (x : Real) : (expOrder
Iso x : Real) = exp x
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = |x| := by
  rw [log_of_ne_zero hx, ← coe_expOrderIso_apply, OrderIso.apply_symm_apply, Subtype.coe_mk]
/-
**Real.exp_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_log (hx : 0 < x) : exp (log x) = x
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem exp_log (hx : 0 < x) : exp (log x) = x := by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx
/-
**Real.exp_log_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_log_of_neg (hx : x < 0) : exp (log x) = -x
参数：hx : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem exp_log_of_neg (hx : x < 0) : exp (log x) = -x := by
  rw [exp_log_eq_abs (ne_of_lt hx)]
  exact abs_of_neg hx
/-
**Real.le_exp_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_exp_log (x : Real) : x <= exp (log x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log.eq_1`：∀ (x : ℝ), Real.log x = if hx : x = 0 then 0 else Real.ex
pOrderIso.symm ⟨|x|, ⋯⟩
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem le_exp_log (x : ℝ) : x ≤ exp (log x) := by
  by_cases h_zero : x = 0
  · rw [h_zero, log, dif_pos rfl, exp_zero]
    exact zero_le_one
  · rw [exp_log_eq_abs h_zero]
    exact le_abs_self _

@[simp, push]
/-
**Real.log_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_exp (x : Real) : log (exp x) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem log_exp (x : ℝ) : log (exp x) = x :=
  exp_injective <| exp_log (exp_pos x)
/-
**Real.log_comp_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.log ∘ Real.exp = id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
@[simp] theorem log_comp_exp : log ∘ exp = id := funext log_exp
/-
**Real.exp_one_mul_le_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_one_mul_le_exp {x : Real} : exp 1 * x <= exp x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `Real.add_one_le_exp`：add_one_le_exp (x : Real) : x + 1 <= Real.exp x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
-/
theorem exp_one_mul_le_exp {x : ℝ} : exp 1 * x ≤ exp x := by
  by_cases hx0 : x ≤ 0
  · apply le_trans (mul_nonpos_of_nonneg_of_nonpos (exp_pos 1).le hx0) (exp_nonneg x)
  · have h := add_one_le_exp (log x)
    rwa [← exp_le_exp, exp_add, exp_log (lt_of_not_ge hx0), mul_comm] at h
/-
**Real.two_mul_le_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：two_mul_le_exp {x : Real} : 2 * x <= exp x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.add_one_le_exp`：add_one_le_exp (x : Real) : x + 1 <= Real.exp x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Real.exp_one_mul_le_exp`：exp_one_mul_le_exp {x : Real} : exp 1 * x <= ex
p x
-/
theorem two_mul_le_exp {x : ℝ} : 2 * x ≤ exp x := by
  by_cases hx0 : x < 0
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by simp only [Nat.ofNat_nonneg]) hx0.le)
      (exp_nonneg x)
  · apply le_trans (mul_le_mul_of_nonneg_right _ (le_of_not_gt hx0)) exp_one_mul_le_exp
    have := Real.add_one_le_exp 1
    rwa [one_add_one_eq_two] at this
/-
**Real.surjOn_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：surjOn_log : SurjOn log (Ioi 0) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
theorem surjOn_log : SurjOn log (Ioi 0) univ := fun x _ => ⟨exp x, exp_pos x, log_exp x⟩
/-
**Real.log_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_surjective : Surjective log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
theorem log_surjective : Surjective log := fun x => ⟨exp x, log_exp x⟩

@[simp]
/-
**Real.range_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：range_log : range log = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Real.log_surjective`：log_surjective : Surjective log
-/
theorem range_log : range log = univ :=
  log_surjective.range_eq

@[simp, push]
/-
**Real.log_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_zero : log 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem log_zero : log 0 = 0 :=
  dif_pos rfl

@[simp, push]
/-
**Real.log_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_one : log 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
-/
theorem log_one : log 1 = 0 :=
  exp_injective <| by rw [exp_log zero_lt_one, exp_zero]

/-- This holds true for all `x : ℝ` because of the junk values `0 / 0 = 0` and `log 0 = 0`. -/
/-
**Real.log_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (x : ℝ), Real.log (x / x) = 0
参数：x : ℝ；x / x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.log_one`：log_one : log 1 = 0

--- 原说明 ---
This holds true for all `x : ℝ` because of the junk values `0 / 0 = 0` and `log 
0 = 0`.
-/
@[simp] lemma log_div_self (x : ℝ) : log (x / x) = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp, push]
/-
**Real.log_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_abs (x : Real) : log |x| = log x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ x = y
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `abs_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [AddL
eftMono α] [AddRightMono α] (a : α), |(|a|)| = |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem log_abs (x : ℝ) : log |x| = log x := by
  by_cases h : x = 0
  · simp [h]
  · rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs]

@[simp, push]
/-
**Real.log_neg_eq_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_neg_eq_log (x : Real) : log (-x) = log x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
theorem log_neg_eq_log (x : ℝ) : log (-x) = log x := by rw [← log_abs x, ← log_abs (-x), abs_neg]
/-
**Real.sinh_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_log {x : Real} (hx : 0 < x) : sinh (log x) = (x - x⁻¹) / 2
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sinh_eq`：∀ (x : ℝ), Real.sinh x = (Real.exp x - Real.exp (-x)) / 2
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
-/
theorem sinh_log {x : ℝ} (hx : 0 < x) : sinh (log x) = (x - x⁻¹) / 2 := by
  rw [sinh_eq, exp_neg, exp_log hx]
/-
**Real.cosh_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_log {x : Real} (hx : 0 < x) : cosh (log x) = (x + x⁻¹) / 2
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.cosh_eq`：cosh_eq (x : Real) : cosh x = (exp x + exp (-x)) / 2
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
-/
theorem cosh_log {x : ℝ} (hx : 0 < x) : cosh (log x) = (x + x⁻¹) / 2 := by
  rw [cosh_eq, exp_neg, exp_log hx]
/-
**Real.surjOn_log'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：surjOn_log' : SurjOn log (Iio 0) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
theorem surjOn_log' : SurjOn log (Iio 0) univ := fun x _ =>
  ⟨-exp x, neg_lt_zero.2 <| exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

@[push]
/-
**Real.log_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x + log y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
-/
theorem log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
  exp_injective <| by
    rw [exp_log_eq_abs (mul_ne_zero hx hy), exp_add, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_mul]

@[push]
/-
**Real.log_div** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x - log y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
-/
theorem log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y :=
  exp_injective <| by
    rw [exp_log_eq_abs (div_ne_zero hx hy), exp_sub, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_div]

@[simp, push]
/-
**Real.log_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_inv (x : Real) : log x⁻¹ = -log x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ x = y
· 使用定理 `Real.exp_log_eq_abs`：exp_log_eq_abs (hx : x != 0) : exp (log x) = |x|
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
-/
theorem log_inv (x : ℝ) : log x⁻¹ = -log x := by
  by_cases hx : x = 0; · simp [hx]
  rw [← exp_eq_exp, exp_log_eq_abs (inv_ne_zero hx), exp_neg, exp_log_eq_abs hx, abs_inv]
/-
**Real.log_le_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= log y ↔ x <= y
参数：h : 0 < x；h₁ : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y := by
  rw [← exp_le_exp, exp_log h, exp_log h₁]

@[gcongr, bound]
/-
**Real.log_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
参数：hx : 0 < x；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
lemma log_le_log (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  (log_le_log_iff hx (hx.trans_le hxy)).2 hxy

@[gcongr, bound]
/-
**Real.log_lt_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
参数：hx : 0 < x；h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
theorem log_lt_log (hx : 0 < x) (h : x < y) : log x < log y := by
  rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)]
/-
**Real.log_lt_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y := by
  rw [← exp_lt_exp, exp_log hx, exp_log hy]
/-
**Real.log_le_iff_le_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_le_iff_le_exp (hx : 0 < x) : log x <= y ↔ x <= exp y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_le_iff_le_exp (hx : 0 < x) : log x ≤ y ↔ x ≤ exp y := by rw [← exp_le_exp, exp_log hx]
/-
**Real.log_lt_iff_lt_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y := by rw [← exp_lt_exp, exp_log hx]
/-
**Real.le_log_iff_exp_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_log_iff_exp_le (hy : 0 < y) : x <= log y ↔ exp x <= y
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_log_iff_exp_le (hy : 0 < y) : x ≤ log y ↔ exp x ≤ y := by rw [← exp_le_exp, exp_log hy]
/-
**Real.lt_log_iff_exp_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y := by rw [← exp_lt_exp, exp_log hy]

/-- One direction of `Real.log_le_iff_le_exp` without positivity assumption. -/
/-
**Real.le_exp_of_log_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_exp_of_log_le (h : log x <= y) : x <= exp y
参数：h : log x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.log_le_iff_le_exp`：log_le_iff_le_exp (hx : 0 < x) : log x <= y ↔ x 
<= exp y

--- 原说明 ---
One direction of `Real.log_le_iff_le_exp` without positivity assumption.
-/
lemma le_exp_of_log_le (h : log x ≤ y) : x ≤ exp y := by
  rcases le_or_gt x 0 with hx | hx
  · exact hx.trans <| exp_nonneg y
  · exact (log_le_iff_le_exp hx).mp h

/-- One direction of `Real.log_lt_iff_lt_exp` without positivity assumption. -/
/-
**Real.lt_exp_of_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_exp_of_log_lt (h : log x < y) : x < exp y
参数：h : log x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.log_lt_iff_lt_exp`：log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x <
 exp y

--- 原说明 ---
One direction of `Real.log_lt_iff_lt_exp` without positivity assumption.
-/
lemma lt_exp_of_log_lt (h : log x < y) : x < exp y := by
  rcases le_or_gt x 0 with hx | hx
  · exact hx.trans_lt <| exp_pos y
  · exact (log_lt_iff_lt_exp hx).mp h
/-
**Real.log_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Real.log_lt_log_iff`：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < 
log y ↔ x < y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem log_pos_iff (hx : 0 ≤ x) : 0 < log x ↔ 1 < x := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← log_one]
  exact log_lt_log_iff zero_lt_one hx

@[bound]
/-
**Real.log_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_pos (hx : 1 < x) : 0 < log x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_pos_iff`：log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem log_pos (hx : 1 < x) : 0 < log x :=
  (log_pos_iff (lt_trans zero_lt_one hx).le).2 hx
/-
**Real.log_pos_of_lt_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_pos_of_lt_neg_one (hx : x < -1) : 0 < log x
参数：hx : x < -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 37 条，此处仅展示前 30 条）
-/
theorem log_pos_of_lt_neg_one (hx : x < -1) : 0 < log x := by
  rw [← neg_neg x, log_neg_eq_log]
  have : 1 < -x := by linarith
  exact log_pos this
/-
**Real.log_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
参数：h : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Real.log_lt_log_iff`：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < 
log y ↔ x < y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 := by
  rw [← log_one]
  exact log_lt_log_iff h zero_lt_one

@[bound]
/-
**Real.log_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
参数：h0 : 0 < x；h1 : x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_neg_iff`：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
-/
theorem log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 :=
  (log_neg_iff h0).2 h1
/-
**Real.log_neg_of_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_neg_of_lt_zero (h0 : x < 0) (h1 : -1 < x) : log x < 0
参数：h0 : x < 0；h1 : -1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
（共 37 条，此处仅展示前 30 条）
-/
theorem log_neg_of_lt_zero (h0 : x < 0) (h1 : -1 < x) : log x < 0 := by
  rw [← neg_neg x, log_neg_eq_log]
  have h0' : 0 < -x := by linarith
  have h1' : -x < 1 := by linarith
  exact log_neg h0' h1'
/-
**Real.log_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_nonneg_iff (hx : 0 < x) : 0 <= log x ↔ 1 <= x
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.log_neg_iff`：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_nonneg_iff (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x := by rw [← not_lt, log_neg_iff hx, not_lt]

@[bound]
/-
**Real.log_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_nonneg (hx : 1 <= x) : 0 <= log x
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_nonneg_iff`：log_nonneg_iff (hx : 0 < x) : 0 <= log x ↔ 1 <= x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem log_nonneg (hx : 1 ≤ x) : 0 ≤ log x :=
  (log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx
/-
**Real.log_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_nonpos_iff (hx : 0 <= x) : log x <= 0 ↔ x <= 1
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.log_pos_iff`：log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem log_nonpos_iff (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← not_lt, log_pos_iff hx.le, not_lt]

@[bound]
/-
**Real.log_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_nonpos (hx : 0 <= x) (h'x : x <= 1) : log x <= 0
参数：hx : 0 <= x；h'x : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_nonpos_iff`：log_nonpos_iff (hx : 0 <= x) : log x <= 0 ↔ x <= 1
-/
theorem log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
  (log_nonpos_iff hx).2 h'x
/-
**Real.log_natCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_natCast_nonneg (n : Nat) : 0 <= log n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
-/
theorem log_natCast_nonneg (n : ℕ) : 0 ≤ log n := by
  if hn : n = 0 then
    simp [hn]
  else
    have : (1 : ℝ) ≤ n := mod_cast Nat.one_le_of_lt <| Nat.pos_of_ne_zero hn
    exact log_nonneg this
/-
**Real.log_neg_natCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_neg_natCast_nonneg (n : Nat) : 0 <= log (-n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.log_natCast_nonneg`：log_natCast_nonneg (n : Nat) : 0 <= log n
-/
theorem log_neg_natCast_nonneg (n : ℕ) : 0 ≤ log (-n) := by
  rw [← log_neg_eq_log, neg_neg]
  exact log_natCast_nonneg _
/-
**Real.log_intCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_intCast_nonneg (n : Int) : 0 <= log n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `lt_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   a < -b ↔ b < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
-/
theorem log_intCast_nonneg (n : ℤ) : 0 ≤ log n := by
  cases lt_trichotomy 0 n with
  | inl hn =>
      have : (1 : ℝ) ≤ n := mod_cast hn
      exact log_nonneg this
  | inr hn =>
      cases hn with
      | inl hn => simp [hn.symm]
      | inr hn =>
          have : (1 : ℝ) ≤ -n := by rw [← neg_zero, ← lt_neg] at hn; exact mod_cast hn
          rw [← log_neg_eq_log]
          exact log_nonneg this
/-
**Real.strictMonoOn_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
-/
theorem strictMonoOn_log : StrictMonoOn log (Set.Ioi 0) := fun _ hx _ _ hxy => log_lt_log hx hxy
/-
**Real.strictAntiOn_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictAntiOn_log : StrictAntiOn log (Set.Iio 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem strictAntiOn_log : StrictAntiOn log (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← log_abs y, ← log_abs x]
  refine log_lt_log (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
/-
**Real.log_injOn_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_injOn_pos : Set.InjOn log (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
-/
theorem log_injOn_pos : Set.InjOn log (Set.Ioi 0) :=
  strictMonoOn_log.injOn
/-
**Real.log_lt_sub_one_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_lt_sub_one_of_pos (hx1 : 0 < x) (hx2 : x != 1) : log x < x - 1
参数：hx1 : 0 < x；hx2 : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Set.InjOn.ne_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x ≠ f y ↔ x ≠ y)
· 使用定理 `Real.log_injOn_pos`：log_injOn_pos : Set.InjOn log (Set.Ioi 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 44 条，此处仅展示前 30 条）
-/
theorem log_lt_sub_one_of_pos (hx1 : 0 < x) (hx2 : x ≠ 1) : log x < x - 1 := by
  have h : log x ≠ 0 := by
    rwa [← log_one, log_injOn_pos.ne_iff hx1]
    exact mem_Ioi.mpr zero_lt_one
  linarith [add_one_lt_exp h, exp_log hx1]
/-
**Real.eq_one_of_pos_of_log_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：eq_one_of_pos_of_log_eq_zero {x : Real} (h₁ : 0 < x) (h₂ : log x = 0) : x 
= 1
参数：h₁ : 0 < x；h₂ : log x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_injOn_pos`：log_injOn_pos : Set.InjOn log (Set.Ioi 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
-/
theorem eq_one_of_pos_of_log_eq_zero {x : ℝ} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
  log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)
/-
**Real.log_ne_zero_of_pos_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_ne_zero_of_pos_of_ne_one {x : Real} (hx_pos : 0 < x) (hx : x != 1) : l
og x != 0
参数：hx_pos : 0 < x；hx : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Real.eq_one_of_pos_of_log_eq_zero`：eq_one_of_pos_of_log_eq_zero {x : Rea
l} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1
-/
theorem log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0 :=
  mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx

@[simp]
/-
**Real.log_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_eq_zero {x : Real} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Real.eq_one_of_pos_of_log_eq_zero`：eq_one_of_pos_of_log_eq_zero {x : Rea
l} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.log_one`：log_one : log 1 = 0
-/
theorem log_eq_zero {x : ℝ} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with (x_lt_zero | rfl | x_gt_zero)
    · refine Or.inr (Or.inr (neg_eq_iff_eq_neg.mp ?_))
      rw [← log_neg_eq_log x] at h
      exact eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h))
  · rintro (rfl | rfl | rfl) <;> simp only [log_one, log_zero, log_neg_eq_log]
/-
**Real.log_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_ne_zero {x : Real} : log x != 0 ↔ x != 0 ∧ x != 1 ∧ x != -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.log_eq_zero`：log_eq_zero {x : Real} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x
 = -1
-/
theorem log_ne_zero {x : ℝ} : log x ≠ 0 ↔ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 := by
  simpa only [not_or] using log_eq_zero.not

@[simp, push]
/-
**Real.log_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp
    · rw [pow_succ, log_mul (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]

@[simp, push]
/-
**Real.log_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_zpow (x : Real) (n : Int) : log (x ^ n) = n * log x
参数：x : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
-/
theorem log_zpow (x : ℝ) (n : ℤ) : log (x ^ n) = n * log x := by
  cases n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, log_pow, Int.cast_natCast]
  · rw [zpow_negSucc, log_inv, log_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]

@[push]
/-
**Real.log_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_sqrt {x : Real} (hx : 0 <= x) : log (√x) = log x / 2
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
-/
theorem log_sqrt {x : ℝ} (hx : 0 ≤ x) : log (√x) = log x / 2 := by
  rw [eq_div_iff, mul_comm, ← Nat.cast_two, ← log_pow, sq_sqrt hx]
  exact two_ne_zero
/-
**Real.log_le_sub_one_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_le_sub_one_of_pos {x : Real} (hx : 0 < x) : log x <= x - 1
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.add_one_le_exp`：add_one_le_exp (x : Real) : x + 1 <= Real.exp x
-/
theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 := by
  rw [le_sub_iff_add_le]
  convert! add_one_le_exp (log x)
  rw [exp_log hx]
/-
**Real.one_sub_inv_le_log_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：one_sub_inv_le_log_of_pos (hx : 0 < x) : 1 - x⁻¹ <= log x
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `Real.log_le_sub_one_of_pos`：log_le_sub_one_of_pos {x : Real} (hx : 0 < x
) : log x <= x - 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma one_sub_inv_le_log_of_pos (hx : 0 < x) : 1 - x⁻¹ ≤ log x := by
  simpa [add_comm] using log_le_sub_one_of_pos (inv_pos.2 hx)

/-- See `Real.log_le_sub_one_of_pos` for the stronger version when `x ≠ 0`. -/
/-
**Real.log_le_self** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_le_self (hx : 0 <= x) : log x <= x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.log_le_sub_one_of_pos`：log_le_sub_one_of_pos {x : Real} (hx : 0 < x
) : log x <= x - 1
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
See `Real.log_le_sub_one_of_pos` for the stronger version when `x ≠ 0`.
-/
lemma log_le_self (hx : 0 ≤ x) : log x ≤ x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (log_le_sub_one_of_pos hx).trans (by linarith)

/-- See `Real.one_sub_inv_le_log_of_pos` for the stronger version when `x ≠ 0`. -/
/-
**Real.neg_inv_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：neg_inv_le_log (hx : 0 <= x) : -x⁻¹ <= log x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用引理 `Real.log_le_self`：log_le_self (hx : 0 <= x) : log x <= x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
See `Real.one_sub_inv_le_log_of_pos` for the stronger version when `x ≠ 0`.
-/
lemma neg_inv_le_log (hx : 0 ≤ x) : -x⁻¹ ≤ log x := by
  rw [neg_le, ← log_inv]; exact log_le_self <| inv_nonneg.2 hx

/-- Bound for `|log x * x|` in the interval `(0, 1]`. -/
/-
**Real.abs_log_mul_self_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_log_mul_self_lt (x : Real) (h1 : 0 < x) (h2 : x <= 1) : |log x * x| < 
1
参数：x : Real；h1 : 0 < x；h2 : x <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_le_sub_one_of_pos`：log_le_sub_one_of_pos {x : Real} (hx : 0 < x
) : log x <= x - 1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
Bound for `|log x * x|` in the interval `(0, 1]`.
-/
theorem abs_log_mul_self_lt (x : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) : |log x * x| < 1 := by
  have : 0 < 1 / x := by simpa only [one_div, inv_pos] using h1
  replace := log_le_sub_one_of_pos this
  replace : log (1 / x) < 1 / x := by linarith
  rw [log_div one_ne_zero h1.ne', log_one, zero_sub, lt_div_iff₀ h1] at this
  have aux : 0 ≤ -log x * x := by
    refine mul_nonneg ?_ h1.le
    rw [← log_inv]
    apply log_nonneg
    rw [← le_inv_comm₀ h1 zero_lt_one, inv_one]
    exact h2
  rw [← abs_of_nonneg aux, neg_mul, abs_neg] at this
  exact this
/-
**Real.le_log_one_add_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_log_one_add_of_nonneg {x : Real} (hx : 0 <= x) : 2 * x / (x + 2) <= log
 (1 + x)
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.le_log_iff_exp_le`：le_log_iff_exp_le (hy : 0 < y) : x <= log y ↔ ex
p x <= y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 66 条，此处仅展示前 30 条）
-/
lemma le_log_one_add_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 2 * x / (x + 2) ≤ log (1 + x) := by
  rw [le_log_iff_exp_le (by grind)]
  convert exp_le_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind
/-
**Real.lt_log_one_add_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_log_one_add_of_pos {x : Real} (hx : 0 < x) : 2 * x / (x + 2) < log (1 +
 x)
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.lt_log_iff_exp_lt`：lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp
 x < y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 63 条，此处仅展示前 30 条）
-/
lemma lt_log_one_add_of_pos {x : ℝ} (hx : 0 < x) : 2 * x / (x + 2) < log (1 + x) := by
  rw [lt_log_iff_exp_lt (by grind)]
  convert exp_lt_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

/-- The real logarithm function tends to `+∞` at `+∞`. -/
/-
**Real.tendsto_log_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_log_atTop : Tendsto log atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.tendsto_comp_exp_atTop`：tendsto_comp_exp_atTop {f : Real -> α} : Te
ndsto (fun x => f (exp x)) atTop l ↔ Tendsto f atTop l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
The real logarithm function tends to `+∞` at `+∞`.
-/
theorem tendsto_log_atTop : Tendsto log atTop atTop :=
  tendsto_comp_exp_atTop.1 <| by simpa only [log_exp] using! tendsto_id
/-
**Real.tendsto_log_nhdsGT_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>] 0) atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>] 0) atBot := by
  simpa [← tendsto_comp_exp_atBot] using! tendsto_id
/-
**Real.tendsto_log_nhdsNE_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!=] 0) atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Real.tendsto_log_nhdsGT_zero`：tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>
] 0) atBot
· 使用定理 `tendsto_abs_nhdsNE_zero`：∀ {G : Type u_1} [inst : TopologicalSpace G] [i
nst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [Order
Topology G], …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem tendsto_log_nhdsNE_zero : Tendsto log (𝓝[≠] 0) atBot := by
  simpa [comp_def] using tendsto_log_nhdsGT_zero.comp tendsto_abs_nhdsNE_zero
/-
**Real.tendsto_log_nhdsLT_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_log_nhdsLT_zero : Tendsto log (𝓝[<] 0) atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
lemma tendsto_log_nhdsLT_zero : Tendsto log (𝓝[<] 0) atBot :=
  tendsto_log_nhdsNE_zero.mono_left <| nhdsWithin_mono _ fun _ h ↦ ne_of_lt h
/-
**Real.continuousOn_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousOn_log : ContinuousOn log {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_of_ne_zero`：log_of_ne_zero (hx : x != 0) : log x = expOrderIso.
symm ⟨|x|, abs_pos.2 hx⟩
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `OrderIso.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpac
e β] [Ord…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuousOn_log : ContinuousOn log {0}ᶜ := by
  simp +unfoldPartialApp only [continuousOn_iff_continuous_domRestrict,
    domRestrict]
  conv in log _ => rw [log_of_ne_zero (show (x : ℝ) ≠ 0 from x.2)]
  exact expOrderIso.symm.continuous.comp (continuous_subtype_val.norm.subtype_mk _)

/-- The real logarithm is continuous as a function from nonzero reals. -/
@[fun_prop]
/-
**Real.continuous_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_log : Continuous fun x : { x : Real // x != 0 } => log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ

--- 原说明 ---
The real logarithm is continuous as a function from nonzero reals.
-/
theorem continuous_log : Continuous fun x : { x : ℝ // x ≠ 0 } => log x :=
  continuousOn_iff_continuous_domRestrict.1 <| continuousOn_log.mono fun _ => id

/-- The real logarithm is continuous as a function from positive reals. -/
@[fun_prop]
/-
**Real.continuous_log'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_log' : Continuous fun x : { x : Real // 0 < x } => log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
The real logarithm is continuous as a function from positive reals.
-/
theorem continuous_log' : Continuous fun x : { x : ℝ // 0 < x } => log x :=
  continuousOn_iff_continuous_domRestrict.1 <| continuousOn_log.mono fun _ hx => ne_of_gt hx
/-
**Real.continuousAt_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_log (hx : x != 0) : ContinuousAt log x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem continuousAt_log (hx : x ≠ 0) : ContinuousAt log x :=
  (continuousOn_log x hx).continuousAt <| isOpen_compl_singleton.mem_nhds hx

@[simp]
/-
**Real.continuousAt_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_log_iff : ContinuousAt log x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_tendsto_nhds_of_tendsto_atBot`：not_tendsto_nhds_of_tendsto_atBot (hf
 : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a)
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.continuousAt_log`：continuousAt_log (hx : x != 0) : ContinuousAt log
 x
-/
theorem continuousAt_log_iff : ContinuousAt log x ↔ x ≠ 0 := by
  refine ⟨?_, continuousAt_log⟩
  rintro h rfl
  exact not_tendsto_nhds_of_tendsto_atBot tendsto_log_nhdsNE_zero _ <|
    h.tendsto.mono_left nhdsWithin_le_nhds

open List in
/-
**Real.log_list_prod** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_list_prod {l : List Real} (h : forall x in l, x != 0) : log l.prod = (
l.map (fun x => log x)).sum
参数：h : forall x in l, x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma log_list_prod {l : List ℝ} (h : ∀ x ∈ l, x ≠ 0) :
    log l.prod = (l.map (fun x ↦ log x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp_all only [ne_eq, mem_cons, or_true, not_false_eq_true, forall_const, forall_eq_or_imp,
      prod_cons, map_cons, sum_cons]
    have : l.prod ≠ 0 := by grind [prod_ne_zero]
    rw [log_mul h.1 this, add_right_inj, ih]

open Multiset in
/-
**Real.log_multiset_prod** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_multiset_prod {s : Multiset Real} (h : forall x in s, x != 0) : log s.
prod = (s.map (fun x => log x)).sum
参数：h : forall x in s, x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_toList`：prod_toList (s : Multiset M) : s.toList.prod = s.p
rod
· 使用引理 `Real.log_list_prod`：log_list_prod {l : List Real} (h : forall x in l, x 
!= 0) : log l.prod = (l.map (fun x => log x)).sum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.sum_map_toList`：∀ {ι : Type u_2} {M : Type u_3} [inst : AddComm
Monoid M] (s : Multiset ι) (f : ι → M),   (List.map f s.toList).sum = (Multiset.
map f s).sum
-/
lemma log_multiset_prod {s : Multiset ℝ} (h : ∀ x ∈ s, x ≠ 0) :
    log s.prod = (s.map (fun x ↦ log x)).sum := by
  rw [← prod_toList, log_list_prod (by simp_all), sum_map_toList]

open Finset in
@[push]
/-
**Real.log_prod** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf : forall x in s, f
 x != 0) : log (∏ i in s, f i) = ∑ i in s, log (f i)
参数：hf : forall x in s, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_map_toList`：prod_map_toList (s : Finset ι) (f : ι -> M) : (s
.toList.map f).prod = s.prod f
· 使用引理 `Real.log_list_prod`：log_list_prod {l : List Real} (h : forall x in l, x 
!= 0) : log l.prod = (l.map (fun x => log x)).sum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Finset.sum_map_toList`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] (s : Finset ι) (f : ι → M), (List.map f s.toList).sum = s.sum f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_prod {α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ x ∈ s, f x ≠ 0) :
    log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i) := by
  rw [← prod_map_toList, log_list_prod (by simp_all)]
  simp

@[push]
/-
**Real._root_.Finsupp.log_prod** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Finsupp.log_prod {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → ℝ)
    (hg : ∀ a, g a (f a) = 0 → f a = 0) : log (f.prod g) = f.sum fun a b ↦ log (g a b) :=
  log_prod fun _x hx h₀ ↦ Finsupp.mem_support_iff.1 hx <| hg _ h₀

-- Note: This is wrong assuming only `f a ≠ 0` (as in `Real.log_prod`).
-- E.g., `f = (2, -1, -1, ...)` (with infinitely many `-1`s).
/-
**Real.log_finprod** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_finprod {α : Type*} {f : α -> Real} (h : forall a, 0 < f a) : log (∏ᶠ 
a, f a) = ∑ᶠ a, log (f a)
参数：h : forall a, 0 < f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `finsum_def`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] (f 
: α → M) [inst_1 : Decidable (Function.HasFiniteSupport f)],   ∑ᶠ (i : α), f i =
…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Real.log_prod`：log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf :
 forall x in s, f x != 0) : log (∏ i in s, f i) = ∑ i in s, log (f i)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma log_finprod {α : Type*} {f : α → ℝ} (h : ∀ a, 0 < f a) :
    log (∏ᶠ a, f a) = ∑ᶠ a, log (f a) := by
  classical
  have H : (fun i ↦ log (f i)).support = f.mulSupport := by
    grind [mem_mulSupport, mem_support, log_eq_zero]
  have H' : HasFiniteMulSupport f ↔ HasFiniteSupport fun a ↦ log (f a) := by
    simp [HasFiniteMulSupport, HasFiniteSupport, H]
  simp only [finprod_def, finsum_def]
  by_cases h' : HasFiniteMulSupport f
  · simp [h', log_prod (fun a _ ↦ (h a).ne'), H'.mp h', H]
  · simp [h', mt H'.mpr h']
/-
**Real.log_nat_eq_sum_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_nat_eq_sum_factorization (n : Nat) : log n = n.factorization.sum fun p
 t => t * log p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.log_prod`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero β] (f : α
 →₀ β) (g : α → β → ℝ),   (∀ (a : α), g a (f a) = 0 → f a = 0) → Real.log (f.pro
d g) =…
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Nat.factorization_zero_right`：factorization_zero_right (n : Nat) : n.fac
torization 0 = 0
· 使用定理 `Nat.cast_finsuppProd`：cast_finsuppProd [CommSemiring R] (g : α -> M -> N
at) : (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b)
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
-/
theorem log_nat_eq_sum_factorization (n : ℕ) :
    log n = n.factorization.sum fun p t => t * log p := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp -- relies on junk values of `log` and `Nat.factorization`
  · simp only [← log_pow, ← Nat.cast_pow]
    rw [← Finsupp.log_prod, ← Nat.cast_finsuppProd, Nat.prod_factorization_pow_eq_self hn]
    intro p hp
    rw [eq_zero_of_pow_eq_zero (Nat.cast_eq_zero.1 hp), Nat.factorization_zero_right]
/-
**Real.tendsto_pow_log_div_mul_add_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_pow_log_div_mul_add_atTop (a b : Real) (n : Nat) (ha : a != 0) : T
endsto (fun x => log x ^ n / (a * x + b)) atTop (𝓝 0)
参数：a b : Real；n : Nat；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_div_pow_mul_exp_add_atTop`：tendsto_div_pow_mul_exp_add_atTo
p (b c : Real) (n : Nat) (hb : 0 != b) : Tendsto (fun x => x ^ n / (b * exp x + 
c)) atTop (𝓝 0)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem tendsto_pow_log_div_mul_add_atTop (a b : ℝ) (n : ℕ) (ha : a ≠ 0) :
    Tendsto (fun x => log x ^ n / (a * x + b)) atTop (𝓝 0) :=
  ((tendsto_div_pow_mul_exp_add_atTop a b n ha.symm).comp tendsto_log_atTop).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using by simp [exp_log hx]
/-
**Real.isLittleO_pow_log_id_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_pow_log_id_atTop {n : Nat} : (fun x => log x ^ n) =o[atTop] id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff_tendsto'`：isLittleO_iff_tendsto' {f g : α -> 𝕜
} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x
 / g x) l (𝓝 0)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.tendsto_pow_log_div_mul_add_atTop`：tendsto_pow_log_div_mul_add_atTo
p (a b : Real) (n : Nat) (ha : a != 0) : Tendsto (fun x => log x ^ n / (a * x + 
b)) atTop (𝓝 0)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem isLittleO_pow_log_id_atTop {n : ℕ} : (fun x => log x ^ n) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x h₁ h₂ using (h₁ h₂).elim
/-
**Real.isLittleO_log_id_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_log_id_atTop : log =o[atTop] id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Real.isLittleO_pow_log_id_atTop`：isLittleO_pow_log_id_atTop {n : Nat} : 
(fun x => log x ^ n) =o[atTop] id
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem isLittleO_log_id_atTop : log =o[atTop] id :=
  isLittleO_pow_log_id_atTop.congr_left fun _ => pow_one _
/-
**Real.isLittleO_const_log_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_const_log_atTop {c : Real} : (fun _ => c) =o[atTop] log
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto'`：∀ {α : Type u_1} {𝕜 : Type u_15} [ins
t : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ᶠ (x : α) in l, g x 
= 0 → f x = 0) → Filter…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem isLittleO_const_log_atTop {c : ℝ} : (fun _ => c) =o[atTop] log := by
  refine Asymptotics.isLittleO_of_tendsto' ?_
    <| Tendsto.div_atTop (a := c) (by simp) tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1] with x hx
  aesop (add safe forward log_pos)

/-- `Real.exp` as an `OpenPartialHomeomorph` with `source = univ` and `target = {z | 0 < z}`. -/
/-
**Real.expPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：OpenPartialHomeomorph ℝ ℝ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x

--- 原说明 ---
`Real.exp` as an `OpenPartialHomeomorph` with `source = univ` and `target = {z |
 0 < z}`.
-/
@[simps] noncomputable def expPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := Real.exp
  invFun := Real.log
  source := univ
  target := Ioi (0 : ℝ)
  map_source' x _ := exp_pos x
  map_target' _ _ := mem_univ _
  left_inv' _ _ := by simp
  right_inv' _ hx := exp_log hx
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  continuousOn_toFun := continuousOn_exp
  continuousOn_invFun x hx := (continuousAt_log (ne_of_gt hx)).continuousWithinAt

@[simp]
/-
**Real.image_log_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ioi {a : Real} (ha : 0 < a) : log '' Ioi a = Ioi (log a)
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ioi_of_strictMonoOn`：ContinuousOn.image_Ioi_of_strict
MonoOn (hf : ContinuousOn f (Ici a)) (hmono : StrictMonoOn f (Ici a)) (htop : Te
ndsto f atTop atTop) : f '' …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem image_log_Ioi {a : ℝ} (ha : 0 < a) : log '' Ioi a = Ioi (log a) :=
  (continuousOn_log.mono fun _ hx ↦ (ha.trans_le hx).ne').image_Ioi_of_strictMonoOn
    (strictMonoOn_log.mono fun _ hx ↦ ha.trans_le hx) tendsto_log_atTop

@[simp]
/-
**Real.image_log_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ici {a : Real} (ha : 0 < a) : log '' Ici a = Ici (log a)
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ici_of_monotoneOn`：ContinuousOn.image_Ici_of_monotone
On (hf : ContinuousOn f (Ici a)) (hmono : MonotoneOn f (Ici a)) (htop : Tendsto 
f atTop atTop) : f '' Ici …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem image_log_Ici {a : ℝ} (ha : 0 < a) : log '' Ici a = Ici (log a) :=
  (continuousOn_log.mono fun _ hx ↦ (ha.trans_le hx).ne').image_Ici_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx ↦ ha.trans_le hx) tendsto_log_atTop

@[simp]
/-
**Real.image_log_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Icc {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Icc a b = 
Icc (log a) (log b)
参数：ha : 0 < a；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Icc_of_monotoneOn`：ContinuousOn.image_Icc_of_monotone
On (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : MonotoneOn f (Icc a b
)) : f '' Icc a b = Icc (f…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
-/
theorem image_log_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log '' Icc a b = Icc (log a) (log b) :=
  (continuousOn_log.mono fun _ hx ↦ (ha.trans_le hx.1).ne').image_Icc_of_monotoneOn hab
    (strictMonoOn_log.monotoneOn.mono fun _ hx ↦ ha.trans_le hx.1)

@[simp]
/-
**Real.image_log_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ico {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Ico a b = 
Ico (log a) (log b)
参数：ha : 0 < a；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ico_of_strictMonoOn`：ContinuousOn.image_Ico_of_strict
MonoOn (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (I
cc a b)) : f '' Ico a b = Ic…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
-/
theorem image_log_Ico {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log '' Ico a b = Ico (log a) (log b) :=
  (continuousOn_log.mono fun _ hx ↦ (ha.trans_le hx.1).ne').image_Ico_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx ↦ ha.trans_le hx.1)

@[simp]
/-
**Real.image_log_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ioc {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Ioc a b = 
Ioc (log a) (log b)
参数：ha : 0 < a；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ioc_of_strictMonoOn`：ContinuousOn.image_Ioc_of_strict
MonoOn (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (I
cc a b)) : f '' Ioc a b = Io…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
-/
theorem image_log_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log '' Ioc a b = Ioc (log a) (log b) :=
  (continuousOn_log.mono fun _ hx ↦ (ha.trans_le hx.1).ne').image_Ioc_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx ↦ ha.trans_le hx.1)

@[simp]
/-
**Real.image_log_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ioo {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Ioo a b = 
Ioo (log a) (log b)
参数：ha : 0 < a；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ioo_of_strictMonoOn`：ContinuousOn.image_Ioo_of_strict
MonoOn (hab : a <= b) (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (I
cc a b)) : f '' Ioo a b = Io…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
-/
theorem image_log_Ioo {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : log '' Ioo a b = Ioo (log a) (log b) :=
  (continuousOn_log.mono fun _ hx ↦ (ha.trans_le hx.1).ne').image_Ioo_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx ↦ ha.trans_le hx.1)

@[simp]
/-
**Real.image_log_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_uIcc {a b : Real} (ha : 0 < a) (hb : 0 < b) : log '' uIcc a b = 
uIcc (log a) (log b)
参数：ha : 0 < a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_uIcc_of_monotoneOn`：ContinuousOn.image_uIcc_of_monoto
neOn (hf : ContinuousOn f [[a, b]]) (hmono : MonotoneOn f [[a, b]]) : f '' [[a, 
b]] = [[f a, f b]]
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
-/
theorem image_log_uIcc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    log '' uIcc a b = uIcc (log a) (log b) :=
  (continuousOn_log.mono fun _ hx ↦ ((lt_min ha hb).trans_le hx.1).ne').image_uIcc_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx ↦ (lt_min ha hb).trans_le hx.1)

@[simp]
/-
**Real.image_log_Ioo_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ioo_zero {a : Real} (ha : 0 < a) : log '' Ioo 0 a = Iio (log a)
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.image_exp_Iio`：image_exp_Iio (a : Real) : exp '' Iio a = Ioo 0 (exp
 a)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Real.log_comp_exp`：Real.log ∘ Real.exp = id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem image_log_Ioo_zero {a : ℝ} (ha : 0 < a) : log '' Ioo 0 a = Iio (log a) := by
  nth_rw 1 [← exp_log ha, ← image_exp_Iio, ← image_comp, log_comp_exp, image_id]

@[simp]
/-
**Real.image_log_Ioc_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_log_Ioc_zero {a : Real} (ha : 0 < a) : log '' Ioc 0 a = Iic (log a)
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.image_exp_Iic`：image_exp_Iic (a : Real) : exp '' Iic a = Ioc 0 (exp
 a)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Real.log_comp_exp`：Real.log ∘ Real.exp = id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem image_log_Ioc_zero {a : ℝ} (ha : 0 < a) : log '' Ioc 0 a = Iic (log a) := by
  nth_rw 1 [← exp_log ha, ← image_exp_Iic, ← image_comp, log_comp_exp, image_id]

end Real

namespace Nat.Prime

/-
**Nat.Prime.log_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：log_pos {p : Nat} (hp : p.Prime) : 0 < Real.log p
参数：hp : p.Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem log_pos {p : ℕ} (hp : p.Prime) : 0 < Real.log p :=
  Real.log_pos <| mod_cast hp.one_lt
/-
**Nat.Prime.log_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：log_ne_zero {p : Nat} (hp : p.Prime) : Real.log p != 0
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.log_pos`：log_pos {p : Nat} (hp : p.Prime) : 0 < Real.log p
-/
theorem log_ne_zero {p : ℕ} (hp : p.Prime) : Real.log p ≠ 0 := hp.log_pos.ne'

end Nat.Prime

section Continuity

open Real

variable {α : Type*}

/-
**Filter.Tendsto.log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.log {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto 
f l (𝓝 x)) (hx : x != 0) : Tendsto (fun x => log (f x)) l (𝓝 (log x))
参数：h : Tendsto f l (𝓝 x)；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuousAt_log`：continuousAt_log (hx : x != 0) : ContinuousAt log
 x
-/
theorem Filter.Tendsto.log {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun x => log (f x)) l (𝓝 (log x)) :=
  (continuousAt_log hx).tendsto.comp h

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}

@[fun_prop]
/-
**Continuous.log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.log (hf : Continuous f) (h₀ : forall x, f x != 0) : Continuous 
fun x => log (f x)
参数：hf : Continuous f；h₀ : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
-/
theorem Continuous.log (hf : Continuous f) (h₀ : ∀ x, f x ≠ 0) : Continuous fun x => log (f x) :=
  continuousOn_log.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.log (hf : ContinuousAt f a) (h₀ : f a ≠ 0) :
    ContinuousAt (fun x => log (f x)) a :=
  hf.log h₀

nonrec theorem ContinuousWithinAt.log (hf : ContinuousWithinAt f s a) (h₀ : f a ≠ 0) :
    ContinuousWithinAt (fun x => log (f x)) s a :=
  hf.log h₀

@[fun_prop]
/-
**ContinuousOn.log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall x in s, f x != 0) : 
ContinuousOn (fun x => log (f x)) s
参数：hf : ContinuousOn f s；h₀ : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.log`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f 
: α → ℝ} {s : Set α} {a : α},   ContinuousWithinAt f s a → f a ≠ 0 → ContinuousW
ithinAt (fun…
-/
theorem ContinuousOn.log (hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => log (f x)) s := fun x hx => (hf x hx).log (h₀ x hx)

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

/-
**Real.tendsto_log_comp_add_sub_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_log_comp_add_sub_log (y : Real) : Tendsto (fun x : Real => log (x 
+ y) - log x) atTop (𝓝 0)
参数：y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.comap_exp_nhds_exp`：comap_exp_nhds_exp (x : Real) : comap exp (𝓝 (e
xp x)) = 𝓝 x
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 58 条，此处仅展示前 30 条）
-/
theorem tendsto_log_comp_add_sub_log (y : ℝ) :
    Tendsto (fun x : ℝ => log (x + y) - log x) atTop (𝓝 0) := by
  have : Tendsto (fun x ↦ 1 + y / x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [← comap_exp_nhds_exp, exp_zero, tendsto_comap_iff, ← add_zero (1 : ℝ)]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-y)] with x hx₀ hxy
  rw [comp_apply, exp_sub, exp_log, exp_log, one_add_div] <;> linarith
/-
**Real.tendsto_log_nat_add_one_sub_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_log_nat_add_one_sub_log : Tendsto (fun k : Nat => log (k + 1) - lo
g k) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_log_comp_add_sub_log`：tendsto_log_comp_add_sub_log (y : Rea
l) : Tendsto (fun x : Real => log (x + y) - log x) atTop (𝓝 0)
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
theorem tendsto_log_nat_add_one_sub_log : Tendsto (fun k : ℕ => log (k + 1) - log k) atTop (𝓝 0) :=
  (tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop

end Real

end TendstoCompAddSub

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

variable {e : ℝ} {d : ℕ}

/-
**Mathlib.Meta.Positivity.log_nonneg_of_isNat** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib
.Meta.Positivity`。
形式化陈述：log_nonneg_of_isNat {n : Nat} (h : NormNum.IsNat e n) : 0 <= Real.log (e :
 Real)
参数：h : NormNum.IsNat e n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Real.log_natCast_nonneg`：log_natCast_nonneg (n : Nat) : 0 <= log n
-/
lemma log_nonneg_of_isNat {n : ℕ} (h : NormNum.IsNat e n) : 0 ≤ Real.log (e : ℝ) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Real.log_natCast_nonneg _
/-
**Mathlib.Meta.Positivity.log_pos_of_isNat** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Me
ta.Positivity`。
形式化陈述：log_pos_of_isNat {n : Nat} (h : NormNum.IsNat e n) (w : Nat.blt 1 n = true
) : 0 < Real.log (e : Real)
参数：h : NormNum.IsNat e n；w : Nat.blt 1 n = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
-/
lemma log_pos_of_isNat {n : ℕ} (h : NormNum.IsNat e n) (w : Nat.blt 1 n = true) :
    0 < Real.log (e : ℝ) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Real.log_pos
  simpa using w
/-
**Mathlib.Meta.Positivity.log_nonneg_of_isNegNat** 是 Mathlib 中的一个引理，位于命名空间 `Math
lib.Meta.Positivity`。
形式化陈述：log_nonneg_of_isNegNat {n : Nat} (h : NormNum.IsInt e (.negOfNat n)) : 0 <
= Real.log (e : Real)
参数：h : NormNum.IsInt e (.negOfNat n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.neg_to_eq`：∀ {α : Type u_1} [inst : Ring α] {
n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n) → ↑n = a' → a =
 -a'
· 使用定理 `Real.log_neg_natCast_nonneg`：log_neg_natCast_nonneg (n : Nat) : 0 <= log
 (-n)
-/
lemma log_nonneg_of_isNegNat {n : ℕ} (h : NormNum.IsInt e (.negOfNat n)) :
    0 ≤ Real.log (e : ℝ) := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  exact Real.log_neg_natCast_nonneg _
/-
**Mathlib.Meta.Positivity.log_pos_of_isNegNat** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib
.Meta.Positivity`。
形式化陈述：log_pos_of_isNegNat {n : Nat} (h : NormNum.IsInt e (.negOfNat n)) (w : Nat
.blt 1 n = true) : 0 < Real.log (e : Real)
参数：h : NormNum.IsInt e (.negOfNat n)；w : Nat.blt 1 n = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.neg_to_eq`：∀ {α : Type u_1} [inst : Ring α] {
n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n) → ↑n = a' → a =
 -a'
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
-/
lemma log_pos_of_isNegNat {n : ℕ} (h : NormNum.IsInt e (.negOfNat n)) (w : Nat.blt 1 n = true) :
    0 < Real.log (e : ℝ) := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  rw [Real.log_neg_eq_log]
  apply Real.log_pos
  simpa using w
/-
**Mathlib.Meta.Positivity.log_pos_of_isNNRat** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.
Meta.Positivity`。
形式化陈述：log_pos_of_isNNRat {n : Nat} : (NormNum.IsNNRat e n d) -> (decide ((1 : Ra
t) < n / d)) -> (0 < Real.log (e : Real)) | ⟨inv, eq⟩, h => by rw [eq]; rw [invO
f_eq_inv]; rw [← div_eq_mul_inv] have : 1 < (n : Real) / d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
lemma log_pos_of_isNNRat {n : ℕ} :
    (NormNum.IsNNRat e n d) → (decide ((1 : ℚ) < n / d)) → (0 < Real.log (e : ℝ))
  | ⟨inv, eq⟩, h => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have : 1 < (n : ℝ) / d := by
      simpa using (Rat.cast_lt (K := ℝ)).2 (of_decide_eq_true h)
    exact Real.log_pos this
/-
**Mathlib.Meta.Positivity.log_pos_of_isRat_neg** 是 Mathlib 中的一个引理，位于命名空间 `Mathli
b.Meta.Positivity`。
形式化陈述：log_pos_of_isRat_neg {n : Int} : (NormNum.IsRat e n d) -> (decide (n / d <
 (-1 : Rat))) -> (0 < Real.log (e : Real)) | ⟨inv, eq⟩, h => by rw [eq]; rw [inv
Of_eq_inv]; rw [← div_eq_mul_inv] have : (n : Real) / d < -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Real.log_pos_of_lt_neg_one`：log_pos_of_lt_neg_one (hx : x < -1) : 0 < lo
g x
-/
lemma log_pos_of_isRat_neg {n : ℤ} :
    (NormNum.IsRat e n d) → (decide (n / d < (-1 : ℚ))) → (0 < Real.log (e : ℝ))
  | ⟨inv, eq⟩, h => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have : (n : ℝ) / d < -1 := by exact_mod_cast of_decide_eq_true h
    exact Real.log_pos_of_lt_neg_one this
/-
**Mathlib.Meta.Positivity.log_nz_of_isNNRat** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.M
eta.Positivity`。
形式化陈述：log_nz_of_isNNRat {n : Nat} : (NormNum.IsNNRat e n d) -> (decide ((0 : Rat
) < n / d)) -> (decide (n / d < (1 : Rat))) -> (Real.log (e : Real) != 0) | ⟨inv
, eq⟩, h₁, h₂ => by rw [eq]; rw [invOf_eq_inv]; rw [← div_eq_mul_inv] have h₁' :
 0 < (n : Real) / d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_pos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linear
Order K] [IsStrictOrderedRing K], 0 < ↑q ↔ 0 < q
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
-/
lemma log_nz_of_isNNRat {n : ℕ} : (NormNum.IsNNRat e n d) → (decide ((0 : ℚ) < n / d))
    → (decide (n / d < (1 : ℚ))) → (Real.log (e : ℝ) ≠ 0)
  | ⟨inv, eq⟩, h₁, h₂ => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have h₁' : 0 < (n : ℝ) / d := by
      simpa using (Rat.cast_pos (K := ℝ)).2 (of_decide_eq_true h₁)
    have h₂' : (n : ℝ) / d < 1 := by
      simpa using (Rat.cast_lt (K := ℝ)).2 (of_decide_eq_true h₂)
    exact ne_of_lt <| Real.log_neg h₁' h₂'
/-
**Mathlib.Meta.Positivity.log_nz_of_isRat_neg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib
.Meta.Positivity`。
形式化陈述：log_nz_of_isRat_neg {n : Int} : (NormNum.IsRat e n d) -> (decide (n / d < 
(0 : Rat))) -> (decide ((-1 : Rat) < n / d)) -> (Real.log (e : Real) != 0) | ⟨in
v, eq⟩, h₁, h₂ => by rw [eq]; rw [invOf_eq_inv]; rw [← div_eq_mul_inv] have h₁' 
: (n : Real) / d < 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Real.log_neg_of_lt_zero`：log_neg_of_lt_zero (h0 : x < 0) (h1 : -1 < x) :
 log x < 0
-/
lemma log_nz_of_isRat_neg {n : ℤ} : (NormNum.IsRat e n d) → (decide (n / d < (0 : ℚ)))
    → (decide ((-1 : ℚ) < n / d)) → (Real.log (e : ℝ) ≠ 0)
  | ⟨inv, eq⟩, h₁, h₂ => by
    rw [eq, invOf_eq_inv, ← div_eq_mul_inv]
    have h₁' : (n : ℝ) / d < 0 := by exact_mod_cast of_decide_eq_true h₁
    have h₂' : -1 < (n : ℝ) / d := by exact_mod_cast of_decide_eq_true h₂
    exact ne_of_lt <| Real.log_neg_of_lt_zero h₁' h₂'

/-- Extension for the `positivity` tactic: `Real.log` of a natural number is always nonnegative. -/
@[positivity Real.log (Nat.cast _)]
meta def evalLogNatCast : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log (Nat.cast $a)) =>
    assertInstancesCommute
    pure (.nonnegative q(Real.log_natCast_nonneg $a))
  | _, _, _ => throwError "not Real.log"

/-- Extension for the `positivity` tactic: `Real.log` of an integer is always nonnegative. -/
@[positivity Real.log (Int.cast _)]
meta def evalLogIntCast : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log (Int.cast $a)) =>
    assertInstancesCommute
    pure (.nonnegative q(Real.log_intCast_nonneg $a))
  | _, _, _ => throwError "not Real.log"

/-- Extension for the `positivity` tactic: `Real.log` of a numeric literal. -/
@[positivity Real.log _]
meta def evalLogNatLit : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log $a) =>
    match ← NormNum.derive a with
    | .isNat (_ : Q(AddMonoidWithOne ℝ)) lit p =>
      assumeInstancesCommute
      have p : Q(NormNum.IsNat $a $lit) := p
      if 1 < lit.natLit! then
        let p' : Q(Nat.blt 1 $lit = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNat $p $p'))
      else
        pure (.nonnegative q(log_nonneg_of_isNat $p))
    | .isNegNat _ lit p =>
      assumeInstancesCommute
      have p : Q(NormNum.IsInt $a (Int.negOfNat $lit)) := p
      if 1 < lit.natLit! then
        let p' : Q(Nat.blt 1 $lit = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNegNat $p $p'))
      else
        pure (.nonnegative q(log_nonneg_of_isNegNat $p))
    | .isNNRat _ q n d p =>
      assumeInstancesCommute
      if q < 1 then
        let w₁ : Q(decide ((0 : ℚ) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        let w₂ : Q(decide ($n / $d < (1 : ℚ)) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.nonzero q(log_nz_of_isNNRat $p $w₁ $w₂))
      else if 1 < q then
        let w : Q(decide ((1 : ℚ) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNNRat $p $w))
      else
        failure
    | .isNegNNRat _ q n d p =>
      assumeInstancesCommute
      if -1 < q then
        let w₁ : Q(decide ((Int.negOfNat $n) / $d < (0 : ℚ)) = true) :=
          (q(Eq.refl true) : Lean.Expr)
        let w₂ : Q(decide ((-1 : ℚ) < (Int.negOfNat $n) / $d) = true) :=
          (q(Eq.refl true) : Lean.Expr)
        pure (.nonzero q(log_nz_of_isRat_neg $p $w₁ $w₂))
      else if q < -1 then
        let w : Q(decide ((Int.negOfNat $n) / $d < (-1 : ℚ)) = true) :=
          (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isRat_neg $p $w))
      else
        failure
    | _ => failure
  | _, _, _ => throwError "not Real.log"

end Mathlib.Meta.Positivity

