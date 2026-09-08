/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.EReal.Basic

/-!
# Extended Nonnegative Real Exponential

We define `exp` as an extension of the exponential of a real
to the extended reals `EReal`. The function takes values
in the extended nonnegative reals `ℝ≥0∞`, with `exp ⊥ = 0` and `exp ⊤ = ⊤`.

## Main Definitions
- `EReal.exp`: The extension of the real exponential to `EReal`.

## Main Results
- `EReal.exp_strictMono`: `exp` is increasing;
- `EReal.exp_neg`, `EReal.exp_add`: `exp` satisfies
  the identities `exp (-x) = (exp x)⁻¹` and `exp (x + y) = exp x * exp y`.

## Tags
ENNReal, EReal, exponential
-/

@[expose] public section
namespace EReal

open scoped ENNReal

/-! ### Definition -/
section Definition

/-- Exponential as a function from `EReal` to `ℝ≥0∞`. -/
noncomputable
/-
**EReal.exp** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：exp (x : EReal) : Real>=0∞
参数：x : EReal。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def exp (x : EReal) : ℝ≥0∞ := EReal.rec 0 (fun x => ENNReal.ofReal (Real.exp x)) ∞ x
/-
**EReal.exp_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊥.exp = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_bot : exp ⊥ = 0 := rfl
/-
**EReal.exp_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：EReal.exp 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma exp_zero : exp 0 = 1 := by simp [exp, ← coe_zero]
/-
**EReal.exp_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊤.exp = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_top : exp ⊤ = ∞ := rfl
/-
**EReal.exp_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : ℝ), (↑x).exp = ENNReal.ofReal (Real.exp x)
参数：x : ℝ；↑x；Real.exp x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_coe (x : ℝ) : exp x = ENNReal.ofReal (Real.exp x) := rfl
/-
**EReal.exp_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : EReal}, x.exp = 0 ↔ x = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
-/
@[simp] lemma exp_eq_zero_iff {x : EReal} : exp x = 0 ↔ x = ⊥ := by
  induction x <;> simp [Real.exp_pos]
/-
**EReal.exp_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : EReal}, x.exp = ⊤ ↔ x = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma exp_eq_top_iff {x : EReal} : exp x = ∞ ↔ x = ⊤ := by
  induction x <;> simp

end Definition

/-! ### Monotonicity -/
section Monotonicity

@[gcongr]
/-
**EReal.exp_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exp_strictMono : StrictMono exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.exp_bot`：⊥.exp = 0
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `EReal.exp_eq_zero_iff`：∀ {x : EReal}, x.exp = 0 ↔ x = ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.ofReal_lt_ofReal_iff'`：ofReal_lt_ofReal_iff' {p q : Real} : ENNR
eal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
-/
lemma exp_strictMono : StrictMono exp := by
  intro x y h
  induction x
  · rw [exp_bot, pos_iff_ne_zero, ne_eq, exp_eq_zero_iff]
    exact h.ne'
  · induction y
    · simp at h
    · simp_rw [exp_coe]
      exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨Real.exp_strictMono (mod_cast h), Real.exp_pos _⟩
    · simp
  · exact (not_top_lt h).elim

@[gcongr]
/-
**EReal.exp_monotone** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exp_monotone : Monotone exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `EReal.exp_strictMono`：exp_strictMono : StrictMono exp
-/
lemma exp_monotone : Monotone exp := exp_strictMono.monotone
/-
**EReal.exp_lt_exp_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, a.exp < b.exp ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `EReal.exp_strictMono`：exp_strictMono : StrictMono exp
-/
@[simp] lemma exp_lt_exp_iff {a b : EReal} : exp a < exp b ↔ a < b := exp_strictMono.lt_iff_lt
/-
**EReal.zero_lt_exp_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, 0 < a.exp ↔ ⊥ < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exp_lt_exp_iff`：∀ {a b : EReal}, a.exp < b.exp ↔ a < b
· 使用定理 `EReal.exp_bot`：⊥.exp = 0
-/
@[simp] lemma zero_lt_exp_iff {a : EReal} : 0 < exp a ↔ ⊥ < a := exp_bot ▸ @exp_lt_exp_iff ⊥ a
/-
**EReal.exp_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, a.exp < ⊤ ↔ a < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exp_lt_exp_iff`：∀ {a b : EReal}, a.exp < b.exp ↔ a < b
· 使用定理 `EReal.exp_top`：⊤.exp = ⊤
-/
@[simp] lemma exp_lt_top_iff {a : EReal} : exp a < ⊤ ↔ a < ⊤ := exp_top ▸ @exp_lt_exp_iff a ⊤
/-
**EReal.exp_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, a.exp < 1 ↔ a < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exp_lt_exp_iff`：∀ {a b : EReal}, a.exp < b.exp ↔ a < b
· 使用定理 `EReal.exp_zero`：EReal.exp 0 = 1
-/
@[simp] lemma exp_lt_one_iff {a : EReal} : exp a < 1 ↔ a < 0 := exp_zero ▸ @exp_lt_exp_iff a 0
/-
**EReal.one_lt_exp_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, 1 < a.exp ↔ 0 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exp_lt_exp_iff`：∀ {a b : EReal}, a.exp < b.exp ↔ a < b
· 使用定理 `EReal.exp_zero`：EReal.exp 0 = 1
-/
@[simp] lemma one_lt_exp_iff {a : EReal} : 1 < exp a ↔ 0 < a := exp_zero ▸ @exp_lt_exp_iff 0 a
/-
**EReal.exp_le_exp_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal}, a.exp ≤ b.exp ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `EReal.exp_strictMono`：exp_strictMono : StrictMono exp
-/
@[simp] lemma exp_le_exp_iff {a b : EReal} : exp a ≤ exp b ↔ a ≤ b := exp_strictMono.le_iff_le
/-
**EReal.exp_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, a.exp ≤ 1 ↔ a ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exp_le_exp_iff`：∀ {a b : EReal}, a.exp ≤ b.exp ↔ a ≤ b
· 使用定理 `EReal.exp_zero`：EReal.exp 0 = 1
-/
@[simp] lemma exp_le_one_iff {a : EReal} : exp a ≤ 1 ↔ a ≤ 0 := exp_zero ▸ @exp_le_exp_iff a 0
/-
**EReal.one_le_exp_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a : EReal}, 1 ≤ a.exp ↔ 0 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exp_le_exp_iff`：∀ {a b : EReal}, a.exp ≤ b.exp ↔ a ≤ b
· 使用定理 `EReal.exp_zero`：EReal.exp 0 = 1
-/
@[simp] lemma one_le_exp_iff {a : EReal} : 1 ≤ exp a ↔ 0 ≤ a := exp_zero ▸ @exp_le_exp_iff 0 a

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

/-
**EReal.exp_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹
参数：x : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EReal.exp_coe`：∀ (x : ℝ), (↑x).exp = ENNReal.ofReal (Real.exp x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
-/
lemma exp_neg (x : EReal) : exp (-x) = (exp x)⁻¹ := by
  induction x
  · simp
  · rw [exp_coe, ← EReal.coe_neg, exp_coe, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      Real.exp_neg]
  · simp
/-
**EReal.exp_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exp_add (x y : EReal) : exp (x + y) = exp x * exp y
参数：x y : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
  induction x
  · simp
  · induction y
    · simp
    · simp only [← EReal.coe_add, exp_coe]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.exp_add]
    · simp only [EReal.coe_add_top, exp_top, exp_coe]
      rw [ENNReal.mul_top]
      simp [Real.exp_pos]
  · induction y
    · simp
    · simp only [EReal.top_add_coe, exp_top, exp_coe]
      rw [ENNReal.top_mul]
      simp [Real.exp_pos]
    · simp

end Morphism

end EReal

