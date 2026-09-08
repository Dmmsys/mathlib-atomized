/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone, Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.EReal.Basic

/-!
# Extended Nonnegative Real Logarithm

We define `log` as an extension of the logarithm of a positive real
to the extended nonnegative reals `ℝ≥0∞`. The function takes values
in the extended reals `EReal`, with `log 0 = ⊥` and `log ⊤ = ⊤`.

## Main Definitions
- `ENNReal.log`: The extension of the real logarithm to `ℝ≥0∞`.

## Main Results
- `ENNReal.log_strictMono`: `log` is increasing;
- `ENNReal.log_injective`, `ENNReal.log_surjective`, `ENNReal.log_bijective`: `log` is
  injective, surjective, and bijective;
- `ENNReal.log_mul_add`, `ENNReal.log_pow`, `ENNReal.log_rpow`: `log` satisfies
  the identities `log (x * y) = log x + log y` and `log (x ^ y) = y * log x`
  (with either `y ∈ ℕ` or `y ∈ ℝ`).

## Tags
ENNReal, EReal, logarithm
-/

@[expose] public section
namespace ENNReal

open scoped NNReal

/-! ### Definition -/
section Definition

/-- The logarithm function defined on the extended nonnegative reals `ℝ≥0∞`
to the extended reals `EReal`. Coincides with the usual logarithm function
and with `Real.log` on positive reals, and takes values `log 0 = ⊥` and `log ⊤ = ⊤`.
Conventions about multiplication in `ℝ≥0∞` and addition in `EReal` make the identity
`log (x * y) = log x + log y` unconditional. -/
/-
**ENNReal.log** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：log (x : Real>=0∞) : EReal
参数：x : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithm function defined on the extended nonnegative reals `ℝ≥0∞`
to the extended reals `EReal`. Coincides with the usual logarithm function
and with `Real.log` on positive reals, and takes values `log 0 = ⊥` and `log ⊤ =
 ⊤`.
Conventions about multiplication in `ℝ≥0∞` and addition in `EReal` make the iden
tity
`log (x * y) = log x + log y` unconditional.
-/
noncomputable def log (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊥
    else if x = ⊤ then ⊤
    else Real.log x.toReal
/-
**ENNReal.log_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.log 0 = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
@[simp] lemma log_zero : log 0 = ⊥ := if_pos rfl
/-
**ENNReal.log_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.log 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma log_one : log 1 = 0 := by simp [log]
/-
**ENNReal.log_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⊤.log = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma log_top : log ⊤ = ⊤ := rfl

@[simp]
/-
**ENNReal.log_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：log_ofReal (x : Real) : log (ENNReal.ofReal x) = if x <= 0 then ⊥ else ↑(R
eal.log x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma log_ofReal (x : ℝ) : log (ENNReal.ofReal x) = if x ≤ 0 then ⊥ else ↑(Real.log x) := by
  simp only [log, ENNReal.ofReal_ne_top,
    ENNReal.ofReal_eq_zero, if_false]
  split_ifs with h_nonpos
  · rfl
  · rw [ENNReal.toReal_ofReal (not_le.mp h_nonpos).le]
/-
**ENNReal.log_ofReal_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：log_ofReal_of_pos {x : Real} (hx : 0 < x) : log (ENNReal.ofReal x) = Real.
log x
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.log_ofReal`：log_ofReal (x : Real) : log (ENNReal.ofReal x) = if 
x <= 0 then ⊥ else ↑(Real.log x)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma log_ofReal_of_pos {x : ℝ} (hx : 0 < x) : log (ENNReal.ofReal x) = Real.log x := by
  rw [log_ofReal, if_neg hx.not_ge]
/-
**ENNReal.log_pos_real** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_pos_real {x : Real>=0∞} (h : x != 0) (h' : x != ⊤) : log x = Real.log 
(ENNReal.toReal x)
参数：h : x != 0；h' : x != ⊤。
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
theorem log_pos_real {x : ℝ≥0∞} (h : x ≠ 0) (h' : x ≠ ⊤) :
    log x = Real.log (ENNReal.toReal x) := by simp [log, h, h']
/-
**ENNReal.log_pos_real'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_pos_real' {x : Real>=0∞} (h : 0 < x.toReal) : log x = Real.log (ENNRea
l.toReal x)
参数：h : 0 < x.toReal。
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
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_pos_real' {x : ℝ≥0∞} (h : 0 < x.toReal) :
    log x = Real.log (ENNReal.toReal x) := by
  simp [log, (ENNReal.toReal_pos_iff.1 h).1.ne', (ENNReal.toReal_pos_iff.1 h).2.ne]
/-
**ENNReal.log_of_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_of_nnreal {x : Real>=0} (h : x != 0) : log (x : Real>=0∞) = Real.log x
参数：h : x != 0。
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
theorem log_of_nnreal {x : ℝ≥0} (h : x ≠ 0) :
    log (x : ℝ≥0∞) = Real.log x := by simp [log, h]

end Definition

/-! ### Monotonicity -/
section Monotonicity

/-
**ENNReal.log_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_strictMono : StrictMono log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem log_strictMono : StrictMono log := by
  intro x y h
  unfold log
  split_ifs <;> simp_all [Real.log_lt_log, toReal_pos_iff, pos_iff_ne_zero, lt_top_iff_ne_top]
/-
**ENNReal.log_monotone** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_monotone : Monotone log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `ENNReal.log_strictMono`：log_strictMono : StrictMono log
-/
theorem log_monotone : Monotone log := log_strictMono.monotone
/-
**ENNReal.log_injective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_injective : Function.Injective log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `ENNReal.log_strictMono`：log_strictMono : StrictMono log
-/
theorem log_injective : Function.Injective log := log_strictMono.injective
/-
**ENNReal.log_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_surjective : Function.Surjective log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.log_ofReal`：log_ofReal (x : Real) : log (ENNReal.ofReal x) = if 
x <= 0 then ⊥ else ↑(Real.log x)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem log_surjective : Function.Surjective log := by
  intro y
  cases y with
  | bot => use 0; simp
  | top => use ⊤; simp
  | coe y => use ENNReal.ofReal (Real.exp y); simp [Real.exp_pos]
/-
**ENNReal.log_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_bijective : Function.Bijective log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_injective`：log_injective : Function.Injective log
· 使用定理 `ENNReal.log_surjective`：log_surjective : Function.Surjective log
-/
theorem log_bijective : Function.Bijective log := ⟨log_injective, log_surjective⟩

@[simp]
/-
**ENNReal.log_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_eq_iff {x y : Real>=0∞} : log x = log y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ENNReal.log_injective`：log_injective : Function.Injective log
-/
theorem log_eq_iff {x y : ℝ≥0∞} : log x = log y ↔ x = y :=
  log_injective.eq_iff
/-
**ENNReal.log_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x.log = ⊥ ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_eq_iff`：log_eq_iff {x y : Real>=0∞} : log x = log y ↔ x = y
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
-/
@[simp] theorem log_eq_bot_iff {x : ℝ≥0∞} : log x = ⊥ ↔ x = 0 := log_zero ▸ @log_eq_iff x 0
/-
**ENNReal.log_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x.log = 0 ↔ x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_eq_iff`：log_eq_iff {x y : Real>=0∞} : log x = log y ↔ x = y
· 使用定理 `ENNReal.log_one`：ENNReal.log 1 = 0
-/
@[simp] theorem log_eq_one_iff {x : ℝ≥0∞} : log x = 0 ↔ x = 1 := log_one ▸ @log_eq_iff x 1
/-
**ENNReal.log_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x.log = ⊤ ↔ x = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_eq_iff`：log_eq_iff {x y : Real>=0∞} : log x = log y ↔ x = y
· 使用定理 `ENNReal.log_top`：⊤.log = ⊤
-/
@[simp] theorem log_eq_top_iff {x : ℝ≥0∞} : log x = ⊤ ↔ x = ⊤ := log_top ▸ @log_eq_iff x ⊤
/-
**ENNReal.log_lt_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y : ENNReal}, x.log < y.log ↔ x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `ENNReal.log_strictMono`：log_strictMono : StrictMono log
-/
@[simp] lemma log_lt_log_iff {x y : ℝ≥0∞} : log x < log y ↔ x < y := log_strictMono.lt_iff_lt
/-
**ENNReal.bot_lt_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, ⊥ < x.log ↔ 0 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_lt_log_iff`：∀ {x y : ENNReal}, x.log < y.log ↔ x < y
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
-/
@[simp] lemma bot_lt_log_iff {x : ℝ≥0∞} : ⊥ < log x ↔ 0 < x := log_zero ▸ @log_lt_log_iff 0 x
/-
**ENNReal.log_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x.log < ⊤ ↔ x < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_lt_log_iff`：∀ {x y : ENNReal}, x.log < y.log ↔ x < y
· 使用定理 `ENNReal.log_top`：⊤.log = ⊤
-/
@[simp] lemma log_lt_top_iff {x : ℝ≥0∞} : log x < ⊤ ↔ x < ⊤ := log_top ▸ @log_lt_log_iff x ⊤
/-
**ENNReal.log_lt_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x.log < 0 ↔ x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_lt_log_iff`：∀ {x y : ENNReal}, x.log < y.log ↔ x < y
· 使用定理 `ENNReal.log_one`：ENNReal.log 1 = 0
-/
@[simp] lemma log_lt_zero_iff {x : ℝ≥0∞} : log x < 0 ↔ x < 1 := log_one ▸ @log_lt_log_iff x 1
/-
**ENNReal.zero_lt_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, 0 < x.log ↔ 1 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_lt_log_iff`：∀ {x y : ENNReal}, x.log < y.log ↔ x < y
· 使用定理 `ENNReal.log_one`：ENNReal.log 1 = 0
-/
@[simp] lemma zero_lt_log_iff {x : ℝ≥0∞} : 0 < log x ↔ 1 < x := log_one ▸ @log_lt_log_iff 1 x
/-
**ENNReal.log_le_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y : ENNReal}, x.log ≤ y.log ↔ x ≤ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `ENNReal.log_strictMono`：log_strictMono : StrictMono log
-/
@[simp] lemma log_le_log_iff {x y : ℝ≥0∞} : log x ≤ log y ↔ x ≤ y := log_strictMono.le_iff_le
/-
**ENNReal.log_le_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x.log ≤ 0 ↔ x ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_le_log_iff`：∀ {x y : ENNReal}, x.log ≤ y.log ↔ x ≤ y
· 使用定理 `ENNReal.log_one`：ENNReal.log 1 = 0
-/
@[simp] lemma log_le_zero_iff {x : ℝ≥0∞} : log x ≤ 0 ↔ x ≤ 1 := log_one ▸ @log_le_log_iff x 1
/-
**ENNReal.zero_le_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, 0 ≤ x.log ↔ 1 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_le_log_iff`：∀ {x y : ENNReal}, x.log ≤ y.log ↔ x ≤ y
· 使用定理 `ENNReal.log_one`：ENNReal.log 1 = 0
-/
@[simp] lemma zero_le_log_iff {x : ℝ≥0∞} : 0 ≤ log x ↔ 1 ≤ x := log_one ▸ @log_le_log_iff 1 x
/-
**ENNReal.log_le_log** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y : ENNReal}, x ≤ y → x.log ≤ y.log
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
-/
@[gcongr] lemma log_le_log {x y : ℝ≥0∞} (h : x ≤ y) : log x ≤ log y := log_monotone h
/-
**ENNReal.log_lt_log** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y : ENNReal}, x < y → x.log < y.log
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.log_strictMono`：log_strictMono : StrictMono log
-/
@[gcongr] lemma log_lt_log {x y : ℝ≥0∞} (h : x < y) : log x < log y := log_strictMono h

end Monotonicity

/-! ### Algebraic properties -/

section Morphism

/-
**ENNReal.log_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_mul_add {x y : Real>=0∞} : log (x * y) = log x + log y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.log_top`：⊤.log = ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `ENNReal.log_pos_real'`：log_pos_real' {x : Real>=0∞} (h : 0 < x.toReal) :
 log x = Real.log (ENNReal.toReal x)
· 使用定理 `ENNReal.top_mul'`：top_mul' : ∞ * a = if a = 0 then 0 else ∞
· 使用定理 `EReal.top_add_coe`：top_add_coe (x : Real) : (⊤ : EReal) + x = ⊤
· 使用定理 `ENNReal.log_eq_top_iff`：∀ {x : ENNReal}, x.log = ⊤ ↔ x = ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
（共 33 条，此处仅展示前 30 条）
-/
theorem log_mul_add {x y : ℝ≥0∞} : log (x * y) = log x + log y := by
  rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
  · simp
  · rw [log_top]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · rw [mul_zero, log_zero, EReal.add_bot]
    · simp
    · rw [log_pos_real' y_real, ENNReal.top_mul', EReal.top_add_coe, log_eq_top_iff]
      simp only [ite_eq_right_iff, zero_ne_top, imp_false]
      exact (ENNReal.toReal_pos_iff.1 y_real).1.ne'
  · rw [log_pos_real' x_real]
    rcases ENNReal.trichotomy y with (rfl | rfl | y_real)
    · simp
    · simp [(ENNReal.toReal_pos_iff.1 x_real).1.ne']
    · rw_mod_cast [log_pos_real', log_pos_real' y_real, ENNReal.toReal_mul]
      · exact Real.log_mul x_real.ne' y_real.ne'
      rw [toReal_mul]
      positivity
/-
**ENNReal.log_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_rpow {x : Real>=0∞} {y : Real} : log (x ^ y) = y * log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_def`：zero_rpow_def (y : Real) : (0 : Real>=0∞) ^ y = i
f 0 < y then 0 else if y = 0 then 1 else ⊤
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥
· 使用引理 `EReal.coe_mul_bot_of_neg`：coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊥ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `ENNReal.log_top`：⊤.log = ⊤
· 使用引理 `EReal.coe_mul_top_of_neg`：coe_mul_top_of_neg {x : Real} (h : x < 0) : (x
 : EReal) * ⊤ = ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
（共 38 条，此处仅展示前 30 条）
-/
theorem log_rpow {x : ℝ≥0∞} {y : ℝ} : log (x ^ y) = y * log x := by
  rcases lt_trichotomy y 0 with (y_neg | rfl | y_pos)
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · simp only [ENNReal.zero_rpow_def y, not_lt_of_gt y_neg, y_neg.ne, if_false, log_top,
        log_zero, EReal.coe_mul_bot_of_neg y_neg]
    · rw [ENNReal.top_rpow_of_neg y_neg, log_zero, log_top, EReal.coe_mul_top_of_neg y_neg]
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
  · simp
  · rcases ENNReal.trichotomy x with (rfl | rfl | x_real)
    · rw [ENNReal.zero_rpow_of_pos y_pos, log_zero, EReal.mul_bot_of_pos]; norm_cast
    · rw [ENNReal.top_rpow_of_pos y_pos, log_top, EReal.mul_top_of_pos]; norm_cast
    · have x_ne_zero := (ENNReal.toReal_pos_iff.1 x_real).1.ne'
      have x_ne_top := (ENNReal.toReal_pos_iff.1 x_real).2.ne
      simp only [log, rpow_eq_zero_iff, x_ne_zero, false_and, x_ne_top, or_self, ↓reduceIte,
        rpow_eq_top_iff]
      norm_cast
      exact ENNReal.toReal_rpow x y ▸ Real.log_rpow x_real y
/-
**ENNReal.log_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：log_pow {x : Real>=0∞} {n : Nat} : log (x ^ n) = n * log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `ENNReal.log_rpow`：log_rpow {x : Real>=0∞} {y : Real} : log (x ^ y) = y *
 log x
· 使用定理 `EReal.coe_natCast`：∀ {n : ℕ}, ↑↑n = ↑n
-/
theorem log_pow {x : ℝ≥0∞} {n : ℕ} : log (x ^ n) = n * log x := by
  rw [← rpow_natCast, log_rpow, EReal.coe_natCast]
/-
**ENNReal.log_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：log_inv {x : Real>=0∞} : log x⁻¹ = - log x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.log_rpow`：log_rpow {x : Real>=0∞} {y : Real} : log (x ^ y) = y *
 log x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma log_inv {x : ℝ≥0∞} : log x⁻¹ = - log x := by
  simp [← rpow_neg_one, log_rpow]

end Morphism

end ENNReal

