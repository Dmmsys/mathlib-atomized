/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Real.Basic

/-!

# Predicates on monomials

In this file we define `UnitMonomial`: type to represent monomials without coefficient as a list of
its exponents.  `[e₁, e₂, ..., eₙ]` corresponds to `basis[0] ^ e₁ * ... * basis[n] ^ eₙ` where
`basis` is the basis of functions.

Then we define some predicates for these lists:
1. `FirstNonzeroIsPos li` means that the first non-zero element of the list `li` is positive.
2. `FirstNonzeroIsNeg li` means that the first non-zero element of the list `li` is negative.
3. `AllZero li` means that all elements in `li` are zero.

This trichotomy determines the asymptotic behaviour of a monomial:
`FirstNonzeroIsPos` means it tends to infinity, `FirstNonzeroIsNeg` means it tends to zero and
`AllZero` means it tends to a constant.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

/-- Unit monomial, represented as a list of its exponents. `[e₁, e₂, ..., eₙ]` corresponds to
`basis[0] ^ e₁ * ... * basis[n] ^ eₙ` where `basis` is the basis of functions. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial** 是 Mathlib 中的一个缩写定义，位于命名空间 `Tactic.Com
puteAsymptotics`。
形式化陈述：UnitMonomial
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unit monomial, represented as a list of its exponents. `[e₁, e₂, ..., eₙ]` corre
sponds to
`basis[0] ^ e₁ * ... * basis[n] ^ eₙ` where `basis` is the basis of functions.
-/
abbrev UnitMonomial := List ℝ

namespace UnitMonomial

/-- Type representing a sign of the first non-zero exponent, returned by `sign`. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.Sign** 是 Mathlib 中的一个归纳类型，位于命名空间 `Tacti
c.ComputeAsymptotics.UnitMonomial`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type representing a sign of the first non-zero exponent, returned by `sign`.
-/
inductive Sign
| pos | neg | zero

/-- Sign of the first non-zero exponent of a unit monomial. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.sign** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.
ComputeAsymptotics.UnitMonomial`。
形式化陈述：Tactic.ComputeAsymptotics.UnitMonomial → Tactic.ComputeAsymptotics.UnitMon
omial.Sign
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sign of the first non-zero exponent of a unit monomial.
-/
noncomputable def sign : UnitMonomial → Sign
  | [] => .zero
  | hd :: tl =>
    if 0 < hd then
      .pos
    else if hd < 0 then
      .neg
    else
      sign tl

/-- Predicate stating that the first non-zero exponent is positive. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos** 是 Mathlib 中的一个定义，位于
命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：FirstNonzeroIsPos (m : UnitMonomial) : Prop
参数：m : UnitMonomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate stating that the first non-zero exponent is positive.
-/
def FirstNonzeroIsPos (m : UnitMonomial) : Prop := m.sign = .pos

/-- Predicate stating that the first non-zero exponent is negative. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg** 是 Mathlib 中的一个定义，位于
命名空间 `Tactic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：FirstNonzeroIsNeg (m : UnitMonomial) : Prop
参数：m : UnitMonomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate stating that the first non-zero exponent is negative.
-/
def FirstNonzeroIsNeg (m : UnitMonomial) : Prop := m.sign = .neg

/-- Predicate stating that all exponents are zero. -/
/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero** 是 Mathlib 中的一个定义，位于命名空间 `Tact
ic.ComputeAsymptotics.UnitMonomial`。
形式化陈述：AllZero (m : UnitMonomial) : Prop
参数：m : UnitMonomial。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate stating that all exponents are zero.
-/
def AllZero (m : UnitMonomial) : Prop := m.sign = .zero

namespace AllZero

/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero.nil** 是 Mathlib 中的一个定理，位于命名空间 `
Tactic.ComputeAsymptotics.UnitMonomial.AllZero`。
形式化陈述：nil : AllZero []
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil : AllZero [] :=
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero.cons_iff** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero`。
形式化陈述：cons_iff {hd : Real} {tl : UnitMonomial} : AllZero (hd :: tl) ↔ hd = 0 ∧ A
llZero tl
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl := by
  grind [AllZero, sign]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero.of_tail** 是 Mathlib 中的一个定理，位于命名
空间 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero`。
形式化陈述：of_tail {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl
) : AllZero (hd :: tl)
参数：h_hd : hd = 0；h_tl : AllZero tl。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero.cons_iff`：cons_iff {hd : 
Real} {tl : UnitMonomial} : AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl
-/
theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) :=
  cons_iff.mpr ⟨h_hd, h_tl⟩
/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero.replicate** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero`。
形式化陈述：replicate {n : Nat} : AllZero (List.replicate n 0)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  induction n <;> grind [AllZero, sign]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero.not_FirstNonzeroIsPos** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero`。
形式化陈述：not_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) : ¬ FirstNonzer
oIsPos li
参数：h : AllZero li。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsPos li := by
  grind [AllZero, FirstNonzeroIsPos]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.AllZero.not_FirstNonzeroIsNeg** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero`。
形式化陈述：not_FirstNonzeroIsNeg {li : UnitMonomial} (h : AllZero li) : ¬ FirstNonzer
oIsNeg li
参数：h : AllZero li。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsNeg li := by
  grind [AllZero, FirstNonzeroIsNeg]

end AllZero

namespace FirstNonzeroIsPos

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.not_nil** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos`。
形式化陈述：not_nil : ¬ FirstNonzeroIsPos []
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_nil : ¬ FirstNonzeroIsPos [] := by simp [FirstNonzeroIsPos, sign]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.cons_iff** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos`。
形式化陈述：cons_iff {hd : Real} {tl : UnitMonomial} : FirstNonzeroIsPos (hd :: tl) ↔ 
0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsPos (hd :: tl) ↔ 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl) := by
  grind [FirstNonzeroIsPos, sign]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.of_head** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos`。
形式化陈述：of_head {hd : Real} (tl : UnitMonomial) (h_hd : 0 < hd) : FirstNonzeroIsPo
s (hd :: tl)
参数：tl : UnitMonomial；h_hd : 0 < hd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [h_hd]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.of_tail** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos`。
形式化陈述：of_tail {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonze
roIsPos tl) : FirstNonzeroIsPos (hd :: tl)
参数：h_hd : hd = 0；h_tl : FirstNonzeroIsPos tl。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsPos tl) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [h_hd, h_tl]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.not_AllZero** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos`。
形式化陈述：not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsPos li) : ¬ AllZero li
参数：h : FirstNonzeroIsPos li。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero.not_FirstNonzeroIsPos`：no
t_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) : ¬ FirstNonzeroIsPos l
i
-/
theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ AllZero li :=
  fun h' ↦ h'.not_FirstNonzeroIsPos h
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.not_FirstNonzeroIsNeg
** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroI
sPos`。
形式化陈述：not_FirstNonzeroIsNeg {li : UnitMonomial} (h : FirstNonzeroIsPos li) : ¬ F
irstNonzeroIsNeg li
参数：h : FirstNonzeroIsPos li。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ FirstNonzeroIsNeg li := by
  grind [FirstNonzeroIsPos, FirstNonzeroIsNeg]

end FirstNonzeroIsPos

namespace FirstNonzeroIsNeg

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg.not_nil** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg`。
形式化陈述：not_nil : ¬ FirstNonzeroIsNeg []
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_nil : ¬ FirstNonzeroIsNeg [] := by simp [FirstNonzeroIsNeg, sign]

@[simp]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg.cons_iff** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg`。
形式化陈述：cons_iff {hd : Real} {tl : UnitMonomial} : FirstNonzeroIsNeg (hd :: tl) ↔ 
hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_iff {hd : ℝ} {tl : UnitMonomial} :
    FirstNonzeroIsNeg (hd :: tl) ↔ hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl) := by
  grind [FirstNonzeroIsNeg, sign]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg.of_head** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg`。
形式化陈述：of_head {hd : Real} (tl : UnitMonomial) (h_hd : hd < 0) : FirstNonzeroIsNe
g (hd :: tl)
参数：tl : UnitMonomial；h_hd : hd < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem of_head {hd : ℝ} (tl : UnitMonomial) (h_hd : hd < 0) :
    FirstNonzeroIsNeg (hd :: tl) := by
  simp [h_hd]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg.of_tail** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg`。
形式化陈述：of_tail {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonze
roIsNeg tl) : FirstNonzeroIsNeg (hd :: tl)
参数：h_hd : hd = 0；h_tl : FirstNonzeroIsNeg tl。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem of_tail {hd : ℝ} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonzeroIsNeg tl) :
    FirstNonzeroIsNeg (hd :: tl) := by
  simp [h_hd, h_tl]
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg.not_AllZero** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg`。
形式化陈述：not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsNeg li) : ¬ AllZero li
参数：h : FirstNonzeroIsNeg li。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.AllZero.not_FirstNonzeroIsNeg`：no
t_FirstNonzeroIsNeg {li : UnitMonomial} (h : AllZero li) : ¬ FirstNonzeroIsNeg l
i
-/
theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ AllZero li :=
  fun h' ↦ h'.not_FirstNonzeroIsNeg h
/-
**Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsNeg.not_FirstNonzeroIsPos
** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroI
sNeg`。
形式化陈述：not_FirstNonzeroIsPos {li : UnitMonomial} (h : FirstNonzeroIsNeg li) : ¬ F
irstNonzeroIsPos li
参数：h : FirstNonzeroIsNeg li。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.UnitMonomial.FirstNonzeroIsPos.not_FirstNonzer
oIsNeg`：not_FirstNonzeroIsNeg {li : UnitMonomial} (h : FirstNonzeroIsPos li) : ¬
 FirstNonzeroIsNeg li
-/
theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ FirstNonzeroIsPos li :=
  fun h' ↦ h'.not_FirstNonzeroIsNeg h

end FirstNonzeroIsNeg

end Tactic.ComputeAsymptotics.UnitMonomial

