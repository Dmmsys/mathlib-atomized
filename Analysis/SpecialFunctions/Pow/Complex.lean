/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/

@[expose] public section

open Real Topology Filter ComplexConjugate Finset Set

namespace Complex

/-- The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log` is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 = 1` and
`0 ^ y = 0` for `y ≠ 0`. -/
/-
**Complex.cpow** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：cpow (x y : Complex) : Complex
参数：x y : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log`
 is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 
= 1` and
`0 ^ y = 0` for `y ≠ 0`.
-/
noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
/-
**Complex.** 是 Mathlib 中的一个实例，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pow ℂ ℂ :=
  ⟨cpow⟩

@[simp]
/-
**Complex.cpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_eq_pow (x y : Complex) : cpow x y = x ^ y
参数：x y : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y :=
  rfl
/-
**Complex.cpow_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_def (x y : Complex) : x ^ y = if x = 0 then if y = 0 then 1 else 0 el
se exp (log x * y)
参数：x y : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cpow_def (x y : ℂ) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl
/-
**Complex.cpow_def_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_def_of_ne_zero {x : Complex} (hx : x != 0) (y : Complex) : x ^ y = ex
p (log x * y)
参数：hx : x != 0；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  if_neg hx

@[simp]
/-
**Complex.cpow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]

@[simp]
/-
**Complex.cpow_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_eq_zero_iff (x y : Complex) : x ^ y = 0 ↔ x = 0 ∧ y != 0
参数：x y : Complex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]
/-
**Complex.cpow_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_ne_zero_iff {x y : Complex} : x ^ y != 0 ↔ x != 0 ∨ y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.cpow_eq_zero_iff`：cpow_eq_zero_iff (x y : Complex) : x ^ y = 0 ↔
 x = 0 ∧ y != 0
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cpow_ne_zero_iff {x y : ℂ} :
    x ^ y ≠ 0 ↔ x ≠ 0 ∨ y = 0 := by
  rw [ne_eq, cpow_eq_zero_iff, not_and_or, ne_eq, not_not]
/-
**Complex.cpow_ne_zero_iff_of_exponent_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x`。
形式化陈述：cpow_ne_zero_iff_of_exponent_ne_zero {x y : Complex} (hy : y != 0) : x ^ y
 != 0 ↔ x != 0
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cpow_ne_zero_iff_of_exponent_ne_zero {x y : ℂ} (hy : y ≠ 0) :
    x ^ y ≠ 0 ↔ x ≠ 0 := by simp [hy]

@[simp]
/-
**Complex.zero_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) ^ x = 0
参数：h : x != 0。
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
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]
/-
**Complex.zero_cpow_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：zero_cpow_eq_iff {x : Complex} {a : Complex} : (0 : Complex) ^ x = a ↔ x !
= 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
-/
theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : (0 : ℂ) ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [cpow_def, if_true] at hyp
    grind
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _
/-
**Complex.eq_zero_cpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：eq_zero_cpow_iff {x : Complex} {a : Complex} : a = (0 : Complex) ^ x ↔ x !
= 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.zero_cpow_eq_iff`：zero_cpow_eq_iff {x : Complex} {a : Complex} :
 (0 : Complex) ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = (0 : ℂ) ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]

@[simp]
/-
**Complex.cpow_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_one (x : Complex) : x ^ (1 : Complex) = x
参数：x : Complex。
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Complex.cpow_def`：cpow_def (x y : Complex) : x ^ y = if x = 0 then if y 
= 0 then 1 else 0 else exp (log x * y)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
-/
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]

@[simp]
/-
**Complex.one_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_def`：cpow_def (x y : Complex) : x ^ y = if x = 0 then if y 
= 0 then 1 else 0 else exp (log x * y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def]
  split_ifs <;> simp_all [one_ne_zero]
/-
**Complex.cpow_add** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) : x ^ (y + z) = x ^ y
 * x ^ z
参数：y z : Complex；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, mul_ite]
  simp_all [exp_add, mul_add]
/-
**Complex.cpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_mul {x y : Complex} (z : Complex) (h₁ : -π < (log x * y).im) (h₂ : (l
og x * y).im <= π) : x ^ (y * z) = (x ^ y) ^ z
参数：z : Complex；h₁ : -π < (log x * y).im；h₂ : (log x * y).im <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.log_exp`：log_exp {x : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= 
π) : log (exp x) = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]
/-
**Complex.cpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
参数：x y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Complex.exp_neg`：exp_neg : exp (-x) = (exp x)⁻¹
-/
theorem cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg]
  split_ifs <;> simp [exp_neg]
/-
**Complex.cpow_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_sub {x : Complex} (y z : Complex) (hx : x != 0) : x ^ (y - z) = x ^ y
 / x ^ z
参数：y z : Complex；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]
/-
**Complex.cpow_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_neg_one (x : Complex) : x ^ (-1 : Complex) = x⁻¹
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
-/
theorem cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ := by simpa using cpow_neg x 1

/-- See also `Complex.cpow_int_mul'`. -/
/-
**Complex.cpow_int_mul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_int_mul (x : Complex) (n : Int) (y : Complex) : x ^ (n * y) = (x ^ y)
 ^ n
参数：x : Complex；n : Int；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Complex.exp_int_mul`：exp_int_mul (z : Complex) (n : Int) : Complex.exp (
n * z) = Complex.exp z ^ n

--- 原说明 ---
See also `Complex.cpow_int_mul'`.
-/
lemma cpow_int_mul (x : ℂ) (n : ℤ) (y : ℂ) : x ^ (n * y) = (x ^ y) ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rcases eq_or_ne y 0 with rfl | hy <;> simp [*, zero_zpow]
  · rw [cpow_def_of_ne_zero hx, cpow_def_of_ne_zero hx, mul_left_comm, exp_int_mul]
/-
**Complex.cpow_mul_int** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_mul_int (x y : Complex) (n : Int) : x ^ (y * n) = (x ^ y) ^ n
参数：x y : Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Complex.cpow_int_mul`：cpow_int_mul (x : Complex) (n : Int) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
-/
lemma cpow_mul_int (x y : ℂ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by rw [mul_comm, cpow_int_mul]
/-
**Complex.cpow_nat_mul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_nat_mul (x : Complex) (n : Nat) (y : Complex) : x ^ (n * y) = (x ^ y)
 ^ n
参数：x : Complex；n : Nat；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Complex.cpow_int_mul`：cpow_int_mul (x : Complex) (n : Int) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
-/
lemma cpow_nat_mul (x : ℂ) (n : ℕ) (y : ℂ) : x ^ (n * y) = (x ^ y) ^ n :=
  mod_cast cpow_int_mul x n y
/-
**Complex.cpow_ofNat_mul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofNat_mul (x : Complex) (n : Nat) [n.AtLeastTwo] (y : Complex) : x ^ 
(ofNat(n) * y) = (x ^ y) ^ ofNat(n)
参数：x : Complex；n : Nat；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.cpow_nat_mul`：cpow_nat_mul (x : Complex) (n : Nat) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
-/
lemma cpow_ofNat_mul (x : ℂ) (n : ℕ) [n.AtLeastTwo] (y : ℂ) :
    x ^ (ofNat(n) * y) = (x ^ y) ^ ofNat(n) :=
  cpow_nat_mul x n y
/-
**Complex.cpow_mul_nat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_mul_nat (x y : Complex) (n : Nat) : x ^ (y * n) = (x ^ y) ^ n
参数：x y : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Complex.cpow_nat_mul`：cpow_nat_mul (x : Complex) (n : Nat) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
-/
lemma cpow_mul_nat (x y : ℂ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [mul_comm, cpow_nat_mul]
/-
**Complex.cpow_mul_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_mul_ofNat (x y : Complex) (n : Nat) [n.AtLeastTwo] : x ^ (y * ofNat(n
)) = (x ^ y) ^ ofNat(n)
参数：x y : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.cpow_mul_nat`：cpow_mul_nat (x y : Complex) (n : Nat) : x ^ (y * 
n) = (x ^ y) ^ n
-/
lemma cpow_mul_ofNat (x y : ℂ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (y * ofNat(n)) = (x ^ y) ^ ofNat(n) :=
  cpow_mul_nat x y n

@[simp, norm_cast]
/-
**Complex.cpow_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Complex) = x ^ n
参数：x : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用引理 `Complex.cpow_nat_mul`：cpow_nat_mul (x : Complex) (n : Nat) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
-/
theorem cpow_natCast (x : ℂ) (n : ℕ) : x ^ (n : ℂ) = x ^ n := by simpa using cpow_nat_mul x n 1

@[simp]
/-
**Complex.cpow_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofNat (x : Complex) (n : Nat) [n.AtLeastTwo] : x ^ (ofNat(n) : Comple
x) = x ^ ofNat(n)
参数：x : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
-/
lemma cpow_ofNat (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℂ) = x ^ ofNat(n) :=
  cpow_natCast x n
/-
**Complex.cpow_two** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_two (x : Complex) : x ^ (2 : Complex) = x ^ (2 : Nat)
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.cpow_ofNat`：cpow_ofNat (x : Complex) (n : Nat) [n.AtLeastTwo] : 
x ^ (ofNat(n) : Complex) = x ^ ofNat(n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ (2 : ℕ) := cpow_ofNat x 2

@[simp, norm_cast]
/-
**Complex.cpow_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_intCast (x : Complex) (n : Int) : x ^ (n : Complex) = x ^ n
参数：x : Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用引理 `Complex.cpow_int_mul`：cpow_int_mul (x : Complex) (n : Int) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
-/
theorem cpow_intCast (x : ℂ) (n : ℤ) : x ^ (n : ℂ) = x ^ n := by simpa using cpow_int_mul x n 1

@[simp]
/-
**Complex.cpow_nat_inv_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_nat_inv_pow (x : Complex) {n : Nat} (hn : n != 0) : (x ^ (n⁻¹ : Compl
ex)) ^ n = x
参数：x : Complex；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.cpow_nat_mul`：cpow_nat_mul (x : Complex) (n : Nat) (y : Complex)
 : x ^ (n * y) = (x ^ y) ^ n
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
-/
theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x := by
  rw [← cpow_nat_mul, mul_inv_cancel₀, cpow_one]
  assumption_mod_cast

@[simp]
/-
**Complex.cpow_ofNat_inv_pow** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofNat_inv_pow (x : Complex) (n : Nat) [n.AtLeastTwo] : (x ^ ((ofNat(n
) : Complex)⁻¹)) ^ (ofNat(n) : Nat) = x
参数：x : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.cpow_nat_inv_pow`：cpow_nat_inv_pow (x : Complex) {n : Nat} (hn :
 n != 0) : (x ^ (n⁻¹ : Complex)) ^ n = x
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma cpow_ofNat_inv_pow (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (x ^ ((ofNat(n) : ℂ)⁻¹)) ^ (ofNat(n) : ℕ) = x :=
  cpow_nat_inv_pow _ (NeZero.ne n)

/-- A version of `Complex.cpow_int_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`. -/
/-
**Complex.cpow_int_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_int_mul' {x : Complex} {n : Int} (hlt : -π < n * x.arg) (hle : n * x.
arg <= π) (y : Complex) : x ^ (n * y) = (x ^ n) ^ y
参数：hlt : -π < n * x.arg；hle : n * x.arg <= π；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_mul`：cpow_mul {x y : Complex} (z : Complex) (h₁ : -π < (log
 x * y).im) (h₂ : (log x * y).im <= π) : x ^ (y * z) = (x ^ y) ^ z
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.cpow_intCast`：cpow_intCast (x : Complex) (n : Int) : x ^ (n : Co
mplex) = x ^ n

--- 原说明 ---
A version of `Complex.cpow_int_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`.
-/
lemma cpow_int_mul' {x : ℂ} {n : ℤ} (hlt : -π < n * x.arg) (hle : n * x.arg ≤ π) (y : ℂ) :
    x ^ (n * y) = (x ^ n) ^ y := by
  rw [mul_comm] at hlt hle
  rw [cpow_mul, cpow_intCast] <;> simpa [log_im]

/-- A version of `Complex.cpow_nat_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`. -/
/-
**Complex.cpow_nat_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_nat_mul' {x : Complex} {n : Nat} (hlt : -π < n * x.arg) (hle : n * x.
arg <= π) (y : Complex) : x ^ (n * y) = (x ^ n) ^ y
参数：hlt : -π < n * x.arg；hle : n * x.arg <= π；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.cpow_int_mul'`：cpow_int_mul' {x : Complex} {n : Int} (hlt : -π <
 n * x.arg) (hle : n * x.arg <= π) (y : Complex) : x ^ (n * y) = (x ^ n) ^ y

--- 原说明 ---
A version of `Complex.cpow_nat_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`.
-/
lemma cpow_nat_mul' {x : ℂ} {n : ℕ} (hlt : -π < n * x.arg) (hle : n * x.arg ≤ π) (y : ℂ) :
    x ^ (n * y) = (x ^ n) ^ y :=
  cpow_int_mul' hlt hle y
/-
**Complex.cpow_ofNat_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofNat_mul' {x : Complex} {n : Nat} [n.AtLeastTwo] (hlt : -π < OfNat.o
fNat n * x.arg) (hle : OfNat.ofNat n * x.arg <= π) (y : Complex) : x ^ (OfNat.of
Nat n * y) = (x ^ ofNat(n)) ^ y
参数：hlt : -π < OfNat.ofNat n * x.arg；hle : OfNat.ofNat n * x.arg <= π；y : Complex
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.cpow_nat_mul'`：cpow_nat_mul' {x : Complex} {n : Nat} (hlt : -π <
 n * x.arg) (hle : n * x.arg <= π) (y : Complex) : x ^ (n * y) = (x ^ n) ^ y
-/
lemma cpow_ofNat_mul' {x : ℂ} {n : ℕ} [n.AtLeastTwo] (hlt : -π < OfNat.ofNat n * x.arg)
    (hle : OfNat.ofNat n * x.arg ≤ π) (y : ℂ) :
    x ^ (OfNat.ofNat n * y) = (x ^ ofNat(n)) ^ y :=
  cpow_nat_mul' hlt hle y
/-
**Complex.pow_cpow_nat_inv** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：pow_cpow_nat_inv {x : Complex} {n : Nat} (h₀ : n != 0) (hlt : -(π / n) < x
.arg) (hle : x.arg <= π / n) : (x ^ n) ^ (n⁻¹ : Complex) = x
参数：h₀ : n != 0；hlt : -(π / n) < x.arg；hle : x.arg <= π / n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.cpow_nat_mul'`：cpow_nat_mul' {x : Complex} {n : Nat} (hlt : -π <
 n * x.arg) (hle : n * x.arg <= π) (y : Complex) : x ^ (n * y) = (x ^ n) ^ y
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
-/
lemma pow_cpow_nat_inv {x : ℂ} {n : ℕ} (h₀ : n ≠ 0) (hlt : -(π / n) < x.arg) (hle : x.arg ≤ π / n) :
    (x ^ n) ^ (n⁻¹ : ℂ) = x := by
  rw [← cpow_nat_mul', mul_inv_cancel₀ (Nat.cast_ne_zero.2 h₀), cpow_one]
  · rwa [← div_lt_iff₀' (Nat.cast_pos.2 h₀.bot_lt), neg_div]
  · rwa [← le_div_iff₀' (Nat.cast_pos.2 h₀.bot_lt)]
/-
**Complex.pow_cpow_ofNat_inv** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：pow_cpow_ofNat_inv {x : Complex} {n : Nat} [n.AtLeastTwo] (hlt : -(π / OfN
at.ofNat n) < x.arg) (hle : x.arg <= π / OfNat.ofNat n) : (x ^ ofNat(n)) ^ ((OfN
at.ofNat n : Complex)⁻¹) = x
参数：hlt : -(π / OfNat.ofNat n) < x.arg；hle : x.arg <= π / OfNat.ofNat n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.pow_cpow_nat_inv`：pow_cpow_nat_inv {x : Complex} {n : Nat} (h₀ :
 n != 0) (hlt : -(π / n) < x.arg) (hle : x.arg <= π / n) : (x ^ n) ^ (n⁻¹ : Comp
lex) = x
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
lemma pow_cpow_ofNat_inv {x : ℂ} {n : ℕ} [n.AtLeastTwo] (hlt : -(π / OfNat.ofNat n) < x.arg)
    (hle : x.arg ≤ π / OfNat.ofNat n) :
    (x ^ ofNat(n)) ^ ((OfNat.ofNat n : ℂ)⁻¹) = x :=
  pow_cpow_nat_inv (NeZero.ne n) hlt hle

/-- See also `Complex.pow_cpow_ofNat_inv` for a version that also works for `x * I`, `0 ≤ x`. -/
/-
**Complex.sq_cpow_two_inv** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：sq_cpow_two_inv {x : Complex} (hx : 0 < x.re) : (x ^ (2 : Nat)) ^ (2⁻¹ : C
omplex) = x
参数：hx : 0 < x.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.pow_cpow_ofNat_inv`：pow_cpow_ofNat_inv {x : Complex} {n : Nat} [
n.AtLeastTwo] (hlt : -(π / OfNat.ofNat n) < x.arg) (hle : x.arg <= π / OfNat.ofN
at n) : (x ^ ofN…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Complex.neg_pi_div_two_lt_arg_iff`：neg_pi_div_two_lt_arg_iff {z : Comple
x} : -(π / 2) < arg z ↔ 0 < re z ∨ 0 <= im z
· 使用定理 `Complex.arg_le_pi_div_two_iff`：arg_le_pi_div_two_iff {z : Complex} : arg
 z <= π / 2 ↔ 0 <= re z ∨ im z < 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
See also `Complex.pow_cpow_ofNat_inv` for a version that also works for `x * I`,
 `0 ≤ x`.
-/
lemma sq_cpow_two_inv {x : ℂ} (hx : 0 < x.re) : (x ^ (2 : ℕ)) ^ (2⁻¹ : ℂ) = x :=
  pow_cpow_ofNat_inv (neg_pi_div_two_lt_arg_iff.2 <| .inl hx)
    (arg_le_pi_div_two_iff.2 <| .inl hx.le)
/-
**Complex.isSquare** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℂ), IsSquare x
参数：x : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.cpow_ofNat_inv_pow`：cpow_ofNat_inv_pow (x : Complex) (n : Nat) [
n.AtLeastTwo] : (x ^ ((ofNat(n) : Complex)⁻¹)) ^ (ofNat(n) : Nat) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma isSquare (x : ℂ) : IsSquare x := ⟨x ^ (2⁻¹ : ℂ), by simp [← sq]⟩
/-
**Complex.mul_cpow_ofReal_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：mul_cpow_ofReal_nonneg {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (r : Compl
ex) : ((a : Complex) * (b : Complex)) ^ r = (a : Complex) ^ r * (b : Complex) ^ 
r
参数：ha : 0 <= a；hb : 0 <= b；r : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.log_ofReal_mul`：log_ofReal_mul {r : Real} (hr : 0 < r) {x : Comp
lex} (hx : x != 0) : log (r * x) = Real.log r + log x
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
-/
theorem mul_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha'.ne'
  have hb'' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_ofReal_mul ha' hb'', ofReal_log ha,
    add_mul, exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']
/-
**Complex.natCast_mul_natCast_cpow** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：natCast_mul_natCast_cpow (m n : Nat) (s : Complex) : (m * n : Complex) ^ s
 = m ^ s * n ^ s
参数：m n : Nat；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.mul_cpow_ofReal_nonneg`：mul_cpow_ofReal_nonneg {a b : Real} (ha 
: 0 <= a) (hb : 0 <= b) (r : Complex) : ((a : Complex) * (b : Complex)) ^ r = (a
 : Complex) ^ r * (b…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
-/
lemma natCast_mul_natCast_cpow (m n : ℕ) (s : ℂ) : (m * n : ℂ) ^ s = m ^ s * n ^ s :=
  ofReal_natCast m ▸ ofReal_natCast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s
/-
**Complex.natCast_cpow_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：natCast_cpow_natCast_mul (n m : Nat) (z : Complex) : (n : Complex) ^ (m * 
z) = ((n : Complex) ^ m) ^ z
参数：n m : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.cpow_nat_mul'`：cpow_nat_mul' {x : Complex} {n : Nat} (hlt : -π <
 n * x.arg) (hle : n * x.arg <= π) (y : Complex) : x ^ (n * y) = (x ^ n) ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.natCast_arg`：natCast_arg {n : Nat} : arg n = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
-/
lemma natCast_cpow_natCast_mul (n m : ℕ) (z : ℂ) : (n : ℂ) ^ (m * z) = ((n : ℂ) ^ m) ^ z := by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [natCast_arg, mul_zero, Left.neg_neg_iff, pi_pos]
  · simp only [natCast_arg, mul_zero, pi_pos.le]
/-
**Complex.inv_cpow_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_cpow_eq_ite (x : Complex) (n : Complex) : x⁻¹ ^ n = if x.arg = π then 
conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹
参数：x : Complex；n : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Complex.log_inv_eq_ite`：log_inv_eq_ite (x : Complex) : log x⁻¹ = if x.ar
g = π then -conj (log x) else -log x
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `RCLike.conj_inv`：conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Complex.exp_neg`：exp_neg : exp (-x) = (exp x)⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ := by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    RCLike.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl
/-
**Complex.inv_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_cpow (x : Complex) (n : Complex) (hx : x.arg != π) : x⁻¹ ^ n = (x ^ n)
⁻¹
参数：x : Complex；n : Complex；hx : x.arg != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.inv_cpow_eq_ite`：inv_cpow_eq_ite (x : Complex) (n : Complex) : x
⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, if_neg hx]
/-
**Complex.inv_cpow_ofReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：inv_cpow_ofReal_nonneg {a : Real} (ha : 0 <= a) (r : Complex) : ((a : Comp
lex)⁻¹) ^ r = (a ^ r : Complex)⁻¹
参数：ha : 0 <= a；r : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.inv_cpow`：inv_cpow (x : Complex) (n : Complex) (hx : x.arg != π)
 : x⁻¹ ^ n = (x ^ n)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
-/
lemma inv_cpow_ofReal_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℂ) :
    ((a : ℂ)⁻¹) ^ r = (a ^ r : ℂ)⁻¹ :=
  inv_cpow _ _ <| by simpa [arg_ofReal_of_nonneg ha] using Real.pi_ne_zero.symm
/-
**Complex.div_cpow_ofReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：div_cpow_ofReal_nonneg {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (r : Compl
ex) : ((a : Complex) / (b : Complex)) ^ r = (a : Complex) ^ r / (b : Complex) ^ 
r
参数：ha : 0 <= a；hb : 0 <= b；r : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.mul_cpow_ofReal_nonneg`：mul_cpow_ofReal_nonneg {a b : Real} (ha 
: 0 <= a) (hb : 0 <= b) (r : Complex) : ((a : Complex) * (b : Complex)) ^ r = (a
 : Complex) ^ r * (b…
· 使用定理 `inv_nonneg_of_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_
1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a → 0 ≤ a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Complex.inv_cpow_ofReal_nonneg`：inv_cpow_ofReal_nonneg {a : Real} (ha : 
0 <= a) (r : Complex) : ((a : Complex)⁻¹) ^ r = (a ^ r : Complex)⁻¹
-/
lemma div_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) / (b : ℂ)) ^ r = (a : ℂ) ^ r / (b : ℂ) ^ r := by
  rw [div_eq_mul_inv, ← ofReal_inv, mul_cpow_ofReal_nonneg ha (inv_nonneg_of_nonneg hb),
    ofReal_inv, inv_cpow_ofReal_nonneg hb, div_eq_mul_inv]

/-- `Complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
/-
**Complex.inv_cpow_eq_ite'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：inv_cpow_eq_ite' (x : Complex) (n : Complex) : (x ^ n)⁻¹ = if x.arg = π th
en conj (x⁻¹ ^ conj n) else x⁻¹ ^ n
参数：x : Complex；n : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.inv_cpow_eq_ite`：inv_cpow_eq_ite (x : Complex) (n : Complex) : x
⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Complex.inv_cpow`：inv_cpow (x : Complex) (n : Complex) (hx : x.arg != π)
 : x⁻¹ ^ n = (x ^ n)⁻¹

--- 原说明 ---
`Complex.inv_cpow_eq_ite` with the `ite` on the other side.
-/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n := by
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj]
  split_ifs with h
  · rfl
  · rw [inv_cpow _ _ h]
/-
**Complex.conj_cpow_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_cpow_eq_ite (x : Complex) (n : Complex) : conj x ^ n = if x.arg = π t
hen x ^ n else conj (x ^ conj n)
参数：x : Complex；n : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.log_conj_eq_ite`：log_conj_eq_ite (x : Complex) : log (conj x) = 
if x.arg = π then log x else conj (log x)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) := by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl
/-
**Complex.conj_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：conj_cpow (x : Complex) (n : Complex) (hx : x.arg != π) : conj x ^ n = con
j (x ^ conj n)
参数：x : Complex；n : Complex；hx : x.arg != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.conj_cpow_eq_ite`：conj_cpow_eq_ite (x : Complex) (n : Complex) :
 conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, if_neg hx]
/-
**Complex.cpow_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_conj (x : Complex) (n : Complex) (hx : x.arg != π) : x ^ conj n = con
j (conj x ^ n)
参数：x : Complex；n : Complex；hx : x.arg != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.conj_cpow`：conj_cpow (x : Complex) (n : Complex) (hx : x.arg != 
π) : conj x ^ n = conj (x ^ conj n)
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
-/
theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]
/-
**Complex.natCast_add_one_cpow_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：natCast_add_one_cpow_ne_zero (n : Nat) (z : Complex) : (n + 1 : Complex) ^
 z != 0
参数：n : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.cpow_eq_zero_iff`：cpow_eq_zero_iff (x y : Complex) : x ^ y = 0 ↔
 x = 0 ∧ y != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma natCast_add_one_cpow_ne_zero (n : ℕ) (z : ℂ) : (n + 1 : ℂ) ^ z ≠ 0 :=
  mt (cpow_eq_zero_iff ..).mp fun H ↦ by norm_cast at H; exact H.1

end Complex

-- section Tactics

-- /-!
-- ## Tactic extensions for complex powers
-- -/


-- namespace NormNum

-- theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
--   rw [← h, hb, Complex.cpow_natCast]

-- theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
--     a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_natCast]

-- open Tactic

-- /-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
-- unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
--   let na ← a.to_rat
--   let icα ← mk_instance_cache α
--   let icβ ← mk_instance_cache β
--   match match_sign b with
--     | Sum.inl b => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
--       let (icα, c, h) ← prove_pow a na icα b'
--       let cr ← c
--       let (icα, c', hc) ← prove_inv icα c cr
--       pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
--     | Sum.inr ff => pure (one, expr.const zero [] a)
--     | Sum.inr tt => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
--       let (icα, c, h) ← prove_pow a na icα b'
--       pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])

-- /-- Evaluate `Complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))

-- /-- Evaluates expressions of the form `cpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_cpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
--   | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
--   | _ => tactic.failed

-- end NormNum

-- end Tactics

