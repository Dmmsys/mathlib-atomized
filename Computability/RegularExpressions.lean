/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Tactic.AdaptationNote

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regexes used in
computer science such as the POSIX standard.

## TODO

Currently, we do not show that regular expressions and DFAs/NFAs are equivalent.
Multiple competing PRs towards that goal are in review.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Regular.20languages.3A.20the.20review.20queue
-/

@[expose] public section

open List Set

open Computability

universe u

variable {α β γ : Type*}

-- Disable generation of unneeded lemmas which the simpNF linter would complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- This is the definition of regular expressions. The names used here are meant to mirror the
[definition of a Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings that match `P`
* `P + Q` (`plus P Q`) matches anything that matches `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
/-
**RegularExpression** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the definition of regular expressions. The names used here are meant to 
mirror the
[definition of a Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings that match `P`
* `P + Q` (`plus P Q`) matches anything that matches `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α

namespace RegularExpression

variable {a b : α}

/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RegularExpression α) :=
  ⟨zero⟩
/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (RegularExpression α) :=
  ⟨plus⟩
/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (RegularExpression α) :=
  ⟨comp⟩
/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (RegularExpression α) :=
  ⟨epsilon⟩
/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (RegularExpression α) :=
  ⟨zero⟩
/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (RegularExpression α) ℕ :=
  ⟨fun n r => npowRec r n⟩

@[simp]
/-
**RegularExpression.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：zero_def : (zero : RegularExpression α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl

@[simp]
/-
**RegularExpression.one_def** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：one_def : (epsilon : RegularExpression α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl

@[simp]
/-
**RegularExpression.plus_def** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：plus_def (P Q : RegularExpression α) : plus P Q = P + Q
参数：P Q : RegularExpression α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q :=
  rfl

@[simp]
/-
**RegularExpression.comp_def** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：comp_def (P Q : RegularExpression α) : comp P Q = P * Q
参数：P Q : RegularExpression α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q :=
  rfl

/-- `matches' P` provides a language which contains all strings that `P` matches.

Not named `matches` since that is a reserved word.
-/
@[simp]
/-
**RegularExpression.matches'** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：matches'_zero : (0 : RegularExpression α).matches' = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`matches' P` provides a language which contains all strings that `P` matches.

Not named `matches` since that is a reserved word.
-/
def matches' : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'
  | star P => P.matches'∗
/-
**RegularExpression.matches'_zero** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1}, RegularExpression.matches' 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_zero : (0 : RegularExpression α).matches' = 0 :=
  rfl
/-
**RegularExpression.matches'_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpressio
n`。
形式化陈述：∀ {α : Type u_1}, RegularExpression.matches' 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_epsilon : (1 : RegularExpression α).matches' = 1 :=
  rfl
/-
**RegularExpression.matches'_char** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} (a : α), (RegularExpression.char a).matches' = {[a]}
参数：a : α；RegularExpression.char a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_char (a : α) : (char a).matches' = {[a]} :=
  rfl
/-
**RegularExpression.matches'_add** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} (P Q : RegularExpression α), (P + Q).matches' = P.matches
' + Q.matches'
参数：P Q : RegularExpression α；P + Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_add (P Q : RegularExpression α) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl
/-
**RegularExpression.matches'_mul** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} (P Q : RegularExpression α), (P * Q).matches' = P.matches
' * Q.matches'
参数：P Q : RegularExpression α；P * Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_mul (P Q : RegularExpression α) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl

@[simp]
/-
**RegularExpression.matches'_pow** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} (P : RegularExpression α) (n : ℕ), (P ^ n).matches' = P.m
atches' ^ n
参数：P : RegularExpression α；n : ℕ；P ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).matches' = P.matches' ^ n
  | 0 => matches'_epsilon
  | n + 1 => (matches'_mul _ _).trans <| Eq.trans
      (congrFun (congrArg HMul.hMul (matches'_pow P n)) (matches' P))
      (pow_succ _ n).symm
/-
**RegularExpression.matches'_star** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} (P : RegularExpression α), P.star.matches' = KStar.kstar 
P.matches'
参数：P : RegularExpression α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
-/
theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ :=
  rfl

/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
/-
**RegularExpression.matchEpsilon** 是 Mathlib 中的一个定义，位于命名空间 `RegularExpression`。
形式化陈述：{α : Type u_1} → RegularExpression α → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`matchEpsilon P` is true if and only if `P` matches the empty string
-/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true

section DecidableEq
variable [DecidableEq α]

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
/-
**RegularExpression.deriv** 是 Mathlib 中的一个定义，位于命名空间 `RegularExpression`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → RegularExpression α → α → RegularExpres
sion α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P
` with respect
  to `a`
-/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

@[simp]
/-
**RegularExpression.deriv_zero** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：deriv_zero (a : α) : deriv 0 a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deriv_zero (a : α) : deriv 0 a = 0 :=
  rfl

@[simp]
/-
**RegularExpression.deriv_one** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：deriv_one (a : α) : deriv 1 a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deriv_one (a : α) : deriv 1 a = 0 :=
  rfl

@[simp]
/-
**RegularExpression.deriv_char_self** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression
`。
形式化陈述：deriv_char_self (a : α) : deriv (char a) a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem deriv_char_self (a : α) : deriv (char a) a = 1 :=
  if_pos rfl

@[simp]
/-
**RegularExpression.deriv_char_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpressio
n`。
形式化陈述：deriv_char_of_ne (h : a != b) : deriv (char a) b = 0
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 :=
  if_neg h

@[simp]
/-
**RegularExpression.deriv_add** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P 
a + deriv Q a
参数：P Q : RegularExpression α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

@[simp]
/-
**RegularExpression.deriv_star** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a 
* star P
参数：P : RegularExpression α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P :=
  rfl

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches'`. -/
/-
**RegularExpression.rmatch** 是 Mathlib 中的一个定义，位于命名空间 `RegularExpression`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → RegularExpression α → List α → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`P.rmatch x` is true if and only if `P` matches `x`. This is a computable defini
tion equivalent
  to `matches'`.
-/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

@[simp]
/-
**RegularExpression.zero_rmatch** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：zero_rmatch (x : List α) : rmatch 0 x = false
参数：x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem zero_rmatch (x : List α) : rmatch 0 x = false := by
  induction x <;> simp [rmatch, matchEpsilon, *]
/-
**RegularExpression.one_rmatch_iff** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`
。
形式化陈述：one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = []
参数：x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RegularExpression.zero_rmatch`：zero_rmatch (x : List α) : rmatch 0 x = f
alse
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [rmatch, matchEpsilon, *]
/-
**RegularExpression.char_rmatch_iff** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression
`。
形式化陈述：char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a]
参数：a : α；x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RegularExpression.rmatch.eq_2`：∀ {α : Type u_1} [inst : DecidableEq α] (
x : RegularExpression α) (a : α) (as : List α),   x.rmatch (a :: as) = (x.deriv 
a).rmatch as
· 使用定理 `RegularExpression.deriv.eq_3`：∀ {α : Type u_1} [inst : DecidableEq α] (x
 a₁ : α), (RegularExpression.char a₁).deriv x = if a₁ = x then 1 else 0
· 使用定理 `List.singleton_inj`：∀ {α : Type u_1} {a b : α}, [a] = [b] ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RegularExpression.rmatch.congr_simp`：∀ {α : Type u_1} {inst : DecidableE
q α} [inst_1 : DecidableEq α] (a a_1 : RegularExpression α),   a = a_1 → ∀ (a_2 
a_3 : List α), a_2 = a_3 …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `RegularExpression.zero_rmatch`：zero_rmatch (x : List α) : rmatch 0 x = f
alse
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by
  rcases x with - | ⟨_, x⟩
  · exact of_decide_eq_true rfl
  · rcases x with - | ⟨head, tail⟩
    · rw [rmatch, deriv, List.singleton_inj]
      split <;> tauto
    · rw [rmatch, rmatch, deriv, cons.injEq]
      split
      · simp_rw [deriv_one, zero_rmatch, reduceCtorEq, and_false]
      · simp_rw [deriv_zero, zero_rmatch, reduceCtorEq, and_false]
/-
**RegularExpression.add_rmatch_iff** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`
。
形式化陈述：add_rmatch_iff (P Q : RegularExpression α) (x : List α) : (P + Q).rmatch x
 ↔ P.rmatch x ∨ Q.rmatch x
参数：P Q : RegularExpression α；x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `RegularExpression.rmatch.eq_2`：∀ {α : Type u_1} [inst : DecidableEq α] (
x : RegularExpression α) (a : α) (as : List α),   x.rmatch (a :: as) = (x.deriv 
a).rmatch as
· 使用定理 `RegularExpression.deriv_add`：deriv_add (P Q : RegularExpression α) (a : 
α) : deriv (P + Q) a = deriv P a + deriv Q a
-/
theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  induction x generalizing P Q with
  | nil => simp only [rmatch, matchEpsilon, Bool.or_eq_true_iff]
  | cons _ _ ih =>
    rw [rmatch, deriv_add]
    exact ih _ _
/-
**RegularExpression.mul_rmatch_iff** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`
。
形式化陈述：mul_rmatch_iff (P Q : RegularExpression α) (x : List α) : (P * Q).rmatch x
 ↔ exists t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u
参数：P Q : RegularExpression α；x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RegularExpression.rmatch.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (
x : RegularExpression α), x.rmatch [] = x.matchEpsilon
· 使用定理 `Bool.and_eq_true_iff`：∀ {x y : Bool}, (x && y) = true ↔ x = true ∧ y = t
rue
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.append_eq_nil_iff`：∀ {α : Type u_1} {p q : List α}, p ++ q = [] ↔ p
 = [] ∧ q = []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bool.and_self`：∀ (b : Bool), (b && b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RegularExpression.rmatch.eq_2`：∀ {α : Type u_1} [inst : DecidableEq α] (
x : RegularExpression α) (a : α) (as : List α),   x.rmatch (a :: as) = (x.deriv 
a).rmatch as
· 使用定理 `RegularExpression.rmatch.congr_simp`：∀ {α : Type u_1} {inst : DecidableE
q α} [inst_1 : DecidableEq α] (a a_1 : RegularExpression α),   a = a_1 → ∀ (a_2 
a_3 : List α), a_2 = a_3 …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `RegularExpression.add_rmatch_iff`：add_rmatch_iff (P Q : RegularExpressio
n α) (x : List α) : (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.cons_eq_cons`：∀ {α : Type u_1} {a b : α} {l l' : List α}, a :: l = 
b :: l' ↔ a = b ∧ l = l'
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by
  induction x generalizing P Q with
  | nil =>
    rw [rmatch]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatch, rmatch]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h₁.symm
      repeat rw [rmatch] at h₂
      simp [h₂]
  | cons a x ih =>
    rw [rmatch]; simp only [deriv]
    split_ifs with hepsilon
    · rw [add_rmatch_iff, ih]
      constructor
      · rintro (⟨t, u, _⟩ | h)
        · exact ⟨a :: t, u, by tauto⟩
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
      · rintro ⟨t, u, h, hP, hQ⟩
        rcases t with - | ⟨b, t⟩
        · right
          rw [List.nil_append] at h
          rw [← h] at hQ
          exact hQ
        · left
          rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert! hP
          exact h.1
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact ⟨a :: t, u, by tauto⟩
      · rcases t with - | ⟨b, t⟩
        · contradiction
        · rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert! hP
          exact h.1
/-
**RegularExpression.star_rmatch_iff** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression
`。
形式化陈述：star_rmatch_iff (P : RegularExpression α) : forall x : List α, (star P).rm
atch x ↔ exists S : List (List α), x = S.flatten ∧ forall t in S, t != [] ∧ P.rm
atch t
参数：P : RegularExpression α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RegularExpression.rmatch.eq_2`：∀ {α : Type u_1} [inst : DecidableEq α] (
x : RegularExpression α) (a : α) (as : List α),   x.rmatch (a :: as) = (x.deriv 
a).rmatch as
· 使用定理 `RegularExpression.deriv.eq_6`：∀ {α : Type u_1} [inst : DecidableEq α] (x
 : α) (P : RegularExpression α), P.star.deriv x = P.deriv x * P.star
· 使用定理 `RegularExpression.mul_rmatch_iff`：mul_rmatch_iff (P Q : RegularExpressio
n α) (x : List α) : (P * Q).rmatch x ↔ exists t u : List α, x = t ++ u ∧ P.rmatc
h t ∧ Q.rmatch u
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x
          = S.flatten ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t :=
  fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · rcases x with - | ⟨a, x⟩
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          lia
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases ht' with
          | head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatch, reduceCtorEq]
            exact ht
          | tail _ ht' => exact helem t' ht'
    · rintro ⟨S, hsum, helem⟩
      rcases x with - | ⟨a, x⟩
      · rfl
      · rw [rmatch, deriv, mul_rmatch_iff]
        rcases S with - | ⟨t', U⟩
        · exact ⟨[], [], by tauto⟩
        · obtain - | ⟨b, t⟩ := t'
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [not_true, Ne, false_and] at helem
          simp only [List.flatten_cons, List.cons_append, List.cons_eq_cons] at hsum
          refine ⟨t, U.flatten, hsum.2, ?_, ?_⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatch] at helem
            convert! helem.2
            exact hsum.1
          · grind
  termination_by t => (P, t.length)

@[simp]
/-
**RegularExpression.rmatch_iff_matches'** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpres
sion`。
形式化陈述：rmatch_iff_matches' (P : RegularExpression α) (x : List α) : P.rmatch x ↔ 
x in P.matches'
参数：P : RegularExpression α；x : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RegularExpression.zero_def`：zero_def : (zero : RegularExpression α) = 0
· 使用定理 `RegularExpression.zero_rmatch`：zero_rmatch (x : List α) : rmatch 0 x = f
alse
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `RegularExpression.one_def`：one_def : (epsilon : RegularExpression α) = 1
· 使用定理 `RegularExpression.one_rmatch_iff`：one_rmatch_iff (x : List α) : rmatch 1
 x ↔ x = []
· 使用定理 `RegularExpression.matches'_epsilon`：∀ {α : Type u_1}, RegularExpression.
matches' 1 = 1
· 使用定理 `Language.mem_one`：mem_one (x : List α) : x in (1 : Language α) ↔ x = []
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `RegularExpression.char_rmatch_iff`：char_rmatch_iff (a : α) (x : List α) 
: rmatch (char a) x ↔ x = [a]
· 使用定理 `RegularExpression.plus_def`：plus_def (P Q : RegularExpression α) : plus 
P Q = P + Q
· 使用定理 `RegularExpression.add_rmatch_iff`：add_rmatch_iff (P Q : RegularExpressio
n α) (x : List α) : (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rmatch_iff_matches' (P : RegularExpression α) (x : List α) :
    P.rmatch x ↔ x ∈ P.matches' := by
  induction P generalizing x with
  | zero =>
    rw [zero_def, zero_rmatch]
    tauto
  | epsilon =>
    rw [one_def, one_rmatch_iff, matches'_epsilon, Language.mem_one]
  | char =>
    rw [char_rmatch_iff]
    rfl
  | plus _ _ ih₁ ih₂ =>
    rw [plus_def, add_rmatch_iff, ih₁, ih₂]
    rfl
  | comp P Q ih₁ ih₂ =>
    simp only [comp_def, mul_rmatch_iff, matches'_mul, Language.mem_mul, *]
    tauto
  | star _ ih =>
    simp only [star_rmatch_iff, matches'_star, ih, Language.mem_kstar_iff_exists_nonempty, and_comm]
/-
**RegularExpression.** 是 Mathlib 中的一个实例，位于命名空间 `RegularExpression`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches') := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

end DecidableEq

/-- Map the alphabet of a regular expression. -/
@[simp]
/-
**RegularExpression.map** 是 Mathlib 中的一个定义，位于命名空间 `RegularExpression`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → RegularExpression α → RegularE
xpression β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map the alphabet of a regular expression.
-/
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | R * S => map f R * map f S
  | star R => star (map f R)

@[simp]
/-
**RegularExpression.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (P : RegularExpression α) (n :
 ℕ),   RegularExpression.map f (P ^ n) = RegularExpression.map f P ^ n
参数：f : α → β；P : RegularExpression α；n : ℕ；P ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => by unfold map; rfl
  | n + 1 => (congr_arg (· * map f P) (RegularExpression.map_pow f P n) :)

@[simp]
/-
**RegularExpression.map_id** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} (P : RegularExpression α), RegularExpression.map id P = P
参数：P : RegularExpression α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | char _ => rfl
  | R + S => by simp_rw [map, map_id]
  | R * S => by simp_rw [map, map_id]
  | star R => by simp_rw [map, map_id]

@[simp]
/-
**RegularExpression.map_map** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (g : β → γ) (f : α → β) (P 
: RegularExpression α),   RegularExpression.map g (RegularExpression.map f P) = 
RegularExpression.map (g ∘ f) P
参数：g : β → γ；f : α → β；P : RegularExpression α；RegularExpression.map f P；g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | char _ => rfl
  | R + S => by simp only [map, map_map]
  | R * S => by simp only [map, map_map]
  | star R => by simp only [map, map_map]

/-- The language of the map is the map of the language. -/
@[simp]
/-
**RegularExpression.matches'_map** 是 Mathlib 中的一个定理，位于命名空间 `RegularExpression`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (P : RegularExpression α),   (
RegularExpression.map f P).matches' = (Language.map f) P.matches'
参数：f : α → β；P : RegularExpression α；RegularExpression.map f P；Language.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularExpression.matches'`：matches'_zero : (0 : RegularExpression α).ma
tches' = 0

--- 原说明 ---
The language of the map is the map of the language.
-/
theorem matches'_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    exact image_singleton
  | R + S => by simp only [matches'_map, map, matches'_add, map_add]
  | R * S => by simp [matches'_map]
  | star R => by simp [matches'_map]

end RegularExpression

