/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Synonym
public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Structures involving `*` and `0` on `WithTop` and `WithBot`
The main results of this section are `WithTop.instOrderedCommSemiring` and
`WithBot.instOrderedCommSemiring`.
-/

@[expose] public section

variable {α : Type*}

namespace WithTop

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithTop α}

/-
**WithTop.instMulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → [MulZeroClass α] → MulZeroClass (WithTo
p α)
参数：WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass : MulZeroClass (WithTop α) where
  mul
    | (a : α), (b : α) => ↑(a * b)
    | (a : α), ⊤ => if a = 0 then 0 else ⊤
    | ⊤, (b : α) => if b = 0 then 0 else ⊤
    | ⊤, ⊤ => ⊤
  mul_zero
    | (a : α) => congr_arg some <| mul_zero _
    | ⊤ => if_pos rfl
  zero_mul
    | (b : α) => congr_arg some <| zero_mul _
    | ⊤ => if_pos rfl
/-
**WithTop.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] (a b : α
), ↑(a * b) = ↑a * ↑b
参数：a b : α；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithTop α) = a * b := rfl
/-
**WithTop.mul_top'** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] (a : Wit
hTop α), a * ⊤ = if a = 0 then 0 else ⊤
参数：a : WithTop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `WithTop.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `WithTop.top_ne_zero`：∀ {α : Type u} [inst : Zero α], ⊤ ≠ 0
-/
lemma mul_top' : ∀ (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm
/-
**WithTop.mul_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {a : Wit
hTop α}, a ≠ 0 → a * ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.mul_top'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma mul_top (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]
/-
**WithTop.top_mul'** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] (b : Wit
hTop α), ⊤ * b = if b = 0 then 0 else ⊤
参数：b : WithTop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `WithTop.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `WithTop.top_ne_zero`：∀ {α : Type u} [inst : Zero α], ⊤ ≠ 0
-/
lemma top_mul' : ∀ (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm
/-
**WithTop.top_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {b : Wit
hTop α}, b ≠ 0 → ⊤ * b = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.top_mul'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma top_mul (hb : b ≠ 0) : ⊤ * b = ⊤ := by rw [top_mul', if_neg hb]
/-
**WithTop.top_mul_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α], ⊤ * ⊤ =
 ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ := rfl
/-
**WithTop.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：mul_def (a b : WithTop α) : a * b = if a = 0 ∨ b = 0 then 0 else WithTop.m
ap₂ (· * ·) a b
参数：a b : WithTop α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `WithTop.map₂_top_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (
f : α → β → γ) (a : WithTop α), WithTop.map₂ f a ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `WithTop.map₂_coe_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (
f : α → β → γ) (a : WithTop α) (b : β),   WithTop.map₂ f a ↑b = WithTop.map (fun
 x => f x b)…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma mul_def (a b : WithTop α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop
/-
**WithTop.mul_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：mul_eq_top_iff : a * b = ⊤ ↔ a != 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithTop.mul_def`：mul_def (a b : WithTop α) : a * b = if a = 0 ∨ b = 0 th
en 0 else WithTop.map₂ (· * ·) a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `WithTop.map₂_top_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (
f : α → β → γ) (a : WithTop α), WithTop.map₂ f a ⊤ = ⊤
-/
lemma mul_eq_top_iff : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by rw [mul_def]; aesop
/-
**WithTop.mul_coe_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {b : α},
   b ≠ 0 → ∀ (a : WithTop α), a * ↑b = Option.bind a fun a => some (a * b)
参数：a : WithTop α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithTop α) = a.bind fun a ↦ ↑(a * b)
  | ⊤ => by simp [top_mul, hb]; rfl
  | (a : α) => rfl
/-
**WithTop.coe_mul_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {a : α},
   a ≠ 0 → ∀ (b : WithTop α), ↑a * b = Option.bind b fun b => some (a * b)
参数：b : WithTop α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithTop α) = b.bind fun b ↦ ↑(a * b)
  | ⊤ => by simp [ha]; rfl
  | (b : α) => rfl

@[simp]
/-
**WithTop.untopD_zero_mul** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：untopD_zero_mul (a b : WithTop α) : (a * b).untopD 0 = a.untopD 0 * b.unto
pD 0
参数：a b : WithTop α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `WithTop.untopD_coe`：∀ {α : Type u_5} (d x : α), WithTop.untopD d ↑x = x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
· 使用定理 `WithTop.untopD_top`：∀ {α : Type u_5} (d : α), WithTop.untopD d ⊤ = d
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `WithTop.coe_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] (a b : α), ↑(a * b) = ↑a * ↑b
-/
lemma untopD_zero_mul (a b : WithTop α) : (a * b).untopD 0 = a.untopD 0 * b.untopD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untopD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untopD_coe, mul_zero]
  cases a; · rw [top_mul hb, untopD_top, zero_mul]
  cases b; · rw [mul_top ha, untopD_top, mul_zero]
  rw [← coe_mul, untopD_coe, untopD_coe, untopD_coe]
/-
**WithTop.mul_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：mul_ne_top {a b : WithTop α} (ha : a != ⊤) (hb : b != ⊤) : a * b != ⊤
参数：ha : a != ⊤；hb : b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mul_ne_top {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b ≠ ⊤ := by
  simp [mul_eq_top_iff, *]
/-
**WithTop.mul_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤
参数：ha : a < ⊤；hb : b < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.lt_top_iff_ne_top`：∀ {α : Type u_1} [inst : LT α] {x : WithTop α
}, x < ⊤ ↔ x ≠ ⊤
· 使用定理 `WithTop.mul_ne_top`：mul_ne_top {a b : WithTop α} (ha : a != ⊤) (hb : b !
= ⊤) : a * b != ⊤
-/
theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  exact mul_ne_top ha hb
/-
**WithTop.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.mem_map₂_iff`：mem_map₂_iff {c : γ} : c in map₂ f a b ↔ exists a' 
b', a' in a ∧ b' in b ∧ f a' b' = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `WithTop.mul_def`：mul_def (a b : WithTop α) : a * b = if a = 0 ∨ b = 0 th
en 0 else WithTop.map₂ (· * ·) a b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithTop α) := by
  refine ⟨fun h₁ => Decidable.byContradiction fun h₂ => ?_⟩
  rw [mul_def, if_neg h₂] at h₁
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, (rfl : _ = _), (rfl : _ = _), hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

variable [Preorder α]
/-
**WithTop.mul_right_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {a : Wit
hTop α} [inst_2 : Preorder α]   [PosMulStrictMono α], 0 < a → a ≠ ⊤ → StrictMono
 fun x => a * x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
protected lemma mul_right_strictMono [PosMulStrictMono α] (h₀ : 0 < a) (hinf : a ≠ ⊤) :
    StrictMono (a * ·) := by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, mul_top h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  exact mul_lt_mul_of_pos_left hbc h₀
/-
**WithTop.mul_left_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {a : Wit
hTop α} [inst_2 : Preorder α]   [MulPosStrictMono α], 0 < a → a ≠ ⊤ → StrictMono
 fun x => x * a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
protected lemma mul_left_strictMono [MulPosStrictMono α] (h₀ : 0 < a) (hinf : a ≠ ⊤) :
    StrictMono (· * a) := by
  lift a to α using hinf
  rintro b c hbc
  lift b to α using hbc.ne_top
  match c with
  | ⊤ => simp [← coe_mul, top_mul h₀.ne']
  | (c : α) =>
  simp only [coe_pos, coe_lt_coe, ← coe_mul, gt_iff_lt] at *
  gcongr

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
/-
**WithTop.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (
WithTop α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ =
 0`.
-/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) where
  __ := instMulZeroClass
  one_mul
    | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
  mul_one
    | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
    | (a : α) => by rw [← coe_one, ← coe_mul, mul_one]

/-- A version of `WithTop.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
/-
**WithTop._root_.MonoidWithZeroHom.withTopMap** 是 Mathlib 中的一个定义，位于命名空间 `WithTop
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.map` for `MonoidWithZeroHom`s.
-/
protected def _root_.MonoidWithZeroHom.withTopMap {R S : Type*} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTopMap, f.toMonoidHom.toOneHom.withTopMap with
    toFun := WithTop.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.toZeroHom.withTopMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      cases x with | top => simp [hy, this] | coe x => ?_
      cases y with
      | top =>
        have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [mul_top hx, mul_top this]
      | coe y => simp [← coe_mul] }
/-
**WithTop.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] : Semigroup
WithZero (WithTop α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithTop α) where
  __ := instMulZeroClass
  mul_assoc a b c := by
    rcases eq_or_ne a 0 with (rfl | ha); · simp only [zero_mul]
    rcases eq_or_ne b 0 with (rfl | hb); · simp only [zero_mul, mul_zero]
    rcases eq_or_ne c 0 with (rfl | hc); · simp only [mul_zero]
    cases a with | top => simp [hb, hc] | coe a => ?_
    cases b with | top => simp [mul_top ha, top_mul hc] | coe b => ?_
    cases c with
    | top =>
      rw [mul_top hb, mul_top ha]
      rw [← coe_zero, ne_eq, coe_eq_coe] at ha hb
      simp [ha, hb]
    | coe c => simp only [← coe_mul, mul_assoc]

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : ℕ}

/-
**WithTop.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instMonoidWithZero : MonoidWithZero (WithTop α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero : MonoidWithZero (WithTop α) where
  __ := instMulZeroOneClass
  __ := instSemigroupWithZero
  npow n a := match a, n with
    | (a : α), n => ↑(a ^ n)
    | ⊤, 0 => 1
    | ⊤, _n + 1 => ⊤
  npow_zero a := by simp_rw [HPow.hPow, Pow.pow]; cases a <;> simp
  npow_succ n a := by simp_rw [HPow.hPow, Pow.pow]; cases n <;> cases a <;> simp [pow_succ]
/-
**WithTop.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MonoidWithZero α] [inst_
2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   (a : α) (n : ℕ), ↑(a ^ n) = ↑a ^
 n
参数：a : α；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithTop α) = a ^ n := rfl
/-
**WithTop.top_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MonoidWithZero α] [inst_
2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_pow : ∀ {n : ℕ}, n ≠ 0 → (⊤ : WithTop α) ^ n = ⊤ | _ + 1, _ => rfl
/-
**WithTop.pow_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MonoidWithZero α] [inst_
2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : WithTop α} {n : ℕ}, x ^ n =
 ⊤ ↔ x = ⊤ ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.top_pow`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Monoi
dWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {n : ℕ}, n ≠ 
0 → ⊤…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
@[simp] lemma pow_eq_top_iff : x ^ n = ⊤ ↔ x = ⊤ ∧ n ≠ 0 := by
  cases x <;> cases n <;> simp [← coe_pow]
/-
**WithTop.pow_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：pow_ne_top_iff : x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_ne_top_iff : x ^ n ≠ ⊤ ↔ x ≠ ⊤ ∨ n = 0 := by simp [pow_eq_top_iff, or_iff_not_imp_left]
/-
**WithTop.pow_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MonoidWithZero α] [inst_
2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : WithTop α} {n : ℕ} [inst_4 
: Preorder α], x ^ n < ⊤ ↔ x < ⊤ ∨ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma pow_lt_top_iff [Preorder α] : x ^ n < ⊤ ↔ x < ⊤ ∨ n = 0 := by
  simp_rw [WithTop.lt_top_iff_ne_top, pow_ne_top_iff]
/-
**WithTop.eq_top_of_pow** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：eq_top_of_pow (n : Nat) (hx : x ^ n = ⊤) : x = ⊤
参数：n : Nat；hx : x ^ n = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.pow_eq_top_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MonoidWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : W
ithTop α} {n…
-/
lemma eq_top_of_pow (n : ℕ) (hx : x ^ n = ⊤) : x = ⊤ := (pow_eq_top_iff.1 hx).1
/-
**WithTop.pow_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：pow_ne_top (hx : x != ⊤) : x ^ n != ⊤
参数：hx : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithTop.pow_ne_top_iff`：pow_ne_top_iff : x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0
-/
lemma pow_ne_top (hx : x ≠ ⊤) : x ^ n ≠ ⊤ := pow_ne_top_iff.2 <| .inl hx
/-
**WithTop.pow_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：pow_lt_top [Preorder α] (hx : x < ⊤) : x ^ n < ⊤
参数：hx : x < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.pow_lt_top_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MonoidWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : W
ithTop α} {n…
-/
lemma pow_lt_top [Preorder α] (hx : x < ⊤) : x ^ n < ⊤ := pow_lt_top_iff.2 <| .inl hx

end MonoidWithZero

/-
**WithTop.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivi
al α] : CommMonoidWithZero (WithTop α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) where
  __ := instMonoidWithZero
  mul_comm a b := by simp_rw [mul_def]; exact if_congr or_comm rfl (Option.map₂_comm mul_comm)
/-
**WithTop.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] [PartialOrder 
α] [CanonicallyOrderedAdd α] : NonUnitalNonAssocSemiring (WithTop α) where toAdd
CommMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] : NonUnitalNonAssocSemiring (WithTop α) where
  toAddCommMonoid := WithTop.addCommMonoid
  __ := WithTop.instMulZeroClass
  right_distrib a b c := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [mul_coe_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (add_mul _ _ _)
  left_distrib c a b := by
    cases c with
    | top => by_cases ha : a = 0 <;> simp [ha]
    | coe c =>
      by_cases hc : c = 0; · simp [hc]
      simp only [coe_mul_eq_bind hc]
      cases a <;> cases b <;> try rfl
      exact congr_arg some (mul_add _ _ _)
/-
**WithTop.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instNonAssocSemiring [NonAssocSemiring α] [PartialOrder α] [CanonicallyOrd
eredAdd α] [Nontrivial α] : NonAssocSemiring (WithTop α) where toNonUnitalNonAss
ocSemiring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [NonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [Nontrivial α] : NonAssocSemiring (WithTop α) where
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := WithTop.instMulZeroOneClass
  __ := WithTop.addCommMonoidWithOne
/-
**WithTop.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring α] [PartialOrder α] [CanonicallyO
rderedAdd α] [NoZeroDivisors α] : NonUnitalSemiring (WithTop α) where toNonUnita
lNonAssocSemiring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [NonUnitalSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] : NonUnitalSemiring (WithTop α) where
  toNonUnitalNonAssocSemiring := WithTop.instNonUnitalNonAssocSemiring
  __ := WithTop.instSemigroupWithZero
/-
**WithTop.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instSemiring [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [NoZe
roDivisors α] [Nontrivial α] : Semiring (WithTop α) where toNonUnitalSemiring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : Semiring (WithTop α) where
  toNonUnitalSemiring := WithTop.instNonUnitalSemiring
  __ := WithTop.instMonoidWithZero
  __ := WithTop.addCommMonoidWithOne
/-
**WithTop.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd 
α] [NoZeroDivisors α] [Nontrivial α] : CommSemiring (WithTop α) where toSemiring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : CommSemiring (WithTop α) where
  toSemiring := WithTop.instSemiring
  __ := WithTop.instCommMonoidWithZero
/-
**WithTop.instIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instIsOrderedRing [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd
 α] [NoZeroDivisors α] [Nontrivial α] : IsOrderedRing (WithTop α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CanonicallyOrderedAdd.toIsOrderedRing`：toIsOrderedRing : IsOrderedRing R
 where add_le_add_left _ _
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
-/
instance instIsOrderedRing [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] : IsOrderedRing (WithTop α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- A version of `WithTop.map` for `RingHom`s. -/
@[simps -fullyApplied]
/-
**WithTop._root_.RingHom.withTopMap** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.map` for `RingHom`s.
-/
protected def _root_.RingHom.withTopMap {R S : Type*}
    [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
    [DecidableEq R] [Nontrivial R]
    [NonAssocSemiring S] [PartialOrder S] [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  { MonoidWithZeroHom.withTopMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.withTopMap with }

variable [CommSemiring α] [PartialOrder α] [OrderBot α]
  [CanonicallyOrderedAdd α] [PosMulStrictMono α]
  {a a₁ a₂ b₁ b₂ : WithTop α}

@[gcongr]
/-
**WithTop.mul_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommSemiring α] [inst_2 
: PartialOrder α] [OrderBot α]   [inst_4 : CanonicallyOrderedAdd α] [PosMulStric
tMono α] {a₁ a₂ b₁ b₂ : WithTop α},   a₁ < a₂ → b₁ < b₂ → a₁ * b₁ < a₂ * b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulStrictMono_iff_mulPosStrictMono`：posMulStrictMono_iff_mulPosStrict
Mono : PosMulStrictMono α ↔ MulPosStrictMono α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.lt_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a < ⊤
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `CanonicallyOrderedAdd.mul_lt_mul_of_lt_of_lt`：∀ {R : Type u} [inst : Com
mSemiring R] [inst_1 : PartialOrder R] [CanonicallyOrderedAdd R] [PosMulStrictMo
no R]   {a b c d : R}, a < b → c <…
-/
protected lemma mul_lt_mul (ha : a₁ < a₂) (hb : b₁ < b₂) : a₁ * b₁ < a₂ * b₂ := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  lift a₁ to α using ha.lt_top.ne
  lift b₁ to α using hb.lt_top.ne
  obtain rfl | ha₂ := eq_or_ne a₂ ⊤
  · rw [top_mul (by simpa [bot_eq_zero] using hb.bot_lt.ne')]
    exact coe_lt_top _
  obtain rfl | hb₂ := eq_or_ne b₂ ⊤
  · rw [mul_top (by simpa [bot_eq_zero] using ha.bot_lt.ne')]
    exact coe_lt_top _
  lift a₂ to α using ha₂
  lift b₂ to α using hb₂
  norm_cast at *
  exact CanonicallyOrderedAdd.mul_lt_mul_of_lt_of_lt ha hb

variable [NoZeroDivisors α] [Nontrivial α] {a b : WithTop α}
/-
**WithTop.pow_right_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommSemiring α] [inst_2 
: PartialOrder α] [OrderBot α]   [inst_4 : CanonicallyOrderedAdd α] [PosMulStric
tMono α] [inst_6 : NoZeroDivisors α] [inst_7 : Nontrivial α] {n : ℕ},   n ≠ 0 → 
StrictMono fun a => a ^ n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma pow_right_strictMono : ∀ {n : ℕ}, n ≠ 0 → StrictMono fun a : WithTop α ↦ a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simpa only [pow_one] using! strictMono_id
  | n + 2, _ => fun x y h ↦ by
    simp_rw [pow_succ _ (n + 1)]
    exact WithTop.mul_lt_mul (WithTop.pow_right_strictMono n.succ_ne_zero h) h
/-
**WithTop.pow_lt_pow_left** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommSemiring α] [inst_2 
: PartialOrder α] [OrderBot α]   [inst_4 : CanonicallyOrderedAdd α] [PosMulStric
tMono α] [inst_6 : NoZeroDivisors α] [inst_7 : Nontrivial α]   {a b : WithTop α}
, a < b → ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pow_right_strictMono`：∀ {α : Type u_1} [inst : DecidableEq α] [i
nst_1 : CommSemiring α] [inst_2 : PartialOrder α] [OrderBot α]   [inst_4 : Canon
icallyOrderedAdd α…
-/
@[gcongr] protected lemma pow_lt_pow_left (hab : a < b) {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n :=
  WithTop.pow_right_strictMono hn hab

end WithTop

namespace WithBot

variable [DecidableEq α]

section MulZeroClass
variable [MulZeroClass α] {a b : WithBot α}

/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulZeroClass (WithBot α) := inferInstanceAs <| MulZeroClass (WithTop α)
/-
**WithBot.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] (a b : α
), ↑(a * b) = ↑a * ↑b
参数：a b : α；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithBot α) = a * b := rfl
/-
**WithBot.mul_bot'** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] (a : Wit
hBot α), a * ⊥ = if a = 0 then 0 else ⊥
参数：a : WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `WithBot.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `WithBot.bot_ne_zero`：∀ {α : Type u} [inst : Zero α], ⊥ ≠ 0
-/
lemma mul_bot' : ∀ (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm
/-
**WithBot.mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {a : Wit
hBot α}, a ≠ 0 → a * ⊥ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.mul_bot'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma mul_bot (h : a ≠ 0) : a * ⊥ = ⊥ := by rw [mul_bot', if_neg h]
/-
**WithBot.bot_mul'** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] (b : Wit
hBot α), ⊥ * b = if b = 0 then 0 else ⊥
参数：b : WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `WithBot.coe_eq_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a = 0 ↔ a 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `WithBot.bot_ne_zero`：∀ {α : Type u} [inst : Zero α], ⊥ ≠ 0
-/
lemma bot_mul' : ∀ (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm
/-
**WithBot.bot_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {b : Wit
hBot α}, b ≠ 0 → ⊥ * b = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.bot_mul'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma bot_mul (hb : b ≠ 0) : ⊥ * b = ⊥ := by rw [bot_mul', if_neg hb]
/-
**WithBot.bot_mul_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α], ⊥ * ⊥ =
 ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ := rfl
/-
**WithBot.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：mul_def (a b : WithBot α) : a * b = if a = 0 ∨ b = 0 then 0 else WithBot.m
ap₂ (· * ·) a b
参数：a b : WithBot α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.mul_bot`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithBot α}, a ≠ 0 → a * ⊥ = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `WithBot.map₂_bot_right`：map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a 
⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `WithBot.map₂_coe_right`：map₂_coe_right (f : α -> β -> γ) (a) (b : β) : m
ap₂ f a b = a.map (f · b)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma mul_def (a b : WithBot α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithBot.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop
/-
**WithBot.mul_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：mul_eq_bot_iff : a * b = ⊥ ↔ a != 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithBot.mul_def`：mul_def (a b : WithBot α) : a * b = if a = 0 ∨ b = 0 th
en 0 else WithBot.map₂ (· * ·) a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `WithBot.map₂_bot_right`：map₂_bot_right (f : α -> β -> γ) (a) : map₂ f a 
⊥ = ⊥
-/
lemma mul_eq_bot_iff : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 := by rw [mul_def]; aesop
/-
**WithBot.mul_coe_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {b : α},
   b ≠ 0 → ∀ (a : WithBot α), a * ↑b = Option.bind a fun a => some (a * b)
参数：a : WithBot α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.bot_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithBot α}, b ≠ 0 → ⊥ * b = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithBot α) = a.bind fun a ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, hb, not_false_eq_true, bot_mul]; rfl
  | (a : α) => rfl
/-
**WithBot.coe_mul_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZeroClass α] {a : α},
   a ≠ 0 → ∀ (b : WithBot α), ↑a * b = Option.bind b fun b => some (a * b)
参数：b : WithBot α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.mul_bot`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithBot α}, a ≠ 0 → a * ⊥ = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithBot α) = b.bind fun b ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, ha, not_false_eq_true, mul_bot]; rfl
  | (b : α) => rfl

@[simp]
/-
**WithBot.unbotD_zero_mul** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotD_zero_mul (a b : WithBot α) : (a * b).unbotD 0 = a.unbotD 0 * b.unbo
tD 0
参数：a b : WithBot α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
· 使用定理 `WithBot.unbotD_coe`：unbotD_coe {α} (d x : α) : unbotD d x = x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithBot.bot_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithBot α}, b ≠ 0 → ⊥ * b = ⊥
· 使用定理 `WithBot.unbotD_bot`：unbotD_bot {α} (d : α) : unbotD d ⊥ = d
· 使用定理 `WithBot.mul_bot`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithBot α}, a ≠ 0 → a * ⊥ = ⊥
· 使用定理 `WithBot.coe_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] (a b : α), ↑(a * b) = ↑a * ↑b
-/
lemma unbotD_zero_mul (a b : WithBot α) : (a * b).unbotD 0 = a.unbotD 0 * b.unbotD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbotD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbotD_coe, mul_zero]
  cases a; · rw [bot_mul hb, unbotD_bot, zero_mul]
  cases b; · rw [mul_bot ha, unbotD_bot, mul_zero]
  rw [← coe_mul, unbotD_coe, unbotD_coe, unbotD_coe]
/-
**WithBot.mul_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：mul_ne_bot {a b : WithBot α} (ha : a != ⊥) (hb : b != ⊥) : a * b != ⊥
参数：ha : a != ⊥；hb : b != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_ne_top`：mul_ne_top {a b : WithTop α} (ha : a != ⊤) (hb : b !
= ⊤) : a * b != ⊤
-/
theorem mul_ne_bot {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a * b ≠ ⊥ :=
  WithTop.mul_ne_top (α := αᵒᵈ) ha hb
/-
**WithBot.bot_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：bot_lt_mul [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b
参数：ha : ⊥ < a；hb : ⊥ < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_lt_top`：mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb
 : b < ⊤) : a * b < ⊤
-/
theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  WithTop.mul_lt_top (α := αᵒᵈ) ha hb
/-
**WithBot.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNoZeroDivisors [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  inferInstanceAs <| NoZeroDivisors (WithTop α)

end MulZeroClass

/-- `Nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
/-
**WithBot.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (
WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥
 = 0`.
-/
instance instMulZeroOneClass [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  inferInstanceAs <| MulZeroOneClass (WithTop α)
/-
**WithBot.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] : Semigroup
WithZero (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero α] [NoZeroDivisors α] :
    SemigroupWithZero (WithBot α) :=
  inferInstanceAs <| SemigroupWithZero (WithTop α)

section MonoidWithZero
variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α]

/-
**WithBot.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instMonoidWithZero : MonoidWithZero (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero : MonoidWithZero (WithBot α) :=
  inferInstanceAs <| MonoidWithZero (WithTop α)
/-
**WithBot.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MonoidWithZero α] [inst_
2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   (a : α) (n : ℕ), ↑(a ^ n) = ↑a ^
 n
参数：a : α；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithBot α) = a ^ n := rfl

end MonoidWithZero

/-
**WithBot.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivi
al α] : CommMonoidWithZero (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidWithZero [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  inferInstanceAs <| CommMonoidWithZero (WithTop α)
/-
**WithBot.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd 
α] [NoZeroDivisors α] [Nontrivial α] : CommSemiring (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] [Nontrivial α] :
    CommSemiring (WithBot α) :=
  inferInstanceAs <| CommSemiring (WithTop α)
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) where
  mul_le_mul_of_nonneg_left x x0 a b h := by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [mul_bot x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_left h x0
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) where
  mul_le_mul_of_nonneg_right x x0 a b h := by
    rcases eq_or_ne x 0 with rfl | x0'
    · simp
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases a
    · simp_rw [bot_mul x0', bot_le]
    cases b
    · exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact mul_le_mul_of_nonneg_right h x0
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) where
  mul_lt_mul_of_pos_left x x0 a b h := by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact mul_lt_mul_of_pos_left h x0
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) where
  mul_lt_mul_of_pos_right x x0 a b h := by
    lift x to α using x0.ne_bot
    cases b
    · exact absurd h not_lt_bot
    cases a
    · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    gcongr
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [mul_bot x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_left h x0
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    rcases eq_or_ne x 0 with rfl | x0'
    · simp at h
    lift x to α
    · rintro rfl
      exact (WithBot.bot_lt_coe (0 : α)).not_ge x0
    cases b
    · rw [bot_mul x0'] at h
      exact absurd h bot_le.not_gt
    cases a
    · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0
    exact lt_of_mul_lt_mul_right h x0
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [PosMulReflectLE α] : PosMulReflectLE (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_left h x0
/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass α] [Preorder α] [MulPosReflectLE α] : MulPosReflectLE (WithBot α) where
  elim := by
    intro ⟨x, x0⟩ a b h
    simp only at h
    lift x to α using x0.ne_bot
    cases a
    · exact bot_le
    cases b
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h
      exact absurd h (bot_lt_coe _).not_ge
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0
    exact le_of_mul_le_mul_right h x0
/-
**WithBot.instIsOrderedRing** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommSemiring α] [inst_2 
: PartialOrder α] [IsOrderedRing α]   [inst_4 : CanonicallyOrderedAdd α] [inst_5
 : NoZeroDivisors α] [inst_6 : Nontrivial α], IsOrderedRing (WithBot α)
参数：WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `WithBot.instPosMulMono`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MulZeroClass α] [inst_2 : Preorder α] [PosMulMono α],   PosMulMono (WithBot α)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `WithBot.instMulPosMono`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MulZeroClass α] [inst_2 : Preorder α] [MulPosMono α],   MulPosMono (WithBot α)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
-/
instance instIsOrderedRing [CommSemiring α] [PartialOrder α] [IsOrderedRing α]
    [CanonicallyOrderedAdd α] [NoZeroDivisors α] [Nontrivial α] :
    IsOrderedRing (WithBot α) where

end WithBot

