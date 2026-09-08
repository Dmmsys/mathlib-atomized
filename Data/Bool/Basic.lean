/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Booleans

This file proves various trivial lemmas about Booleans and their
relation to decidable propositions.

## Tags
bool, boolean, Bool, De Morgan

-/

@[expose] public section

namespace Bool

section

/-!
This section contains lemmas about Booleans which were present in core Lean 3.
The remainder of this file contains lemmas about Booleans from mathlib 3.
-/

/-
**Bool.true_eq_false_eq_False** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：true_eq_false_eq_False : ¬(true = false)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
This section contains lemmas about Booleans which were present in core Lean 3.
The remainder of this file contains lemmas about Booleans from mathlib 3.
-/
theorem true_eq_false_eq_False : ¬(true = false) := by decide
/-
**Bool.false_eq_true_eq_False** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：false_eq_true_eq_False : ¬(false = true)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem false_eq_true_eq_False : ¬(false = true) := by decide
/-
**Bool.eq_false_eq_not_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：eq_false_eq_not_eq_true (b : Bool) : (¬(b = true)) = (b = false)
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_false_eq_not_eq_true (b : Bool) : (¬(b = true)) = (b = false) := by simp
/-
**Bool.eq_true_eq_not_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：eq_true_eq_not_eq_false (b : Bool) : (¬(b = false)) = (b = true)
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_true_eq_not_eq_false (b : Bool) : (¬(b = false)) = (b = true) := by simp
/-
**Bool.eq_false_of_not_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：eq_false_of_not_eq_true {b : Bool} : ¬b = true -> b = false
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.eq_false_eq_not_eq_true`：eq_false_eq_not_eq_true (b : Bool) : (¬(b 
= true)) = (b = false)
-/
theorem eq_false_of_not_eq_true {b : Bool} : ¬b = true → b = false :=
  Eq.mp (eq_false_eq_not_eq_true b)
/-
**Bool.eq_true_of_not_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：eq_true_of_not_eq_false {b : Bool} : ¬b = false -> b = true
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.eq_true_eq_not_eq_false`：eq_true_eq_not_eq_false (b : Bool) : (¬(b 
= false)) = (b = true)
-/
theorem eq_true_of_not_eq_false {b : Bool} : ¬b = false → b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)
/-
**Bool.and_eq_true_eq_eq_true_and_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_eq_true_eq_eq_true_and_eq_true (a b : Bool) : ((a && b) = true) = (a =
 true ∧ b = true)
参数：a b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.and_eq_true`：∀ (a b : Bool), ((a && b) = true) = (a = true ∧ b = tr
ue)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem and_eq_true_eq_eq_true_and_eq_true (a b : Bool) :
    ((a && b) = true) = (a = true ∧ b = true) := by simp
/-
**Bool.or_eq_true_eq_eq_true_or_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：or_eq_true_eq_eq_true_or_eq_true (a b : Bool) : ((a || b) = true) = (a = t
rue ∨ b = true)
参数：a b : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.or_eq_true`：∀ (a b : Bool), ((a || b) = true) = (a = true ∨ b = tru
e)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem or_eq_true_eq_eq_true_or_eq_true (a b : Bool) :
    ((a || b) = true) = (a = true ∨ b = true) := by simp
/-
**Bool.not_eq_true_eq_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false)
参数：a : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by grind
/-
**Bool.and_eq_false_eq_eq_false_or_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_eq_false_eq_eq_false_or_eq_false (a b : Bool) : ((a && b) = false) = (
a = false ∨ b = false)
参数：a b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by grind
/-
**Bool.or_eq_false_eq_eq_false_and_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：or_eq_false_eq_eq_false_and_eq_false (a b : Bool) : ((a || b) = false) = (
a = false ∧ b = false)
参数：a b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by grind
/-
**Bool.not_eq_false_eq_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true)
参数：a : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by grind
/-
**Bool.coe_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：coe_false : ↑false = False
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_false : ↑false = False := by simp
/-
**Bool.coe_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：coe_true : ↑true = True
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_true : ↑true = True := by simp
/-
**Bool.coe_sort_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：coe_sort_false : (false : Prop) = False
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sort_false : (false : Prop) = False := by simp
/-
**Bool.coe_sort_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：coe_sort_true : (true : Prop) = True
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sort_true : (true : Prop) = True := by simp
/-
**Bool.decide_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p
参数：p : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp
/-
**Bool.decide_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：decide_true {p : Prop} [Decidable p] : p -> decide p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.decide_iff`：decide_iff (p : Prop) [d : Decidable p] : decide p = tr
ue ↔ p
-/
theorem decide_true {p : Prop} [Decidable p] : p → decide p :=
  (decide_iff p).2
/-
**Bool.of_decide_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：of_decide_true {p : Prop} [Decidable p] : decide p -> p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bool.decide_iff`：decide_iff (p : Prop) [d : Decidable p] : decide p = tr
ue ↔ p
-/
theorem of_decide_true {p : Prop} [Decidable p] : decide p → p :=
  (decide_iff p).1
/-
**Bool.bool_iff_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：bool_iff_false {b : Bool} : ¬b ↔ b = false
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by grind
/-
**Bool.bool_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：bool_eq_false {b : Bool} : ¬b -> b = false
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bool.bool_iff_false`：bool_iff_false {b : Bool} : ¬b ↔ b = false
-/
theorem bool_eq_false {b : Bool} : ¬b → b = false :=
  bool_iff_false.1
/-
**Bool.decide_false_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：decide_false_iff (p : Prop) {_ : Decidable p} : decide p = false ↔ ¬p
参数：p : Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Bool.bool_iff_false`：bool_iff_false {b : Bool} : ¬b ↔ b = false
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Bool.decide_iff`：decide_iff (p : Prop) [d : Decidable p] : decide p = tr
ue ↔ p
-/
theorem decide_false_iff (p : Prop) {_ : Decidable p} : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))
/-
**Bool.decide_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：decide_false {p : Prop} [Decidable p] : ¬p -> decide p = false
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.decide_false_iff`：decide_false_iff (p : Prop) {_ : Decidable p} : d
ecide p = false ↔ ¬p
-/
theorem decide_false {p : Prop} [Decidable p] : ¬p → decide p = false :=
  (decide_false_iff p).2
/-
**Bool.of_decide_false** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：of_decide_false {p : Prop} [Decidable p] : decide p = false -> ¬p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bool.decide_false_iff`：decide_false_iff (p : Prop) {_ : Decidable p} : d
ecide p = false ↔ ¬p
-/
theorem of_decide_false {p : Prop} [Decidable p] : decide p = false → ¬p :=
  (decide_false_iff p).1
/-
**Bool.decide_congr** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide
 p = decide q
参数：h : p ↔ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `decide_eq_decide`：∀ {p q : Prop} {x : Decidable p} {x_1 : Decidable q}, 
decide p = decide q ↔ (p ↔ q)
-/
theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h
/-
**Bool.coe_xor_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：coe_xor_iff (a b : Bool) : xor a b ↔ Xor (a = true) (b = true)
参数：a b : Bool。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor (a = true) (b = true) := by grind

end

/-
**Bool.dichotomy** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：dichotomy (b : Bool) : b = false ∨ b = true
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dichotomy (b : Bool) : b = false ∨ b = true := by grind
/-
**Bool.not_ne_id** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_ne_id : not != id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.false_ne_true`：false ≠ true
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem not_ne_id : not ≠ id := fun h ↦ false_ne_true <| congrFun h true
/-
**Bool.or_inl** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：or_inl {a b : Bool} (H : a) : a || b
参数：H : a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.true_or`：∀ (b : Bool), (true || b) = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]
/-
**Bool.or_inr** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：or_inr {a b : Bool} (H : b) : a || b
参数：H : b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem or_inr {a b : Bool} (H : b) : a || b := by grind
/-
**Bool.and_elim_left** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_elim_left : forall {a b : Bool}, a && b -> a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide
/-
**Bool.and_intro** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_intro : forall {a b : Bool}, a -> b -> a && b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem and_intro : ∀ {a b : Bool}, a → b → a && b := by decide
/-
**Bool.and_elim_right** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_elim_right : forall {a b : Bool}, a && b -> b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide
/-
**Bool.eq_not_iff** 是 Mathlib 中的一个引理，位于命名空间 `Bool`。
形式化陈述：eq_not_iff : forall {a b : Bool}, a = !b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma eq_not_iff : ∀ {a b : Bool}, a = !b ↔ a ≠ b := by decide
/-
**Bool.not_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Bool`。
形式化陈述：not_eq_iff : forall {a b : Bool}, (!a) = b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma not_eq_iff : ∀ {a b : Bool}, (!a) = b ↔ a ≠ b := by decide
/-
**Bool.ne_not** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：ne_not {a b : Bool} : a != !b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.not_eq_not`：∀ {a b : Bool}, ¬a = !b ↔ a = b
-/
theorem ne_not {a b : Bool} : a ≠ !b ↔ a = b :=
  not_eq_not
/-
**Bool.not_ne_self** 是 Mathlib 中的一个引理，位于命名空间 `Bool`。
形式化陈述：not_ne_self : forall b : Bool, (!b) != b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma not_ne_self : ∀ b : Bool, (!b) ≠ b := by decide
/-
**Bool.self_ne_not** 是 Mathlib 中的一个引理，位于命名空间 `Bool`。
形式化陈述：self_ne_not : forall b : Bool, b != !b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma self_ne_not : ∀ b : Bool, b ≠ !b := by decide
/-
**Bool.eq_or_eq_not** 是 Mathlib 中的一个引理，位于命名空间 `Bool`。
形式化陈述：eq_or_eq_not : forall a b, a = b ∨ a = !b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma eq_or_eq_not : ∀ a b, a = b ∨ a = !b := by decide

-- TODO naming issue: these two `not` are different.
/-
**Bool.not_iff_not** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：not_iff_not : forall {b : Bool}, !b ↔ ¬b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem not_iff_not : ∀ {b : Bool}, !b ↔ ¬b := by simp
/-
**Bool.eq_true_of_not_eq_false'** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：eq_true_of_not_eq_false' {a : Bool} : (!a) = false -> a = true
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem eq_true_of_not_eq_false' {a : Bool} : (!a) = false → a = true := by decide +revert
/-
**Bool.eq_false_of_not_eq_true'** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：eq_false_of_not_eq_true' {a : Bool} : (!a) = true -> a = false
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem eq_false_of_not_eq_true' {a : Bool} : (!a) = true → a = false := by decide +revert
/-
**Bool.bne_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：bne_eq_xor : bne = xor
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bne_eq_xor : bne = xor := by constructor

attribute [simp] xor_assoc
/-
**Bool.xor_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：xor_iff_ne : forall {x y : Bool}, xor x y = true ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem xor_iff_ne : ∀ {x y : Bool}, xor x y = true ↔ x ≠ y := by decide

/-! ### De Morgan's laws for Booleans -/

/-
**Bool.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Bool`。
形式化陈述：linearOrder : LinearOrder Bool where le_refl
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### De Morgan's laws for Booleans
-/
instance linearOrder : LinearOrder Bool where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := by decide
  max_def := by decide
  min_def := by decide
/-
**Bool.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：lt_iff : forall {x y : Bool}, x < y ↔ x = false ∧ y = true
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem lt_iff : ∀ {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide

@[simp]
/-
**Bool.false_lt_true** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：false_lt_true : false < true
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.lt_iff`：lt_iff : forall {x y : Bool}, x < y ↔ x = false ∧ y = true
-/
theorem false_lt_true : false < true :=
  lt_iff.2 ⟨rfl, rfl⟩
/-
**Bool.le_iff_imp** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：le_iff_imp : forall {x y : Bool}, x <= y ↔ x -> y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem le_iff_imp : ∀ {x y : Bool}, x ≤ y ↔ x → y := by decide
/-
**Bool.and_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_le_left : forall x y : Bool, (x && y) <= x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem and_le_left : ∀ x y : Bool, (x && y) ≤ x := by decide
/-
**Bool.and_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：and_le_right : forall x y : Bool, (x && y) <= y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem and_le_right : ∀ x y : Bool, (x && y) ≤ y := by decide
/-
**Bool.le_and** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：le_and : forall {x y z : Bool}, x <= y -> x <= z -> x <= (y && z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem le_and : ∀ {x y z : Bool}, x ≤ y → x ≤ z → x ≤ (y && z) := by decide
/-
**Bool.left_le_or** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：left_le_or : forall x y : Bool, x <= (x || y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem left_le_or : ∀ x y : Bool, x ≤ (x || y) := by decide
/-
**Bool.right_le_or** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：right_le_or : forall x y : Bool, y <= (x || y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem right_le_or : ∀ x y : Bool, y ≤ (x || y) := by decide
/-
**Bool.or_le** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：or_le : forall {x y z}, x <= z -> y <= z -> (x || y) <= z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem or_le : ∀ {x y z}, x ≤ z → y ≤ z → (x || y) ≤ z := by decide

/-- convert a `ℕ` to a `Bool`, `0 -> false`, everything else -> `true` -/
/-
**Bool.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `Bool`。
形式化陈述：ofNat (n : Nat) : Bool
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
convert a `ℕ` to a `Bool`, `0 -> false`, everything else -> `true`
-/
def ofNat (n : Nat) : Bool :=
  decide (n ≠ 0)

@[simp, grind =]
/-
**Bool.ofNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：ofNat_zero : ofNat 0 = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_zero : ofNat 0 = false := rfl

@[simp, grind =]
/-
**Bool.ofNat_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：ofNat_add_one {n : Nat} : ofNat (n + 1) = true
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_add_one {n : Nat} : ofNat (n + 1) = true := rfl
/-
**Bool.toNat_beq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：∀ (b : Bool), (b.toNat == 0) = !b
参数：b : Bool；b.toNat == 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toNat_beq_zero (b : Bool) : (b.toNat == 0) = !b := by grind
/-
**Bool.toNat_bne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：∀ (b : Bool), (b.toNat != 0) = b
参数：b : Bool；b.toNat != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.toNat_beq_zero`：∀ (b : Bool), (b.toNat == 0) = !b
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toNat_bne_zero (b : Bool) : (b.toNat != 0) = b := by simp [bne]
/-
**Bool.toNat_beq_one** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：∀ (b : Bool), (b.toNat == 1) = b
参数：b : Bool；b.toNat == 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma toNat_beq_one (b : Bool) : (b.toNat == 1) = b := by cases b <;> rfl
/-
**Bool.toNat_bne_one** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：∀ (b : Bool), (b.toNat != 1) = !b
参数：b : Bool；b.toNat != 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.toNat_beq_one`：∀ (b : Bool), (b.toNat == 1) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toNat_bne_one (b : Bool) : (b.toNat != 1) = !b := by simp [bne]
/-
**Bool.ofNat_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：ofNat_le_ofNat {n m : Nat} (h : n <= m) : ofNat n <= ofNat m
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
-/
theorem ofNat_le_ofNat {n m : Nat} (h : n ≤ m) : ofNat n ≤ ofNat m := by
  simp only [ofNat, ne_eq, _root_.decide_not]
  cases Nat.decEq n 0 with
  | isTrue hn => grind [Bool.false_le]
  | isFalse hn => cases Nat.decEq m 0 with grind [Bool.le_true]
/-
**Bool.toNat_le_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ <= b₁) : toNat b₀ <= toNat b₁
参数：h : b₀ <= b₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
-/
theorem toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ ≤ b₁) : toNat b₀ ≤ toNat b₁ := by
  cases b₀ <;> cases b₁ <;> simp_all +decide
/-
**Bool.ofNat_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：ofNat_toNat (b : Bool) : ofNat (toNat b) = b
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_toNat (b : Bool) : ofNat (toNat b) = b := by grind [cases Bool]

@[simp]
/-
**Bool.injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：injective_iff {α : Sort*} {f : Bool -> α} : Function.Injective f ↔ f false
 != f true
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.false_ne_true`：false ≠ true
-/
theorem injective_iff {α : Sort*} {f : Bool → α} : Function.Injective f ↔ f false ≠ f true :=
  ⟨fun Hinj Heq ↦ false_ne_true (Hinj Heq), fun H x y ↦ by grind [cases Bool]⟩

/-- **Kaminski's Equation** -/
/-
**Bool.apply_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bool`。
形式化陈述：apply_apply_apply (f : Bool -> Bool) (x : Bool) : f (f (f x)) = f x
参数：f : Bool -> Bool；x : Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Kaminski's Equation**
-/
theorem apply_apply_apply (f : Bool → Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> grind [cases Bool]

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
/-
**Bool.xor3** 是 Mathlib 中的一个定义，位于命名空间 `Bool`。
形式化陈述：Bool → Bool → Bool → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`xor3 x y c` is `((x XOR y) XOR c)`.
-/
protected def xor3 (x y c : Bool) :=
  xor (xor x y) c

/-- `carry x y c` is `x && y || x && c || y && c`. -/
/-
**Bool.carry** 是 Mathlib 中的一个定义，位于命名空间 `Bool`。
形式化陈述：Bool → Bool → Bool → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`carry x y c` is `x && y || x && c || y && c`.
-/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c

end Bool

