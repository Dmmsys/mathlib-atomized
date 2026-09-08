/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Order.WithBot

/-! # Adjoining top/bottom elements to ordered monoids.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

open Function

namespace WithTop

section One

variable [One α] {a : α}

@[to_additive]
/-
**WithTop.one** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：one : One (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one : One (WithTop α) :=
  ⟨(1 : α)⟩

@[to_additive (attr := simp, norm_cast)]
/-
**WithTop.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_one : ((1 : α) : WithTop α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**WithTop.coe_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：coe_eq_one : (a : WithTop α) = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
-/
lemma coe_eq_one : (a : WithTop α) = 1 ↔ a = 1 := coe_eq_coe
/-
**WithTop.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : One α] {a : α}, ↑a ≠ 1 ↔ a ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `WithTop.coe_eq_one`：coe_eq_one : (a : WithTop α) = 1 ↔ a = 1
-/
@[to_additive] lemma coe_ne_one : (a : WithTop α) ≠ 1 ↔ a ≠ 1 := coe_eq_one.ne

@[to_additive (attr := simp, norm_cast)]
/-
**WithTop.one_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：one_eq_coe : 1 = (a : WithTop α) ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `WithTop.coe_eq_one`：coe_eq_one : (a : WithTop α) = 1 ↔ a = 1
-/
lemma one_eq_coe : 1 = (a : WithTop α) ↔ a = 1 := eq_comm.trans coe_eq_one
/-
**WithTop.top_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : One α], ⊤ ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_ne_coe`：∀ {α : Type u_1} {a : α}, ⊤ ≠ ↑a
-/
@[to_additive (attr := simp)] lemma top_ne_one : (⊤ : WithTop α) ≠ 1 := top_ne_coe
/-
**WithTop.one_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : One α], 1 ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
@[to_additive (attr := simp)] lemma one_ne_top : (1 : WithTop α) ≠ ⊤ := coe_ne_top

@[to_additive (attr := simp)]
/-
**WithTop.untop_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：untop_one : (1 : WithTop α).untop coe_ne_top = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
theorem untop_one : (1 : WithTop α).untop coe_ne_top = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**WithTop.untopD_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：untopD_one (d : α) : (1 : WithTop α).untopD d = 1
参数：d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem untopD_one (d : α) : (1 : WithTop α).untopD d = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
/-
**WithTop.one_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：one_le_coe [LE α] {a : α} : 1 <= (a : WithTop α) ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
theorem one_le_coe [LE α] {a : α} : 1 ≤ (a : WithTop α) ↔ 1 ≤ a :=
  coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]
/-
**WithTop.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_le_one [LE α] {a : α} : (a : WithTop α) <= 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
theorem coe_le_one [LE α] {a : α} : (a : WithTop α) ≤ 1 ↔ a ≤ 1 :=
  coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]
/-
**WithTop.one_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
theorem one_lt_coe [LT α] {a : α} : 1 < (a : WithTop α) ↔ 1 < a :=
  coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
/-
**WithTop.coe_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
theorem coe_lt_one [LT α] {a : α} : (a : WithTop α) < 1 ↔ a < 1 :=
  coe_lt_coe

@[to_additive (attr := simp)]
/-
**WithTop.map_one** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : One α] {β : Type u_1} (f : α → β), WithTop.map f 1 
= ↑(f 1)
参数：f : α → β；f 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) :=
  rfl

@[to_additive]
/-
**WithTop.map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：map_eq_one_iff {α} {f : α -> β} {v : WithTop α} [One β] : WithTop.map f v 
= 1 ↔ exists x, v = .some x ∧ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_eq_some_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {y 
: β} {v : WithTop α}, WithTop.map f v = ↑y ↔ ∃ x, v = ↑x ∧ f x = y
-/
theorem map_eq_one_iff {α} {f : α → β} {v : WithTop α} [One β] :
    WithTop.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1 := map_eq_some_iff

@[to_additive]
/-
**WithTop.one_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：one_eq_map_iff {α} {f : α -> β} {v : WithTop α} [One β] : 1 = WithTop.map 
f v ↔ exists x, v = .some x ∧ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.some_eq_map_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {y 
: β} {v : WithTop α}, ↑y = WithTop.map f v ↔ ∃ x, v = ↑x ∧ f x = y
-/
theorem one_eq_map_iff {α} {f : α → β} {v : WithTop α} [One β] :
    1 = WithTop.map f v ↔ ∃ x, v = .some x ∧ f x = 1 := some_eq_map_iff
/-
**WithTop.zeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTo
p α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithTop α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

@[to_additive]
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [IsBotOneClass α] : IsBotOneClass (WithTop α) where
  isBot_one x := by cases x <;> simp

end One

section Add

variable [Add α] {w x y z : WithTop α} {a b : α}

/-
**WithTop.add** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：add : Add (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add : Add (WithTop α) :=
  ⟨WithTop.map₂ (· + ·)⟩
/-
**WithTop.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a + ↑b
参数：a b : α；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithTop α) := rfl
/-
**WithTop.top_add** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] (x : WithTop α), ⊤ + x = ⊤
参数：x : WithTop α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_add (x : WithTop α) : ⊤ + x = ⊤ := rfl
/-
**WithTop.add_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = ⊤
参数：x : WithTop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma add_top (x : WithTop α) : x + ⊤ = ⊤ := by cases x <;> rfl
/-
**WithTop.add_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y : WithTop α}, x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma add_eq_top : x + y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by cases x <;> cases y <;> simp [← coe_add]
/-
**WithTop.add_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_ne_top : x + y != ⊤ ↔ x != ⊤ ∧ y != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma add_ne_top : x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by cases x <;> cases y <;> simp [← coe_add]

@[simp]
/-
**WithTop.add_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, add_ne_top]
/-
**WithTop.add_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {a b : WithTop α} {c : α}, a + b = ↑c ↔ ∃ a'
 b', ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem add_eq_coe :
    ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊤, b, c => by simp
  | some a, ⊤, c => by simp
  | some a, some b, c => by norm_cast; simp
/-
**WithTop.add_coe_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_coe_eq_top_iff : x + b = ⊤ ↔ x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma add_coe_eq_top_iff : x + b = ⊤ ↔ x = ⊤ := by simp
/-
**WithTop.coe_add_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：coe_add_eq_top_iff : a + y = ⊤ ↔ y = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_add_eq_top_iff : a + y = ⊤ ↔ y = ⊤ := by simp
/-
**WithTop._root_.IsAddLeftRegular.withTop** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsAddLeftRegular.withTop (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]
/-
**WithTop._root_.IsAddRightRegular.withTop** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsAddRightRegular.withTop (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithTop α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_top, some_eq_coe, ← coe_add, ha.eq_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**WithTop._root_.AddLECancellable.withTop** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddLECancellable.withTop [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithTop α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_top]
  · simp [none_eq_top]
  · simp [some_eq_coe, ← coe_add, none_eq_top]
  · simpa [none_eq_top, some_eq_coe, ← coe_add] using fun a ↦ ha a
/-
**WithTop.add_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_right_inj [IsRightCancelAdd α] (hz : z != ⊤) : x + z = y + z ↔ x = y
参数：hz : z != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsAddRightRegular.withTop`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddR
ightRegular a → IsAddRightRegular ↑a
· 使用定理 `IsAddRightRegular.all`：∀ {R : Type u_2} [inst : Add R] [IsRightCancelAdd
 R] (g : R), IsAddRightRegular g
-/
lemma add_right_inj [IsRightCancelAdd α] (hz : z ≠ ⊤) : x + z = y + z ↔ x = y := by
  lift z to α using hz; exact (IsAddRightRegular.all _).withTop.eq_iff
/-
**WithTop.add_right_cancel** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_right_cancel [IsRightCancelAdd α] (hz : z != ⊤) (h : x + z = y + z) : 
x = y
参数：hz : z != ⊤；h : x + z = y + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithTop.add_right_inj`：add_right_inj [IsRightCancelAdd α] (hz : z != ⊤) 
: x + z = y + z ↔ x = y
-/
lemma add_right_cancel [IsRightCancelAdd α] (hz : z ≠ ⊤) (h : x + z = y + z) : x = y :=
  (WithTop.add_right_inj hz).1 h
/-
**WithTop.add_left_inj** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_left_inj [IsLeftCancelAdd α] (hx : x != ⊤) : x + y = x + z ↔ y = z
参数：hx : x != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsAddLeftRegular.withTop`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddLe
ftRegular a → IsAddLeftRegular ↑a
· 使用定理 `IsAddLeftRegular.all`：∀ {R : Type u_2} [inst : Add R] [IsLeftCancelAdd R
] (g : R), IsAddLeftRegular g
-/
lemma add_left_inj [IsLeftCancelAdd α] (hx : x ≠ ⊤) : x + y = x + z ↔ y = z := by
  lift x to α using hx; exact (IsAddLeftRegular.all _).withTop.eq_iff
/-
**WithTop.add_left_cancel** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：add_left_cancel [IsLeftCancelAdd α] (hx : x != ⊤) (h : x + y = x + z) : y 
= z
参数：hx : x != ⊤；h : x + y = x + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithTop.add_left_inj`：add_left_inj [IsLeftCancelAdd α] (hx : x != ⊤) : x
 + y = x + z ↔ y = z
-/
lemma add_left_cancel [IsLeftCancelAdd α] (hx : x ≠ ⊤) (h : x + y = x + z) : y = z :=
  (WithTop.add_left_inj hx).1 h
/-
**WithTop.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithTop α) where elim x 
y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
instance addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr
/-
**WithTop.addRightMono** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addRightMono [LE α] [AddRightMono α] : AddRightMono (WithTop α) where elim
 x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
instance addRightMono [LE α] [AddRightMono α] : AddRightMono (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ ↦ by gcongr
/-
**WithTop.addLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithTop α
) where elim x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
-/
instance addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left
/-
**WithTop.addRightReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithTo
p α) where elim x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
-/
instance addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithTop α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right
/-
**WithTop.le_of_add_le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LE α] [AddLeft
ReflectLE α], x ≠ ⊤ → x + y ≤ x + z → y ≤ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
-/
protected lemma le_of_add_le_add_left [LE α] [AddLeftReflectLE α] (hx : x ≠ ⊤) :
    x + y ≤ x + z → y ≤ z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left
/-
**WithTop.le_of_add_le_add_right** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LE α] [AddRigh
tReflectLE α], z ≠ ⊤ → x + z ≤ y + z → x ≤ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
-/
protected lemma le_of_add_le_add_right [LE α] [AddRightReflectLE α] (hz : z ≠ ⊤) :
    x + z ≤ y + z → x ≤ y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right
/-
**WithTop.add_lt_add_left** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LT α] [AddLeft
StrictMono α], x ≠ ⊤ → y < z → x + y < x + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
protected lemma add_lt_add_left [LT α] [AddLeftStrictMono α] (hx : x ≠ ⊤) :
    y < z → x + y < x + z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr
/-
**WithTop.add_lt_add_right** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LT α] [AddRigh
tStrictMono α], z ≠ ⊤ → x < y → x + z < y + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
-/
protected lemma add_lt_add_right [LT α] [AddRightStrictMono α] (hz : z ≠ ⊤) :
    x < y → x + z < y + z := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr

@[gcongr]
/-
**WithTop.add_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {w x y z : WithTop α} [inst_1 : Preorder α] 
[AddLeftStrictMono α] [AddRightStrictMono α],   x < z → y < w → x + y < z + w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithTop.add_lt_add_left`：∀ {α : Type u} [inst : Add α] {x y z : WithTop 
α} [inst_1 : LT α] [AddLeftStrictMono α], x ≠ ⊤ → y < z → x + y < x + z
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `WithTop.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithTop
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊤ → x < y → x + z < y + z
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
protected theorem add_lt_add [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]
    (xz : x < z) (yw : y < w) : x + y < z + w := by
  apply (WithTop.add_lt_add_left xz.ne_top yw).trans_le
  cases w
  · simp
  · exact (WithTop.add_lt_add_right coe_ne_top xz).le
/-
**WithTop.add_le_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LE α] [AddLeft
Mono α] [AddLeftReflectLE α],   x ≠ ⊤ → (x + y ≤ x + z ↔ y ≤ z)
参数：x + y ≤ x + z ↔ y ≤ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_of_add_le_add_left`：∀ {α : Type u} [inst : Add α] {x y z : Wi
thTop α} [inst_1 : LE α] [AddLeftReflectLE α], x ≠ ⊤ → x + y ≤ x + z → y ≤ z
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x ≠ ⊤) :
    x + y ≤ x + z ↔ y ≤ z := ⟨WithTop.le_of_add_le_add_left hx, fun _ ↦ by gcongr⟩
/-
**WithTop.add_le_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LE α] [AddRigh
tMono α] [AddRightReflectLE α],   z ≠ ⊤ → (x + z ≤ y + z ↔ x ≤ y)
参数：x + z ≤ y + z ↔ x ≤ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_of_add_le_add_right`：∀ {α : Type u} [inst : Add α] {x y z : W
ithTop α} [inst_1 : LE α] [AddRightReflectLE α], z ≠ ⊤ → x + z ≤ y + z → x ≤ y
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z ≠ ⊤) :
    x + z ≤ y + z ↔ x ≤ y := ⟨WithTop.le_of_add_le_add_right hz, fun _ ↦ by gcongr⟩
/-
**WithTop.add_lt_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LT α] [AddLeft
StrictMono α] [AddLeftReflectLT α],   x ≠ ⊤ → (x + y < x + z ↔ y < z)
参数：x + y < x + z ↔ y < z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
· 使用定理 `WithTop.add_lt_add_left`：∀ {α : Type u} [inst : Add α] {x y z : WithTop 
α} [inst_1 : LT α] [AddLeftStrictMono α], x ≠ ⊤ → y < z → x + y < x + z
-/
protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x ≠ ⊤) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithTop.add_lt_add_left hx⟩
/-
**WithTop.add_lt_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithTop α} [inst_1 : LT α] [AddRigh
tStrictMono α] [AddRightReflectLT α],   z ≠ ⊤ → (x + z < y + z ↔ x < y)
参数：x + z < y + z ↔ x < y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
· 使用定理 `WithTop.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithTop
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊤ → x < y → x + z < y + z
-/
protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z ≠ ⊤) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithTop.add_lt_add_right hz⟩
/-
**WithTop.add_lt_add_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {w x y z : WithTop α} [inst_1 : Preorder α] 
[AddLeftStrictMono α] [AddRightMono α],   w ≠ ⊤ → w ≤ y → x < z → w + x < y + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithTop.add_lt_add_left`：∀ {α : Type u} [inst : Add α] {x y z : WithTop 
α} [inst_1 : LT α] [AddLeftStrictMono α], x ≠ ⊤ → y < z → x + y < x + z
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w ≠ ⊤) (hwy : w ≤ y) (hxz : x < z) :
    w + x < y + z :=
  (WithTop.add_lt_add_left hw hxz).trans_le <| by gcongr
/-
**WithTop.add_lt_add_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : Add α] {w x y z : WithTop α} [inst_1 : Preorder α] 
[AddLeftMono α] [AddRightStrictMono α],   x ≠ ⊤ → w < y → x ≤ z → w + x < y + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithTop.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithTop
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊤ → x < y → x + z < y + z
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x ≠ ⊤) (hwy : w < y) (hxz : x ≤ z) :
    w + x < y + z :=
  (WithTop.add_lt_add_right hx hwy).trans_le <| by gcongr
/-
**WithTop.addLECancellable_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：addLECancellable_of_ne_top [LE α] [AddLeftReflectLE α] (hx : x != ⊤) : Add
LECancellable x
参数：hx : x != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_of_add_le_add_left`：∀ {α : Type u} [inst : Add α] {x y z : Wi
thTop α} [inst_1 : LE α] [AddLeftReflectLE α], x ≠ ⊤ → x + y ≤ x + z → y ≤ z
-/
lemma addLECancellable_of_ne_top [LE α] [AddLeftReflectLE α]
    (hx : x ≠ ⊤) : AddLECancellable x := fun _b _c ↦ WithTop.le_of_add_le_add_left hx
/-
**WithTop.addLECancellable_of_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：addLECancellable_of_lt_top [Preorder α] [AddLeftReflectLE α] (hx : x < ⊤) 
: AddLECancellable x
参数：hx : x < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.addLECancellable_of_ne_top`：addLECancellable_of_ne_top [LE α] [A
ddLeftReflectLE α] (hx : x != ⊤) : AddLECancellable x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma addLECancellable_of_lt_top [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊤) : AddLECancellable x := addLECancellable_of_ne_top hx.ne
/-
**WithTop.addLECancellable_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) : AddLECancellabl
e (a : WithTop α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.addLECancellable_of_ne_top`：addLECancellable_of_ne_top [LE α] [A
ddLeftReflectLE α] (hx : x != ⊤) : AddLECancellable x
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithTop α) := addLECancellable_of_ne_top coe_ne_top
/-
**WithTop.addLECancellable_iff_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：addLECancellable_iff_ne_top [Nonempty α] [Preorder α] [AddLeftReflectLE α]
 : AddLECancellable x ↔ x != ⊤ where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithTop.addLECancellable_of_ne_top`：addLECancellable_of_ne_top [LE α] [A
ddLeftReflectLE α] (hx : x != ⊤) : AddLECancellable x
-/
lemma addLECancellable_iff_ne_top [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊤ where
  mp := by rintro h rfl; exact (coe_lt_top <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := addLECancellable_of_ne_top

--  There is no `WithTop.map_mul_of_mulHom`, since `WithTop` does not have a multiplication.
@[simp]
/-
**WithTop.map_add** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Add α] {F : Type u_1} [inst_1 : Add β]
 [inst_2 : FunLike F α β] [AddHomClass F α β]   (f : F) (a b : WithTop α), WithT
op.map (⇑f) (a + b) = WithTop.map (⇑f) a + WithTop.map (⇑f) b
参数：f : F；a b : WithTop α；⇑f；a + b；⇑f；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.top_add`：∀ {α : Type u} [inst : Add α] (x : WithTop α), ⊤ + x = 
⊤
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.map_coe`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (a : α), Wi
thTop.map f ↑a = ↑(f a)
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
-/
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithTop α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (top_add _).symm
  · induction b
    · exact (add_top _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

end Add

/-
**WithTop.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addSemigroup [AddSemigroup α] : AddSemigroup (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addSemigroup [AddSemigroup α] : AddSemigroup (WithTop α) :=
  { WithTop.add with
    add_assoc := fun _ _ _ => Option.map₂_assoc add_assoc }
/-
**WithTop.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithTop α) :=
  { WithTop.addSemigroup with
    add_comm := fun _ _ => Option.map₂_comm add_comm }
/-
**WithTop.addZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addZeroClass [AddZeroClass α] : AddZeroClass (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addZeroClass [AddZeroClass α] : AddZeroClass (WithTop α) :=
  { WithTop.zero, WithTop.add with
    zero_add := Option.map₂_left_identity zero_add
    add_zero := Option.map₂_right_identity add_zero }

section AddMonoid
variable [AddMonoid α]

/-
**WithTop.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addMonoid : AddMonoid (WithTop α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid (WithTop α) where
  __ := WithTop.addSemigroup
  __ := WithTop.addZeroClass
  nsmul n a := match a, n with
    | (a : α), n => ↑(n • a)
    | ⊤, 0 => 0
    | ⊤, _n + 1 => ⊤
  nsmul_zero a := by simp_rw [HSMul.hSMul, SMul.smul]; cases a <;> simp [zero_nsmul]
  nsmul_succ n a := by
    simp_rw [HSMul.hSMul, SMul.smul]
    cases a <;> cases n <;> simp [succ_nsmul, coe_add]
/-
**WithTop.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoid α] (a : α) (n : ℕ), ↑(n • a) = n • ↑a
参数：a : α；n : ℕ；n • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithTop α) := rfl

/-- Coercion from `α` to `WithTop α` as an `AddMonoidHom`. -/
/-
**WithTop.addHom** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：addHom : α ->+ WithTop α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `α` to `WithTop α` as an `AddMonoidHom`.
-/
def addHom : α →+ WithTop α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl
/-
**WithTop.coe_addHom** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoid α], ⇑WithTop.addHom = WithTop.some
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithTop α) = WithTop.some := rfl

end AddMonoid

/-
**WithTop.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }
/-
**WithTop.natCast** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：natCast [NatCast α] : NatCast (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance natCast [NatCast α] : NatCast (WithTop α) :=
  ⟨fun n => ↑(n : α)⟩

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/-
**WithTop.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addMonoidWithOne : AddMonoidWithOne (WithTop α) where natCast_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne : AddMonoidWithOne (WithTop α) where
  natCast_zero := by simp [NatCast.natCast]
  natCast_succ := fun n => by simp [NatCast.natCast]
/-
**WithTop.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_natCast (n : ℕ) : ((n : α) : WithTop α) = n := rfl
/-
**WithTop.top_ne_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ), ⊤ ≠ ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_ne_coe`：∀ {α : Type u_1} {a : α}, ⊤ ≠ ↑a
-/
@[simp] lemma top_ne_natCast (n : ℕ) : (⊤ : WithTop α) ≠ n := top_ne_coe
/-
**WithTop.natCast_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ), ↑n ≠ ⊤
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
@[simp] lemma natCast_ne_top (n : ℕ) : (n : WithTop α) ≠ ⊤ := coe_ne_top
/-
**WithTop.natCast_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst_1 : LT α] (n : ℕ), ↑n < ⊤
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
@[simp] lemma natCast_lt_top [LT α] (n : ℕ) : (n : WithTop α) < ⊤ := coe_lt_top _
/-
**WithTop.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
, ↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α) : WithTop α) = ofNat(n) := rfl
/-
**WithTop.coe_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
 (m : α),   ↑m = OfNat.ofNat n ↔ m = OfNat.ofNat n
参数：n : ℕ；m : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
-/
@[simp] lemma coe_eq_ofNat (n : ℕ) [n.AtLeastTwo] (m : α) :
    (m : WithTop α) = ofNat(n) ↔ m = ofNat(n) :=
  coe_eq_coe
/-
**WithTop.ofNat_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
 (m : α),   OfNat.ofNat n = ↑m ↔ OfNat.ofNat n = m
参数：n : ℕ；m : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
-/
@[simp] lemma ofNat_eq_coe (n : ℕ) [n.AtLeastTwo] (m : α) :
    ofNat(n) = (m : WithTop α) ↔ ofNat(n) = m :=
  coe_eq_coe
/-
**WithTop.ofNat_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
, OfNat.ofNat n ≠ ⊤
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_ne_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ↑n ≠ ⊤
-/
@[simp] lemma ofNat_ne_top (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : WithTop α) ≠ ⊤ :=
  natCast_ne_top n
/-
**WithTop.top_ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
, ⊤ ≠ OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_ne_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ⊤ ≠ ↑n
-/
@[simp] lemma top_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (⊤ : WithTop α) ≠ ofNat(n) :=
  top_ne_natCast n
/-
**WithTop.map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : AddMonoidWithOne α] {f : α → β} (n : ℕ
) [inst_1 : n.AtLeastTwo],   WithTop.map f (OfNat.ofNat n) = ↑(f (OfNat.ofNat n)
)
参数：n : ℕ；OfNat.ofNat n；f (OfNat.ofNat n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_coe`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (a : α), Wi
thTop.map f ↑a = ↑(f a)
-/
@[simp] lemma map_ofNat {f : α → β} (n : ℕ) [n.AtLeastTwo] :
    WithTop.map f (ofNat(n) : WithTop α) = f (ofNat(n)) := map_coe f n
/-
**WithTop.map_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : AddMonoidWithOne α] {f : α → β} (n : ℕ
), WithTop.map f ↑n = ↑(f ↑n)
参数：n : ℕ；f ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_coe`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (a : α), Wi
thTop.map f ↑a = ↑(f a)
-/
@[simp] lemma map_natCast {f : α → β} (n : ℕ) :
    WithTop.map f (n : WithTop α) = f n := map_coe f n
/-
**WithTop.map_eq_ofNat_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：map_eq_ofNat_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithTop β} : a
.map f = ofNat(n) ↔ exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_eq_some_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {y 
: β} {v : WithTop α}, WithTop.map f v = ↑y ↔ ∃ x, v = ↑x ∧ f x = y
-/
lemma map_eq_ofNat_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithTop β} :
    a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff
/-
**WithTop.ofNat_eq_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：ofNat_eq_map_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithTop β} : o
fNat(n) = a.map f ↔ exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.some_eq_map_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {y 
: β} {v : WithTop α}, ↑y = WithTop.map f v ↔ ∃ x, v = ↑x ∧ f x = y
-/
lemma ofNat_eq_map_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithTop β} :
    ofNat(n) = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff
/-
**WithTop.map_eq_natCast_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：map_eq_natCast_iff {f : β -> α} {n : Nat} {a : WithTop β} : a.map f = n ↔ 
exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_eq_some_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {y 
: β} {v : WithTop α}, WithTop.map f v = ↑y ↔ ∃ x, v = ↑x ∧ f x = y
-/
lemma map_eq_natCast_iff {f : β → α} {n : ℕ} {a : WithTop β} :
    a.map f = n ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff
/-
**WithTop.natCast_eq_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：natCast_eq_map_iff {f : β -> α} {n : Nat} {a : WithTop β} : n = a.map f ↔ 
exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.some_eq_map_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {y 
: β} {v : WithTop α}, ↑y = WithTop.map f v ↔ ∃ x, v = ↑x ∧ f x = y
-/
lemma natCast_eq_map_iff {f : β → α} {n : ℕ} {a : WithTop β} :
    n = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff

end AddMonoidWithOne

/-
**WithTop.charZero** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithTop α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithTop α) :=
  { cast_injective := Function.Injective.comp (f := Nat.cast (R := α))
      (fun _ _ => WithTop.coe_eq_coe.1) Nat.cast_injective }
/-
**WithTop.addCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (With
Top α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithTop α) :=
  { WithTop.addMonoidWithOne, WithTop.addCommMonoid with }

-- instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) where
--   add_le_add_left _ _ := add_le_add_left
--
-- instance linearOrderedAddCommMonoidWithTop [LinearOrderedAddCommMonoid α] :
--     LinearOrderedAddCommMonoidWithTop (WithTop α) :=
--   { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid with
--     top_add' := WithTop.top_add }
--
/-
**WithTop.existsAddOfLE** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：existsAddOfLE [LE α] [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithTop α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.not_top_le_coe`：∀ {α : Type u_1} [inst : LE α] (a : α), ¬⊤ ≤ ↑a
-/
instance existsAddOfLE [LE α] [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithTop α) :=
  ⟨fun {a} {b} =>
    match a, b with
    | ⊤, ⊤ => by simp
    | (a : α), ⊤ => fun _ => ⟨⊤, rfl⟩
    | (a : α), (b : α) => fun h => by
      obtain ⟨c, rfl⟩ := exists_add_of_le (WithTop.coe_le_coe.1 h)
      exact ⟨c, rfl⟩
    | ⊤, (b : α) => fun h => (not_top_le_coe _ h).elim⟩

-- instance canonicallyOrderedAddCommMonoid [CanonicallyOrderedAddCommMonoid α] :
--     CanonicallyOrderedAddCommMonoid (WithTop α) :=
--   { WithTop.orderBot, WithTop.orderedAddCommMonoid, WithTop.existsAddOfLE with
--     le_self_add := fun a b =>
--       match a, b with
--       | ⊤, ⊤ => le_rfl
--       | (a : α), ⊤ => le_top
--       | (a : α), (b : α) => WithTop.coe_le_coe.2 le_self_add
--       | ⊤, (b : α) => le_rfl }
--
-- instance [CanonicallyLinearOrderedAddCommMonoid α] :
--     CanonicallyLinearOrderedAddCommMonoid (WithTop α) :=
--   { WithTop.canonicallyOrderedAddCommMonoid, WithTop.linearOrder with }

@[to_additive (attr := simp) top_pos]
/-
**WithTop.one_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：one_lt_top [One α] [LT α] : (1 : WithTop α) < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem one_lt_top [One α] [LT α] : (1 : WithTop α) < ⊤ := coe_lt_top _

/-- A version of `WithTop.map` for `OneHom`s. -/
@[to_additive (attr := simps -fullyApplied)
  /-- A version of `WithTop.map` for `ZeroHom`s -/]
/-
**WithTop._root_.OneHom.withTopMap** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def _root_.OneHom.withTopMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_one' := by rw [WithTop.map_one, map_one, coe_one]

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps -fullyApplied]
/-
**WithTop._root_.AddHom.withTopMap** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.map` for `AddHom`s.
-/
protected def _root_.AddHom.withTopMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithTop M) (WithTop N) where
  toFun := WithTop.map f
  map_add' := WithTop.map_add f

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
/-
**WithTop._root_.AddMonoidHom.withTopMap** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.map` for `AddMonoidHom`s.
-/
protected def _root_.AddMonoidHom.withTopMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithTop M →+ WithTop N :=
  { ZeroHom.withTopMap f.toZeroHom, AddHom.withTopMap f.toAddHom with toFun := WithTop.map f }

end WithTop

namespace WithBot
section One
variable [One α] {a : α}

/-
**WithBot.one** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：{α : Type u} → [One α] → One (WithBot α)
参数：WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance one : One (WithBot α) := ⟨(1 : α)⟩
/-
**WithBot.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : One α], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp, norm_cast)] lemma coe_one : ((1 : α) : WithBot α) = 1 := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**WithBot.coe_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_eq_one : (a : WithBot α) = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
-/
lemma coe_eq_one : (a : WithBot α) = 1 ↔ a = 1 := coe_eq_coe

@[to_additive (attr := simp, norm_cast)]
/-
**WithBot.one_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：one_eq_coe : 1 = (a : WithBot α) ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `WithBot.coe_eq_one`：coe_eq_one : (a : WithBot α) = 1 ↔ a = 1
-/
lemma one_eq_coe : 1 = (a : WithBot α) ↔ a = 1 := eq_comm.trans coe_eq_one
/-
**WithBot.bot_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : One α], ⊥ ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.bot_ne_coe`：bot_ne_coe : ⊥ != (a : WithBot α)
-/
@[to_additive (attr := simp)] lemma bot_ne_one : (⊥ : WithBot α) ≠ 1 := bot_ne_coe
/-
**WithBot.one_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : One α], 1 ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
@[to_additive (attr := simp)] lemma one_ne_bot : (1 : WithBot α) ≠ ⊥ := coe_ne_bot

@[to_additive (attr := simp)]
/-
**WithBot.unbot_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
theorem unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**WithBot.unbotD_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：unbotD_one (d : α) : (1 : WithBot α).unbotD d = 1
参数：d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unbotD_one (d : α) : (1 : WithBot α).unbotD d = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast) coe_nonneg]
/-
**WithBot.one_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：one_le_coe [LE α] : 1 <= (a : WithBot α) ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem one_le_coe [LE α] : 1 ≤ (a : WithBot α) ↔ 1 ≤ a := coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_le_zero]
/-
**WithBot.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_le_one [LE α] : (a : WithBot α) <= 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem coe_le_one [LE α] : (a : WithBot α) ≤ 1 ↔ a ≤ 1 := coe_le_coe

@[to_additive (attr := simp, norm_cast) coe_pos]
/-
**WithBot.one_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：one_lt_coe [LT α] : 1 < (a : WithBot α) ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
theorem one_lt_coe [LT α] : 1 < (a : WithBot α) ↔ 1 < a := coe_lt_coe

@[to_additive (attr := simp, norm_cast) coe_lt_zero]
/-
**WithBot.coe_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：coe_lt_one [LT α] : (a : WithBot α) < 1 ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
theorem coe_lt_one [LT α] : (a : WithBot α) < 1 ↔ a < 1 := coe_lt_coe

@[to_additive (attr := simp)]
/-
**WithBot.bot_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：bot_lt_one [LT α] : ⊥ < (1 : WithBot α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
-/
theorem bot_lt_one [LT α] : ⊥ < (1 : WithBot α) := bot_lt_coe _

@[to_additive (attr := simp)]
/-
**WithBot.map_one** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : One α] {β : Type u_1} (f : α → β), WithBot.map f 1 
= ↑(f 1)
参数：f : α → β；f 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_one {β} (f : α → β) : (1 : WithBot α).map f = (f 1 : WithBot β) :=
  rfl

@[to_additive]
/-
**WithBot.map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：map_eq_one_iff {α} {f : α -> β} {v : WithBot α} [One β] : WithBot.map f v 
= 1 ↔ exists x, v = .some x ∧ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.map_eq_some_iff`：map_eq_some_iff {f : α -> β} {y : β} {v : WithB
ot α} : WithBot.map f v = .some y ↔ exists x, v = .some x ∧ f x = y
-/
theorem map_eq_one_iff {α} {f : α → β} {v : WithBot α} [One β] :
    WithBot.map f v = 1 ↔ ∃ x, v = .some x ∧ f x = 1 := map_eq_some_iff

@[to_additive]
/-
**WithBot.one_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：one_eq_map_iff {α} {f : α -> β} {v : WithBot α} [One β] : 1 = WithBot.map 
f v ↔ exists x, v = .some x ∧ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.some_eq_map_iff`：some_eq_map_iff {f : α -> β} {y : β} {v : WithB
ot α} : .some y = WithBot.map f v ↔ exists x, v = .some x ∧ f x = y
-/
theorem one_eq_map_iff {α} {f : α → β} {v : WithBot α} [One β] :
    1 = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = 1 := some_eq_map_iff
/-
**WithBot.zeroLEOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBo
t α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
instance zeroLEOneClass [Zero α] [LE α] [ZeroLEOneClass α] : ZeroLEOneClass (WithBot α) :=
  ⟨coe_le_coe.2 zero_le_one⟩

end One

section Add
variable [Add α] {w x y z : WithBot α} {a b : α}

/-
**WithBot.add** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：add : Add (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add : Add (WithBot α) :=
  ⟨WithBot.map₂ (· + ·)⟩
/-
**WithBot.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a + ↑b
参数：a b : α；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (a b : α) : ↑(a + b) = (a + b : WithBot α) := rfl
/-
**WithBot.bot_add** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] (x : WithBot α), ⊥ + x = ⊥
参数：x : WithBot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma bot_add (x : WithBot α) : ⊥ + x = ⊥ := rfl
/-
**WithBot.add_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = ⊥
参数：x : WithBot α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma add_bot (x : WithBot α) : x + ⊥ = ⊥ := by cases x <;> rfl
/-
**WithBot.add_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y : WithBot α}, x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma add_eq_bot : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ := by cases x <;> cases y <;> simp [← coe_add]
/-
**WithBot.add_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_ne_bot : x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma add_ne_bot : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := by cases x <;> cases y <;> simp [← coe_add]

@[simp]
/-
**WithBot.bot_lt_add** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：bot_lt_add [LT α] : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bot_lt_add [LT α] : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp_rw [WithBot.bot_lt_iff_ne_bot, add_ne_bot]
/-
**WithBot.add_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {a b : WithBot α} {c : α}, a + b = ↑c ↔ ∃ a'
 b', ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem add_eq_coe :
    ∀ {a b : WithBot α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊥, b, c => by simp
  | some a, ⊥, c => by simp
  | some a, some b, c => by norm_cast; simp
/-
**WithBot.add_coe_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_coe_eq_bot_iff : x + b = ⊥ ↔ x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma add_coe_eq_bot_iff : x + b = ⊥ ↔ x = ⊥ := by simp
/-
**WithBot.coe_add_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_add_eq_bot_iff : a + y = ⊥ ↔ y = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_add_eq_bot_iff : a + y = ⊥ ↔ y = ⊥ := by simp
/-
**WithBot._root_.IsAddLeftRegular.withBot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsAddLeftRegular.withBot (ha : IsAddLeftRegular a) :
    IsAddLeftRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _
/-
**WithBot._root_.IsAddRightRegular.withBot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsAddRightRegular.withBot (ha : IsAddRightRegular a) :
    IsAddRightRegular (a : WithBot α) := by
  rintro (_ | b) (_ | c) <;> simp [none_eq_bot, some_eq_coe, ← coe_add]; simpa using @ha _ _

set_option backward.isDefEq.respectTransparency false in
/-
**WithBot._root_.AddLECancellable.withBot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddLECancellable.withBot [LE α] (ha : AddLECancellable a) :
    AddLECancellable (a : WithBot α) := by
  rintro (_ | b) (_ | c)
  · simp [none_eq_bot]
  · simp [none_eq_bot]
  · simp [some_eq_coe, ← coe_add, none_eq_bot]
  · simpa [none_eq_bot, some_eq_coe, ← coe_add] using fun a ↦ ha a
/-
**WithBot.add_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_right_inj [IsRightCancelAdd α] (hz : z != ⊥) : x + z = y + z ↔ x = y
参数：hz : z != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma add_right_inj [IsRightCancelAdd α] (hz : z ≠ ⊥) : x + z = y + z ↔ x = y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]
/-
**WithBot.add_right_cancel** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_right_cancel [IsRightCancelAdd α] (hz : z != ⊥) (h : x + z = y + z) : 
x = y
参数：hz : z != ⊥；h : x + z = y + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.add_right_inj`：add_right_inj [IsRightCancelAdd α] (hz : z != ⊥) 
: x + z = y + z ↔ x = y
-/
lemma add_right_cancel [IsRightCancelAdd α] (hz : z ≠ ⊥) (h : x + z = y + z) : x = y :=
  (WithBot.add_right_inj hz).1 h
/-
**WithBot.add_left_inj** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_left_inj [IsLeftCancelAdd α] (hx : x != ⊥) : x + y = x + z ↔ y = z
参数：hx : x != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma add_left_inj [IsLeftCancelAdd α] (hx : x ≠ ⊥) : x + y = x + z ↔ y = z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]
/-
**WithBot.add_left_cancel** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_left_cancel [IsLeftCancelAdd α] (hx : x != ⊥) (h : x + y = x + z) : y 
= z
参数：hx : x != ⊥；h : x + y = x + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.add_left_inj`：add_left_inj [IsLeftCancelAdd α] (hx : x != ⊥) : x
 + y = x + z ↔ y = z
-/
lemma add_left_cancel [IsLeftCancelAdd α] (hx : x ≠ ⊥) (h : x + y = x + z) : y = z :=
  (WithBot.add_left_inj hx).1 h
/-
**WithBot.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithBot α) where elim x 
y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
instance addLeftMono [LE α] [AddLeftMono α] : AddLeftMono (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr
/-
**WithBot.addRightMono** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addRightMono [LE α] [AddRightMono α] : AddRightMono (WithBot α) where elim
 x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
instance addRightMono [LE α] [AddRightMono α] : AddRightMono (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using fun _ ↦ by gcongr
/-
**WithBot.addLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithBot α
) where elim x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
-/
instance addLeftReflectLT [LT α] [AddLeftReflectLT α] : AddLeftReflectLT (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add]; simpa using lt_of_add_lt_add_left
/-
**WithBot.addRightReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithBo
t α) where elim x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
-/
instance addRightReflectLT [LT α] [AddRightReflectLT α] : AddRightReflectLT (WithBot α) where
  elim x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_add, swap]; simpa using lt_of_add_lt_add_right
/-
**WithBot.le_of_add_le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LE α] [AddLeft
ReflectLE α], x ≠ ⊥ → x + y ≤ x + z → y ≤ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
-/
protected lemma le_of_add_le_add_left [LE α] [AddLeftReflectLE α] (hx : x ≠ ⊥) :
    x + y ≤ x + z → y ≤ z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using le_of_add_le_add_left
/-
**WithBot.le_of_add_le_add_right** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LE α] [AddRigh
tReflectLE α], z ≠ ⊥ → x + z ≤ y + z → x ≤ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
-/
protected lemma le_of_add_le_add_right [LE α] [AddRightReflectLE α] (hz : z ≠ ⊥) :
    x + z ≤ y + z → x ≤ y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using le_of_add_le_add_right
/-
**WithBot.add_lt_add_left** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LT α] [AddLeft
StrictMono α], x ≠ ⊥ → y < z → x + y < x + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
protected lemma add_lt_add_left [LT α] [AddLeftStrictMono α] (hx : x ≠ ⊥) :
    y < z → x + y < x + z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr
/-
**WithBot.add_lt_add_right** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LT α] [AddRigh
tStrictMono α], z ≠ ⊥ → x < y → x + z < y + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
-/
protected lemma add_lt_add_right [LT α] [AddRightStrictMono α] (hz : z ≠ ⊥) :
    x < y → x + z < y + z := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]; simpa using fun _ ↦ by gcongr
/-
**WithBot.add_le_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LE α] [AddLeft
Mono α] [AddLeftReflectLE α],   x ≠ ⊥ → (x + y ≤ x + z ↔ y ≤ z)
参数：x + y ≤ x + z ↔ y ≤ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.le_of_add_le_add_left`：∀ {α : Type u} [inst : Add α] {x y z : Wi
thBot α} [inst_1 : LE α] [AddLeftReflectLE α], x ≠ ⊥ → x + y ≤ x + z → y ≤ z
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
protected lemma add_le_add_iff_left [LE α] [AddLeftMono α] [AddLeftReflectLE α] (hx : x ≠ ⊥) :
    x + y ≤ x + z ↔ y ≤ z := ⟨WithBot.le_of_add_le_add_left hx, fun _ ↦ by gcongr⟩
/-
**WithBot.add_le_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LE α] [AddRigh
tMono α] [AddRightReflectLE α],   z ≠ ⊥ → (x + z ≤ y + z ↔ x ≤ y)
参数：x + z ≤ y + z ↔ x ≤ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.le_of_add_le_add_right`：∀ {α : Type u} [inst : Add α] {x y z : W
ithBot α} [inst_1 : LE α] [AddRightReflectLE α], z ≠ ⊥ → x + z ≤ y + z → x ≤ y
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
protected lemma add_le_add_iff_right [LE α] [AddRightMono α] [AddRightReflectLE α] (hz : z ≠ ⊥) :
    x + z ≤ y + z ↔ x ≤ y := ⟨WithBot.le_of_add_le_add_right hz, fun _ ↦ by gcongr⟩
/-
**WithBot.add_lt_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LT α] [AddLeft
StrictMono α] [AddLeftReflectLT α],   x ≠ ⊥ → (x + y < x + z ↔ y < z)
参数：x + y < x + z ↔ y < z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
· 使用定理 `WithBot.add_lt_add_left`：∀ {α : Type u} [inst : Add α] {x y z : WithBot 
α} [inst_1 : LT α] [AddLeftStrictMono α], x ≠ ⊥ → y < z → x + y < x + z
-/
protected lemma add_lt_add_iff_left [LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (hx : x ≠ ⊥) :
    x + y < x + z ↔ y < z := ⟨lt_of_add_lt_add_left, WithBot.add_lt_add_left hx⟩
/-
**WithBot.add_lt_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {x y z : WithBot α} [inst_1 : LT α] [AddRigh
tStrictMono α] [AddRightReflectLT α],   z ≠ ⊥ → (x + z < y + z ↔ x < y)
参数：x + z < y + z ↔ x < y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
· 使用定理 `WithBot.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithBot
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊥ → x < y → x + z < y + z
-/
protected lemma add_lt_add_iff_right [LT α] [AddRightStrictMono α] [AddRightReflectLT α]
    (hz : z ≠ ⊥) : x + z < y + z ↔ x < y := ⟨lt_of_add_lt_add_right, WithBot.add_lt_add_right hz⟩
/-
**WithBot.add_lt_add_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {w x y z : WithBot α} [inst_1 : Preorder α] 
[AddLeftStrictMono α] [AddRightMono α],   w ≠ ⊥ → w ≤ y → x < z → w + x < y + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithBot.add_lt_add_left`：∀ {α : Type u} [inst : Add α] {x y z : WithBot 
α} [inst_1 : LT α] [AddLeftStrictMono α], x ≠ ⊥ → y < z → x + y < x + z
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
-/
protected theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w ≠ ⊥) (hwy : w ≤ y) (hxz : x < z) :
    w + x < y + z :=
  (WithBot.add_lt_add_left hw hxz).trans_le <| by gcongr
/-
**WithBot.add_lt_add_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : Add α] {w x y z : WithBot α} [inst_1 : Preorder α] 
[AddLeftMono α] [AddRightStrictMono α],   x ≠ ⊥ → w < y → x ≤ z → w + x < y + z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithBot.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithBot
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊥ → x < y → x + z < y + z
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
protected theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x ≠ ⊥) (hwy : w < y) (hxz : x ≤ z) :
    w + x < y + z :=
  (WithBot.add_lt_add_right hx hwy).trans_le <| by gcongr
/-
**WithBot.addLECancellable_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：addLECancellable_of_ne_bot [LE α] [AddLeftReflectLE α] (hx : x != ⊥) : Add
LECancellable x
参数：hx : x != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.le_of_add_le_add_left`：∀ {α : Type u} [inst : Add α] {x y z : Wi
thBot α} [inst_1 : LE α] [AddLeftReflectLE α], x ≠ ⊥ → x + y ≤ x + z → y ≤ z
-/
lemma addLECancellable_of_ne_bot [LE α] [AddLeftReflectLE α]
    (hx : x ≠ ⊥) : AddLECancellable x := fun _b _c ↦ WithBot.le_of_add_le_add_left hx
/-
**WithBot.addLECancellable_of_lt_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：addLECancellable_of_lt_bot [Preorder α] [AddLeftReflectLE α] (hx : x < ⊥) 
: AddLECancellable x
参数：hx : x < ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.addLECancellable_of_ne_bot`：addLECancellable_of_ne_bot [LE α] [A
ddLeftReflectLE α] (hx : x != ⊥) : AddLECancellable x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma addLECancellable_of_lt_bot [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊥) : AddLECancellable x := addLECancellable_of_ne_bot hx.ne
/-
**WithBot.addLECancellable_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) : AddLECancellabl
e (a : WithBot α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.addLECancellable_of_ne_bot`：addLECancellable_of_ne_bot [LE α] [A
ddLeftReflectLE α] (hx : x != ⊥) : AddLECancellable x
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
lemma addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithBot α) := addLECancellable_of_ne_bot coe_ne_bot
/-
**WithBot.addLECancellable_iff_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：addLECancellable_iff_ne_bot [Nonempty α] [Preorder α] [AddLeftReflectLE α]
 : AddLECancellable x ↔ x != ⊥ where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.addLECancellable_of_ne_bot`：addLECancellable_of_ne_bot [LE α] [A
ddLeftReflectLE α] (hx : x != ⊥) : AddLECancellable x
-/
lemma addLECancellable_iff_ne_bot [Nonempty α] [Preorder α]
    [AddLeftReflectLE α] : AddLECancellable x ↔ x ≠ ⊥ where
  mp := by rintro h rfl; exact (bot_lt_coe <| Classical.arbitrary _).not_ge <| h <| by simp
  mpr := addLECancellable_of_ne_bot

/--
Addition in `WithBot (WithTop α)` is right cancellative provided the element
being cancelled is not `⊤` or `⊥`.
-/
/-
**WithBot.add_le_add_iff_right'** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：add_le_add_iff_right' {α : Type*} [Add α] [LE α] [AddRightMono α] [AddRigh
tReflectLE α] {a b c : WithBot (WithTop α)} (hc : c != ⊥) (hc' : c != ⊤) : a + c
 <= b + c ↔ a <= b
参数：WithTop α；hc : c != ⊥；hc' : c != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Addition in `WithBot (WithTop α)` is right cancellative provided the element
being cancelled is not `⊤` or `⊥`.
-/
lemma add_le_add_iff_right' {α : Type*} [Add α] [LE α]
    [AddRightMono α] [AddRightReflectLE α]
    {a b c : WithBot (WithTop α)} (hc : c ≠ ⊥) (hc' : c ≠ ⊤) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a <;> induction b <;> induction c <;> norm_cast at * <;>
    aesop (add simp WithTop.add_le_add_iff_right)

--  There is no `WithBot.map_mul_of_mulHom`, since `WithBot` does not have a multiplication.
@[simp]
/-
**WithBot.map_add** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Add α] {F : Type u_1} [inst_1 : Add β]
 [inst_2 : FunLike F α β] [AddHomClass F α β]   (f : F) (a b : WithBot α), WithB
ot.map (⇑f) (a + b) = WithBot.map (⇑f) a + WithBot.map (⇑f) b
参数：f : F；a b : WithBot α；⇑f；a + b；⇑f；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.bot_add`：∀ {α : Type u} [inst : Add α] (x : WithBot α), ⊥ + x = 
⊥
· 使用定理 `WithBot.add_bot`：∀ {α : Type u} [inst : Add α] (x : WithBot α), x + ⊥ = 
⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.map_coe`：map_coe (f : α -> β) (a : α) : map f a = f a
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
-/
protected theorem map_add {F} [Add β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : WithBot α) :
    (a + b).map f = a.map f + b.map f := by
  induction a
  · exact (bot_add _).symm
  · induction b
    · exact (add_bot _).symm
    · rw [map_coe, map_coe, ← coe_add, ← coe_add, ← map_add]
      rfl

end Add

/-
**WithBot.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addSemigroup [AddSemigroup α] : AddSemigroup (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addSemigroup [AddSemigroup α] : AddSemigroup (WithBot α) :=
  inferInstanceAs <| AddSemigroup (WithTop α)
/-
**WithBot.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (WithBot α) :=
  inferInstanceAs <| AddCommSemigroup (WithTop α)
/-
**WithBot.addZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addZeroClass [AddZeroClass α] : AddZeroClass (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addZeroClass [AddZeroClass α] : AddZeroClass (WithBot α) :=
  inferInstanceAs <| AddZeroClass (WithTop α)

section AddMonoid
variable [AddMonoid α]

/-
**WithBot.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addMonoid : AddMonoid (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid (WithBot α) :=
  inferInstanceAs <| AddMonoid (WithTop α)

/-- Coercion from `α` to `WithBot α` as an `AddMonoidHom`. -/
/-
**WithBot.addHom** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
形式化陈述：addHom : α ->+ WithBot α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `α` to `WithBot α` as an `AddMonoidHom`.
-/
def addHom : α →+ WithBot α where
  toFun := WithTop.some
  map_zero' := rfl
  map_add' _ _ := rfl
/-
**WithBot.coe_addHom** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoid α], ⇑WithBot.addHom = WithBot.some
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_addHom : ⇑(addHom : α →+ WithBot α) = WithBot.some := rfl

@[simp, norm_cast]
/-
**WithBot.coe_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：coe_nsmul (a : α) (n : Nat) : ↑(n • a) = n • (a : WithBot α)
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
lemma coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithBot α) :=
  (addHom : α →+ WithBot α).map_nsmul _ _

end AddMonoid

/-
**WithBot.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (WithBot α) :=
  inferInstanceAs <| AddCommMonoid (WithTop α)

section NatCast
variable [NatCast α]

/-
**WithBot.** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (WithBot α) where natCast n := (n : α)
/-
**WithBot.unbotD_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : NatCast α] (d : α) (n : ℕ), WithBot.unbotD d ↑n = ↑
n
参数：d : α；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma unbotD_natCast (d : α) (n : ℕ) : unbotD d n = n := rfl

@[to_dual (attr := simp)]
/-
**WithBot.unbotD_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：unbotD_ofNat (d : α) (n : Nat) [n.AtLeastTwo] : unbotD d ofNat(n) = ofNat(
n)
参数：d : α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unbotD_ofNat (d : α) (n : ℕ) [n.AtLeastTwo] : unbotD d ofNat(n) = ofNat(n) := rfl

end NatCast

section AddMonoidWithOne
variable [AddMonoidWithOne α]

/-
**WithBot.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addMonoidWithOne : AddMonoidWithOne (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne : AddMonoidWithOne (WithBot α) :=
  inferInstanceAs <| AddMonoidWithOne (WithTop α)
/-
**WithBot.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_natCast (n : ℕ) : ((n : α) : WithBot α) = n := rfl
/-
**WithBot.natCast_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ), ↑n ≠ ⊥
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
@[simp] lemma natCast_ne_bot (n : ℕ) : (n : WithBot α) ≠ ⊥ := coe_ne_bot
/-
**WithBot.bot_ne_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ), ⊥ ≠ ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.bot_ne_coe`：bot_ne_coe : ⊥ != (a : WithBot α)
-/
@[simp] lemma bot_ne_natCast (n : ℕ) : (⊥ : WithBot α) ≠ n := bot_ne_coe
/-
**WithBot.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
, ↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α) : WithBot α) = ofNat(n) := rfl
/-
**WithBot.coe_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
 (m : α),   ↑m = OfNat.ofNat n ↔ m = OfNat.ofNat n
参数：n : ℕ；m : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
-/
@[simp] lemma coe_eq_ofNat (n : ℕ) [n.AtLeastTwo] (m : α) :
    (m : WithBot α) = ofNat(n) ↔ m = ofNat(n) :=
  coe_eq_coe
/-
**WithBot.ofNat_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
 (m : α),   OfNat.ofNat n = ↑m ↔ OfNat.ofNat n = m
参数：n : ℕ；m : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
-/
@[simp] lemma ofNat_eq_coe (n : ℕ) [n.AtLeastTwo] (m : α) :
    ofNat(n) = (m : WithBot α) ↔ ofNat(n) = m :=
  coe_eq_coe
/-
**WithBot.ofNat_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
, OfNat.ofNat n ≠ ⊥
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.natCast_ne_bot`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ↑n ≠ ⊥
-/
@[simp] lemma ofNat_ne_bot (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : WithBot α) ≠ ⊥ :=
  natCast_ne_bot n
/-
**WithBot.bot_ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ) [inst_1 : n.AtLeastTwo]
, ⊥ ≠ OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.bot_ne_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ⊥ ≠ ↑n
-/
@[simp] lemma bot_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (⊥ : WithBot α) ≠ ofNat(n) :=
  bot_ne_natCast n
/-
**WithBot.map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : AddMonoidWithOne α] {f : α → β} (n : ℕ
) [inst_1 : n.AtLeastTwo],   WithBot.map f (OfNat.ofNat n) = ↑(f (OfNat.ofNat n)
)
参数：n : ℕ；OfNat.ofNat n；f (OfNat.ofNat n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.map_coe`：map_coe (f : α -> β) (a : α) : map f a = f a
-/
@[simp] lemma map_ofNat {f : α → β} (n : ℕ) [n.AtLeastTwo] :
    WithBot.map f (ofNat(n) : WithBot α) = f ofNat(n) := map_coe f n
/-
**WithBot.map_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : AddMonoidWithOne α] {f : α → β} (n : ℕ
), WithBot.map f ↑n = ↑(f ↑n)
参数：n : ℕ；f ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.map_coe`：map_coe (f : α -> β) (a : α) : map f a = f a
-/
@[simp] lemma map_natCast {f : α → β} (n : ℕ) :
    WithBot.map f (n : WithBot α) = f n := map_coe f n
/-
**WithBot.map_eq_ofNat_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：map_eq_ofNat_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithBot β} : a
.map f = ofNat(n) ↔ exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.map_eq_some_iff`：map_eq_some_iff {f : α -> β} {y : β} {v : WithB
ot α} : WithBot.map f v = .some y ↔ exists x, v = .some x ∧ f x = y
-/
lemma map_eq_ofNat_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithBot β} :
    a.map f = ofNat(n) ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff
/-
**WithBot.ofNat_eq_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：ofNat_eq_map_iff {f : β -> α} {n : Nat} [n.AtLeastTwo] {a : WithBot β} : o
fNat(n) = a.map f ↔ exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.some_eq_map_iff`：some_eq_map_iff {f : α -> β} {y : β} {v : WithB
ot α} : .some y = WithBot.map f v ↔ exists x, v = .some x ∧ f x = y
-/
lemma ofNat_eq_map_iff {f : β → α} {n : ℕ} [n.AtLeastTwo] {a : WithBot β} :
    ofNat(n) = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff
/-
**WithBot.map_eq_natCast_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：map_eq_natCast_iff {f : β -> α} {n : Nat} {a : WithBot β} : a.map f = n ↔ 
exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.map_eq_some_iff`：map_eq_some_iff {f : α -> β} {y : β} {v : WithB
ot α} : WithBot.map f v = .some y ↔ exists x, v = .some x ∧ f x = y
-/
lemma map_eq_natCast_iff {f : β → α} {n : ℕ} {a : WithBot β} :
    a.map f = n ↔ ∃ x, a = .some x ∧ f x = n := map_eq_some_iff
/-
**WithBot.natCast_eq_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithBot`。
形式化陈述：natCast_eq_map_iff {f : β -> α} {n : Nat} {a : WithBot β} : n = a.map f ↔ 
exists x, a = .some x ∧ f x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.some_eq_map_iff`：some_eq_map_iff {f : α -> β} {y : β} {v : WithB
ot α} : .some y = WithBot.map f v ↔ exists x, v = .some x ∧ f x = y
-/
lemma natCast_eq_map_iff {f : β → α} {n : ℕ} {a : WithBot β} :
    n = a.map f ↔ ∃ x, a = .some x ∧ f x = n := some_eq_map_iff
/-
**WithBot.bot_lt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WithBot`。
形式化陈述：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst_1 : LT α] (n : ℕ), ⊥ < ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
-/
@[simp] lemma bot_lt_natCast [LT α] (n : ℕ) : (⊥ : WithBot α) < n :=
  WithBot.bot_lt_coe _

end AddMonoidWithOne

/-
**WithBot.charZero** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance charZero [AddMonoidWithOne α] [CharZero α] : CharZero (WithBot α) :=
  inferInstanceAs <| CharZero (WithTop α)
/-
**WithBot.addCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `WithBot`。
形式化陈述：addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (With
Bot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoidWithOne [AddCommMonoidWithOne α] : AddCommMonoidWithOne (WithBot α) :=
  inferInstanceAs <| AddCommMonoidWithOne (WithTop α)

/-- A version of `WithBot.map` for `OneHom`s. -/
@[to_additive (attr := simps -fullyApplied)
  /-- A version of `WithBot.map` for `ZeroHom`s -/]
/-
**WithBot._root_.OneHom.withBotMap** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def _root_.OneHom.withBotMap {M N : Type*} [One M] [One N] (f : OneHom M N) :
    OneHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_one' := by rw [WithBot.map_one, map_one, coe_one]

/-- A version of `WithBot.map` for `AddHom`s. -/
@[simps -fullyApplied]
/-
**WithBot._root_.AddHom.withBotMap** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithBot.map` for `AddHom`s.
-/
protected def _root_.AddHom.withBotMap {M N : Type*} [Add M] [Add N] (f : AddHom M N) :
    AddHom (WithBot M) (WithBot N) where
  toFun := WithBot.map f
  map_add' := WithBot.map_add f

/-- A version of `WithBot.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
/-
**WithBot._root_.AddMonoidHom.withBotMap** 是 Mathlib 中的一个定义，位于命名空间 `WithBot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithBot.map` for `AddMonoidHom`s.
-/
protected def _root_.AddMonoidHom.withBotMap {M N : Type*} [AddZeroClass M] [AddZeroClass N]
    (f : M →+ N) : WithBot M →+ WithBot N :=
  { ZeroHom.withBotMap f.toZeroHom, AddHom.withBotMap f.toAddHom with toFun := WithBot.map f }

end WithBot

namespace AddEquiv

variable {γ : Type*} [Add α] [Add β] [Add γ] (e e₁ : α ≃+ β) (e₂ : β ≃+ γ)

/-- A `AddEquiv` version of `Equiv.withBotCongr`. -/
@[to_dual (attr := simps! apply) /-- A `AddEquiv` version of `Equiv.withTopCongr`. -/]
/-
**AddEquiv.withBotCongr** 是 Mathlib 中的一个定义，位于命名空间 `AddEquiv`。
形式化陈述：withBotCongr : WithBot α ≃+ WithBot β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `AddEquiv` version of `Equiv.withBotCongr`.
-/
def withBotCongr : WithBot α ≃+ WithBot β where
  __ := e.toEquiv.withBotCongr
  map_add' := e.toAddHom.withBotMap.map_add'

@[to_dual (attr := simp)]
/-
**AddEquiv.coe_withBotCongr** 是 Mathlib 中的一个引理，位于命名空间 `AddEquiv`。
形式化陈述：coe_withBotCongr : e.withBotCongr = WithBot.map e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_withBotCongr : e.withBotCongr = WithBot.map e := rfl

@[to_dual (attr := simp)]
/-
**AddEquiv.withBotCongr_toEquiv** 是 Mathlib 中的一个引理，位于命名空间 `AddEquiv`。
形式化陈述：withBotCongr_toEquiv : e.withBotCongr = (e : α ≃ β).withBotCongr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma withBotCongr_toEquiv : e.withBotCongr = (e : α ≃ β).withBotCongr := rfl

@[to_dual (attr := simp)]
/-
**AddEquiv.withBotCongr_toAddHom** 是 Mathlib 中的一个引理，位于命名空间 `AddEquiv`。
形式化陈述：withBotCongr_toAddHom : e.withBotCongr = (e : AddHom α β).withBotMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquivClass.instAddHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Add M] [inst_1 : Add N] [inst_2 : EquivLike F M N]   [h : AddEquiv
Class F M N], AddHo…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma withBotCongr_toAddHom : e.withBotCongr = (e : AddHom α β).withBotMap := rfl

@[to_dual (attr := simp)]
/-
**AddEquiv.withBotCongr_refl** 是 Mathlib 中的一个引理，位于命名空间 `AddEquiv`。
形式化陈述：withBotCongr_refl : (AddEquiv.refl α).withBotCongr = AddEquiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `WithBot.map_id`：map_id : map (id : α -> α) = id
-/
lemma withBotCongr_refl : (AddEquiv.refl α).withBotCongr = AddEquiv.refl _ :=
  AddEquiv.ext <| congr_fun WithBot.map_id

@[to_dual (attr := simp)]
/-
**AddEquiv.withBotCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：withBotCongr_symm : e.withBotCongr.symm = e.symm.withBotCongr
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withBotCongr_symm : e.withBotCongr.symm = e.symm.withBotCongr := rfl

@[to_dual (attr := simp)]
/-
**AddEquiv.withBotCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：withBotCongr_trans : (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂
.withBotCongr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.withBotCongr_apply`：∀ {α : Type u} {β : Type v} [inst : Add α] 
[inst_1 : Add β] (e : α ≃+ β) (a : WithBot α),   e.withBotCongr a = WithBot.map 
(⇑e) a
· 使用定理 `WithBot.map_map`：map_map (h : β -> γ) (g : α -> β) (a : WithBot α) : map
 h (map g a) = map (h ∘ g) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem withBotCongr_trans :
    (e₁.trans e₂).withBotCongr = e₁.withBotCongr.trans e₂.withBotCongr := by
  ext x
  simp

end AddEquiv

