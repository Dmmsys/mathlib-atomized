/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Eckmann-Hilton argument

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `EckmannHilton.commMonoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `EckmannHilton.commGroup`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/

public section

universe u

namespace EckmannHilton

variable {X : Type u}

/-- Local notation for `m a b`. -/
local notation a " <" m:51 "> " b => m a b

/-- `IsUnital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`. -/
/-
**EckmannHilton.IsUnital** 是 Mathlib 中的一个归纳类型，位于命名空间 `EckmannHilton`。
形式化陈述：{X : Type u} → (X → X → X) → X → Prop
参数：X → X → X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsUnital m e` expresses that `e : X` is a left and right unit
for the binary operation `m : X → X → X`.
-/
structure IsUnital (m : X → X → X) (e : X) : Prop extends Std.LawfulIdentity m e

@[to_additive EckmannHilton.AddZeroClass.IsUnital]
/-
**EckmannHilton.MulOneClass.isUnital** 是 Mathlib 中的一个定理，位于命名空间 `EckmannHilton.Mu
lOneClass`。
形式化陈述：∀ {X : Type u} [_G : MulOneClass X], EckmannHilton.IsUnital (fun x1 x2 => 
x1 * x2) 1
参数：fun x1 x2 => x1 * x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOneClass.one_mul`：∀ {M : Type u} [self : MulOneClass M] (a : M), 1 * 
a = a
· 使用定理 `MulOneClass.mul_one`：∀ {M : Type u} [self : MulOneClass M] (a : M), a * 
1 = a
-/
theorem MulOneClass.isUnital [_G : MulOneClass X] : IsUnital (· * ·) (1 : X) :=
  IsUnital.mk { left_id := MulOneClass.one_mul,
                right_id := MulOneClass.mul_one }

variable {m₁ m₂ : X → X → X} {e₁ e₂ : X}
variable (h₁ : IsUnital m₁ e₁) (h₂ : IsUnital m₂ e₂)
variable (distrib : ∀ a b c d, ((a <m₂> b) <m₁> c <m₂> d) = (a <m₁> c) <m₂> b <m₁> d)

include h₁ h₂ distrib

/-- If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structure,
see `eckmann_hilton.CommMonoid`. -/
/-
**EckmannHilton.one** 是 Mathlib 中的一个定理，位于命名空间 `EckmannHilton`。
形式化陈述：one : e₁ = e₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Std.LawfulLeftIdentity.left_id`：∀ {α : Sort u} {β : Sort u_1} {op : α → 
β → β} {o : outParam α} [self : Std.LawfulLeftIdentity op o] (a : β), op o a = a
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `EckmannHilton.IsUnital.toLawfulIdentity`：∀ {X : Type u} {m : X → X → X} 
{e : X}, EckmannHilton.IsUnital m e → Std.LawfulIdentity m e
· 使用定理 `Std.LawfulRightIdentity.right_id`：∀ {α : Sort u} {β : Sort u_1} {op : α 
→ β → α} {o : outParam β} [self : Std.LawfulRightIdentity op o] (a : α),   op a 
o = a
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o

--- 原说明 ---
If a type carries two unital binary operations that distribute over each other,
then they have the same unit elements.

In fact, the two operations are the same, and give a commutative monoid structur
e,
see `eckmann_hilton.CommMonoid`.
-/
theorem one : e₁ = e₂ := by
  simpa only [h₁.left_id, h₁.right_id, h₂.left_id, h₂.right_id] using distrib e₂ e₁ e₁ e₂

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.CommMonoid`. -/
/-
**EckmannHilton.mul** 是 Mathlib 中的一个定理，位于命名空间 `EckmannHilton`。
形式化陈述：mul : m₁ = m₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EckmannHilton.one`：one : e₁ = e₂
· 使用定理 `Std.LawfulRightIdentity.right_id`：∀ {α : Sort u} {β : Sort u_1} {op : α 
→ β → α} {o : outParam β} [self : Std.LawfulRightIdentity op o] (a : α),   op a 
o = a
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o
· 使用定理 `EckmannHilton.IsUnital.toLawfulIdentity`：∀ {X : Type u} {m : X → X → X} 
{e : X}, EckmannHilton.IsUnital m e → Std.LawfulIdentity m e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Std.LawfulLeftIdentity.left_id`：∀ {α : Sort u} {β : Sort u_1} {op : α → 
β → β} {o : outParam α} [self : Std.LawfulLeftIdentity op o] (a : β), op o a = a
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a type carries two unital binary operations that distribute over each other,
then these operations are equal.

In fact, they give a commutative monoid structure, see `eckmann_hilton.CommMonoi
d`.
-/
theorem mul : m₁ = m₂ := by
  funext a b
  calc
    m₁ a b = m₁ (m₂ a e₁) (m₂ e₁ b) := by
      { simp only [one h₁ h₂ distrib, h₂.left_id, h₂.right_id] }
    _ = m₂ a b := by simp only [distrib, h₁.left_id, h₁.right_id]

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.CommMonoid`. -/
/-
**EckmannHilton.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `EckmannHilton`。
形式化陈述：mul_comm : Std.Commutative m₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EckmannHilton.mul`：mul : m₁ = m₂
· 使用定理 `Std.LawfulLeftIdentity.left_id`：∀ {α : Sort u} {β : Sort u_1} {op : α → 
β → β} {o : outParam α} [self : Std.LawfulLeftIdentity op o] (a : β), op o a = a
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `EckmannHilton.IsUnital.toLawfulIdentity`：∀ {X : Type u} {m : X → X → X} 
{e : X}, EckmannHilton.IsUnital m e → Std.LawfulIdentity m e
· 使用定理 `Std.LawfulRightIdentity.right_id`：∀ {α : Sort u} {β : Sort u_1} {op : α 
→ β → α} {o : outParam β} [self : Std.LawfulRightIdentity op o] (a : α),   op a 
o = a
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If a type carries two unital binary operations that distribute over each other,
then these operations are commutative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.CommMonoi
d`.
-/
theorem mul_comm : Std.Commutative m₂ :=
  ⟨fun a b => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib e₂ a b e₂⟩

/-- If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.CommMonoid`. -/
/-
**EckmannHilton.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `EckmannHilton`。
形式化陈述：mul_assoc : Std.Associative m₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EckmannHilton.mul`：mul : m₁ = m₂
· 使用定理 `Std.LawfulLeftIdentity.left_id`：∀ {α : Sort u} {β : Sort u_1} {op : α → 
β → β} {o : outParam α} [self : Std.LawfulLeftIdentity op o] (a : β), op o a = a
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `EckmannHilton.IsUnital.toLawfulIdentity`：∀ {X : Type u} {m : X → X → X} 
{e : X}, EckmannHilton.IsUnital m e → Std.LawfulIdentity m e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Std.LawfulRightIdentity.right_id`：∀ {α : Sort u} {β : Sort u_1} {op : α 
→ β → α} {o : outParam β} [self : Std.LawfulRightIdentity op o] (a : α),   op a 
o = a
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o

--- 原说明 ---
If a type carries two unital binary operations that distribute over each other,
then these operations are associative.

In fact, they give a commutative monoid structure, see `eckmann_hilton.CommMonoi
d`.
-/
theorem mul_assoc : Std.Associative m₂ :=
  ⟨fun a b c => by simpa [mul h₁ h₂ distrib, h₂.left_id, h₂.right_id] using distrib a b e₂ c⟩

/-- If a type carries a unital magma structure that distributes over a unital binary
operation, then the magma structure is a commutative monoid. -/
@[to_additive
      /-- If a type carries a unital additive magma structure that distributes over a unital binary
      operation, then the additive magma structure is a commutative additive monoid. -/]
/-
**EckmannHilton.commMonoid** 是 Mathlib 中的一个缩写定义，位于命名空间 `EckmannHilton`。
形式化陈述：commMonoid [h : MulOneClass X] (distrib : forall a b c d, ((a * b) <m₁> c 
* d) = (a <m₁> c) * b <m₁> d) : CommMonoid X
参数：distrib : forall a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulOneClass.one_mul`：∀ {M : Type u} [self : MulOneClass M] (a : M), 1 * 
a = a
· 使用定理 `MulOneClass.mul_one`：∀ {M : Type u} [self : MulOneClass M] (a : M), a * 
1 = a
-/
abbrev commMonoid [h : MulOneClass X]
    (distrib : ∀ a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d) : CommMonoid X :=
  { h with
      mul_comm := (mul_comm h₁ MulOneClass.isUnital distrib).comm,
      mul_assoc := (mul_assoc h₁ MulOneClass.isUnital distrib).assoc }

/-- If a type carries a group structure that distributes over a unital binary operation,
then the group is commutative. -/
@[to_additive
      /-- If a type carries an additive group structure that distributes over a unital binary
      operation, then the additive group is commutative. -/]
/-
**EckmannHilton.commGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `EckmannHilton`。
形式化陈述：commGroup [G : Group X] (distrib : forall a b c d, ((a * b) <m₁> c * d) = 
(a <m₁> c) * b <m₁> d) : CommGroup X
参数：distrib : forall a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.mul_comm`：∀ {M : Type u} [self : CommMonoid M] (a b : M), a *
 b = b * a
-/
abbrev commGroup [G : Group X]
    (distrib : ∀ a b c d, ((a * b) <m₁> c * d) = (a <m₁> c) * b <m₁> d) : CommGroup X :=
  { G, EckmannHilton.commMonoid h₁ distrib with .. }

end EckmannHilton

