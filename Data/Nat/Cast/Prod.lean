/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Nat.Cast.Defs

/-!
# The product of two `AddMonoidWithOne`s.
-/

public section

assert_not_exists MonoidWithZero

variable {α β : Type*}

namespace Prod

variable [AddMonoidWithOne α] [AddMonoidWithOne β]

/-
**Prod.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instAddMonoidWithOne : AddMonoidWithOne (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne : AddMonoidWithOne (α × β) :=
  { Prod.instAddMonoid, @Prod.instOne α β _ _ with
    natCast := fun n => (n, n)
    natCast_zero := congr_arg₂ Prod.mk Nat.cast_zero Nat.cast_zero
    natCast_succ := fun _ => congr_arg₂ Prod.mk (Nat.cast_succ _) (Nat.cast_succ _) }

@[simp]
/-
**Prod.fst_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_natCast (n : Nat) : (n : α × β).fst = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem fst_natCast (n : ℕ) : (n : α × β).fst = n := by induction n <;> simp [*]

@[simp]
/-
**Prod.fst_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : α × β).1 = (ofNat(n) : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : α × β).1 = (ofNat(n) : α) :=
  rfl

@[simp]
/-
**Prod.snd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_natCast (n : Nat) : (n : α × β).snd = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem snd_natCast (n : ℕ) : (n : α × β).snd = n := by induction n <;> simp [*]

@[simp]
/-
**Prod.snd_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : α × β).2 = (ofNat(n) : β)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : α × β).2 = (ofNat(n) : β) :=
  rfl

end Prod

