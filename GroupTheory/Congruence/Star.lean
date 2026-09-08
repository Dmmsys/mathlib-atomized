/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.Algebra.Star.Basic

/-!
# Helpers for working with star operators on quotients.

TODO: consider defining `Star` versions of `Con` and `AddCon`.
-/

@[expose] public section

section Mul
variable {M : Type*} [Mul M] [StarMul M] {r : M → M → Prop}

/-
**ConGen.Rel.star** 是 Mathlib 中的一个定理，位于命名空间 `ConGen.Rel`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] [inst_1 : StarMul M] {r : M → M → Prop},  
 (∀ (a b : M), r a b → r (star a) (star b)) → ∀ ⦃a b : M⦄, ConGen.Rel r a b → Co
nGen.Rel r (star a) (star b)
参数：∀ (a b : M), r a b → r (star a) (star b)。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConGen.Rel.brecOn`：∀ {M : Type u_1} [inst : Mul M] {r : M → M → Prop} {m
otive : (a a_1 : M) → ConGen.Rel r a a_1 → Prop} {a a_1 : M}   (t : ConGen.Rel r
 a a_1)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
-/
theorem ConGen.Rel.star (hr : ∀ a b, r a b → r (star a) (star b))
    ⦃a b : M⦄ : Rel r a b → Rel r (star a) (star b)
  | refl _ => .refl _
  | symm h => .symm <| h.star hr
  | trans h1 h2 => .trans  (h1.star hr) (h2.star hr)
  | of _ _ h => .of _ _ (hr _ _ h)
  | mul h1 h2 => by
    rw [star_mul, star_mul]
    exact (h2.star hr).mul (h1.star hr)
/-
**conGen_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conGen_star (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b : M⦄ : co
nGen r a b -> conGen r (star a) (star b)
参数：hr : forall a b, r a b -> r (star a) (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConGen.Rel.star`：∀ {M : Type u_1} [inst : Mul M] [inst_1 : StarMul M] {r
 : M → M → Prop},   (∀ (a b : M), r a b → r (star a) (star b)) → ∀ ⦃a b : M⦄, Co
nGen.…
-/
theorem conGen_star (hr : ∀ a b, r a b → r (star a) (star b)) ⦃a b : M⦄ :
    conGen r a b → conGen r (star a) (star b) := (ConGen.Rel.star hr ·)

end Mul

section Add
variable {A : Type*} [AddMonoid A] [StarAddMonoid A] {r : A → A → Prop}

/-
**AddConGen.Rel.star** 是 Mathlib 中的一个定理，位于命名空间 `AddConGen.Rel`。
形式化陈述：∀ {A : Type u_1} [inst : AddMonoid A] [inst_1 : StarAddMonoid A] {r : A → 
A → Prop},   (∀ (a b : A), r a b → r (star a) (star b)) → ∀ ⦃a b : A⦄, AddConGen
.Rel r a b → AddConGen.Rel r (star a) (star b)
参数：∀ (a b : A), r a b → r (star a) (star b)。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConGen.Rel.brecOn`：∀ {M : Type u_1} [inst : Add M] {r : M → M → Prop}
 {motive : (a a_1 : M) → AddConGen.Rel r a a_1 → Prop} {a a_1 : M}   (t : AddCon
Gen.Rel r …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
-/
theorem AddConGen.Rel.star (hr : ∀ a b, r a b → r (star a) (star b))
    ⦃a b : A⦄ : Rel r a b → Rel r (star a) (star b)
  | refl _ => .refl _
  | symm h => .symm <| h.star hr
  | trans h1 h2 => .trans  (h1.star hr) (h2.star hr)
  | of _ _ h => .of _ _ (hr _ _ h)
  | add h1 h2 => by
    rw [star_add, star_add]
    exact (h1.star hr).add (h2.star hr)
/-
**addConGen_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：addConGen_star (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b : A⦄ :
 addConGen r a b -> addConGen r (star a) (star b)
参数：hr : forall a b, r a b -> r (star a) (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConGen.Rel.star`：∀ {A : Type u_1} [inst : AddMonoid A] [inst_1 : Star
AddMonoid A] {r : A → A → Prop},   (∀ (a b : A), r a b → r (star a) (star b)) → 
∀ ⦃a b :…
-/
theorem addConGen_star (hr : ∀ a b, r a b → r (star a) (star b)) ⦃a b : A⦄ :
    addConGen r a b → addConGen r (star a) (star b) := (AddConGen.Rel.star hr ·)

end Add

