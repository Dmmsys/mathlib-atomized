/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Free monoids have unique products
-/

public section

assert_not_exists Cardinal Subsemiring Algebra Submodule StarModule

open Finset

/-- Any `FreeMonoid` has the `TwoUniqueProds` property. -/
/-
**FreeMonoid.instTwoUniqueProds** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FreeMonoid.instTwoUniqueProds {κ : Type*} : TwoUniqueProds (FreeMonoid κ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TwoUniqueProds.of_mulHom`：∀ {G : Type u} {H : Type v} [inst : Mul G] [in
st_1 : Mul H] (f : H →ₙ* G),   (∀ ⦃a b c d : H⦄, a * b = c * d → f a = f c ∧ f b
 = f d → a = c…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.append_inj`：∀ {α : Type u_1} {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ 
++ t₂ → s₁.length = s₂.length → s₁ = s₂ ∧ t₁ = t₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiplicative.instTwoUniqueProdsOfTwoUniqueSums`：∀ {M : Type u_1} [inst
 : Add M] [TwoUniqueSums M], TwoUniqueProds (Multiplicative M)
· 使用定理 `TwoUniqueSums.of_covariant_left`：∀ {G : Type u} [inst : Add G] [IsLeftCa
ncelAdd G] [inst_2 : LinearOrder G] [AddRightStrictMono G], TwoUniqueSums G
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Any `FreeMonoid` has the `TwoUniqueProds` property.
-/
instance FreeMonoid.instTwoUniqueProds {κ : Type*} : TwoUniqueProds (FreeMonoid κ) :=
  .of_mulHom ⟨Multiplicative.ofAdd ∘ List.length, fun _ _ ↦ congr_arg _ List.length_append⟩
    (fun _ _ _ _ h h' ↦ List.append_inj h <| Equiv.injective Multiplicative.ofAdd h'.1)

/-- Any `FreeAddMonoid` has the `TwoUniqueSums` property. -/
/-
**FreeAddMonoid.instTwoUniqueSums** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FreeAddMonoid.instTwoUniqueSums {κ : Type*} : TwoUniqueSums (FreeAddMonoid
 κ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TwoUniqueSums.of_addHom`：∀ {G : Type u} {H : Type v} [inst : Add G] [ins
t_1 : Add H] (f : H →ₙ+ G),   (∀ ⦃a b c d : H⦄, a + b = c + d → f a = f c ∧ f b 
= f d → a = c…
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.append_inj`：∀ {α : Type u_1} {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ 
++ t₂ → s₁.length = s₂.length → s₁ = s₂ ∧ t₁ = t₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TwoUniqueSums.of_covariant_left`：∀ {G : Type u} [inst : Add G] [IsLeftCa
ncelAdd G] [inst_2 : LinearOrder G] [AddRightStrictMono G], TwoUniqueSums G
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Any `FreeAddMonoid` has the `TwoUniqueSums` property.
-/
instance FreeAddMonoid.instTwoUniqueSums {κ : Type*} : TwoUniqueSums (FreeAddMonoid κ) :=
  .of_addHom ⟨_, fun _ _ => List.length_append⟩ (fun _ _ _ _ h h' ↦ List.append_inj h h'.1)
