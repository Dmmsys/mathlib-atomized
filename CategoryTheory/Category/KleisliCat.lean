/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`CategoryTheory/Monad/Kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with CategoryTheory.Monad
-/

@[expose] public section


universe u v

namespace CategoryTheory

-- This file is about Lean 3 declaration "Kleisli".

/-- The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unusedArguments]
/-
**CategoryTheory.KleisliCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：KleisliCat (_ : Type u -> Type v)
参数：_ : Type u -> Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed
 to be lawful
yet.
-/
def KleisliCat (_ : Type u → Type v) :=
  Type u

/-- Construct an object of the Kleisli category from a type. -/
/-
**CategoryTheory.KleisliCat.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Kleisli
Cat`。
形式化陈述：(m : Type u → Type u_1) → Type u → CategoryTheory.KleisliCat m
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of the Kleisli category from a type.
-/
def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  α
/-
**CategoryTheory.KleisliCat.categoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.KleisliCat`。
形式化陈述：{m : Type u → Type v} → [Monad m] → CategoryTheory.CategoryStruct.{max u v
, u + 1} (CategoryTheory.KleisliCat m)
参数：CategoryTheory.KleisliCat m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] :
    CategoryStruct (KleisliCat m) where
  Hom α β := α → m β
  id _ x := pure x
  comp f g := f >=> g

@[ext]
/-
**CategoryTheory.KleisliCat.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Kleisl
iCat`。
形式化陈述：∀ {m : Type u → Type v} [inst : Monad m] (α β : CategoryTheory.KleisliCat 
m) (f g : α ⟶ β),   (∀ (x : α), f x = g x) → f = g
参数：α β : CategoryTheory.KleisliCat m；f g : α ⟶ β；∀ (x : α), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem KleisliCat.ext {m} [Monad.{u, v} m] (α β : KleisliCat m)
    (f g : α ⟶ β) (h : ∀ x, f x = g x) : f = g := funext h

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.KleisliCat.category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.K
leisliCat`。
形式化陈述：{m : Type u → Type v} →   [inst : Monad m] → [LawfulMonad m] → CategoryThe
ory.Category.{max u v, u + 1} (CategoryTheory.KleisliCat m)
参数：CategoryTheory.KleisliCat m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  ext <;>
  simp +unfoldPartialApp [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

@[simp]
/-
**CategoryTheory.KleisliCat.id_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Kle
isliCat`。
形式化陈述：∀ {m : Type u_1 → Type u_2} [inst : Monad m] (α : CategoryTheory.KleisliCa
t m),   CategoryTheory.CategoryStruct.id α = pure
参数：α : CategoryTheory.KleisliCat m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem KleisliCat.id_def {m} [Monad m] (α : KleisliCat m) : 𝟙 α = @pure m _ α :=
  rfl
/-
**CategoryTheory.KleisliCat.comp_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.K
leisliCat`。
形式化陈述：∀ {m : Type u_1 → Type u_2} [inst : Monad m] (α β γ : CategoryTheory.Kleis
liCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α),   CategoryTheory.CategoryStruct.comp
 xs ys a = xs a >>= ys
参数：α β γ : CategoryTheory.KleisliCat m；xs : α ⟶ β；ys : β ⟶ γ；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem KleisliCat.comp_def {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    (xs ≫ ys) a = xs a >>= ys :=
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (KleisliCat id) :=
  ⟨PUnit⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α) :=
  ⟨show α from default⟩

end CategoryTheory

