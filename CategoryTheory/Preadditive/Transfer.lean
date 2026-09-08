/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Pulling back a preadditive structure along a fully faithful functor

A preadditive structure on a category `D` transfers to a preadditive structure on `C` for a given
fully faithful functor `F : C ⥤ D`.
-/

@[expose] public section
namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable {F : C ⥤ D} (hF : F.FullyFaithful)

namespace Preadditive


/-- If `D` is a preadditive category, any fully faithful functor `F : C ⥤ D` induces a preadditive
/-
**CategoryTheory.Preadditive.on** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Preadd
itive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on `C`. -/
@[instance_reducible]
/-
**CategoryTheory.Preadditive.ofFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Preadditive`。
形式化陈述：ofFullyFaithful : Preadditive C where homGroup P Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is a preadditive category, any fully faithful functor `F : C ⥤ D` induces
 a preadditive
structure on `C`.
-/
def ofFullyFaithful : Preadditive C where
  homGroup P Q := hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

end Preadditive

open Preadditive
namespace Functor.FullyFaithful

/-- The preadditive structure on `C` induced by a fully faithful functor `F : C ⥤ D` makes `F` an
additive functor. -/
/-
**CategoryTheory.Functor.FullyFaithful.additive_ofFullyFaithful** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：additive_ofFullyFaithful : letI : Preadditive C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.homEquiv_apply`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.homEquiv_symm_apply`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The preadditive structure on `C` induced by a fully faithful functor `F : C ⥤ D`
 makes `F` an
additive functor.
-/
lemma additive_ofFullyFaithful :
    letI : Preadditive C := Preadditive.ofFullyFaithful hF
    F.Additive :=
  letI : Preadditive C := Preadditive.ofFullyFaithful hF
  { map_add := by simp [Equiv.add_def] }

end Functor.FullyFaithful

namespace Equivalence

/-- The preadditive structure on `C` induced by an equivalence `e : C ≌ D` makes `e.inverse` an
additive functor. -/
/-
**CategoryTheory.Equivalence.additive_inverse_of_FullyFaithful** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：additive_inverse_of_FullyFaithful (e : C ≌ D) : letI : Preadditive C
参数：e : C ≌ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.additive_ofFullyFaithful`：additive_
ofFullyFaithful : letI : Preadditive C

--- 原说明 ---
The preadditive structure on `C` induced by an equivalence `e : C ≌ D` makes `e.
inverse` an
additive functor.
-/
lemma additive_inverse_of_FullyFaithful (e : C ≌ D) :
    letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
    e.inverse.Additive :=
  letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
  letI : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  e.inverse_additive

end Equivalence

end CategoryTheory

