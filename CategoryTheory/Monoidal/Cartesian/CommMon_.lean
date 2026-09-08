/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Yoneda embedding of `CommMon C`
-/

public section

assert_not_exists MonoidWithZero

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] {X : C}

variable (X) in
/-- If `X` represents a presheaf of commutative monoids, then `X` is a commutative monoid object. -/
/-
**CategoryTheory.IsCommMonObj.ofRepresentableBy** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsCommMonObj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory 
C] (X : C) (F : CategoryTheory.Functor Cᵒᵖ CommMonCat)   (α : (F.comp (CategoryT
heory.forget CommMonCat)).RepresentableBy X), CategoryTheory.IsCommMonObj X
参数：X : C；F : CategoryTheory.Functor Cᵒᵖ CommMonCat；α : (F.comp (CategoryTheory.f
orget CommMonCat)).RepresentableBy X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv'_comp`：∀ {C : Type u_1} 
{D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_fst`：braiding_hom_
fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_snd`：braiding_hom_
snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `X` represents a presheaf of commutative monoids, then `X` is a commutative m
onoid object.
-/
lemma IsCommMonObj.ofRepresentableBy (F : Cᵒᵖ ⥤ CommMonCat) (α : (F ⋙ forget _).RepresentableBy X) :
    letI : MonObj X := .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
    IsCommMonObj X := by
  let : MonObj X := .ofRepresentableBy X (F ⋙ forget₂ CommMonCat MonCat) α
  have : μ = α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X)) := rfl
  constructor
  simp_rw [this, ← α.homEquiv'.apply_eq_iff_eq, α.homEquiv'_comp,
    Equiv.apply_symm_apply, map_mul, ← α.homEquiv'_comp, op_tensorObj,
    braiding_hom_fst, braiding_hom_snd, _root_.mul_comm]

end CategoryTheory

