/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Mathlib.Tactic.Attr.Register

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.
We use the `to_additive` attribute in order to generate a parallel API for additive monoids.

## Simp set for monoid object tautologies

In this file, we also provide a simp set called `mon_tauto` whose goal is to prove all tautologies
about morphisms from some (tensor) power of `M` to `M`, where `M` is a (commutative) monoid object
in a (braided) monoidal category.

Please read the documentation in `Mathlib/Tactic/Attr/Register.lean` for full details.

## TODO

* Check that `Mon MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the Cartesian monoidal structure on `MonCat` first,
  available in https://github.com/leanprover-community/mathlib3/pull/3463)
* More generally, check that `Mon (Mon C) ≌ CommMon C` when `C` is braided.
* Check that `Mon TopCat ≌ [bundled topological monoids]`.
* Check that `Mon AddCommGrpCat ≌ RingCat`.
  (We've already got `Mon (ModuleCat R) ≌ AlgCat R`,
  in `Mathlib/CategoryTheory/Monoidal/Internal/Module.lean`.)
* Can you transport this monoidal structure to `RingCat` or `AlgCat R`?
  How does it compare to the "native" one?
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃ u

open Function CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- An additive monoid object internal to a monoidal category. -/
/-
**CategoryTheory.AddMonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：AddMonObj (X : C) where /-- The zero morphism of an additive monoid object
. -/ zero : 𝟙_ C ⟶ X /-- The addition morphism of an additive monoid object. -/ 
add : X otimes X ⟶ X zero_add (X) : zero ▷ X ≫ add = (fun_ X).hom
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive monoid object internal to a monoidal category.
-/
class AddMonObj (X : C) where
  /-- The zero morphism of an additive monoid object. -/
  zero : 𝟙_ C ⟶ X
  /-- The addition morphism of an additive monoid object. -/
  add : X ⊗ X ⟶ X
  zero_add (X) : zero ▷ X ≫ add = (λ_ X).hom := by cat_disch
  add_zero (X) : X ◁ zero ≫ add = (ρ_ X).hom := by cat_disch
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `_root_.add_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  add_assoc (X) : (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add := by cat_disch

/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
@[to_additive]
/-
**CategoryTheory.MonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：MonObj (X : C) where /-- The unit morphism of a monoid object. -/ one : 𝟙_
 C ⟶ X /-- The multiplication morphism of a monoid object. -/ mul : X otimes X ⟶
 X one_mul (X) : one ▷ X ≫ mul = (fun_ X).hom
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "alg
ebra object".
-/
class MonObj (X : C) where
  /-- The unit morphism of a monoid object. -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  mul : X ⊗ X ⟶ X
  one_mul (X) : one ▷ X ≫ mul = (λ_ X).hom := by cat_disch
  mul_one (X) : X ◁ one ≫ mul = (ρ_ X).hom := by cat_disch
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `_root_.mul_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  mul_assoc (X) : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by cat_disch

namespace AddMonObj

variable {M : C} [MonObj M]

@[inherit_doc] scoped notation "σ" => AddMonObj.add
@[inherit_doc] scoped notation "σ[" M "]" => AddMonObj.add (X := M)
@[inherit_doc] scoped notation "ζ" => AddMonObj.zero
@[inherit_doc] scoped notation "ζ[" M "]" => AddMonObj.zero (X := M)

end AddMonObj

namespace MonObj
variable {M X Y : C} [MonObj M]

@[inherit_doc] scoped notation "μ" => MonObj.mul
@[inherit_doc] scoped notation "μ[" M "]" => MonObj.mul (X := M)
@[inherit_doc] scoped notation "η" => MonObj.one
@[inherit_doc] scoped notation "η[" M "]" => MonObj.one (X := M)

set_option linter.translateOverwrite false in
attribute [to_additive existing (attr := reassoc (attr := simp))] one_mul mul_one mul_assoc

/-- Transfer `MonObj` along an isomorphism. -/
-- Note: The simps lemmas are not tagged simp because their `#discr_tree_simp_key` are too generic.
@[to_additive (attr := simps! -isSimp, instance_reducible)
/-- Transfer `AddMonObj` along an isomorphism. -/]
/-
**CategoryTheory.MonObj.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonObj`。
形式化陈述：ofIso (e : M ≅ X) : MonObj X where one
参数：e : M ≅ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofIso (e : M ≅ X) : MonObj X where
  one := η[M] ≫ e.hom
  mul := (e.inv ⊗ₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (λ_ X).inv]
    simp only [comp_whiskerRight, tensorHom_def, Category.assoc,
      hom_inv_whiskerRight_assoc]
    simp [← tensorHom_def_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv]
    simp only [MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
      whiskerLeft_hom_inv_assoc, Iso.inv_hom_id]
    simp [← tensorHom_def'_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  mul_assoc := by simpa [← id_tensorHom, ← tensorHom_id,
      -associator_conjugation, associator_naturality_assoc] using
      congr(((e.inv ⊗ₘ e.inv) ⊗ₘ e.inv) ≫ $(MonObj.mul_assoc M) ≫ e.hom)

@[to_additive (attr := simps)]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonObj (𝟙_ C) where
  one := 𝟙 _
  mul := (λ_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

@[to_additive (attr := ext)]
/-
**CategoryTheory.MonObj.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonObj`。
形式化陈述：ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul) : h₁ = h₂
参数：h₁ h₂ : MonObj X；H : h₁.mul = h₂.mul。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.MonObj.one_mul`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul) : h₁ = h₂ := by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (λ_ _).inv ≫ (h₁.one ⊗ₘ h₂.one) ≫ h₁.mul
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

end MonObj

open scoped MonObj

namespace Mathlib.Tactic.MonTauto
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {M W X X₁ X₂ X₃ Y Y₁ Y₂ Y₃ Z Z₁ Z₂ : C} [MonObj M]

attribute [mon_tauto] Category.id_comp Category.comp_id Category.assoc
  id_tensorHom_id tensorμ tensorδ
  tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc
  leftUnitor_tensor_hom leftUnitor_tensor_hom_assoc
  leftUnitor_tensor_inv leftUnitor_tensor_inv_assoc
  rightUnitor_tensor_hom rightUnitor_tensor_hom_assoc
  rightUnitor_tensor_inv rightUnitor_tensor_inv_assoc

attribute [mon_tauto ←] tensorHom_id id_tensorHom

@[reassoc (attr := mon_tauto)]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.associator_hom_comp_tensorHom_tensorHom
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：associator_hom_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z
₁ ⟶ Z₂) : (α_ X₁ Y₁ Z₁).hom ≫ (f otimesₘ g otimesₘ h) = ((f otimesₘ g) otimesₘ h
) ≫ (α_ X₂ Y₂ Z₂).hom
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂；h : Z₁ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.associator_conjugation`：associator_conju
gation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') : (f otimesₘ 
g) otimesₘ h = (α_ X Y Z).hom ≫ (f otimesₘ g…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f ⊗ₘ g ⊗ₘ h) = ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).hom := by simp

@[reassoc (attr := mon_tauto)]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.associator_inv_comp_tensorHom_tensorHom
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：associator_inv_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z
₁ ⟶ Z₂) : (α_ X₁ Y₁ Z₁).inv ≫ ((f otimesₘ g) otimesₘ h) = (f otimesₘ g otimesₘ h
) ≫ (α_ X₂ Y₂ Z₂).inv
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂；h : Z₁ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.associator_conjugation`：associator_conju
gation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') : (f otimesₘ 
g) otimesₘ h = (α_ X Y Z).hom ≫ (f otimesₘ g…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).inv ≫ ((f ⊗ₘ g) ⊗ₘ h) = (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).inv := by simp

@[reassoc (attr := mon_tauto)]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.associator_hom_comp_tensorHom_tensorHom
_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：associator_hom_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (
h : Z₁ ⟶ Z₂) (gh : Y₂ otimes Z₂ ⟶ W) : (α_ X₁ Y₁ Z₁).hom ≫ (f otimesₘ ((g otimes
ₘ h) ≫ gh)) = ((f otimesₘ g) otimesₘ h) ≫ (α_ X₂ Y₂ Z₂).hom ≫ (𝟙 _ otimesₘ gh)
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂；h : Z₁ ⟶ Z₂；gh : Y₂ otimes Z₂ ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (gh : Y₂ ⊗ Z₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ gh)) =
      ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).hom ≫ (𝟙 _ ⊗ₘ gh) := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.associator_inv_comp_tensorHom_tensorHom
_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：associator_inv_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (
h : Z₁ ⟶ Z₂) (fg : X₂ otimes Y₂ ⟶ W) : (α_ X₁ Y₁ Z₁).inv ≫ (((f otimesₘ g) ≫ fg)
 otimesₘ h) = (f otimesₘ g otimesₘ h) ≫ (α_ X₂ Y₂ Z₂).inv ≫ (fg otimesₘ 𝟙 _)
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂；h : Z₁ ⟶ Z₂；fg : X₂ otimes Y₂ ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (fg : X₂ ⊗ Y₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).inv ≫ (((f ⊗ₘ g) ≫ fg) ⊗ₘ h) =
      (f ⊗ₘ g ⊗ₘ h) ≫ (α_ X₂ Y₂ Z₂).inv ≫ (fg ⊗ₘ 𝟙 _) := by simp [tensorHom_def']
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.eq_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {M : C}   [inst_2 : CategoryTheory.MonObj M],   (
CategoryTheory.MonoidalCategoryStruct.leftUnitor M).hom =     CategoryTheory.Cat
egoryStruct.comp       (CategoryTheory.MonoidalCategoryStruct.tensorHom Category
Theory.MonObj.one (CategoryTheory.CategoryStruct.id M))       CategoryTheory.Mon
Obj.mul
参数：CategoryTheory.MonoidalCategoryStruct.leftUnitor M；CategoryTheory.MonoidalCat
egoryStruct.tensorHom CategoryTheory.MonObj.one (CategoryTheory.CategoryStruct.i
d M)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonObj.one_mul`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := mon_tauto)] lemma eq_one_mul : (λ_ M).hom = (η ⊗ₘ 𝟙 M) ≫ μ := by simp
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.eq_mul_one** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {M : C}   [inst_2 : CategoryTheory.MonObj M],   (
CategoryTheory.MonoidalCategoryStruct.rightUnitor M).hom =     CategoryTheory.Ca
tegoryStruct.comp       (CategoryTheory.MonoidalCategoryStruct.tensorHom (Catego
ryTheory.CategoryStruct.id M) CategoryTheory.MonObj.one)       CategoryTheory.Mo
nObj.mul
参数：CategoryTheory.MonoidalCategoryStruct.rightUnitor M；CategoryTheory.MonoidalCa
tegoryStruct.tensorHom (CategoryTheory.CategoryStruct.id M) CategoryTheory.MonOb
j.one。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := mon_tauto)] lemma eq_mul_one : (ρ_ M).hom = (𝟙 M ⊗ₘ η) ≫ μ := by simp

@[to_additive (attr := reassoc (attr := mon_tauto))]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.leftUnitor_inv_one_tensor_mul** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：leftUnitor_inv_one_tensor_mul (f : X₁ ⟶ M) : (fun_ _).inv ≫ (η otimesₘ f) 
≫ μ = f
参数：f : X₁ ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonObj.one_mul`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_inv_one_tensor_mul (f : X₁ ⟶ M) :
    (λ_ _).inv ≫ (η ⊗ₘ f) ≫ μ = f := by simp [tensorHom_def']

@[to_additive (attr := reassoc (attr := mon_tauto))]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：rightUnitor_inv_tensor_one_mul (f : X₁ ⟶ M) : (ρ_ _).inv ≫ (f otimesₘ η) ≫
 μ = f
参数：f : X₁ ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_inv_tensor_one_mul (f : X₁ ⟶ M) :
    (ρ_ _).inv ≫ (f ⊗ₘ η) ≫ μ = f := by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.mul_assoc_hom** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：mul_assoc_hom (f : X ⟶ M) : (α_ X M M).hom ≫ (f otimesₘ μ) ≫ μ = ((f otime
sₘ 𝟙 M) ≫ μ otimesₘ 𝟙 M) ≫ μ
参数：f : X ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonObj.mul_assoc`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [sel
f : CategoryTheory.Mo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_assoc_hom (f : X ⟶ M) :
    (α_ X M M).hom ≫ (f ⊗ₘ μ) ≫ μ = ((f ⊗ₘ 𝟙 M) ≫ μ ⊗ₘ 𝟙 M) ≫ μ := by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]
/-
**CategoryTheory.Mathlib.Tactic.MonTauto.mul_assoc_inv** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Mathlib.Tactic.MonTauto`。
形式化陈述：mul_assoc_inv (f : X ⟶ M) : (α_ M M X).inv ≫ (μ otimesₘ f) ≫ μ = (𝟙 M otim
esₘ (𝟙 M otimesₘ f) ≫ μ) ≫ μ
参数：f : X ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonObj.mul_assoc`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [sel
f : CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_assoc_inv (f : X ⟶ M) :
    (α_ M M X).inv ≫ (μ ⊗ₘ f) ≫ μ = (𝟙 M ⊗ₘ (𝟙 M ⊗ₘ f) ≫ μ) ≫ μ := by simp [tensorHom_def']

end Mathlib.Tactic.MonTauto

variable {M N O X : C} [MonObj M] [MonObj N] [MonObj O]

open AddMonObj in
/-- The property that a morphism between additive monoid objects is an additive monoid morphism. -/
/-
**CategoryTheory._root_.CategoryTheory.IsAddMonHom** 是 Mathlib 中的一个类，位于命名空间 `Cat
egoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism between additive monoid objects is an additive mono
id morphism.
-/
class _root_.CategoryTheory.IsAddMonHom
    {M' N' : C} [AddMonObj M'] [AddMonObj N'] (f : M' ⟶ N') : Prop where
  zero_hom (f) : ζ ≫ f = ζ := by cat_disch
  add_hom (f) : σ ≫ f = (f ⊗ₘ f) ≫ σ := by cat_disch

/-- The property that a morphism between monoid objects is a monoid morphism. -/
@[to_additive]
/-
**CategoryTheory.IsMonHom** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsMonHom (f : M ⟶ N) : Prop where one_hom (f) : η ≫ f = η
参数：f : M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism between monoid objects is a monoid morphism.
-/
class IsMonHom (f : M ⟶ N) : Prop where
  one_hom (f) : η ≫ f = η := by cat_disch
  mul_hom (f) : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch

set_option linter.translateOverwrite false in
attribute [to_additive existing (attr := reassoc (attr := simp))] IsMonHom.one_hom IsMonHom.mul_hom

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (𝟙 M) where
/-
**CategoryTheory.instIsAddMonHomComp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {M N O : C}   [inst_2 : CategoryTheory.AddMonObj 
M] [inst_3 : CategoryTheory.AddMonObj N] [inst_4 : CategoryTheory.AddMonObj O]  
 (f : M ⟶ N) (g : N ⟶ O) [CategoryTheory.IsAddMonHom f] [CategoryTheory.IsAddMon
Hom g],   CategoryTheory.IsAddMonHom (CategoryTheory.CategoryStruct.comp f g)
参数：f : M ⟶ N；g : N ⟶ O；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsAddMonHom.zero_hom_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M' 
N' : C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.IsAddMonHom.zero_hom`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M' N' : C
}   {inst_2 : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsAddMonHom.add_hom_assoc`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M' N
' : C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.IsAddMonHom.add_hom`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M' N' : C}
   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
-/
instance instIsAddMonHomComp {M N O : C} [AddMonObj M] [AddMonObj N] [AddMonObj O]
    (f : M ⟶ N) (g : N ⟶ O)
    [IsAddMonHom f] [IsAddMonHom g] : IsAddMonHom (f ≫ g) where

@[to_additive existing]
/-
**CategoryTheory.instIsMonHomComp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {M N O : C}   [inst_2 : CategoryTheory.MonObj M] 
[inst_3 : CategoryTheory.MonObj N] [inst_4 : CategoryTheory.MonObj O] (f : M ⟶ N
)   (g : N ⟶ O) [CategoryTheory.IsMonHom f] [CategoryTheory.IsMonHom g],   Categ
oryTheory.IsMonHom (CategoryTheory.CategoryStruct.comp f g)
参数：f : M ⟶ N；g : N ⟶ O；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsMonHom.one_hom_assoc`：∀ {C : Type u₁} {inst : CategoryT
heory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C
}   {inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsMonHom.mul_hom_assoc`：∀ {C : Type u₁} {inst : CategoryT
heory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C
}   {inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
-/
instance instIsMonHomComp (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g] : IsMonHom (f ≫ g) where

attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
@[to_additive]
/-
**CategoryTheory.isMonHom_ofIso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isMonHom_ofIso (e : M ≅ X) : letI
参数：e : M ≅ X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.ofIso_mul`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M X : C}   [i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isMonHom_ofIso (e : M ≅ X) : letI := MonObj.ofIso e; IsMonHom e.hom := by
  let := MonObj.ofIso e; exact { }

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ≅ N) [IsMonHom f.hom] : IsMonHom f.inv where
  one_hom := by simp [Iso.comp_inv_eq]
  mul_hom := by simp [Iso.comp_inv_eq]

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : M ⟶ N} [IsIso f] [IsMonHom f] : IsMonHom (asIso f).hom := ‹_›

variable (C) in
/-- An additive monoid object internal to a monoidal category. -/
/-
**CategoryTheory.AddMon** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryThe
ory.MonoidalCategory C] → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive monoid object internal to a monoidal category.
-/
structure AddMon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [addMon : AddMonObj X]

variable (C) in
/-- A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
@[to_additive AddMon]
/-
**CategoryTheory.Mon** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryThe
ory.MonoidalCategory C] → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "alg
ebra object".
-/
structure Mon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]

attribute [instance] Mon.mon AddMon.addMon

namespace Mon

variable (C) in
/-- The trivial monoid object. We later show this is initial in `Mon C`.
-/
@[to_additive (attr := simps!)
/-- The trivial additive monoid object. We later show this is initial in `AddMon C` -/]
/-
**CategoryTheory.Mon.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：trivial : Mon C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def trivial : Mon C := mk (𝟙_ C)

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Mon C) :=
  ⟨trivial C⟩

end Mon

namespace MonObj

variable {M : C} [MonObj M]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.one_mul_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mo
nObj`。
形式化陈述：one_mul_hom {Z : C} (f : Z ⟶ M) : (η[M] otimesₘ f) ≫ μ[M] = (fun_ Z).hom ≫
 f
参数：f : Z ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {X₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g :…
· 使用定理 `CategoryTheory.MonObj.one_mul`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X Y : C} (f : X ⟶ Y),   CategoryTheory.Cat…
-/
theorem one_mul_hom {Z : C} (f : Z ⟶ M) : (η[M] ⊗ₘ f) ≫ μ[M] = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, one_mul, leftUnitor_naturality]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.mul_one_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mo
nObj`。
形式化陈述：mul_one_hom {Z : C} (f : Z ⟶ M) : (f otimesₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f
参数：f : Z ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def_assoc`：∀ {C : Type u} {𝒞 :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X
₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_naturality`：∀ {C : Type u} {
𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C]
 {X Y : C} (f : X ⟶ Y),   CategoryTheory.Cat…
-/
theorem mul_one_hom {Z : C} (f : Z ⟶ M) : (f ⊗ₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc, mul_one, rightUnitor_naturality]

variable (M) in
@[to_additive (attr := reassoc)]
/-
**CategoryTheory.MonObj.mul_assoc_flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.MonObj`。
形式化陈述：mul_assoc_flip : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.mul_assoc`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [sel
f : CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_assoc_flip : M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ := by
  simp

end MonObj

namespace MonObj

/-!
In this section, we prove that the category of monoids in a braided monoidal category is monoidal.

Given two monoids `M` and `N` in a braided monoidal category `C`,
the multiplication on the tensor product `M.X ⊗ N.X` is defined in the obvious way:
it is the tensor product of the multiplications on `M` and `N`,
except that the tensor factors in the source come in the wrong order,
which we fix by pre-composing with a permutation isomorphism constructed from the braiding.

(There is a subtlety here: in fact there are two ways to do these,
using either the positive or negative crossing.)

A more conceptual way of understanding this definition is the following:
The braiding on `C` gives rise to a monoidal structure on
the tensor product functor from `C × C` to `C`.
A pair of monoids in `C` gives rise to a monoid in `C × C`,
which the tensor product functor by being monoidal takes to a monoid in `C`.
The permutation isomorphism appearing in the definition of
the multiplication on the tensor product of two monoids is
an instance of a more general family of isomorphisms
which together form a strength that equips the tensor product functor with a monoidal structure,
and the monoid axioms for the tensor product follow from the monoid axioms for the tensor factors
plus the properties of the strength (i.e., monoidal functor axioms).
The strength `tensorμ` of the tensor product functor has been defined in
`Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`.
Its properties, stated as independent lemmas in that module,
are used extensively in the proofs below.
Notice that we could have followed the above plan not only conceptually
but also as a possible implementation and
could have constructed the tensor product of monoids via `mapMon`,
but we chose to give a more explicit definition directly in terms of `tensorμ`.

To complete the definition of the monoidal category structure on the category of monoids,
we need to provide definitions of associator and unitors.
The obvious candidates are the associator and unitors from `C`,
but we need to prove that they are monoid morphisms, i.e., compatible with unit and multiplication.
These properties translate to the monoidality of the associator and unitors
(with respect to the monoidal structures on the functors they relate),
which have also been proved in `Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`.

-/

-- The proofs that associators and unitors preserve monoid units don't require braiding.
@[to_additive]
/-
**CategoryTheory.MonObj.one_associator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.MonObj`。
形式化陈述：one_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] : ((fun_ (𝟙_ C
)).inv ≫ ((fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ η[N]) otimesₘ η[P])) ≫ (α_ M N P).ho
m = (fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ (fun_ (𝟙_ C)).inv ≫ (η[N] otimesₘ η[P]))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_tensor_inv`：leftUnitor_tensor
_inv (X Y : C) : (fun_ (X otimes Y)).inv = (fun_ X).inv ▷ Y ≫ (α_ (𝟙_ C) X Y).ho
m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N]) ⊗ₘ η[P])) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ (λ_ (𝟙_ C)).inv ≫ (η[N] ⊗ₘ η[P])) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), ← tensorHom_comp_tensorHom]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, ← tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  simp

@[to_additive]
/-
**CategoryTheory.MonObj.one_leftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.MonObj`。
形式化陈述：one_leftUnitor {M : C} [MonObj M] : ((fun_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) otimesₘ
 η[M])) ≫ (fun_ M).hom = η
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_leftUnitor {M : C} [MonObj M] :
    ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ η[M])) ≫ (λ_ M).hom = η := by
  simp

@[to_additive]
/-
**CategoryTheory.MonObj.one_rightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MonObj`。
形式化陈述：one_rightUnitor {M : C} [MonObj M] : ((fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ 𝟙 
(𝟙_ C))) ≫ (ρ_ M).hom = η
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_rightUnitor {M : C} [MonObj M] :
    ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

@[to_additive AddMon_tensor_zero_add]
/-
**CategoryTheory.MonObj.Mon_tensor_one_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MonObj`。
形式化陈述：Mon_tensor_one_mul (M N : C) [MonObj M] [MonObj N] : (((fun_ (𝟙_ C)).inv ≫
 (η[M] otimesₘ η[N])) ▷ (M otimes N)) ≫ tensorμ M N M N ≫ (μ otimesₘ μ) = (fun_ 
(M otimes N)).hom
参数：M N : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorμ_natural_left`：tensorμ_natural_le
ft {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C) : (f₁ otimesₘ f₂)
 ▷ (Z₁ otimes Z₂) ≫ tensorμ Y₁ Y₂ Z₁ Z₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.MonObj.one_mul`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_left_unitality`：tensor_left_unita
lity (X₁ X₂ : C) : (fun_ (X₁ otimes X₂)).hom = ((fun_ (𝟙_ C)).inv ▷ (X₁ otimes X
₂)) ≫ tensorμ (𝟙_ C) (𝟙_ C) X₁ X₂ ≫ ((fun_ …
-/
lemma Mon_tensor_one_mul (M N : C) [MonObj M] [MonObj N] :
    (((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (λ_ (M ⊗ N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

@[to_additive AddMon_tensor_add_zero]
/-
**CategoryTheory.MonObj.Mon_tensor_mul_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.MonObj`。
形式化陈述：Mon_tensor_mul_one (M N : C) [MonObj M] [MonObj N] : (M otimes N) ◁ ((fun_
 (𝟙_ C)).inv ≫ (η[M] otimesₘ η[N])) ≫ tensorμ M N M N ≫ (μ[M] otimesₘ μ[N]) = (ρ
_ (M otimes N)).hom
参数：M N : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorμ_natural_right`：tensorμ_natural_r
ight (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) : (Z₁ otimes Z₂
) ◁ (f₁ otimesₘ f₂) ≫ tensorμ Z₁ Z₂ Y₁ Y₂ =…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_right_unitality`：tensor_right_uni
tality (X₁ X₂ : C) : (ρ_ (X₁ otimes X₂)).hom = ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).i
nv) ≫ tensorμ X₁ X₂ (𝟙_ C) (𝟙_ C) ≫ ((ρ_ X₁)…
-/
lemma Mon_tensor_mul_one (M N : C) [MonObj M] [MonObj N] :
    (M ⊗ N) ◁ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ₘ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] ⊗ₘ μ[N]) =
      (ρ_ (M ⊗ N)).hom := by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

@[to_additive AddMon_tensor_add_assoc]
/-
**CategoryTheory.MonObj.Mon_tensor_mul_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MonObj`。
形式化陈述：Mon_tensor_mul_assoc (M N : C) [MonObj M] [MonObj N] : ((tensorμ M N M N ≫
 (μ otimesₘ μ)) ▷ (M otimes N)) ≫ tensorμ M N M N ≫ (μ otimesₘ μ) = (α_ (M otime
s N : C) (M otimes N) (M otimes N)).hom ≫ ((M otimes N : C) ◁ (tensorμ M N M N ≫
 (μ otimesₘ μ))) ≫ tensorμ M N M N ≫ (μ otimesₘ μ)
参数：M N : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorμ_natural_left`：tensorμ_natural_le
ft {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (Z₁ Z₂ : C) : (f₁ otimesₘ f₂)
 ▷ (Z₁ otimes Z₂) ≫ tensorμ Y₁ Y₂ Z₁ Z₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.MonObj.mul_assoc`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [sel
f : CategoryTheory.Mo…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_associativity`：tensor_associativi
ty (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C) : (tensorμ X₁ X₂ Y₁ Y₂ ▷ (Z₁ otimes Z₂)) ≫ tensorμ (X
₁ otimes Y₁) (X₂ otimes Y₂) Z₁ Z₂ ≫ ((α_ X…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorμ_natural_right`：tensorμ_natural_r
ight (Z₁ Z₂ : C) {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) : (Z₁ otimes Z₂
) ◁ (f₁ otimesₘ f₂) ≫ tensorμ Z₁ Z₂ Y₁ Y₂ =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Mon_tensor_mul_assoc (M N : C) [MonObj M] [MonObj N] :
    ((tensorμ M N M N ≫ (μ ⊗ₘ μ)) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ₘ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensorμ M N M N ≫ (μ ⊗ₘ μ))) ≫
          tensorμ M N M N ≫ (μ ⊗ₘ μ) := by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_assoc, mul_assoc, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

@[to_additive]
/-
**CategoryTheory.MonObj.mul_associator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.MonObj`。
形式化陈述：mul_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] : (tensorμ (M 
otimes N) P (M otimes N) P ≫ (tensorμ M N M N ≫ (μ otimesₘ μ) otimesₘ μ)) ≫ (α_ 
M N P).hom = ((α_ M N P).hom otimesₘ (α_ M N P).hom) ≫ tensorμ M (N otimes P) M 
(N otimes P) ≫ (μ otimesₘ tensorμ N P N P ≫ (μ otimesₘ μ))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.associator_monoidal`：associator_monoidal
 (X₁ X₂ X₃ Y₁ Y₂ Y₃ : C) : tensorμ (X₁ otimes X₂) X₃ (Y₁ otimes Y₂) Y₃ ≫ (tensor
μ X₁ X₂ Y₁ Y₂ ▷ (X₃ otimes Y₃)) ≫ (α_ (X₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] :
    (tensorμ (M ⊗ N) P (M ⊗ N) P ≫
          (tensorμ M N M N ≫ (μ ⊗ₘ μ) ⊗ₘ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ₘ (α_ M N P).hom) ≫
        tensorμ M (N ⊗ P) M (N ⊗ P) ≫
          (μ ⊗ₘ tensorμ N P N P ≫ (μ ⊗ₘ μ)) := by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

@[to_additive]
/-
**CategoryTheory.MonObj.mul_leftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.MonObj`。
形式化陈述：mul_leftUnitor {M : C} [MonObj M] : (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((fun_ (𝟙
_ C)).hom otimesₘ μ)) ≫ (fun_ M).hom = ((fun_ M).hom otimesₘ (fun_ M).hom) ≫ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_naturality`：∀ {C : Type u} {𝒞
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] 
{X Y : C} (f : X ⟶ Y),   CategoryTheory.Cat…
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_monoidal`：leftUnitor_monoidal
 (X₁ X₂ : C) : (fun_ X₁).hom otimesₘ (fun_ X₂).hom = tensorμ (𝟙_ C) X₁ (𝟙_ C) X₂
 ≫ ((fun_ (𝟙_ C)).hom ▷ (X₁ otimes X₂)) ≫…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_leftUnitor {M : C} [MonObj M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ₘ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

@[to_additive]
/-
**CategoryTheory.MonObj.mul_rightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.MonObj`。
形式化陈述：mul_rightUnitor {M : C} [MonObj M] : (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ otime
sₘ (fun_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom = ((ρ_ M).hom otimesₘ (ρ_ M).hom) ≫ μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_naturality`：∀ {C : Type u} {
𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C]
 {X Y : C} (f : X ⟶ Y),   CategoryTheory.Cat…
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_monoidal`：rightUnitor_monoid
al (X₁ X₂ : C) : (ρ_ X₁).hom otimesₘ (ρ_ X₂).hom = tensorμ X₁ (𝟙_ C) X₂ (𝟙_ C) ≫
 ((X₁ otimes X₂) ◁ (fun_ (𝟙_ C)).hom) ≫ (ρ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_rightUnitor {M : C} [MonObj M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ₘ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

namespace tensorObj

-- We don't want `tensorObj.one_def` to be simp as it would loop with `IsMonHom.one_hom` applied
-- to `(λ_ N.X).inv`.
@[to_additive (attr := simps -isSimp)]
/-
**CategoryTheory.MonObj.tensorObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon
Obj.tensorObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : C} [MonObj M] [MonObj N] : MonObj (M ⊗ N) where
  one := (λ_ (𝟙_ C)).inv ≫ (η ⊗ₘ η)
  mul := tensorμ M N M N ≫ (μ ⊗ₘ μ)
  one_mul := Mon_tensor_one_mul M N
  mul_one := Mon_tensor_mul_one M N
  mul_assoc := Mon_tensor_mul_assoc M N

end tensorObj

open IsMonHom

variable {X Y Z W : C} [MonObj X] [MonObj Y] [MonObj Z] [MonObj W]

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : X ⟶ Y} {g : Z ⟶ W} [IsMonHom f] [IsMonHom g] : IsMonHom (f ⊗ₘ g) where
  one_hom := by
    dsimp [tensorObj.one_def]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, one_hom, one_hom]
  mul_hom := by
    dsimp [tensorObj.mul_def]
    slice_rhs 1 2 => rw [tensorμ_natural]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, mul_hom, mul_hom, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (𝟙 X) where

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : Y ⟶ Z} [IsMonHom f] : IsMonHom (X ◁ f) where
  one_hom := by simpa using ((inferInstance : IsMonHom (𝟙 X ⊗ₘ f))).one_hom
  mul_hom := by simpa using ((inferInstance : IsMonHom (𝟙 X ⊗ₘ f))).mul_hom

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : X ⟶ Y} [IsMonHom f] : IsMonHom (f ▷ Z) where
  one_hom := by simpa using ((inferInstance : IsMonHom (f ⊗ₘ (𝟙 Z)))).one_hom
  mul_hom := by simpa using ((inferInstance : IsMonHom (f ⊗ₘ (𝟙 Z)))).mul_hom

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (α_ X Y Z).hom :=
  ⟨one_associator, mul_associator⟩

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (λ_ X).hom :=
  ⟨one_leftUnitor, mul_leftUnitor⟩

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (ρ_ X).hom :=
  ⟨one_rightUnitor, mul_rightUnitor⟩

@[to_additive]
/-
**CategoryTheory.MonObj.one_braiding** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.M
onObj`。
形式化陈述：one_braiding (X Y : C) [MonObj X] [MonObj Y] : η ≫ (β_ X Y).hom = η
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality`：braiding_naturality 
{X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (f otimesₘ g) ≫ (braiding Y Y').hom 
= (braiding X X').hom ≫ (g otimesₘ f)
· 使用定理 `CategoryTheory.braiding_tensorUnit_right`：braiding_tensorUnit_right (X :
 C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_tensorHom`：eval_tensorHom {f g h i : C} {η 
η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f otimes h ⟶ g otimes i} (e_η : η = η') (e_θ : θ
 = θ') (e_ι : η' otimesₘ θ' …
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalHorizontalComp_cons_cons`：evalHorizontalComp
_cons_cons {f f' g g' h h' i i' : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {β : f
' ≅ g'} {θ : g' ⟶ h'} {θs : h' ⟶ i'} {ηθ :…
· 使用定理 `Mathlib.Tactic.Monoidal.evalHorizontalCompAux_of`：evalHorizontalCompAux_
of {f g h i : C} (η : f ⟶ g) (θ : h ⟶ i) : η otimesₘ θ = (Iso.refl _).hom ≫ (η o
timesₘ θ) ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalHorizontalComp_nil_nil`：evalHorizontalComp_n
il_nil {f g h i : C} (α : f ≅ g) (β : h ≅ i) : (α otimesᵢ β).hom = (α otimesᵢ β)
.hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_tensorHom`：naturality_tensorHom {p f₁
 g₁ f₂ g₂ pf₁ pf₁f₂ : C} {η : f₁ ≅ g₁} {θ : f₂ ≅ g₂} (η_f₁ : p otimes f₁ ≅ pf₁) 
(η_g₁ : p otimes g₁ ≅ pf₁) (η_f₂ :…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
-/
lemma one_braiding (X Y : C) [MonObj X] [MonObj Y] : η ≫ (β_ X Y).hom = η := by
  simp only [tensorObj.one_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

end BraidedCategory

end MonObj

namespace AddMon

/-- A morphism of additive monoid objects. -/
@[ext]
/-
**CategoryTheory.AddMon.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.AddMon`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → CategoryTheory.AddMon C → CategoryTheor
y.AddMon C → Type v₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of additive monoid objects.
-/
structure Hom (M N : AddMon C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isAddMonHom_hom : IsAddMonHom hom]

attribute [instance] Hom.isAddMonHom_hom

end AddMon

namespace Mon

/-- A morphism of monoid objects. -/
@[ext, to_additive]
/-
**CategoryTheory.Mon.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → CategoryTheory.Mon C → CategoryTheory.M
on C → Type v₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of monoid objects.
-/
structure Hom (M N : Mon C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isMonHom_hom : IsMonHom hom]

attribute [instance] Hom.isMonHom_hom

/-- Construct a morphism `M ⟶ N` of `Mon C` from a map `f : M ⟶ N` and
compatibilities with the unit and the multiplication. -/
@[to_additive
/-- Construct a morphism `M ⟶ N` of `AddMon C` from a map `f : M ⟶ N` and
compatibilities with the zero and the addition. -/]
/-
**CategoryTheory.Mon.Hom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon.Hom`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {M N : CategoryTheory.Mon C} →   
      (f : M.X ⟶ N.X) →           autoParam (CategoryTheory.CategoryStruct.comp 
CategoryTheory.MonObj.one f = CategoryTheory.MonObj.one)               CategoryT
heory.Mon.Hom.mk'._auto_1 →             autoParam                 (CategoryTheor
y.CategoryStruct.comp CategoryTheory.MonObj.mul f =                   CategoryTh
eory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.tensorHom f f)  
                   CategoryTheory.MonObj.mul)                 CategoryTheory.Mon
.Hom.mk'._auto_3 →               M.Hom N
参数：f : M.X ⟶ N.X；CategoryTheory.CategoryStruct.comp CategoryTheory.MonObj.one f 
= CategoryTheory.MonObj.one；CategoryTheory.CategoryStruct.comp CategoryTheory.Mo
nObj.mul f =                   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.MonoidalCategoryStruct.tensorHom f f)                     CategoryTheory.MonOb
j.mul。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Hom.mk' {M N : Mon C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch) : Hom M N :=
  have : IsMonHom f := ⟨one_f, mul_f⟩
  .mk f

/-- The identity morphism on a monoid object. -/
@[to_additive (attr := simps)
/-- The identity morphism on an additive monoid object. -/]
/-
**CategoryTheory.Mon.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：id (M : Mon C) : Hom M M
参数：M : Mon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def id (M : Mon C) : Hom M M := ⟨𝟙 M.X⟩

@[to_additive]
/-
**CategoryTheory.Mon.homInhabited** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`
。
形式化陈述：homInhabited (M : Mon C) : Inhabited (Hom M M)
参数：M : Mon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance homInhabited (M : Mon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[to_additive (attr := simps)
/-- Composition of morphisms of additive monoid objects. -/]
/-
**CategoryTheory.Mon.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：comp {M N O : Mon C} (f : Hom M N) (g : Hom N O) : Hom M O where hom
参数：f : Hom M N；g : Hom N O。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comp {M N O : Mon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Mon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

/-- Construct a morphism `Mon.mk G ⟶ Mon.mk H` from a  map `f : G ⟶ H` and a `IsMonHom f`
instance. -/
@[to_additive (attr := simps!)
/-- Construct a morphism `AddMon.mk G ⟶ AddMon.mk H` from a  map `f : G ⟶ H` and a `IsAddMonHom f`
instance. -/]
/-
**CategoryTheory.Mon.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：ofHom {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] : Mon.mk A 
⟶ Mon.mk B
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofHom {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] : Mon.mk A ⟶ Mon.mk B :=
  .mk f

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Mon C} (f : M ⟶ N) : IsMonHom f.hom := f.isMonHom_hom

@[to_additive (attr := ext)]
/-
**CategoryTheory.Mon.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon.Hom`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {M N : CategoryTheory.Mon C} {f g : M ⟶ N}, f.h
om = g.hom → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
-/
lemma Hom.ext' {M N : Mon C} {f g : M ⟶ N} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

@[to_additive]
/-
**CategoryTheory.Mon.hom_injective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon
`。
形式化陈述：hom_injective {M N : Mon C} : Injective (Hom.hom : (M ⟶ N) -> (M.X ⟶ N.X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
-/
lemma hom_injective {M N : Mon C} : Injective (Hom.hom : (M ⟶ N) → (M.X ⟶ N.X)) :=
  fun _ _ ↦ Hom.ext

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.id_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：id_hom' (M : Mon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X
参数：M : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom' (M : Mon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[to_additive (attr := simp, reassoc)]
/-
**CategoryTheory.Mon.comp_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：comp_hom' {M N K : Mon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : Hom M K).hom 
= f.hom ≫ g.hom
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom' {M N K : Mon C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[to_additive (attr := simps)
/-- The forgetful functor from additive monoid objects to the ambient category. -/]
/-
**CategoryTheory.Mon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：forget : Mon C ⥤ C where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def forget : Mon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

@[to_additive]
/-
**CategoryTheory.Mon.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.M
on`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C],   (CategoryTheory.Mon.forget C).Faithful
参数：CategoryTheory.Mon.forget C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mon.Hom.ext'`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {M N : CategoryT
heory.Mon C} {f g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Mon.forget_map`：∀ (C : Type u₁) [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {X Y : Categor
yTheory.Mon C} (f :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (forget C).Faithful where

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : Mon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
@[to_additive /-- The forgetful functor from additive monoid objects to the ambient category
reflects isomorphisms. -/]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨.mk' (inv f.hom), by cat_disch⟩⟩

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Mon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

/-- Construct an isomorphism of monoid objects by giving a monoid isomorphism between the underlying
objects. -/
@[to_additive (attr := simps)
/-- Construct an isomorphism of additive monoid objects by giving a additive monoid
isomorphism between the underlying objects. -/]
/-
**CategoryTheory.Mon.mkIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：mkIso' {M N : C} [MonObj M] [MonObj N] (e : M ≅ N) [IsMonHom e.hom] : mk M
 ≅ mk N where hom
参数：e : M ≅ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mkIso' {M N : C} [MonObj M] [MonObj N] (e : M ≅ N) [IsMonHom e.hom] : mk M ≅ mk N where
  hom := Hom.mk e.hom
  inv := Hom.mk e.inv

/-- Construct an isomorphism of monoid objects by giving an isomorphism between the underlying
objects and checking compatibility with unit and multiplication only in the forward direction. -/
@[to_additive
/-- Construct an isomorphism of additive monoid objects by giving an isomorphism between
the underlying objects and checking compatibility with zero and addition only in
the forward direction. -/]
/-
**CategoryTheory.Mon.mkIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：mkIso {M N : Mon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X]
参数：e : M.X ≅ N.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev mkIso {M N : Mon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simps)]
/-
**CategoryTheory.Mon.uniqueHomFromTrivial** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Mon`。
形式化陈述：uniqueHomFromTrivial (A : Mon C) : Unique (trivial C ⟶ A) where default.ho
m
参数：A : Mon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHomFromTrivial (A : Mon C) : Unique (trivial C ⟶ A) where
  default.hom := η[A.X]
  default.isMonHom_hom.mul_hom := by simp [unitors_equal]
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_one, IsMonHom.one_hom]

open CategoryTheory.Limits

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasInitial (Mon C) :=
  hasInitial_of_unique (Mon.trivial C)

section BraidedCategory
variable [BraidedCategory C]

@[to_additive (attr := simps! tensorObj_X tensorHom_hom)]
/-
**CategoryTheory.Mon.monMonoidalStruct** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Mon`。
形式化陈述：monMonoidalStruct : MonoidalCategoryStruct (Mon C) where tensorObj M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monMonoidalStruct : MonoidalCategoryStruct (Mon C) where
  tensorObj M N := ⟨M.X ⊗ N.X⟩
  tensorHom f g := Hom.mk (f.hom ⊗ₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
  associator M N P := mkIso' <| associator M.X N.X P.X
  leftUnitor M := mkIso' <| leftUnitor M.X
  rightUnitor M := mkIso' <| rightUnitor M.X

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensorUnit_X** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`
。
形式化陈述：tensorUnit_X : (𝟙_ (Mon C)).X = 𝟙_ C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_X : (𝟙_ (Mon C)).X = 𝟙_ C := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensorUnit_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
n`。
形式化陈述：tensorUnit_one : η[(𝟙_ (Mon C)).X] = 𝟙 (𝟙_ C)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_one : η[(𝟙_ (Mon C)).X] = 𝟙 (𝟙_ C) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensorUnit_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
n`。
形式化陈述：tensorUnit_mul : μ[(𝟙_ (Mon C)).X] = (fun_ (𝟙_ C)).hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_mul : μ[(𝟙_ (Mon C)).X] = (λ_ (𝟙_ C)).hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensorObj_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon
`。
形式化陈述：tensorObj_one (X Y : Mon C) : η[(X otimes Y).X] = (fun_ (𝟙_ C)).inv ≫ (η[X
.X] otimesₘ η[Y.X])
参数：X Y : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_one (X Y : Mon C) : η[(X ⊗ Y).X] = (λ_ (𝟙_ C)).inv ≫ (η[X.X] ⊗ₘ η[Y.X]) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensorObj_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon
`。
形式化陈述：tensorObj_mul (X Y : Mon C) : μ[(X otimes Y).X] = tensorμ X.X Y.X X.X Y.X 
≫ (μ[X.X] otimesₘ μ[Y.X])
参数：X Y : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_mul (X Y : Mon C) :
    μ[(X ⊗ Y).X] = tensorμ X.X Y.X X.X Y.X ≫ (μ[X.X] ⊗ₘ μ[Y.X]) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.whiskerLeft_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.M
on`。
形式化陈述：whiskerLeft_hom {X Y : Mon C} (f : X ⟶ Y) (Z : Mon C) : (f ▷ Z).hom = f.ho
m ▷ Z.X
参数：f : X ⟶ Y；Z : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_hom {X Y : Mon C} (f : X ⟶ Y) (Z : Mon C) : (f ▷ Z).hom = f.hom ▷ Z.X := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.whiskerRight_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Mon`。
形式化陈述：whiskerRight_hom (X : Mon C) {Y Z : Mon C} (f : Y ⟶ Z) : (X ◁ f).hom = X.X
 ◁ f.hom
参数：X : Mon C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_hom (X : Mon C) {Y Z : Mon C} (f : Y ⟶ Z) : (X ◁ f).hom = X.X ◁ f.hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.leftUnitor_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Mon`。
形式化陈述：leftUnitor_hom_hom (X : Mon C) : (fun_ X).hom.hom = (fun_ X.X).hom
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_hom (X : Mon C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.leftUnitor_inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Mon`。
形式化陈述：leftUnitor_inv_hom (X : Mon C) : (fun_ X).inv.hom = (fun_ X.X).inv
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_inv_hom (X : Mon C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.rightUnitor_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Mon`。
形式化陈述：rightUnitor_hom_hom (X : Mon C) : (ρ_ X).hom.hom = (ρ_ X.X).hom
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_hom (X : Mon C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.rightUnitor_inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Mon`。
形式化陈述：rightUnitor_inv_hom (X : Mon C) : (ρ_ X).inv.hom = (ρ_ X.X).inv
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_inv_hom (X : Mon C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.associator_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Mon`。
形式化陈述：associator_hom_hom (X Y Z : Mon C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X)
.hom
参数：X Y Z : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_hom_hom (X Y Z : Mon C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.associator_inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Mon`。
形式化陈述：associator_inv_hom (X Y Z : Mon C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X)
.inv
参数：X Y Z : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_inv_hom (X Y Z : Mon C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensor_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：tensor_one (M N : Mon C) : η[(M otimes N).X] = (fun_ (𝟙_ C)).inv ≫ (η[M.X]
 otimesₘ η[N.X])
参数：M N : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_one (M N : Mon C) : η[(M ⊗ N).X] = (λ_ (𝟙_ C)).inv ≫ (η[M.X] ⊗ₘ η[N.X]) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.tensor_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：tensor_mul (M N : Mon C) : μ[(M otimes N).X] = tensorμ M.X N.X M.X N.X ≫ (
μ[M.X] otimesₘ μ[N.X])
参数：M N : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_mul (M N : Mon C) : μ[(M ⊗ N).X] = tensorμ M.X N.X M.X N.X ≫ (μ[M.X] ⊗ₘ μ[N.X]) := rfl

@[to_additive]
/-
**CategoryTheory.Mon.monMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：monMonoidal : MonoidalCategory (Mon C) where tensorHom_def
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monMonoidal : MonoidalCategory (Mon C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

-- We don't want `tensorObj.one_def` to be simp as it would loop with `IsMonHom.one_hom` applied
-- to `(λ_ N.X).inv`.
@[to_additive (attr := simps! -isSimp)]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : C} [MonObj M] [MonObj N] : MonObj (M ⊗ N) :=
  inferInstanceAs <| MonObj (Mon.mk M ⊗ Mon.mk N).X

variable (C)

set_option backward.defeqAttrib.useBackward true in
/-- The forgetful functor from `Mon C` to `C` is monoidal when `C` is monoidal. -/
@[to_additive /-- The forgetful functor from `AddMon C` to `C` is monoidal when `C` is monoidal. -/]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Mon C` to `C` is monoidal when `C` is monoidal.
-/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_μ (X Y : Mon C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.forget_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_δ (X Y : Mon C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end BraidedCategory
end Mon

/-!
We next show that if `C` is symmetric, then `Mon C` is braided, and indeed symmetric.

Note that `Mon C` is *not* braided in general when `C` is only braided.

The more interesting construction is the 2-category of monoids in `C`,
bimodules between the monoids, and intertwiners between the bimodules.

When `C` is braided, that is a monoidal 2-category.
-/
section SymmetricCategory

variable [SymmetricCategory C]

namespace MonObj

@[to_additive]
/-
**CategoryTheory.MonObj.mul_braiding** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.M
onObj`。
形式化陈述：mul_braiding (X Y : C) [MonObj X] [MonObj Y] : μ ≫ (β_ X Y).hom = ((β_ X Y
).hom otimesₘ (β_ X Y).hom) ≫ μ
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality`：braiding_naturality 
{X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (f otimesₘ g) ≫ (braiding Y Y').hom 
= (braiding X X').hom ≫ (g otimesₘ f)
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_assoc`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (W X Y 
Z : C) {Z_1 : C}   (h :     Category…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_hom_hom_hom_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_hom_inv_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] (X : C) {Y Z : C}   (f : Y ≅ Z) {Z_1 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}   [self
 : CategoryTheory.SymmetricCate…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_left`：associat
or_inv_naturality_left {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) ≫ (α
_ X' Y Z).inv = (α_ X Y Z).inv ≫ f ▷ Y ▷ Z
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality_right`：associator_
naturality_right (X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f ≫ (α_ X Y 
Z').hom = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_braiding (X Y : C) [MonObj X] [MonObj Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom ⊗ₘ (β_ X Y).hom) ≫ μ := by
  dsimp [tensorObj.mul_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp, ← comp_whiskerRight, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.assoc, pentagon_inv_assoc,
    Iso.hom_inv_id_assoc]
  slice_lhs 1 2 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 2 3 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 =>
    rw [← associator_naturality_right]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  simp only [Category.assoc]

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} [MonObj X] [MonObj Y] : IsMonHom (β_ X Y).hom :=
  ⟨one_braiding X Y, mul_braiding X Y⟩

end MonObj

namespace Mon

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SymmetricCategory (Mon C) where
  braiding X Y := mkIso' (β_ X.X Y.X)

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.braiding_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Mon`。
形式化陈述：braiding_hom_hom (M N : Mon C) : (β_ M N).hom.hom = (β_ M.X N.X).hom
参数：M N : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma braiding_hom_hom (M N : Mon C) : (β_ M N).hom.hom = (β_ M.X N.X).hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.braiding_inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Mon`。
形式化陈述：braiding_inv_hom (M N : Mon C) : (β_ M N).inv.hom = (β_ M.X N.X).inv
参数：M N : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma braiding_inv_hom (M N : Mon C) : (β_ M N).inv.hom = (β_ M.X N.X).inv := rfl

end Mon
end SymmetricCategory

variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor

section LaxMonoidal
variable [F.LaxMonoidal] [F'.LaxMonoidal] [G.LaxMonoidal] (X Y : C) [MonObj X] [MonObj Y]
  (f : X ⟶ Y) [IsMonHom f]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
@[to_additive
/-- The image of an additive monoid object under a lax monoidal functor is an additive
monoid object.-/]
/-
**CategoryTheory.Functor.monObjObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：monObjObj : MonObj (F.obj X) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev monObjObj : MonObj (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul := by simp [← F.map_comp]
  mul_one := by simp [← F.map_comp]
  mul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, MonObj.mul_assoc]
    simp

scoped[CategoryTheory.Obj] attribute [instance] CategoryTheory.Functor.monObjObj
  CategoryTheory.Functor.addMonObjObj

open scoped Obj

@[to_additive (attr := reassoc, simp) ζ_def]
/-
**CategoryTheory.Functor.obj.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[to_additive (attr := reassoc, simp) σ_def]
/-
**CategoryTheory.Functor.obj.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

@[to_additive]
/-
**CategoryTheory.Functor.map.instIsMonHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor.map`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F : CategoryTheory.
Functor C D} [inst_4 : F.LaxMonoidal] (X Y : C) [inst_5 : CategoryTheory.MonObj 
X]   [inst_6 : CategoryTheory.MonObj Y] (f : X ⟶ Y) [CategoryTheory.IsMonHom f],
 CategoryTheory.IsMonHom (F.map f)
参数：X Y : C；f : X ⟶ Y；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {D : Type u₂}   [inst_2 : CategoryT…
-/
instance map.instIsMonHom : IsMonHom (F.map f) where
  one_hom := by simp [← map_comp]
  mul_hom := by simp [← map_comp]

open MonObj

-- TODO: mapMod F A : Mod A ⥤ Mod (F.mapMon A)
variable (F) in
/-- A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon C ⥤ Mon D`.
-/
@[to_additive (attr := simps)
/-- A lax monoidal functor takes additive monoid objects to additive monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `AddMon C ⥤ AddMon D`.
-/]
/-
**CategoryTheory.Functor.mapMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：mapMon : Mon C ⥤ Mon D where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMon : Mon C ⥤ Mon D where
  obj A := .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[to_additive (attr := simp)]
/-
**CategoryTheory.Functor.id_mapMon_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：id_mapMon_one (X : Mon C) : η[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ η[X.X]
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_mapMon_one (X : Mon C) : η[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ η[X.X] := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Functor.id_mapMon_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：id_mapMon_mul (X : Mon C) : μ[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ μ[X.X]
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_mapMon_mul (X : Mon C) : μ[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ μ[X.X] := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Functor.comp_mapMon_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：comp_mapMon_one (X : Mon C) : η[((F ⋙ G).mapMon.obj X).X] = ε (F ⋙ G) ≫ (F
 ⋙ G).map η[X.X]
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapMon_one (X : Mon C) :
    η[((F ⋙ G).mapMon.obj X).X] = ε (F ⋙ G) ≫ (F ⋙ G).map η[X.X] :=
  rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Functor.comp_mapMon_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：comp_mapMon_mul (X : Mon C) : μ[((F ⋙ G).mapMon.obj X).X] = «μ» (F ⋙ G) _ 
_ ≫ (F ⋙ G).map μ[X.X]
参数：X : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapMon_mul (X : Mon C) :
    μ[((F ⋙ G).mapMon.obj X).X] = «μ» (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[X.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on monoid objects. -/
@[to_additive (attr := simps!)
/-- The identity functor is also the identity on additive monoid objects. -/]
/-
**CategoryTheory.Functor.mapMonIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon C) :=
  NatIso.ofComponents fun X ↦ Mon.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on monoid objects. -/
@[to_additive (attr := simps!)
/-- The composition functor is also the composition on additive monoid objects. -/]
/-
**CategoryTheory.Functor.mapMonCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapMonCompIso : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMonCompIso : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X ↦ Mon.mkIso (.refl _)

@[to_additive]
/-
**CategoryTheory.Functor.Faithful.mapMon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F : CategoryTheory.
Functor C D} [inst_4 : F.LaxMonoidal] [F.Faithful], F.mapMon.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
· 使用定理 `CategoryTheory.Functor.Faithful.map_injective`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected instance Faithful.mapMon [F.Faithful] : F.mapMon.Faithful where
  map_injective {_X _Y} _f _g hfg := Mon.Hom.ext <| map_injective congr(($hfg).hom)

set_option backward.defeqAttrib.useBackward true in
/-- Natural transformations between functors lift to monoid objects. -/
@[to_additive (attr := simps!)
/-- Natural transformations between functors lift to additive monoid objects. -/]
/-
**CategoryTheory.Functor.mapMonNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：mapMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapMon ⟶ F'.mapMon
 where app X
参数：f : F ⟶ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapMon ⟶ F'.mapMon where
  app X := .mk' (f.app _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural isomorphisms between functors lift to monoid objects. -/
@[to_additive (attr := simps!)
/-- Natural isomorphisms between functors lift to additive monoid objects. -/]
/-
**CategoryTheory.Functor.mapMonNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：mapMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapMon ≅ F'.mapM
on
参数：e : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapMon ≅ F'.mapMon :=
  NatIso.ofComponents fun X ↦ Mon.mkIso (e.app _)

attribute [local simp] ε_tensorHom_comp_μ_assoc in
@[to_additive instIsAddMonHomε]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (ε F) where

end LaxMonoidal

section OplaxMonoidal
variable [F.OplaxMonoidal]

open scoped MonObj in
/-- Pullback a monoid object along a fully faithful oplax monoidal functor. -/
@[to_additive (attr := simps)
/-- Pullback an additive monoid object along a fully faithful oplax monoidal functor. -/]
/-
**CategoryTheory.Functor.FullyFaithful.monObj** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             {F : CategoryTheory.Functor C D} →               [F.
OplaxMonoidal] →                 F.FullyFaithful → (X : C) → [CategoryTheory.Mon
Obj (F.obj X)] → CategoryTheory.MonObj X
参数：X : C；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev FullyFaithful.monObj (hF : F.FullyFaithful) (X : C) [MonObj (F.obj X)] : MonObj X where
  one := hF.preimage <| OplaxMonoidal.η F ≫ η[F.obj X]
  mul := hF.preimage <| OplaxMonoidal.δ F X X ≫ μ[F.obj X]
  one_mul := hF.map_injective <| by simp [← δ_natural_left_assoc]
  mul_one := hF.map_injective <| by simp [← δ_natural_right_assoc]
  mul_assoc := hF.map_injective <| by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

end OplaxMonoidal

section Monoidal
variable [F.Monoidal]

open scoped Obj

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/-
**CategoryTheory.Functor.Full.mapMon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F : CategoryTheory.
Functor C D} [inst_4 : F.Monoidal] [F.Full] [F.Faithful], F.mapMon.Full
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoε`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Mon.instIsMonHomHom`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {M N : Ca
tegoryTheory.Mon C} (f :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_assoc`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoμ`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
-/
protected instance Full.mapMon [F.Full] [F.Faithful] : F.mapMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      isMonHom_hom.one_hom :=
        F.map_injective <| by simpa [← hg, cancel_epi] using IsMonHom.one_hom f.hom
      isMonHom_hom.mul_hom :=
        F.map_injective <| by simpa [← hg, cancel_epi] using IsMonHom.mul_hom f.hom },
      Mon.Hom.ext hg⟩
/-
**CategoryTheory.Functor.FullyFaithful.isAddMonHom_preimage** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F : CategoryTheory.
Functor C D} [inst_4 : F.Monoidal] (hF : F.FullyFaithful) {X Y : C}   [inst_5 : 
CategoryTheory.AddMonObj X] [inst_6 : CategoryTheory.AddMonObj Y] (f : F.obj X ⟶
 F.obj Y)   [CategoryTheory.IsAddMonHom f], CategoryTheory.IsAddMonHom (hF.preim
age f)
参数：hF : F.FullyFaithful；f : F.obj X ⟶ F.obj Y；hF.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoε`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.IsAddMonHom.zero_hom`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M' N' : C
}   {inst_2 : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoμ`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.IsAddMonHom.add_hom`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M' N' : C}
   {inst_2 : CategoryThe…
-/
instance FullyFaithful.isAddMonHom_preimage (hF : F.FullyFaithful) {X Y : C}
    [AddMonObj X] [AddMonObj Y] (f : F.obj X ⟶ F.obj Y) [IsAddMonHom f] :
    IsAddMonHom (hF.preimage f) where
  zero_hom := hF.map_injective (by simp [← cancel_epi (ε F), ← obj.ζ_def_assoc, ← obj.ζ_def])
  add_hom := hF.map_injective (by
    simp [← obj.σ_def_assoc, ← obj.σ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)])

@[to_additive existing]
/-
**CategoryTheory.Functor.FullyFaithful.isMonHom_preimage** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor.FullyFaithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   {F : CategoryTheory.
Functor C D} [inst_4 : F.Monoidal] (hF : F.FullyFaithful) {X Y : C}   [inst_5 : 
CategoryTheory.MonObj X] [inst_6 : CategoryTheory.MonObj Y] (f : F.obj X ⟶ F.obj
 Y)   [CategoryTheory.IsMonHom f], CategoryTheory.IsMonHom (hF.preimage f)
参数：hF : F.FullyFaithful；f : F.obj X ⟶ F.obj Y；hF.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoε`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.instIsIsoμ`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D 
: Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
-/
instance FullyFaithful.isMonHom_preimage (hF : F.FullyFaithful) {X Y : C}
    [MonObj X] [MonObj Y] (f : F.obj X ⟶ F.obj Y) [IsMonHom f] :
    IsMonHom (hF.preimage f) where
  one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `F.mapMon : Mon C ⥤ Mon D` is fully
faithful too. -/
@[to_additive (attr := simps)
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `F.mapAddMon : AddMon C ⥤ AddMon D`
is fully faithful too. -/]
/-
**CategoryTheory.Functor.FullyFaithful.mapMon** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             {F : CategoryTheory.Functor C D} → [inst_4 : F.Monoi
dal] → F.FullyFaithful → F.mapMon.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def FullyFaithful.mapMon (hF : F.FullyFaithful) : F.mapMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
open Monoidal in
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on monoid objects as on objects. -/
@[to_additive (attr := simp)
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on additive monoid objects as on objects. -/]
/-
**CategoryTheory.Functor.essImage_mapMon** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：essImage_mapMon [F.Full] [F.Faithful] {M : Mon D} : F.mapMon.essImage M ↔ 
F.essImage M.X where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonObj.ofIso_one`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M X : C}   [i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Monoidal.ε_η_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonObj.ofIso_mul`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M X : C}   [i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
-/
lemma essImage_mapMon [F.Full] [F.Faithful] {M : Mon D} :
    F.mapMon.essImage M ↔ F.essImage M.X where
  mp := by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(Mon.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    let : MonObj (F.obj N) := .ofIso e.symm
    let : MonObj N := (FullyFaithful.ofFullyFaithful F).monObj N
    refine ⟨.mk N, ⟨Mon.mkIso e ?_ ?_⟩⟩ <;> simp

end Monoidal

section BraidedCategory
variable [BraidedCategory C] [BraidedCategory D] (F)

open scoped Obj

attribute [-simp] IsMonHom.one_hom_assoc in
attribute [local simp← ] tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc in
attribute [local simp] tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc MonObj.tensorObj.one_def
  MonObj.tensorObj.mul_def in
@[to_additive instIsAddMonHomμ]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.LaxBraided] (M N : C) [MonObj M] [MonObj N] : IsMonHom («μ» F M N) where
  one_hom := by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [-simp] IsMonHom.one_hom IsMonHom.one_hom_assoc IsMonHom.mul_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
@[to_additive]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε := .mk (ε F)
  «μ» M N := .mk («μ» F M.X N.X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [-simp] IsMonHom.one_hom IsMonHom.one_hom_assoc IsMonHom.mul_hom in
attribute [local simp← ] tensorHom_comp_tensorHom tensorHom_comp_tensorHom_assoc in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
@[to_additive]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Braided] : F.mapMon.Monoidal :=
  CoreMonoidal.toMonoidal {
    εIso := Mon.mkIso (Monoidal.εIso F)
    μIso M N := Mon.mkIso (Monoidal.μIso F M.X N.X) <| by simp [← Functor.map_comp]
  }

end BraidedCategory

variable [SymmetricCategory C] [SymmetricCategory D]

@[to_additive]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.LaxBraided] : F.mapMon.LaxBraided where
  braided M N := by ext; exact Functor.LaxBraided.braided ..

@[to_additive]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Braided] : F.mapMon.Braided where

set_option backward.defeqAttrib.useBackward true in
variable (C D) in
/-- `mapMon` is functorial in the lax monoidal functor. -/
@[to_additive (attr := simps)
/-- `mapAddMon` is functorial in the lax monoidal functor. -/]
/-
**CategoryTheory.Functor.mapMonFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon C ⥤ Mon D where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMonFunctor : LaxMonoidalFunctor C D ⥤ Mon C ⥤ Mon D where
  obj F := F.mapMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

end Functor

open CategoryTheory.Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [a.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to monoid objects. -/
@[to_additive (attr := simps)
/-- An adjunction of monoidal functors lifts to an adjunction of their lifts to additive
monoid objects. -/]
/-
**CategoryTheory.Adjunction.mapMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adj
unction`。
形式化陈述：mapMon : F.mapMon ⊣ G.mapMon where unit
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.IsMonoidal.instIsMonoidalUnit`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCa
tegory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Adjunction.IsMonoidal.instIsMonoidalCounit`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoidal
Category C] {D : Type u₂}   [inst_2 : CategoryT…
-/
def mapMon : F.mapMon ⊣ G.mapMon where
  unit := mapMonIdIso.inv ≫ mapMonNatTrans a.unit ≫ mapMonCompIso.hom
  counit := mapMonCompIso.inv ≫ mapMonNatTrans a.counit ≫ mapMonIdIso.hom

end Adjunction

namespace Equivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories lifts to an equivalence of their monoid objects. -/
@[to_additive (attr := simps)
/-- An equivalence of categories lifts to an equivalence of their additive monoid objects. -/]
/-
**CategoryTheory.Equivalence.mapMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Eq
uivalence`。
形式化陈述：mapMon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal
] : Mon C ≌ Mon D where functor
参数：e : C ≌ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.Equivalence.instIsMonoidalUnit`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalC
ategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Adjunction.Equivalence.instIsMonoidalCounit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoida
lCategory C] {D : Type u₂}   [inst_2 : CategoryT…
-/
def mapMon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
    Mon C ≌ Mon D where
  functor := e.functor.mapMon
  inverse := e.inverse.mapMon
  unitIso := mapMonIdIso.symm ≪≫ mapMonNatIso e.unitIso ≪≫ mapMonCompIso
  counitIso := mapMonCompIso.symm ≪≫ mapMonNatIso e.counitIso ≪≫ mapMonIdIso

end Equivalence

namespace Mon

namespace EquivLaxMonoidalFunctorPUnit

variable (C) in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps) laxMonoidalToAddMon
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.laxMonoidalToMon** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ⥤ Mon C w
here obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ⥤ Mon C where
  obj F := (F.mapMon : Mon _ ⥤ Mon C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps!) addMonToLaxMonoidalObj
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidalObj** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：monToLaxMonoidalObj (A : Mon C) : Discrete PUnit.{w + 1} ⥤ C
参数：A : Mon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monToLaxMonoidalObj (A : Mon C) :
    Discrete PUnit.{w + 1} ⥤ C := (Functor.const _).obj A.X

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Mon C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

@[to_additive (attr := simp) addMonToLaxMonoidalObj_ε]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidalObj_** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monToLaxMonoidalObj_ε (A : Mon C) :
    ε (monToLaxMonoidalObj A) = η[A.X] := rfl

@[to_additive (attr := simp) addMonToLaxMonoidalObj_μ]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidalObj_** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monToLaxMonoidalObj_μ (A : Mon C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = μ[A.X] := rfl

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps) addMonToLaxMonoidal
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidal** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：monToLaxMonoidal : Mon C ⥤ LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C w
here obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monToLaxMonoidal : Mon C ⥤ LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C where
  obj A := LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps!)
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.unitIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：unitIso : 𝟭 (LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C) ≅ laxMonoidalT
oMon C ⋙ monToLaxMonoidal C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F ↦ LaxMonoidalFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `counitIso`. -/
@[to_additive (attr := simps!) /-- Auxiliary definition for `counitIso`. -/]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.counitIsoAux** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：counitIsoAux (F : Mon C) : ((monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C).
obj F).X ≅ ((𝟭 (Mon C)).obj F).X
参数：F : Mon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `counitIso`.
-/
def counitIsoAux (F : Mon C) :
    ((monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C).obj F).X ≅ ((𝟭 (Mon C)).obj F).X :=
  Iso.refl _

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_zero]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidal_laxMonoidalTo
Mon_obj_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFuncto
rPUnit`。
形式化陈述：monToLaxMonoidal_laxMonoidalToMon_obj_one (F : Mon C) : η[((monToLaxMonoid
al C ⋙ laxMonoidalToMon C).obj F).X] = η[F.X] ≫ 𝟙 _
参数：F : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monToLaxMonoidal_laxMonoidalToMon_obj_one (F : Mon C) :
    η[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = η[F.X] ≫ 𝟙 _ :=
  rfl

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_add]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.monToLaxMonoidal_laxMonoidalTo
Mon_obj_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFuncto
rPUnit`。
形式化陈述：monToLaxMonoidal_laxMonoidalToMon_obj_mul (F : Mon C) : μ[((monToLaxMonoid
al C ⋙ laxMonoidalToMon C).obj F).X] = μ[F.X] ≫ 𝟙 _
参数：F : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monToLaxMonoidal_laxMonoidalToMon_obj_mul (F : Mon C) :
    μ[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = μ[F.X] ≫ 𝟙 _ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.isMonHom_counitIsoAux** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   (F : CategoryTheory.Mon C),   CategoryTheory.Is
MonHom (CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.counitIsoAux C F).hom
参数：C : Type u₁；F : CategoryTheory.Mon C；CategoryTheory.Mon.EquivLaxMonoidalFunct
orPUnit.counitIsoAux C F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem isMonHom_counitIsoAux (F : Mon C) :
    IsMonHom (counitIsoAux C F).hom where

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps!)
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/-
**CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit.counitIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Mon.EquivLaxMonoidalFunctorPUnit`。
形式化陈述：counitIso : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def counitIso : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon C) :=
  NatIso.ofComponents fun F ↦
    letI : IsMonHom (counitIsoAux.{w} C F).hom := isMonHom_counitIsoAux C F
    mkIso (counitIsoAux.{w} C F)

end EquivLaxMonoidalFunctorPUnit

open EquivLaxMonoidalFunctorPUnit

attribute [local simp] eqToIso_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[to_additive (attr := simps!)
/--
Additive monoid objects in `C` are "just" lax monoidal functors from
the trivial monoidal category to `C`.
-/]
/-
**CategoryTheory.Mon.equivLaxMonoidalFunctorPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Mon`。
形式化陈述：equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{w + 1})
 C ≌ Mon C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivLaxMonoidalFunctorPUnit : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ≌ Mon C where
  functor := laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

end Mon

section

variable [BraidedCategory.{v₁} C]

open AddMonObj in
/-- Predicate for an additive monoid object to be commutative. -/
/-
**CategoryTheory.IsCommAddMonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsCommAddMonObj (X : C) [AddMonObj X] where add_comm (X) : (β_ X X).hom ≫ 
σ = σ
参数：X : C；X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for an additive monoid object to be commutative.
-/
class IsCommAddMonObj (X : C) [AddMonObj X] where
  add_comm (X) : (β_ X X).hom ≫ σ = σ := by cat_disch

/-- Predicate for a monoid object to be commutative. -/
@[to_additive]
/-
**CategoryTheory.IsCommMonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsCommMonObj (X : C) [MonObj X] where mul_comm (X) : (β_ X X).hom ≫ μ = μ
参数：X : C；X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for a monoid object to be commutative.
-/
class IsCommMonObj (X : C) [MonObj X] where
  mul_comm (X) : (β_ X X).hom ≫ μ = μ := by cat_disch

open scoped MonObj

namespace IsCommMonObj

attribute [reassoc (attr := simp, mon_tauto)] mul_comm

variable (M) in
@[to_additive (attr := reassoc (attr := simp, mon_tauto))]
/-
**CategoryTheory.IsCommMonObj.mul_comm'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.IsCommMonObj`。
形式化陈述：mul_comm' [IsCommMonObj M] : (β_ M M).inv ≫ μ = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.IsCommMonObj.mul_comm`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_comm' [IsCommMonObj M] : (β_ M M).inv ≫ μ = μ := by simp [← cancel_epi (β_ M M).hom]

@[to_additive]
/-
**CategoryTheory.IsCommMonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsCommM
onObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCommMonObj (𝟙_ C) where
  mul_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal]

end IsCommMonObj

variable (M) in
@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.mul_mul_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.MonObj`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (M : C)   [inst_2 : CategoryTheory.MonObj M] [ins
t_3 : CategoryTheory.BraidedCategory C] [CategoryTheory.IsCommMonObj M],   Categ
oryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategory.tensorμ M M M M) 
      (CategoryTheory.CategoryStruct.comp         (CategoryTheory.MonoidalCatego
ryStruct.tensorHom CategoryTheory.MonObj.mul CategoryTheory.MonObj.mul)         
CategoryTheory.MonObj.mul) =     CategoryTheory.CategoryStruct.comp       (Categ
oryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.MonObj.mul CategoryThe
ory.MonObj.mul)       CategoryTheory.MonObj.mul
参数：M : C；CategoryTheory.MonoidalCategory.tensorμ M M M M；CategoryTheory.Category
Struct.comp         (CategoryTheory.MonoidalCategoryStruct.tensorHom CategoryThe
ory.MonObj.mul CategoryTheory.MonObj.mul)         CategoryTheory.MonObj.mul；Cate
goryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.MonObj.mul CategoryTh
eory.MonObj.mul。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Mathlib.Tactic.MonTauto.mul_assoc_inv`：mul_assoc_inv (f :
 X ⟶ M) : (α_ M M X).inv ≫ (μ otimesₘ f) ≫ μ = (𝟙 M otimesₘ (𝟙 M otimesₘ f) ≫ μ)
 ≫ μ
· 使用引理 `CategoryTheory.Mathlib.Tactic.MonTauto.mul_assoc_hom`：mul_assoc_hom (f :
 X ⟶ M) : (α_ X M M).hom ≫ (f otimesₘ μ) ≫ μ = ((f otimesₘ 𝟙 M) ≫ μ otimesₘ 𝟙 M)
 ≫ μ
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom_id`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X₁ X₂
 : C),   CategoryTheory.MonoidalCateg…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsCommMonObj.mul_comm`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.Mathlib.Tactic.MonTauto.associator_hom_comp_tensorHom_ten
sorHom_comp_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [
inst_1 : CategoryTheory.MonoidalCategory C]   {W X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f : X₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MonObj.mul_mul_mul_comm [IsCommMonObj M] :
    tensorμ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]

variable (M) in
@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.mul_mul_mul_comm'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonObj`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] (M : C)   [inst_2 : CategoryTheory.MonObj M] [ins
t_3 : CategoryTheory.BraidedCategory C] [CategoryTheory.IsCommMonObj M],   Categ
oryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategory.tensorδ M M M M) 
      (CategoryTheory.CategoryStruct.comp         (CategoryTheory.MonoidalCatego
ryStruct.tensorHom CategoryTheory.MonObj.mul CategoryTheory.MonObj.mul)         
CategoryTheory.MonObj.mul) =     CategoryTheory.CategoryStruct.comp       (Categ
oryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.MonObj.mul CategoryThe
ory.MonObj.mul)       CategoryTheory.MonObj.mul
参数：M : C；CategoryTheory.MonoidalCategory.tensorδ M M M M；CategoryTheory.Category
Struct.comp         (CategoryTheory.MonoidalCategoryStruct.tensorHom CategoryThe
ory.MonObj.mul CategoryTheory.MonObj.mul)         CategoryTheory.MonObj.mul；Cate
goryTheory.MonoidalCategoryStruct.tensorHom CategoryTheory.MonObj.mul CategoryTh
eory.MonObj.mul。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Mathlib.Tactic.MonTauto.mul_assoc_inv`：mul_assoc_inv (f :
 X ⟶ M) : (α_ M M X).inv ≫ (μ otimesₘ f) ≫ μ = (𝟙 M otimesₘ (𝟙 M otimesₘ f) ≫ μ)
 ≫ μ
· 使用引理 `CategoryTheory.Mathlib.Tactic.MonTauto.mul_assoc_hom`：mul_assoc_hom (f :
 X ⟶ M) : (α_ X M M).hom ≫ (f otimesₘ μ) ≫ μ = ((f otimesₘ 𝟙 M) ≫ μ otimesₘ 𝟙 M)
 ≫ μ
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom_id`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X₁ X₂
 : C),   CategoryTheory.MonoidalCateg…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.IsCommMonObj.mul_comm'`：mul_comm' [IsCommMonObj M] : (β_ 
M M).inv ≫ μ = μ
· 使用定理 `CategoryTheory.Mathlib.Tactic.MonTauto.associator_hom_comp_tensorHom_ten
sorHom_comp_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [
inst_1 : CategoryTheory.MonoidalCategory C]   {W X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f : X₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MonObj.mul_mul_mul_comm' [IsCommMonObj M] :
    tensorδ M M M M ≫ (μ ⊗ₘ μ) ≫ μ = (μ ⊗ₘ μ) ≫ μ := by simp only [mon_tauto]

end

section SymmetricCategory
variable [SymmetricCategory C] {M N W X Y Z : C} [MonObj M] [MonObj N]

@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj M] [IsCommMonObj N] : IsCommMonObj (M ⊗ N) where
  mul_comm := by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, MonObj.tensorObj.mul_def,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]

end SymmetricCategory
end CategoryTheory

