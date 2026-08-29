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
the category of lax monoidal functors from the unit monoidal category to `C`. We also show that if
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

/--
Definition of `AddMonObj` / `AddMonObj` 的定义

English:
class AddMonObj
  parameters: (X : C)
  axioms and operations (5):
    - zero : 𝟙_ C ⟶ X
    - add : X otimes X ⟶ X
    - zero_add((X)) : zero ▷ X ≫ add = (fun_ X).hom  [default: by cat_disch]
    - add_zero((X)) : X ◁ zero ≫ add = (ρ_ X).hom  [default: by cat_disch]
    - add_assoc((X)) : (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add  [default: by cat_disch]

中文:
类 加法MonObj
  参数: (X : C)
  公理与运算 (5 个):
    - zero : 𝟙_ C ⟶ X
    - add : X otimes X ⟶ X
    - zero_add((X)) : zero ▷ X ≫ add = (fun_ X).hom  [默认: by cat_disch]
    - add_zero((X)) : X ◁ zero ≫ add = (ρ_ X).hom  [默认: by cat_disch]
    - add_assoc((X)) : (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add  [默认: by cat_disch]

Depends on / 依赖: add_zero, cat_disch
-/
class AddMonObj (X : C) where
  /-- The zero morphism of an additive monoid object. -/
  zero : 𝟙_ C ⟶ X
  /-- The addition morphism of an additive monoid object. -/
  add : X otimes X ⟶ X
  zero_add (X) : zero ▷ X ≫ add = (fun_ X).hom := by cat_disch
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
/--
Definition of `MonObj` / `MonObj` 的定义

English:
class MonObj
  parameters: (X : C)
  axioms and operations (5):
    - one : 𝟙_ C ⟶ X
    - mul : X otimes X ⟶ X
    - one_mul((X)) : one ▷ X ≫ mul = (fun_ X).hom  [default: by cat_disch]
    - mul_one((X)) : X ◁ one ≫ mul = (ρ_ X).hom  [default: by cat_disch]
    - mul_assoc((X)) : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul  [default: by cat_disch]

中文:
类 MonObj
  参数: (X : C)
  公理与运算 (5 个):
    - one : 𝟙_ C ⟶ X
    - mul : X otimes X ⟶ X
    - one_mul((X)) : one ▷ X ≫ mul = (fun_ X).hom  [默认: by cat_disch]
    - mul_one((X)) : X ◁ one ≫ mul = (ρ_ X).hom  [默认: by cat_disch]
    - mul_assoc((X)) : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul  [默认: by cat_disch]

Depends on / 依赖: cat_disch, mul_one
-/
class MonObj (X : C) where
  /-- The unit morphism of a monoid object. -/
  one : 𝟙_ C ⟶ X
  /-- The multiplication morphism of a monoid object. -/
  mul : X otimes X ⟶ X
  one_mul (X) : one ▷ X ≫ mul = (fun_ X).hom := by cat_disch
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
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : M ≅ X)
  body: η[M] ≫ e.hom
  mul := (e.inv otimesₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (fun_ X).inv]
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
      congr(((e.inv otimesₘ e.inv) otimesₘ e.inv) ≫ $(MonObj.mul_assoc M) ≫ e.hom)

@[to_additive (attr := simps)]

中文:
定义 ofIso
  签名: (e : M ≅ X)
  定义体: η[M] ≫ e.hom
  mul := (e.inv otimesₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (fun_ X).inv]
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
      congr(((e.inv otimesₘ e.inv) otimesₘ e.inv) ≫ $(MonObj.mul_assoc M) ≫ e.hom)

@[to_additive (attr := simps)]

Depends on / 依赖: e.hom
-/
def ofIso (e : M ≅ X) : MonObj X where
  one := η[M] ≫ e.hom
  mul := (e.inv otimesₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (fun_ X).inv]
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
      congr(((e.inv otimesₘ e.inv) otimesₘ e.inv) ≫ $(MonObj.mul_assoc M) ≫ e.hom)

@[to_additive (attr := simps)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonObj (𝟙_ C)
  body: 𝟙 _
  mul := (fun_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

@[to_additive (attr := ext)]

中文:
实例 :
  签名: MonObj (𝟙_ C)
  定义体: 𝟙 _
  mul := (fun_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

@[to_additive (attr := ext)]
-/
instance : MonObj (𝟙_ C) where
  one := 𝟙 _
  mul := (fun_ _).hom
  mul_assoc := by monoidal_coherence
  mul_one := by monoidal_coherence

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul)
  statement: h₁ = h₂
  proof: by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (fun_ _).inv ≫ (h₁.one otimesₘ h₂.one) ≫ h₁.mul
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

中文:
定理 ext
  条件: {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul)
  结论: h₁ = h₂
  证明: by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (fun_ _).inv ≫ (h₁.one otimesₘ h₂.one) ≫ h₁.mul
  · simp [tensorHom_def, H, ← unitors_equal]
  · simp [tensorHom_def']

Depends on / 依赖: fun_, tensorHom_def, unitors_equal
-/
theorem ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul) : h₁ = h₂ := by
  suffices h₁.one = h₂.one by cases h₁; cases h₂; subst H this; rfl
  trans (fun_ _).inv ≫ (h₁.one otimesₘ h₂.one) ≫ h₁.mul
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
/--
lemma `associator_hom_comp_tensorHom_tensorHom` / 引理 `associator_hom_comp_tensorHom_tensorHom`

English:
lemma associator_hom_comp_tensorHom_tensorHom
  given: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  proof: by simp

@[reassoc (attr := mon_tauto)]

中文:
引理 associator_hom_comp_tensorHom_tensorHom
  条件: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  证明: by simp

@[reassoc (attr := mon_tauto)]
-/
lemma associator_hom_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f otimesₘ g otimesₘ h) = ((f otimesₘ g) otimesₘ h) ≫ (α_ X₂ Y₂ Z₂).hom := by simp

@[reassoc (attr := mon_tauto)]
/--
lemma `associator_inv_comp_tensorHom_tensorHom` / 引理 `associator_inv_comp_tensorHom_tensorHom`

English:
lemma associator_inv_comp_tensorHom_tensorHom
  given: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  proof: by simp

@[reassoc (attr := mon_tauto)]

中文:
引理 associator_inv_comp_tensorHom_tensorHom
  条件: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  证明: by simp

@[reassoc (attr := mon_tauto)]
-/
lemma associator_inv_comp_tensorHom_tensorHom (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    (α_ X₁ Y₁ Z₁).inv ≫ ((f otimesₘ g) otimesₘ h) = (f otimesₘ g otimesₘ h) ≫ (α_ X₂ Y₂ Z₂).inv := by simp

@[reassoc (attr := mon_tauto)]
/--
lemma `associator_hom_comp_tensorHom_tensorHom_comp` / 引理 `associator_hom_comp_tensorHom_tensorHom_comp`

English:
lemma associator_hom_comp_tensorHom_tensorHom_comp
  statement: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  proof: by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]

中文:
引理 associator_hom_comp_tensorHom_tensorHom_comp
  结论: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  证明: by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]

Depends on / 依赖: tensorHom_def
-/
lemma associator_hom_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (gh : Y₂ otimes Z₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).hom ≫ (f otimesₘ ((g otimesₘ h) ≫ gh)) =
      ((f otimesₘ g) otimesₘ h) ≫ (α_ X₂ Y₂ Z₂).hom ≫ (𝟙 _ otimesₘ gh) := by simp [tensorHom_def]

@[reassoc (attr := mon_tauto)]
/--
lemma `associator_inv_comp_tensorHom_tensorHom_comp` / 引理 `associator_inv_comp_tensorHom_tensorHom_comp`

English:
lemma associator_inv_comp_tensorHom_tensorHom_comp
  statement: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  proof: by simp [tensorHom_def']

中文:
引理 associator_inv_comp_tensorHom_tensorHom_comp
  结论: (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
  证明: by simp [tensorHom_def']

Depends on / 依赖: tensorHom_def
-/
lemma associator_inv_comp_tensorHom_tensorHom_comp (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (fg : X₂ otimes Y₂ ⟶ W) :
    (α_ X₁ Y₁ Z₁).inv ≫ (((f otimesₘ g) ≫ fg) otimesₘ h) =
      (f otimesₘ g otimesₘ h) ≫ (α_ X₂ Y₂ Z₂).inv ≫ (fg otimesₘ 𝟙 _) := by simp [tensorHom_def']

/--
lemma `eq_one_mul` / 引理 `eq_one_mul`

English:
lemma eq_one_mul
  statement: (fun_ M).hom = (η otimesₘ 𝟙 M) ≫ μ
  proof: by simp

中文:
引理 eq_one_mul
  结论: (fun_ M).hom = (η otimesₘ 𝟙 M) ≫ μ
  证明: by simp
-/
@[to_additive (attr := mon_tauto)] lemma eq_one_mul : (fun_ M).hom = (η otimesₘ 𝟙 M) ≫ μ := by simp
/--
lemma `eq_mul_one` / 引理 `eq_mul_one`

English:
lemma eq_mul_one
  statement: (ρ_ M).hom = (𝟙 M otimesₘ η) ≫ μ
  proof: by simp

@[to_additive (attr := reassoc (attr := mon_tauto))]

中文:
引理 eq_mul_one
  结论: (ρ_ M).hom = (𝟙 M otimesₘ η) ≫ μ
  证明: by simp

@[to_additive (attr := reassoc (attr := mon_tauto))]
-/
@[to_additive (attr := mon_tauto)] lemma eq_mul_one : (ρ_ M).hom = (𝟙 M otimesₘ η) ≫ μ := by simp

@[to_additive (attr := reassoc (attr := mon_tauto))]
/--
lemma `leftUnitor_inv_one_tensor_mul` / 引理 `leftUnitor_inv_one_tensor_mul`

English:
lemma leftUnitor_inv_one_tensor_mul
  given: (f : X₁ ⟶ M)
  proof: by simp [tensorHom_def']

@[to_additive (attr := reassoc (attr := mon_tauto))]

中文:
引理 leftUnitor_inv_one_tensor_mul
  条件: (f : X₁ ⟶ M)
  证明: by simp [tensorHom_def']

@[to_additive (attr := reassoc (attr := mon_tauto))]

Depends on / 依赖: F.map, tensorHom_def
-/
lemma leftUnitor_inv_one_tensor_mul (f : X₁ ⟶ M) :
    (fun_ _).inv ≫ (η otimesₘ f) ≫ μ = f := by simp [tensorHom_def']

@[to_additive (attr := reassoc (attr := mon_tauto))]
/--
lemma `rightUnitor_inv_tensor_one_mul` / 引理 `rightUnitor_inv_tensor_one_mul`

English:
lemma rightUnitor_inv_tensor_one_mul
  given: (f : X₁ ⟶ M)
  proof: by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]

中文:
引理 rightUnitor_inv_tensor_one_mul
  条件: (f : X₁ ⟶ M)
  证明: by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]

Depends on / 依赖: tensorHom_def
-/
lemma rightUnitor_inv_tensor_one_mul (f : X₁ ⟶ M) :
    (ρ_ _).inv ≫ (f otimesₘ η) ≫ μ = f := by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]
/--
lemma `mul_assoc_hom` / 引理 `mul_assoc_hom`

English:
lemma mul_assoc_hom
  given: (f : X ⟶ M)
  proof: by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]

中文:
引理 mul_assoc_hom
  条件: (f : X ⟶ M)
  证明: by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]

Depends on / 依赖: tensorHom_def
-/
lemma mul_assoc_hom (f : X ⟶ M) :
    (α_ X M M).hom ≫ (f otimesₘ μ) ≫ μ = ((f otimesₘ 𝟙 M) ≫ μ otimesₘ 𝟙 M) ≫ μ := by simp [tensorHom_def]

@[to_additive (attr := reassoc (attr := mon_tauto))]
/--
lemma `mul_assoc_inv` / 引理 `mul_assoc_inv`

English:
lemma mul_assoc_inv
  given: (f : X ⟶ M)
  proof: by simp [tensorHom_def']

中文:
引理 mul_assoc_inv
  条件: (f : X ⟶ M)
  证明: by simp [tensorHom_def']

Depends on / 依赖: tensorHom_def
-/
lemma mul_assoc_inv (f : X ⟶ M) :
    (α_ M M X).inv ≫ (μ otimesₘ f) ≫ μ = (𝟙 M otimesₘ (𝟙 M otimesₘ f) ≫ μ) ≫ μ := by simp [tensorHom_def']

end Mathlib.Tactic.MonTauto

variable {M N O X : C} [MonObj M] [MonObj N] [MonObj O]

open AddMonObj in
/--
Definition of `_root_.CategoryTheory.IsAddMonHom` / `_root_.CategoryTheory.IsAddMonHom` 的定义

English:
class _root_.CategoryTheory.IsAddMonHom
  axioms and operations (2):
    - zero_hom((f)) : ζ ≫ f = ζ  [default: by cat_disch]
    - add_hom((f)) : σ ≫ f = (f otimesₘ f) ≫ σ  [default: by cat_disch]

中文:
类 _root_.范畴论.是加法幺半群态射
  公理与运算 (2 个):
    - zero_hom((f)) : ζ ≫ f = ζ  [默认: by cat_disch]
    - add_hom((f)) : σ ≫ f = (f otimesₘ f) ≫ σ  [默认: by cat_disch]

Depends on / 依赖: add_hom, cat_disch
-/
class _root_.CategoryTheory.IsAddMonHom
    {M' N' : C} [AddMonObj M'] [AddMonObj N'] (f : M' ⟶ N') : Prop where
  zero_hom (f) : ζ ≫ f = ζ := by cat_disch
  add_hom (f) : σ ≫ f = (f otimesₘ f) ≫ σ := by cat_disch

/-- The property that a morphism between monoid objects is a monoid morphism. -/
@[to_additive]
/--
Definition of `IsMonHom` / `IsMonHom` 的定义

English:
class IsMonHom
  parameters: (f : M ⟶ N)
  axioms and operations (2):
    - one_hom((f)) : η ≫ f = η  [default: by cat_disch]
    - mul_hom((f)) : μ ≫ f = (f otimesₘ f) ≫ μ  [default: by cat_disch]

中文:
类 是幺半群态射
  参数: (f : M ⟶ N)
  公理与运算 (2 个):
    - one_hom((f)) : η ≫ f = η  [默认: by cat_disch]
    - mul_hom((f)) : μ ≫ f = (f otimesₘ f) ≫ μ  [默认: by cat_disch]

Depends on / 依赖: cat_disch, mul_hom
-/
class IsMonHom (f : M ⟶ N) : Prop where
  one_hom (f) : η ≫ f = η := by cat_disch
  mul_hom (f) : μ ≫ f = (f otimesₘ f) ≫ μ := by cat_disch

set_option linter.translateOverwrite false in
attribute [to_additive existing (attr := reassoc (attr := simp))] IsMonHom.one_hom IsMonHom.mul_hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (𝟙 M)

中文:
实例 :
  签名: 是幺半群态射 (𝟙 M)
-/
instance : IsMonHom (𝟙 M) where

/--
Instance `instIsAddMonHomComp` / 实例 `instIsAddMonHomComp`

English:
instance instIsAddMonHomComp
  signature: {M N O : C} [AddMonObj M] [AddMonObj N] [AddMonObj O]

中文:
实例 instIsAddMonHomComp
  签名: {M N O : C} [加法MonObj M] [加法MonObj N] [加法MonObj O]
-/
instance instIsAddMonHomComp {M N O : C} [AddMonObj M] [AddMonObj N] [AddMonObj O]
    (f : M ⟶ N) (g : N ⟶ O)
    [IsAddMonHom f] [IsAddMonHom g] : IsAddMonHom (f ≫ g) where

@[to_additive existing]
/--
Instance `instIsMonHomComp` / 实例 `instIsMonHomComp`

English:
instance instIsMonHomComp
  signature: (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g]

中文:
实例 instIsMonHomComp
  签名: (f : M ⟶ N) (g : N ⟶ O) [是幺半群态射 f] [是幺半群态射 g]
-/
instance instIsMonHomComp (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g] : IsMonHom (f ≫ g) where

attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
@[to_additive]
/--
Instance `isMonHom_ofIso` / 实例 `isMonHom_ofIso`

English:
instance isMonHom_ofIso
  signature: (e : M ≅ X)
  body: MonObj.ofIso e; IsMonHom e.hom := by
  let := MonObj.ofIso e; exact { }

@[to_additive]

中文:
实例 isMonHom_ofIso
  签名: (e : M ≅ X)
  定义体: MonObj.ofIso e; IsMonHom e.hom := by
  let := MonObj.ofIso e; exact { }

@[to_additive]

Depends on / 依赖: IsMonHom, MonObj, MonObj.ofIso, e.hom
-/
instance isMonHom_ofIso (e : M ≅ X) : letI := MonObj.ofIso e; IsMonHom e.hom := by
  let := MonObj.ofIso e; exact { }

@[to_additive]
instance (f : M ≅ N) [IsMonHom f.hom] : IsMonHom f.inv where
  one_hom := by simp [Iso.comp_inv_eq]
  mul_hom := by simp [Iso.comp_inv_eq]

@[to_additive]
instance {f : M ⟶ N} [IsIso f] [IsMonHom f] : IsMonHom (asIso f).hom := ‹_›

variable (C) in
/--
Definition of `AddMon` / `AddMon` 的定义

English:
structure AddMon
  parameters: where
  axioms and operations (2):
    - X : C
    - [addMon : AddMonObj X]

中文:
结构 加法幺半群
  参数: where
  公理与运算 (2 个):
    - X : C
    - [addMon : 加法MonObj X]
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
/--
Definition of `Mon` / `Mon` 的定义

English:
structure Mon
  parameters: where
  axioms and operations (2):
    - X : C
    - [mon : MonObj X]

中文:
结构 幺半群
  参数: where
  公理与运算 (2 个):
    - X : C
    - [mon : MonObj X]
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
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Mon C
  body: mk (𝟙_ C)

@[to_additive]

中文:
定义 trivial
  签名: : 幺半群 C
  定义体: mk (𝟙_ C)

@[to_additive]
-/
def trivial : Mon C := mk (𝟙_ C)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Mon C)
  body: ⟨trivial C⟩

中文:
实例 :
  签名: 可居 (幺半群 C)
  定义体: ⟨trivial C⟩
-/
instance : Inhabited (Mon C) :=
  ⟨trivial C⟩

end Mon

namespace MonObj

variable {M : C} [MonObj M]

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `one_mul_hom` / 定理 `one_mul_hom`

English:
theorem one_mul_hom
  given: {Z : C} (f : Z ⟶ M)
  statement: (η[M] otimesₘ f) ≫ μ[M] = (fun_ Z).hom ≫ f
  proof: by
  rw [tensorHom_def'_assoc]; rw [one_mul]; rw [leftUnitor_naturality]

@[to_additive (attr := reassoc (attr := simp))]

中文:
定理 one_mul_hom
  条件: {Z : C} (f : Z ⟶ M)
  结论: (η[M] otimesₘ f) ≫ μ[M] = (fun_ Z).hom ≫ f
  证明: by
  rw [tensorHom_def'_assoc]; rw [one_mul]; rw [leftUnitor_naturality]

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: _assoc, leftUnitor_naturality, one_mul, tensorHom_def
-/
theorem one_mul_hom {Z : C} (f : Z ⟶ M) : (η[M] otimesₘ f) ≫ μ[M] = (fun_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc]; rw [one_mul]; rw [leftUnitor_naturality]

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `mul_one_hom` / 定理 `mul_one_hom`

English:
theorem mul_one_hom
  given: {Z : C} (f : Z ⟶ M)
  statement: (f otimesₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f
  proof: by
  rw [tensorHom_def_assoc]; rw [mul_one]; rw [rightUnitor_naturality]

中文:
定理 mul_one_hom
  条件: {Z : C} (f : Z ⟶ M)
  结论: (f otimesₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f
  证明: by
  rw [tensorHom_def_assoc]; rw [mul_one]; rw [rightUnitor_naturality]

Depends on / 依赖: mul_one, rightUnitor_naturality, tensorHom_def_assoc
-/
theorem mul_one_hom {Z : C} (f : Z ⟶ M) : (f otimesₘ η[M]) ≫ μ[M] = (ρ_ Z).hom ≫ f := by
  rw [tensorHom_def_assoc]; rw [mul_one]; rw [rightUnitor_naturality]

variable (M) in
@[to_additive (attr := reassoc)]
/--
theorem `mul_assoc_flip` / 定理 `mul_assoc_flip`

English:
theorem mul_assoc_flip
  statement: M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ
  proof: by
  simp

中文:
定理 mul_assoc_flip
  结论: M ◁ μ ≫ μ = (α_ M M M).inv ≫ μ ▷ M ≫ μ
  证明: by
  simp
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
/--
lemma `one_associator` / 引理 `one_associator`

English:
lemma one_associator
  given: {M N P : C} [MonObj M] [MonObj N] [MonObj P]
  proof: by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), ← tensorHom_comp_tensorHom]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, ← tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  simp

@[to_additive]

中文:
引理 one_associator
  条件: {M N P : C} [MonObj M] [MonObj N] [MonObj P]
  证明: by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), ← tensorHom_comp_tensorHom]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, ← tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  simp

@[to_additive]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Iso.cancel_iso_inv_left, associator_naturality, cancel_iso_inv_left, id_comp, leftUnitor_tensor_inv, slice_lhs, slice_rhs, tensorHom_comp_tensorHom, tensorHom_id
-/
lemma one_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] :
    ((fun_ (𝟙_ C)).inv ≫ ((fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ η[N]) otimesₘ η[P])) ≫ (α_ M N P).hom =
      (fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ (fun_ (𝟙_ C)).inv ≫ (η[N] otimesₘ η[P])) := by
  simp only [Category.assoc, Iso.cancel_iso_inv_left]
  slice_lhs 1 3 => rw [← Category.id_comp (η : 𝟙_ C ⟶ P), ← tensorHom_comp_tensorHom]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_rhs 1 2 => rw [← Category.id_comp η, ← tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_id, ← leftUnitor_tensor_inv]
  simp

@[to_additive]
/--
lemma `one_leftUnitor` / 引理 `one_leftUnitor`

English:
lemma one_leftUnitor
  given: {M : C} [MonObj M]
  proof: by
  simp

@[to_additive]

中文:
引理 one_leftUnitor
  条件: {M : C} [MonObj M]
  证明: by
  simp

@[to_additive]
-/
lemma one_leftUnitor {M : C} [MonObj M] :
    ((fun_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) otimesₘ η[M])) ≫ (fun_ M).hom = η := by
  simp

@[to_additive]
/--
lemma `one_rightUnitor` / 引理 `one_rightUnitor`

English:
lemma one_rightUnitor
  given: {M : C} [MonObj M]
  proof: by
  simp [← unitors_equal]

中文:
引理 one_rightUnitor
  条件: {M : C} [MonObj M]
  证明: by
  simp [← unitors_equal]

Depends on / 依赖: unitors_equal
-/
lemma one_rightUnitor {M : C} [MonObj M] :
    ((fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ 𝟙 (𝟙_ C))) ≫ (ρ_ M).hom = η := by
  simp [← unitors_equal]

section BraidedCategory

variable [BraidedCategory C]

@[to_additive AddMon_tensor_zero_add]
/--
lemma `Mon_tensor_one_mul` / 引理 `Mon_tensor_one_mul`

English:
lemma Mon_tensor_one_mul
  given: (M N : C) [MonObj M] [MonObj N]
  proof: by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

@[to_additive AddMon_tensor_add_zero]

中文:
引理 Mon_tensor_one_mul
  条件: (M N : C) [MonObj M] [MonObj N]
  证明: by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

@[to_additive AddMon_tensor_add_zero]

Depends on / 依赖: comp_whiskerRight_assoc, one_mul, slice_lhs, tensorHom_comp_tensorHom, tensor_left_unitality
-/
lemma Mon_tensor_one_mul (M N : C) [MonObj M] [MonObj N] :
    (((fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ η[N])) ▷ (M otimes N)) ≫
        tensorμ M N M N ≫ (μ otimesₘ μ) =
      (fun_ (M otimes N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

@[to_additive AddMon_tensor_add_zero]
/--
lemma `Mon_tensor_mul_one` / 引理 `Mon_tensor_mul_one`

English:
lemma Mon_tensor_mul_one
  given: (M N : C) [MonObj M] [MonObj N]
  proof: by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

@[to_additive AddMon_tensor_add_assoc]

中文:
引理 Mon_tensor_mul_one
  条件: (M N : C) [MonObj M] [MonObj N]
  证明: by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

@[to_additive AddMon_tensor_add_assoc]

Depends on / 依赖: mul_one, slice_lhs, tensorHom_comp_tensorHom, tensor_right_unitality, whiskerLeft_comp_assoc
-/
lemma Mon_tensor_mul_one (M N : C) [MonObj M] [MonObj N] :
    (M otimes N) ◁ ((fun_ (𝟙_ C)).inv ≫ (η[M] otimesₘ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] otimesₘ μ[N]) =
      (ρ_ (M otimes N)).hom := by
  simp only [whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

@[to_additive AddMon_tensor_add_assoc]
/--
lemma `Mon_tensor_mul_assoc` / 引理 `Mon_tensor_mul_assoc`

English:
lemma Mon_tensor_mul_assoc
  given: (M N : C) [MonObj M] [MonObj N]
  proof: by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_assoc, mul_assoc, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

@[to_additive]

中文:
引理 Mon_tensor_mul_assoc
  条件: (M N : C) [MonObj M] [MonObj N]
  证明: by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_assoc, mul_assoc, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

@[to_additive]

Depends on / 依赖: comp_whiskerRight_assoc, mul_assoc, slice_lhs, tensorHom_comp_tensorHom, tensor_associativity, whiskerLeft_comp_assoc
-/
lemma Mon_tensor_mul_assoc (M N : C) [MonObj M] [MonObj N] :
    ((tensorμ M N M N ≫ (μ otimesₘ μ)) ▷ (M otimes N)) ≫
        tensorμ M N M N ≫ (μ otimesₘ μ) =
      (α_ (M otimes N : C) (M otimes N) (M otimes N)).hom ≫
        ((M otimes N : C) ◁ (tensorμ M N M N ≫ (μ otimesₘ μ))) ≫
          tensorμ M N M N ≫ (μ otimesₘ μ) := by
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, mul_assoc, mul_assoc, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

@[to_additive]
/--
lemma `mul_associator` / 引理 `mul_associator`

English:
lemma mul_associator
  given: {M N P : C} [MonObj M] [MonObj N] [MonObj P]
  proof: by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

@[to_additive]

中文:
引理 mul_associator
  条件: {M N P : C} [MonObj M] [MonObj N] [MonObj P]
  证明: by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

@[to_additive]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, associator_monoidal, associator_naturality, id_comp, id_tensorHom, slice_lhs, slice_rhs, tensorHom_comp_tensorHom, tensorHom_id
-/
lemma mul_associator {M N P : C} [MonObj M] [MonObj N] [MonObj P] :
    (tensorμ (M otimes N) P (M otimes N) P ≫
          (tensorμ M N M N ≫ (μ otimesₘ μ) otimesₘ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom otimesₘ (α_ M N P).hom) ≫
        tensorμ M (N otimes P) M (N otimes P) ≫
          (μ otimesₘ tensorμ N P N P ≫ (μ otimesₘ μ)) := by
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], ← tensorHom_comp_tensorHom]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, ← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

@[to_additive]
/--
lemma `mul_leftUnitor` / 引理 `mul_leftUnitor`

English:
lemma mul_leftUnitor
  given: {M : C} [MonObj M]
  proof: by
  rw [← Category.comp_id (fun_ (𝟙_ C)).hom]; rw [← Category.id_comp μ]; rw [← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

@[to_additive]

中文:
引理 mul_leftUnitor
  条件: {M : C} [MonObj M]
  证明: by
  rw [← Category.comp_id (fun_ (𝟙_ C)).hom]; rw [← Category.id_comp μ]; rw [← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

@[to_additive]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, fun_, id_comp, id_tensorHom, leftUnitor_monoidal, leftUnitor_naturality, slice_lhs, tensorHom_comp_tensorHom, tensorHom_id
-/
lemma mul_leftUnitor {M : C} [MonObj M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((fun_ (𝟙_ C)).hom otimesₘ μ)) ≫ (fun_ M).hom =
      ((fun_ M).hom otimesₘ (fun_ M).hom) ≫ μ := by
  rw [← Category.comp_id (fun_ (𝟙_ C)).hom]; rw [← Category.id_comp μ]; rw [← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.id_comp]

@[to_additive]
/--
lemma `mul_rightUnitor` / 引理 `mul_rightUnitor`

English:
lemma mul_rightUnitor
  given: {M : C} [MonObj M]
  proof: by
  rw [← Category.id_comp μ]; rw [← Category.comp_id (fun_ (𝟙_ C)).hom]; rw [← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

中文:
引理 mul_rightUnitor
  条件: {M : C} [MonObj M]
  证明: by
  rw [← Category.id_comp μ]; rw [← Category.comp_id (fun_ (𝟙_ C)).hom]; rw [← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, fun_, id_comp, id_tensorHom, rightUnitor_monoidal, rightUnitor_naturality, slice_lhs, tensorHom_comp_tensorHom, tensorHom_id
-/
lemma mul_rightUnitor {M : C} [MonObj M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ otimesₘ (fun_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom otimesₘ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ]; rw [← Category.comp_id (fun_ (𝟙_ C)).hom]; rw [← tensorHom_comp_tensorHom]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.id_comp]

namespace tensorObj

-- We don't want `tensorObj.one_def` to be simp as it would loop with `IsMonHom.one_hom` applied
-- to `(λ_ N.X).inv`.
@[to_additive (attr := simps -isSimp)]
instance {M N : C} [MonObj M] [MonObj N] : MonObj (M otimes N) where
  one := (fun_ (𝟙_ C)).inv ≫ (η otimesₘ η)
  mul := tensorμ M N M N ≫ (μ otimesₘ μ)
  one_mul := Mon_tensor_one_mul M N
  mul_one := Mon_tensor_mul_one M N
  mul_assoc := Mon_tensor_mul_assoc M N

end tensorObj

open IsMonHom

variable {X Y Z W : C} [MonObj X] [MonObj Y] [MonObj Z] [MonObj W]

@[to_additive]
instance {f : X ⟶ Y} {g : Z ⟶ W} [IsMonHom f] [IsMonHom g] : IsMonHom (f otimesₘ g) where
  one_hom := by
    dsimp [tensorObj.one_def]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, one_hom, one_hom]
  mul_hom := by
    dsimp [tensorObj.mul_def]
    slice_rhs 1 2 => rw [tensorμ_natural]
    slice_lhs 2 3 => rw [tensorHom_comp_tensorHom, mul_hom, mul_hom, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (𝟙 X)

中文:
实例 :
  签名: 是幺半群态射 (𝟙 X)
-/
instance : IsMonHom (𝟙 X) where

@[to_additive]
instance {f : Y ⟶ Z} [IsMonHom f] : IsMonHom (X ◁ f) where
  one_hom := by simpa using ((inferInstance : IsMonHom (𝟙 X otimesₘ f))).one_hom
  mul_hom := by simpa using ((inferInstance : IsMonHom (𝟙 X otimesₘ f))).mul_hom

@[to_additive]
instance {f : X ⟶ Y} [IsMonHom f] : IsMonHom (f ▷ Z) where
  one_hom := by simpa using ((inferInstance : IsMonHom (f otimesₘ (𝟙 Z)))).one_hom
  mul_hom := by simpa using ((inferInstance : IsMonHom (f otimesₘ (𝟙 Z)))).mul_hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (α_ X Y Z).hom
  body: ⟨one_associator, mul_associator⟩

@[to_additive]

中文:
实例 :
  签名: 是幺半群态射 (α_ X Y Z).hom
  定义体: ⟨one_associator, mul_associator⟩

@[to_additive]

Depends on / 依赖: mul_associator, one_associator
-/
instance : IsMonHom (α_ X Y Z).hom :=
  ⟨one_associator, mul_associator⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (fun_ X).hom
  body: ⟨one_leftUnitor, mul_leftUnitor⟩

@[to_additive]

中文:
实例 :
  签名: 是幺半群态射 (fun_ X).hom
  定义体: ⟨one_leftUnitor, mul_leftUnitor⟩

@[to_additive]

Depends on / 依赖: mul_leftUnitor, one_leftUnitor
-/
instance : IsMonHom (fun_ X).hom :=
  ⟨one_leftUnitor, mul_leftUnitor⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (ρ_ X).hom
  body: ⟨one_rightUnitor, mul_rightUnitor⟩

@[to_additive]

中文:
实例 :
  签名: 是幺半群态射 (ρ_ X).hom
  定义体: ⟨one_rightUnitor, mul_rightUnitor⟩

@[to_additive]

Depends on / 依赖: mul_rightUnitor, one_rightUnitor
-/
instance : IsMonHom (ρ_ X).hom :=
  ⟨one_rightUnitor, mul_rightUnitor⟩

@[to_additive]
/--
lemma `one_braiding` / 引理 `one_braiding`

English:
lemma one_braiding
  given: (X Y : C) [MonObj X] [MonObj Y]
  statement: η ≫ (β_ X Y).hom = η
  proof: by
  simp only [tensorObj.one_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

中文:
引理 one_braiding
  条件: (X Y : C) [MonObj X] [MonObj Y]
  结论: η ≫ (β_ X Y).hom = η
  证明: by
  simp only [tensorObj.one_def, Category.assoc, BraidedCategory.braiding_naturality,
    braiding_tensorUnit_right, Iso.cancel_iso_inv_left]
  monoidal

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_naturality, Category, Category.assoc, Iso.cancel_iso_inv_left, braiding_naturality, braiding_tensorUnit_right, cancel_iso_inv_left, monoidal, one_def, tensorObj, tensorObj.one_def
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
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : AddMon C)
  axioms and operations (2):
    - hom : M.X ⟶ N.X
    - [isAddMonHom_hom : IsAddMonHom hom]

中文:
结构 态射
  参数: (M N : 加法幺半群 C)
  公理与运算 (2 个):
    - hom : M.X ⟶ N.X
    - [isAddMonHom_hom : 是加法幺半群态射 hom]
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
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : Mon C)
  axioms and operations (2):
    - hom : M.X ⟶ N.X
    - [isMonHom_hom : IsMonHom hom]

中文:
结构 态射
  参数: (M N : 幺半群 C)
  公理与运算 (2 个):
    - hom : M.X ⟶ N.X
    - [isMonHom_hom : 是幺半群态射 hom]
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
/--
Definition of `Hom.mk'` / `Hom.mk'` 的定义

English:
abbreviation Hom.mk'
  signature: {M N : Mon C} (f : M.X ⟶ N.X)
  body: have : IsMonHom f := ⟨one_f, mul_f⟩
  .mk f

中文:
缩写 态射.mk'
  签名: {M N : 幺半群 C} (f : M.X ⟶ N.X)
  定义体: have : IsMonHom f := ⟨one_f, mul_f⟩
  .mk f
-/
abbrev Hom.mk' {M N : Mon C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f otimesₘ f) ≫ μ := by cat_disch) : Hom M N :=
  have : IsMonHom f := ⟨one_f, mul_f⟩
  .mk f

/-- The identity morphism on a monoid object. -/
@[to_additive (attr := simps)
/-- The identity morphism on an additive monoid object. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (M : Mon C)
  body: ⟨𝟙 M.X⟩

@[to_additive]

中文:
定义 id
  签名: (M : 幺半群 C)
  定义体: ⟨𝟙 M.X⟩

@[to_additive]
-/
def id (M : Mon C) : Hom M M := ⟨𝟙 M.X⟩

@[to_additive]
/--
Instance `homInhabited` / 实例 `homInhabited`

English:
instance homInhabited
  signature: (M : Mon C)
  body: ⟨id M⟩

中文:
实例 homInhabited
  签名: (M : 幺半群 C)
  定义体: ⟨id M⟩
-/
instance homInhabited (M : Mon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[to_additive (attr := simps)
/-- Composition of morphisms of additive monoid objects. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M N O : Mon C} (f : Hom M N) (g : Hom N O)
  body: f.hom ≫ g.hom

@[to_additive]

中文:
定义 comp
  签名: {M N O : 幺半群 C} (f : 态射 M N) (g : 态射 N O)
  定义体: f.hom ≫ g.hom

@[to_additive]

Depends on / 依赖: f.hom, g.hom
-/
def comp {M N O : Mon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Mon C)
  body: Hom M N
  id := id
  comp f g := comp f g

中文:
实例 :
  签名: 范畴 (幺半群 C)
  定义体: Hom M N
  id := id
  comp f g := comp f g
-/
instance : Category (Mon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

/-- Construct a morphism `Mon.mk G ⟶ Mon.mk H` from a map `f : G ⟶ H` and a `IsMonHom f`
instance. -/
@[to_additive (attr := simps!)
/-- Construct a morphism `AddMon.mk G ⟶ AddMon.mk H` from a map `f : G ⟶ H` and a `IsAddMonHom f`
instance. -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]
  body: .mk f

@[to_additive]

中文:
定义 ofHom
  签名: {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [是幺半群态射 f]
  定义体: .mk f

@[to_additive]
-/
def ofHom {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] : Mon.mk A ⟶ Mon.mk B :=
  .mk f

@[to_additive]
instance {M N : Mon C} (f : M ⟶ N) : IsMonHom f.hom := f.isMonHom_hom

@[to_additive (attr := ext)]
/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  given: {M N : Mon C} {f g : M ⟶ N} (w : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext w

@[to_additive]

中文:
引理 态射.ext'
  条件: {M N : 幺半群 C} {f g : M ⟶ N} (w : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext w

@[to_additive]
-/
lemma Hom.ext' {M N : Mon C} {f g : M ⟶ N} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

@[to_additive]
/--
lemma `hom_injective` / 引理 `hom_injective`

English:
lemma hom_injective
  given: {M N : Mon C}
  statement: Injective (Hom.hom : (M ⟶ N) -> (M.X ⟶ N.X))
  proof: fun _ _ => Hom.ext

@[to_additive (attr := simp)]

中文:
引理 hom_injective
  条件: {M N : 幺半群 C}
  结论: 单射 (态射.hom : (M ⟶ N) -> (M.X ⟶ N.X))
  证明: fun _ _ => Hom.ext

@[to_additive (attr := simp)]

Depends on / 依赖: Hom.ext
-/
lemma hom_injective {M N : Mon C} : Injective (Hom.hom : (M ⟶ N) -> (M.X ⟶ N.X)) :=
  fun _ _ => Hom.ext

@[to_additive (attr := simp)]
/--
theorem `id_hom'` / 定理 `id_hom'`

English:
theorem id_hom'
  given: (M : Mon C)
  statement: (𝟙 M : Hom M M).hom = 𝟙 M.X
  proof: rfl

@[to_additive (attr := simp, reassoc)]

中文:
定理 id_hom'
  条件: (M : 幺半群 C)
  结论: (𝟙 M : 态射 M M).hom = 𝟙 M.X
  证明: rfl

@[to_additive (attr := simp, reassoc)]
-/
theorem id_hom' (M : Mon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[to_additive (attr := simp, reassoc)]
/--
theorem `comp_hom'` / 定理 `comp_hom'`

English:
theorem comp_hom'
  given: {M N K : Mon C} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

中文:
定理 comp_hom'
  条件: {M N K : 幺半群 C} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl
-/
theorem comp_hom' {M N K : Mon C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[to_additive (attr := simps)
/-- The forgetful functor from additive monoid objects to the ambient category. -/]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Mon C ⥤ C where
  body: A.X
  map f := f.hom

中文:
定义 forget
  签名: : 幺半群 C ⥤ C where
  定义体: A.X
  map f := f.hom
-/
def forget : Mon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

@[to_additive]
/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget C).Faithful where

中文:
实例 forget_faithful
  签名: : (forget C).忠实 where
-/
instance forget_faithful : (forget C).Faithful where

@[to_additive]
instance {A B : Mon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
@[to_additive /-- The forgetful functor from additive monoid objects to the ambient category
reflects isomorphisms. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).ReflectsIsomorphisms
  body: ⟨⟨.mk' (inv f.hom), by cat_disch⟩⟩

@[to_additive]

中文:
实例 :
  签名: (forget C).反映同构
  定义体: ⟨⟨.mk' (inv f.hom), by cat_disch⟩⟩

@[to_additive]

Depends on / 依赖: cat_disch, f.hom
-/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e := ⟨⟨.mk' (inv f.hom), by cat_disch⟩⟩

@[to_additive]
instance {M N : Mon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom :=
inferInstanceAs IsIso (forget C).map f

/-- Construct an isomorphism of monoid objects by giving a monoid isomorphism between the underlying
objects. -/
@[to_additive (attr := simps)
/-- Construct an isomorphism of additive monoid objects by giving a additive monoid
isomorphism between the underlying objects. -/]
/--
Definition of `mkIso'` / `mkIso'` 的定义

English:
definition mkIso'
  signature: {M N : C} [MonObj M] [MonObj N] (e : M ≅ N) [IsMonHom e.hom]
  body: Hom.mk e.hom
  inv := Hom.mk e.inv

中文:
定义 mkIso'
  签名: {M N : C} [MonObj M] [MonObj N] (e : M ≅ N) [是幺半群态射 e.hom]
  定义体: Hom.mk e.hom
  inv := Hom.mk e.inv

Depends on / 依赖: Hom.mk, e.hom
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
/--
Definition of `mkIso` / `mkIso` 的定义

English:
abbreviation mkIso
  signature: {M N : Mon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
  body: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

中文:
缩写 mkIso
  签名: {M N : 幺半群 C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
  定义体: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

Depends on / 依赖: IsMonHom, cat_disch, e.hom, mul_f, one_f
-/
abbrev mkIso {M N : Mon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom otimesₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simps)]
/--
Instance `uniqueHomFromTrivial` / 实例 `uniqueHomFromTrivial`

English:
instance uniqueHomFromTrivial
  signature: (A : Mon C)
  body: η[A.X]
  default.isMonHom_hom.mul_hom := by simp [unitors_equal]
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_one]; rw [IsMonHom.one_hom]

中文:
实例 uniqueHomFromTrivial
  签名: (A : 幺半群 C)
  定义体: η[A.X]
  default.isMonHom_hom.mul_hom := by simp [unitors_equal]
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_one]; rw [IsMonHom.one_hom]
-/
instance uniqueHomFromTrivial (A : Mon C) : Unique (trivial C ⟶ A) where
  default.hom := η[A.X]
  default.isMonHom_hom.mul_hom := by simp [unitors_equal]
  uniq f := by
    ext
    rw [← Category.id_comp f.hom]
    dsimp only [trivial_X]
    rw [← trivial_mon_one]; rw [IsMonHom.one_hom]

open CategoryTheory.Limits

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasInitial (Mon C)
  body: hasInitial_of_unique (Mon.trivial C)

中文:
实例 :
  签名: HasInitial (幺半群 C)
  定义体: hasInitial_of_unique (Mon.trivial C)

Depends on / 依赖: Mon.trivial, hasInitial_of_unique
-/
instance : HasInitial (Mon C) :=
  hasInitial_of_unique (Mon.trivial C)

section BraidedCategory
variable [BraidedCategory C]

@[to_additive (attr := simps! tensorObj_X tensorHom_hom)]
/--
Instance `monMonoidalStruct` / 实例 `monMonoidalStruct`

English:
instance monMonoidalStruct
  signature: : MonoidalCategoryStruct (Mon C) where
  body: ⟨M.X otimes N.X⟩
  tensorHom f g := Hom.mk (f.hom otimesₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
associator M N P := mkIso' associator M.X N.X P.X
leftUnitor M := mkIso' leftUnitor M.X
rightUnitor M := mkIso' rightUnitor M.X

@[to_additive (attr := simp)]

中文:
实例 monMonoidalStruct
  签名: : 幺半群范畴结构 (幺半群 C) where
  定义体: ⟨M.X otimes N.X⟩
  tensorHom f g := Hom.mk (f.hom otimesₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
associator M N P := mkIso' associator M.X N.X P.X
leftUnitor M := mkIso' leftUnitor M.X
rightUnitor M := mkIso' rightUnitor M.X

@[to_additive (attr := simp)]

Depends on / 依赖: otimes
-/
instance monMonoidalStruct : MonoidalCategoryStruct (Mon C) where
  tensorObj M N := ⟨M.X otimes N.X⟩
  tensorHom f g := Hom.mk (f.hom otimesₘ g.hom)
  whiskerRight f Y := Hom.mk (f.hom ▷ Y.X)
  whiskerLeft X _ _ g := Hom.mk (X.X ◁ g.hom)
  tensorUnit := ⟨𝟙_ C⟩
associator M N P := mkIso' associator M.X N.X P.X
leftUnitor M := mkIso' leftUnitor M.X
rightUnitor M := mkIso' rightUnitor M.X

@[to_additive (attr := simp)]
/--
lemma `tensorUnit_X` / 引理 `tensorUnit_X`

English:
lemma tensorUnit_X
  statement: (𝟙_ (Mon C)).X = 𝟙_ C
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorUnit_X
  结论: (𝟙_ (幺半群 C)).X = 𝟙_ C
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorUnit_X : (𝟙_ (Mon C)).X = 𝟙_ C := rfl

@[to_additive (attr := simp)]
/--
lemma `tensorUnit_one` / 引理 `tensorUnit_one`

English:
lemma tensorUnit_one
  statement: η[(𝟙_ (Mon C)).X] = 𝟙 (𝟙_ C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorUnit_one
  结论: η[(𝟙_ (幺半群 C)).X] = 𝟙 (𝟙_ C)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorUnit_one : η[(𝟙_ (Mon C)).X] = 𝟙 (𝟙_ C) := rfl

@[to_additive (attr := simp)]
/--
lemma `tensorUnit_mul` / 引理 `tensorUnit_mul`

English:
lemma tensorUnit_mul
  statement: μ[(𝟙_ (Mon C)).X] = (fun_ (𝟙_ C)).hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorUnit_mul
  结论: μ[(𝟙_ (幺半群 C)).X] = (fun_ (𝟙_ C)).hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorUnit_mul : μ[(𝟙_ (Mon C)).X] = (fun_ (𝟙_ C)).hom := rfl

@[to_additive (attr := simp)]
/--
lemma `tensorObj_one` / 引理 `tensorObj_one`

English:
lemma tensorObj_one
  given: (X Y : Mon C)
  statement: η[(X otimes Y).X] = (fun_ (𝟙_ C)).inv ≫ (η[X.X] otimesₘ η[Y.X])
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorObj_one
  条件: (X Y : 幺半群 C)
  结论: η[(X otimes Y).X] = (fun_ (𝟙_ C)).inv ≫ (η[X.X] otimesₘ η[Y.X])
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorObj_one (X Y : Mon C) : η[(X otimes Y).X] = (fun_ (𝟙_ C)).inv ≫ (η[X.X] otimesₘ η[Y.X]) := rfl

@[to_additive (attr := simp)]
/--
lemma `tensorObj_mul` / 引理 `tensorObj_mul`

English:
lemma tensorObj_mul
  given: (X Y : Mon C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensorObj_mul
  条件: (X Y : 幺半群 C)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensorObj_mul (X Y : Mon C) :
    μ[(X otimes Y).X] = tensorμ X.X Y.X X.X Y.X ≫ (μ[X.X] otimesₘ μ[Y.X]) := rfl

@[to_additive (attr := simp)]
/--
lemma `whiskerLeft_hom` / 引理 `whiskerLeft_hom`

English:
lemma whiskerLeft_hom
  given: {X Y : Mon C} (f : X ⟶ Y) (Z : Mon C)
  statement: (f ▷ Z).hom = f.hom ▷ Z.X
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 whiskerLeft_hom
  条件: {X Y : 幺半群 C} (f : X ⟶ Y) (Z : 幺半群 C)
  结论: (f ▷ Z).hom = f.hom ▷ Z.X
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma whiskerLeft_hom {X Y : Mon C} (f : X ⟶ Y) (Z : Mon C) : (f ▷ Z).hom = f.hom ▷ Z.X := rfl

@[to_additive (attr := simp)]
/--
lemma `whiskerRight_hom` / 引理 `whiskerRight_hom`

English:
lemma whiskerRight_hom
  given: (X : Mon C) {Y Z : Mon C} (f : Y ⟶ Z)
  statement: (X ◁ f).hom = X.X ◁ f.hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 whiskerRight_hom
  条件: (X : 幺半群 C) {Y Z : 幺半群 C} (f : Y ⟶ Z)
  结论: (X ◁ f).hom = X.X ◁ f.hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma whiskerRight_hom (X : Mon C) {Y Z : Mon C} (f : Y ⟶ Z) : (X ◁ f).hom = X.X ◁ f.hom := rfl

@[to_additive (attr := simp)]
/--
lemma `leftUnitor_hom_hom` / 引理 `leftUnitor_hom_hom`

English:
lemma leftUnitor_hom_hom
  given: (X : Mon C)
  statement: (fun_ X).hom.hom = (fun_ X.X).hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 leftUnitor_hom_hom
  条件: (X : 幺半群 C)
  结论: (fun_ X).hom.hom = (fun_ X.X).hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma leftUnitor_hom_hom (X : Mon C) : (fun_ X).hom.hom = (fun_ X.X).hom := rfl

@[to_additive (attr := simp)]
/--
lemma `leftUnitor_inv_hom` / 引理 `leftUnitor_inv_hom`

English:
lemma leftUnitor_inv_hom
  given: (X : Mon C)
  statement: (fun_ X).inv.hom = (fun_ X.X).inv
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 leftUnitor_inv_hom
  条件: (X : 幺半群 C)
  结论: (fun_ X).inv.hom = (fun_ X.X).inv
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma leftUnitor_inv_hom (X : Mon C) : (fun_ X).inv.hom = (fun_ X.X).inv := rfl

@[to_additive (attr := simp)]
/--
lemma `rightUnitor_hom_hom` / 引理 `rightUnitor_hom_hom`

English:
lemma rightUnitor_hom_hom
  given: (X : Mon C)
  statement: (ρ_ X).hom.hom = (ρ_ X.X).hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 rightUnitor_hom_hom
  条件: (X : 幺半群 C)
  结论: (ρ_ X).hom.hom = (ρ_ X.X).hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma rightUnitor_hom_hom (X : Mon C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl

@[to_additive (attr := simp)]
/--
lemma `rightUnitor_inv_hom` / 引理 `rightUnitor_inv_hom`

English:
lemma rightUnitor_inv_hom
  given: (X : Mon C)
  statement: (ρ_ X).inv.hom = (ρ_ X.X).inv
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 rightUnitor_inv_hom
  条件: (X : 幺半群 C)
  结论: (ρ_ X).inv.hom = (ρ_ X.X).inv
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma rightUnitor_inv_hom (X : Mon C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[to_additive (attr := simp)]
/--
lemma `associator_hom_hom` / 引理 `associator_hom_hom`

English:
lemma associator_hom_hom
  given: (X Y Z : Mon C)
  statement: (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 associator_hom_hom
  条件: (X Y Z : 幺半群 C)
  结论: (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma associator_hom_hom (X Y Z : Mon C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl

@[to_additive (attr := simp)]
/--
lemma `associator_inv_hom` / 引理 `associator_inv_hom`

English:
lemma associator_inv_hom
  given: (X Y Z : Mon C)
  statement: (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 associator_inv_hom
  条件: (X Y Z : 幺半群 C)
  结论: (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma associator_inv_hom (X Y Z : Mon C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[to_additive (attr := simp)]
/--
lemma `tensor_one` / 引理 `tensor_one`

English:
lemma tensor_one
  given: (M N : Mon C)
  statement: η[(M otimes N).X] = (fun_ (𝟙_ C)).inv ≫ (η[M.X] otimesₘ η[N.X])
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 tensor_one
  条件: (M N : 幺半群 C)
  结论: η[(M otimes N).X] = (fun_ (𝟙_ C)).inv ≫ (η[M.X] otimesₘ η[N.X])
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma tensor_one (M N : Mon C) : η[(M otimes N).X] = (fun_ (𝟙_ C)).inv ≫ (η[M.X] otimesₘ η[N.X]) := rfl

@[to_additive (attr := simp)]
/--
lemma `tensor_mul` / 引理 `tensor_mul`

English:
lemma tensor_mul
  given: (M N : Mon C)
  statement: μ[(M otimes N).X] = tensorμ M.X N.X M.X N.X ≫ (μ[M.X] otimesₘ μ[N.X])
  proof: rfl

@[to_additive]

中文:
引理 tensor_mul
  条件: (M N : 幺半群 C)
  结论: μ[(M otimes N).X] = tensorμ M.X N.X M.X N.X ≫ (μ[M.X] otimesₘ μ[N.X])
  证明: rfl

@[to_additive]
-/
lemma tensor_mul (M N : Mon C) : μ[(M otimes N).X] = tensorμ M.X N.X M.X N.X ≫ (μ[M.X] otimesₘ μ[N.X]) := rfl

@[to_additive]
/--
Instance `monMonoidal` / 实例 `monMonoidal`

English:
instance monMonoidal
  signature: : MonoidalCategory (Mon C) where
  body: by intros; ext; simp [tensorHom_def]

中文:
实例 monMonoidal
  签名: : 幺半群范畴 (幺半群 C) where
  定义体: by intros; ext; simp [tensorHom_def]

Depends on / 依赖: intros, tensorHom_def
-/
instance monMonoidal : MonoidalCategory (Mon C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]

-- We don't want `tensorObj.one_def` to be simp as it would loop with `IsMonHom.one_hom` applied
-- to `(λ_ N.X).inv`.
@[to_additive (attr := simps! -isSimp)]
instance {M N : C} [MonObj M] [MonObj N] : MonObj (M otimes N) :=
inferInstanceAs MonObj (Mon.mk M otimes Mon.mk N).X

variable (C)

set_option backward.defeqAttrib.useBackward true in
/-- The forgetful functor from `Mon C` to `C` is monoidal when `C` is monoidal. -/
@[to_additive /-- The forgetful functor from `AddMon C` to `C` is monoidal when `C` is monoidal. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[to_additive (attr := simp)]

中文:
实例 :
  签名: (forget C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[to_additive (attr := simp)]

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

@[to_additive (attr := simp)]
/--
lemma `forget_ε` / 引理 `forget_ε`

English:
lemma forget_ε
  statement: ε (forget C) = 𝟙 (𝟙_ C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 forget_ε
  结论: ε (forget C) = 𝟙 (𝟙_ C)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma forget_ε : ε (forget C) = 𝟙 (𝟙_ C) := rfl

@[to_additive (attr := simp)]
/--
lemma `forget_η` / 引理 `forget_η`

English:
lemma forget_η
  statement: «η» (forget C) = 𝟙 (𝟙_ C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 forget_η
  结论: «η» (forget C) = 𝟙 (𝟙_ C)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl

@[to_additive (attr := simp)]
/--
lemma `forget_μ` / 引理 `forget_μ`

English:
lemma forget_μ
  given: (X Y : Mon C)
  statement: «μ» (forget C) X Y = 𝟙 (X.X otimes Y.X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 forget_μ
  条件: (X Y : 幺半群 C)
  结论: «μ» (forget C) X Y = 𝟙 (X.X otimes Y.X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma forget_μ (X Y : Mon C) : «μ» (forget C) X Y = 𝟙 (X.X otimes Y.X) := rfl

@[to_additive (attr := simp)]
/--
lemma `forget_δ` / 引理 `forget_δ`

English:
lemma forget_δ
  given: (X Y : Mon C)
  statement: δ (forget C) X Y = 𝟙 (X.X otimes Y.X)
  proof: rfl

中文:
引理 forget_δ
  条件: (X Y : 幺半群 C)
  结论: δ (forget C) X Y = 𝟙 (X.X otimes Y.X)
  证明: rfl
-/
lemma forget_δ (X Y : Mon C) : δ (forget C) X Y = 𝟙 (X.X otimes Y.X) := rfl

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
/--
lemma `mul_braiding` / 引理 `mul_braiding`

English:
lemma mul_braiding
  given: (X Y : C) [MonObj X] [MonObj Y]
  proof: by
  dsimp [tensorObj.mul_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp]; rw [← comp_whiskerRight]; rw [SymmetricCategory.symmetry]
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

中文:
引理 mul_braiding
  条件: (X Y : C) [MonObj X] [MonObj Y]
  证明: by
  dsimp [tensorObj.mul_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp]; rw [← comp_whiskerRight]; rw [SymmetricCategory.symmetry]
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

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_naturality, BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom, Category, Category.assoc, Iso.inv_hom_id_assoc, braiding_naturality, braiding_tensor_left_hom, braiding_tensor_right_hom, comp_whiskerRight, inv_hom_id_assoc, mul_def, pentagon_assoc, pentagon_inv_hom_hom_hom_inv_assoc, slice_lhs, tensorObj, tensorObj.mul_def, whiskerLeft_comp, whiskerLeft_hom_inv_assoc
-/
lemma mul_braiding (X Y : C) [MonObj X] [MonObj Y] :
    μ ≫ (β_ X Y).hom = ((β_ X Y).hom otimesₘ (β_ X Y).hom) ≫ μ := by
  dsimp [tensorObj.mul_def]
  simp only [tensorμ, Category.assoc, BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom,
    comp_whiskerRight, whisker_assoc, whiskerLeft_comp, pentagon_assoc,
    pentagon_inv_hom_hom_hom_inv_assoc, Iso.inv_hom_id_assoc, whiskerLeft_hom_inv_assoc]
  slice_lhs 3 4 =>
    -- We use symmetry here:
    rw [← whiskerLeft_comp]; rw [← comp_whiskerRight]; rw [SymmetricCategory.symmetry]
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
instance {X Y : C} [MonObj X] [MonObj Y] : IsMonHom (β_ X Y).hom :=
  ⟨one_braiding X Y, mul_braiding X Y⟩

end MonObj

namespace Mon

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SymmetricCategory (Mon C)
  body: mkIso' (β_ X.X Y.X)

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 对称范畴 (幺半群 C)
  定义体: mkIso' (β_ X.X Y.X)

@[to_additive (attr := simp)]
-/
instance : SymmetricCategory (Mon C) where
  braiding X Y := mkIso' (β_ X.X Y.X)

@[to_additive (attr := simp)]
/--
lemma `braiding_hom_hom` / 引理 `braiding_hom_hom`

English:
lemma braiding_hom_hom
  given: (M N : Mon C)
  statement: (β_ M N).hom.hom = (β_ M.X N.X).hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 braiding_hom_hom
  条件: (M N : 幺半群 C)
  结论: (β_ M N).hom.hom = (β_ M.X N.X).hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma braiding_hom_hom (M N : Mon C) : (β_ M N).hom.hom = (β_ M.X N.X).hom := rfl

@[to_additive (attr := simp)]
/--
lemma `braiding_inv_hom` / 引理 `braiding_inv_hom`

English:
lemma braiding_inv_hom
  given: (M N : Mon C)
  statement: (β_ M N).inv.hom = (β_ M.X N.X).inv
  proof: rfl

中文:
引理 braiding_inv_hom
  条件: (M N : 幺半群 C)
  结论: (β_ M N).inv.hom = (β_ M.X N.X).inv
  证明: rfl
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
/--
Definition of `monObjObj` / `monObjObj` 的定义

English:
abbreviation monObjObj
  signature: : MonObj (F.obj X) where
  body: ε F ≫ F.map η
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

中文:
缩写 monObjObj
  签名: : MonObj (F.obj X) where
  定义体: ε F ≫ F.map η
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

Depends on / 依赖: F.map, SuccOrder, SuccOrder.limitRecOn, isSuccLimit, limitRecOn, some.succ
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
/--
lemma `obj.η_def` / 引理 `obj.η_def`

English:
lemma obj.η_def
  statement: (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η
  proof: rfl

@[to_additive (attr := reassoc, simp) σ_def]

中文:
引理 obj.η_def
  结论: (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η
  证明: rfl

@[to_additive (attr := reassoc, simp) σ_def]

Depends on / 依赖: Nonempty, Nonempty.some, uniqueOfSubsingleton
-/
lemma obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl

@[to_additive (attr := reassoc, simp) σ_def]
/--
lemma `obj.μ_def` / 引理 `obj.μ_def`

English:
lemma obj.μ_def
  statement: μ = LaxMonoidal.μ F X X ≫ F.map μ
  proof: rfl

@[to_additive]

中文:
引理 obj.μ_def
  结论: μ = 松弛幺半群.μ F X X ≫ F.map μ
  证明: rfl

@[to_additive]
-/
lemma obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

@[to_additive]
/--
Instance `map.instIsMonHom` / 实例 `map.instIsMonHom`

English:
instance map.instIsMonHom
  signature: : IsMonHom (F.map f) where
  body: by simp [← map_comp]
  mul_hom := by simp [← map_comp]

中文:
实例 map.instIsMonHom
  签名: : 是幺半群态射 (F.map f) where
  定义体: by simp [← map_comp]
  mul_hom := by simp [← map_comp]

Depends on / 依赖: map_comp, mul_hom
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
/--
Definition of `mapMon` / `mapMon` 的定义

English:
definition mapMon
  signature: : Mon C ⥤ Mon D where
  body: .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[to_additive (attr := simp)]

中文:
定义 mapMon
  签名: : 幺半群 C ⥤ 幺半群 D where
  定义体: .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[to_additive (attr := simp)]

Depends on / 依赖: F.obj
-/
def mapMon : Mon C ⥤ Mon D where
  obj A := .mk (F.obj A.X)
  map f := .mk (F.map f.hom)

@[to_additive (attr := simp)]
/--
theorem `id_mapMon_one` / 定理 `id_mapMon_one`

English:
theorem id_mapMon_one
  given: (X : Mon C)
  statement: η[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ η[X.X]
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 id_mapMon_one
  条件: (X : 幺半群 C)
  结论: η[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ η[X.X]
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem id_mapMon_one (X : Mon C) : η[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ η[X.X] := rfl

@[to_additive (attr := simp)]
/--
theorem `id_mapMon_mul` / 定理 `id_mapMon_mul`

English:
theorem id_mapMon_mul
  given: (X : Mon C)
  statement: μ[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ μ[X.X]
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 id_mapMon_mul
  条件: (X : 幺半群 C)
  结论: μ[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ μ[X.X]
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem id_mapMon_mul (X : Mon C) : μ[((𝟭 C).mapMon.obj X).X] = 𝟙 _ ≫ μ[X.X] := rfl

@[to_additive (attr := simp)]
/--
theorem `comp_mapMon_one` / 定理 `comp_mapMon_one`

English:
theorem comp_mapMon_one
  given: (X : Mon C)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comp_mapMon_one
  条件: (X : 幺半群 C)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comp_mapMon_one (X : Mon C) :
    η[((F ⋙ G).mapMon.obj X).X] = ε (F ⋙ G) ≫ (F ⋙ G).map η[X.X] :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_mapMon_mul` / 定理 `comp_mapMon_mul`

English:
theorem comp_mapMon_mul
  given: (X : Mon C)
  proof: rfl

中文:
定理 comp_mapMon_mul
  条件: (X : 幺半群 C)
  证明: rfl
-/
theorem comp_mapMon_mul (X : Mon C) :
    μ[((F ⋙ G).mapMon.obj X).X] = «μ» (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[X.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on monoid objects. -/
@[to_additive (attr := simps!)
/-- The identity functor is also the identity on additive monoid objects. -/]
/--
Definition of `mapMonIdIso` / `mapMonIdIso` 的定义

English:
definition mapMonIdIso
  signature: : mapMon (𝟭 C) ≅ 𝟭 (Mon C)
  body: NatIso.ofComponents fun X => Mon.mkIso (.refl _)

中文:
定义 mapMonIdIso
  签名: : mapMon (𝟭 C) ≅ 𝟭 (幺半群 C)
  定义体: NatIso.ofComponents fun X => Mon.mkIso (.refl _)

Depends on / 依赖: Mon.mkIso, NatIso, NatIso.ofComponents, ofComponents
-/
def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon C) :=
  NatIso.ofComponents fun X => Mon.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on monoid objects. -/
@[to_additive (attr := simps!)
/-- The composition functor is also the composition on additive monoid objects. -/]
/--
Definition of `mapMonCompIso` / `mapMonCompIso` 的定义

English:
definition mapMonCompIso
  signature: : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon
  body: NatIso.ofComponents fun X => Mon.mkIso (.refl _)

@[to_additive]

中文:
定义 mapMonCompIso
  签名: : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon
  定义体: NatIso.ofComponents fun X => Mon.mkIso (.refl _)

@[to_additive]

Depends on / 依赖: Mon.mkIso, NatIso, NatIso.ofComponents, ofComponents
-/
def mapMonCompIso : (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X => Mon.mkIso (.refl _)

@[to_additive]
/--
Instance `Faithful.mapMon` / 实例 `Faithful.mapMon`

English:
instance Faithful.mapMon
  signature: [F.Faithful]
  body: Mon.Hom.ext map_injective congr(($hfg).hom)

中文:
实例 忠实.mapMon
  签名: [F.忠实]
  定义体: Mon.Hom.ext map_injective congr(($hfg).hom)
-/
protected instance Faithful.mapMon [F.Faithful] : F.mapMon.Faithful where
map_injective {_X _Y} _f _g hfg := Mon.Hom.ext map_injective congr(($hfg).hom)

set_option backward.defeqAttrib.useBackward true in
/-- Natural transformations between functors lift to monoid objects. -/
@[to_additive (attr := simps!)
/-- Natural transformations between functors lift to additive monoid objects. -/]
/--
Definition of `mapMonNatTrans` / `mapMonNatTrans` 的定义

English:
definition mapMonNatTrans
  signature: (f : F ⟶ F') [NatTrans.IsMonoidal f]
  body: .mk' (f.app _)

中文:
定义 mapMon自然数Trans
  签名: (f : F ⟶ F') [自然变换.是幺半群 f]
  定义体: .mk' (f.app _)

Depends on / 依赖: f.app
-/
def mapMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapMon ⟶ F'.mapMon where
  app X := .mk' (f.app _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural isomorphisms between functors lift to monoid objects. -/
@[to_additive (attr := simps!)
/-- Natural isomorphisms between functors lift to additive monoid objects. -/]
/--
Definition of `mapMonNatIso` / `mapMonNatIso` 的定义

English:
definition mapMonNatIso
  signature: (e : F ≅ F') [NatTrans.IsMonoidal e.hom]
  body: NatIso.ofComponents fun X => Mon.mkIso (e.app _)

中文:
定义 mapMon自然数Iso
  签名: (e : F ≅ F') [自然变换.是幺半群 e.hom]
  定义体: NatIso.ofComponents fun X => Mon.mkIso (e.app _)

Depends on / 依赖: Mon.mkIso, NatIso, NatIso.ofComponents, e.app, ofComponents
-/
def mapMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapMon ≅ F'.mapMon :=
  NatIso.ofComponents fun X => Mon.mkIso (e.app _)

attribute [local simp] ε_tensorHom_comp_μ_assoc in
@[to_additive instIsAddMonHomε]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (ε F)

中文:
实例 :
  签名: 是幺半群态射 (ε F)
-/
instance : IsMonHom (ε F) where

end LaxMonoidal

section OplaxMonoidal
variable [F.OplaxMonoidal]

open scoped MonObj in
/-- Pullback a monoid object along a fully faithful oplax monoidal functor. -/
@[to_additive (attr := simps)
/-- Pullback an additive monoid object along a fully faithful oplax monoidal functor. -/]
/--
Definition of `FullyFaithful.monObj` / `FullyFaithful.monObj` 的定义

English:
abbreviation FullyFaithful.monObj
  signature: (hF : F.FullyFaithful) (X : C) [MonObj (F.obj X)]
  body: hF.preimage OplaxMonoidal.η F ≫ η[F.obj X]
mul := hF.preimage OplaxMonoidal.δ F X X ≫ μ[F.obj X]
one_mul := hF.map_injective by simp [← δ_natural_left_assoc]
mul_one := hF.map_injective by simp [← δ_natural_right_assoc]
mul_assoc := hF.map_injective by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

中文:
缩写 满忠实.monObj
  签名: (hF : F.满忠实) (X : C) [MonObj (F.obj X)]
  定义体: hF.preimage OplaxMonoidal.η F ≫ η[F.obj X]
mul := hF.preimage OplaxMonoidal.δ F X X ≫ μ[F.obj X]
one_mul := hF.map_injective by simp [← δ_natural_left_assoc]
mul_one := hF.map_injective by simp [← δ_natural_right_assoc]
mul_assoc := hF.map_injective by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

Depends on / 依赖: F.obj, OplaxMonoidal, hF.preimage, preimage
-/
abbrev FullyFaithful.monObj (hF : F.FullyFaithful) (X : C) [MonObj (F.obj X)] : MonObj X where
one := hF.preimage OplaxMonoidal.η F ≫ η[F.obj X]
mul := hF.preimage OplaxMonoidal.δ F X X ≫ μ[F.obj X]
one_mul := hF.map_injective by simp [← δ_natural_left_assoc]
mul_one := hF.map_injective by simp [← δ_natural_right_assoc]
mul_assoc := hF.map_injective by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

end OplaxMonoidal

section Monoidal
variable [F.Monoidal]

open scoped Obj

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/--
Instance `Full.mapMon` / 实例 `Full.mapMon`

English:
instance Full.mapMon
  signature: [F.Full] [F.Faithful]
  body: let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      isMonHom_hom.one_hom :=
F.map_injective by simpa [← hg, cancel_epi] using IsMonHom.one_hom f.hom
      isMonHom_hom.mul_hom :=
F.map_injective by simpa [← hg, cancel_epi] using IsMonHom.mul_hom f.hom },
      Mon.Hom.ext hg⟩

中文:
实例 满.mapMon
  签名: [F.满] [F.忠实]
  定义体: let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      isMonHom_hom.one_hom :=
F.map_injective by simpa [← hg, cancel_epi] using IsMonHom.one_hom f.hom
      isMonHom_hom.mul_hom :=
F.map_injective by simpa [← hg, cancel_epi] using IsMonHom.mul_hom f.hom },
      Mon.Hom.ext hg⟩
-/
protected instance Full.mapMon [F.Full] [F.Faithful] : F.mapMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      isMonHom_hom.one_hom :=
F.map_injective by simpa [← hg, cancel_epi] using IsMonHom.one_hom f.hom
      isMonHom_hom.mul_hom :=
F.map_injective by simpa [← hg, cancel_epi] using IsMonHom.mul_hom f.hom },
      Mon.Hom.ext hg⟩

/--
Instance `FullyFaithful.isAddMonHom_preimage` / 实例 `FullyFaithful.isAddMonHom_preimage`

English:
instance FullyFaithful.isAddMonHom_preimage
  signature: (hF : F.FullyFaithful) {X Y : C}
  body: hF.map_injective (by simp [← cancel_epi (ε F), ← obj.ζ_def_assoc, ← obj.ζ_def])
  add_hom := hF.map_injective (by
    simp [← obj.σ_def_assoc, ← obj.σ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)])

@[to_additive existing]

中文:
实例 满忠实.isAddMonHom_preimage
  签名: (hF : F.满忠实) {X Y : C}
  定义体: hF.map_injective (by simp [← cancel_epi (ε F), ← obj.ζ_def_assoc, ← obj.ζ_def])
  add_hom := hF.map_injective (by
    simp [← obj.σ_def_assoc, ← obj.σ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)])

@[to_additive existing]

Depends on / 依赖: cancel_epi, hF.map_injective, map_injective
-/
instance FullyFaithful.isAddMonHom_preimage (hF : F.FullyFaithful) {X Y : C}
    [AddMonObj X] [AddMonObj Y] (f : F.obj X ⟶ F.obj Y) [IsAddMonHom f] :
    IsAddMonHom (hF.preimage f) where
  zero_hom := hF.map_injective (by simp [← cancel_epi (ε F), ← obj.ζ_def_assoc, ← obj.ζ_def])
  add_hom := hF.map_injective (by
    simp [← obj.σ_def_assoc, ← obj.σ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)])

@[to_additive existing]
/--
Instance `FullyFaithful.isMonHom_preimage` / 实例 `FullyFaithful.isMonHom_preimage`

English:
instance FullyFaithful.isMonHom_preimage
  signature: (hF : F.FullyFaithful) {X Y : C}
  body: hF.map_injective by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
mul_hom := hF.map_injective by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

中文:
实例 满忠实.isMonHom_preimage
  签名: (hF : F.满忠实) {X Y : C}
  定义体: hF.map_injective by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
mul_hom := hF.map_injective by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

Depends on / 依赖: cancel_epi, hF.map_injective, map_injective
-/
instance FullyFaithful.isMonHom_preimage (hF : F.FullyFaithful) {X Y : C}
    [MonObj X] [MonObj Y] (f : F.obj X ⟶ F.obj Y) [IsMonHom f] :
    IsMonHom (hF.preimage f) where
one_hom := hF.map_injective by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
mul_hom := hF.map_injective by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `F.mapMon : Mon C ⥤ Mon D` is fully
faithful too. -/
@[to_additive (attr := simps)
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `F.mapAddMon : AddMon C ⥤ AddMon D`
is fully faithful too. -/]
/--
Definition of `FullyFaithful.mapMon` / `FullyFaithful.mapMon` 的定义

English:
definition FullyFaithful.mapMon
  signature: (hF : F.FullyFaithful)
  body: .mk' hF.preimage f.hom

中文:
定义 满忠实.mapMon
  签名: (hF : F.满忠实)
  定义体: .mk' hF.preimage f.hom
-/
protected def FullyFaithful.mapMon (hF : F.FullyFaithful) : F.mapMon.FullyFaithful where
preimage {X Y} f := .mk' hF.preimage f.hom

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] MonObj.ofIso_one MonObj.ofIso_mul in
open Monoidal in
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on monoid objects as on objects. -/
@[to_additive (attr := simp)
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on additive monoid objects as on objects. -/]
/--
lemma `essImage_mapMon` / 引理 `essImage_mapMon`

English:
lemma essImage_mapMon
  given: [F.Full] [F.Faithful] {M : Mon D}
  proof: by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(Mon.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    let : MonObj (F.obj N) := .ofIso e.symm
    let : MonObj N := (FullyFaithful.ofFullyFaithful F).monObj N
    refine ⟨.mk N, ⟨Mon.mkIso e ?_ ?_⟩⟩ <;> simp

中文:
引理 essImage_mapMon
  条件: [F.满] [F.忠实] {M : 幺半群 D}
  证明: by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(Mon.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    let : MonObj (F.obj N) := .ofIso e.symm
    let : MonObj N := (FullyFaithful.ofFullyFaithful F).monObj N
    refine ⟨.mk N, ⟨Mon.mkIso e ?_ ?_⟩⟩ <;> simp

Depends on / 依赖: F.obj, FullyFaithful, FullyFaithful.ofFullyFaithful, Mon.forget, Mon.mkIso, MonObj, e.symm, forget, mapIso, monObj, ofFullyFaithful
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.LaxBraided]
  signature: (M N : C) [MonObj M] [MonObj N]
  body: by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

中文:
实例 [F.松弛辫]
  签名: (M N : C) [MonObj M] [MonObj N]
  定义体: by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

Depends on / 依赖: Functor, Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc, map_comp
-/
instance [F.LaxBraided] (M N : C) [MonObj M] [MonObj N] : IsMonHom («μ» F M N) where
  one_hom := by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [-simp] IsMonHom.one_hom IsMonHom.one_hom_assoc IsMonHom.mul_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.LaxBraided]
  signature: : F.mapMon.LaxMonoidal where
  body: .mk (ε F)
  «μ» M N := .mk («μ» F M.X N.X)

中文:
实例 [F.松弛辫]
  签名: : F.mapMon.松弛幺半群 where
  定义体: .mk (ε F)
  «μ» M N := .mk («μ» F M.X N.X)
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Braided]
  signature: : F.mapMon.Monoidal
  body: CoreMonoidal.toMonoidal {
    εIso := Mon.mkIso (Monoidal.εIso F)
μIso M N := Mon.mkIso (Monoidal.μIso F M.X N.X) by simp [← Functor.map_comp]
  }

中文:
实例 [F.辫]
  签名: : F.mapMon.幺半群
  定义体: CoreMonoidal.toMonoidal {
    εIso := Mon.mkIso (Monoidal.εIso F)
μIso M N := Mon.mkIso (Monoidal.μIso F M.X N.X) by simp [← Functor.map_comp]
  }

Depends on / 依赖: CoreMonoidal, CoreMonoidal.toMonoidal, Functor, Functor.map_comp, Mon.mkIso, Monoidal, map_comp, toMonoidal
-/
instance [F.Braided] : F.mapMon.Monoidal :=
  CoreMonoidal.toMonoidal {
    εIso := Mon.mkIso (Monoidal.εIso F)
μIso M N := Mon.mkIso (Monoidal.μIso F M.X N.X) by simp [← Functor.map_comp]
  }

end BraidedCategory

variable [SymmetricCategory C] [SymmetricCategory D]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.LaxBraided]
  signature: : F.mapMon.LaxBraided where
  body: by ext; exact Functor.LaxBraided.braided ..

@[to_additive]

中文:
实例 [F.松弛辫]
  签名: : F.mapMon.松弛辫 where
  定义体: by ext; exact Functor.LaxBraided.braided ..

@[to_additive]

Depends on / 依赖: Functor, Functor.LaxBraided.braided, LaxBraided, braided
-/
instance [F.LaxBraided] : F.mapMon.LaxBraided where
  braided M N := by ext; exact Functor.LaxBraided.braided ..

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Braided]
  signature: : F.mapMon.Braided where

中文:
实例 [F.辫]
  签名: : F.mapMon.辫 where
-/
instance [F.Braided] : F.mapMon.Braided where

set_option backward.defeqAttrib.useBackward true in
variable (C D) in
/-- `mapMon` is functorial in the lax monoidal functor. -/
@[to_additive (attr := simps)
/-- `mapAddMon` is functorial in the lax monoidal functor. -/]
/--
Definition of `mapMonFunctor` / `mapMonFunctor` 的定义

English:
definition mapMonFunctor
  signature: : LaxMonoidalFunctor C D ⥤ Mon C ⥤ Mon D where
  body: F.mapMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

中文:
定义 mapMonFunctor
  签名: : 松弛幺半群函子 C D ⥤ 幺半群 C ⥤ 幺半群 D where
  定义体: F.mapMon
  map α := { app A := .mk' (α.hom.app A.X) }
  map_comp _ _ := rfl

Depends on / 依赖: F.mapMon, mapMon
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
/--
Definition of `mapMon` / `mapMon` 的定义

English:
definition mapMon
  signature: : F.mapMon ⊣ G.mapMon where
  body: mapMonIdIso.inv ≫ mapMonNatTrans a.unit ≫ mapMonCompIso.hom
  counit := mapMonCompIso.inv ≫ mapMonNatTrans a.counit ≫ mapMonIdIso.hom

中文:
定义 mapMon
  签名: : F.mapMon ⊣ G.mapMon where
  定义体: mapMonIdIso.inv ≫ mapMonNatTrans a.unit ≫ mapMonCompIso.hom
  counit := mapMonCompIso.inv ≫ mapMonNatTrans a.counit ≫ mapMonIdIso.hom

Depends on / 依赖: a.unit, mapMonCompIso, mapMonCompIso.hom, mapMonIdIso, mapMonIdIso.inv, mapMonNatTrans
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
/--
Definition of `mapMon` / `mapMon` 的定义

English:
definition mapMon
  signature: (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]
  body: e.functor.mapMon
  inverse := e.inverse.mapMon
  unitIso := mapMonIdIso.symm ≪≫ mapMonNatIso e.unitIso ≪≫ mapMonCompIso
  counitIso := mapMonCompIso.symm ≪≫ mapMonNatIso e.counitIso ≪≫ mapMonIdIso

中文:
定义 mapMon
  签名: (e : C ≌ D) [e.functor.幺半群] [e.inverse.幺半群] [e.是幺半群]
  定义体: e.functor.mapMon
  inverse := e.inverse.mapMon
  unitIso := mapMonIdIso.symm ≪≫ mapMonNatIso e.unitIso ≪≫ mapMonCompIso
  counitIso := mapMonCompIso.symm ≪≫ mapMonNatIso e.counitIso ≪≫ mapMonIdIso

Depends on / 依赖: e.functor.mapMon, functor, mapMon
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
/--
Definition of `laxMonoidalToMon` / `laxMonoidalToMon` 的定义

English:
definition laxMonoidalToMon
  signature: : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ⥤ Mon C where
  body: (F.mapMon : Mon _ ⥤ Mon C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

中文:
定义 laxMonoidalToMon
  签名: : 松弛幺半群函子 (离散 命题单元.{w + 1}) C ⥤ 幺半群 C where
  定义体: (F.mapMon : Mon _ ⥤ Mon C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

Depends on / 依赖: Discrete, F.mapMon, mapMon
-/
def laxMonoidalToMon : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ⥤ Mon C where
  obj F := (F.mapMon : Mon _ ⥤ Mon C).obj (trivial (Discrete PUnit))
  map α := ((Functor.mapMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps!) addMonToLaxMonoidalObj
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/--
Definition of `monToLaxMonoidalObj` / `monToLaxMonoidalObj` 的定义

English:
definition monToLaxMonoidalObj
  signature: (A : Mon C)
  body: (Functor.const _).obj A.X

中文:
定义 monToLaxMonoidalObj
  签名: (A : 幺半群 C)
  定义体: (Functor.const _).obj A.X

Depends on / 依赖: Functor, Functor.const
-/
def monToLaxMonoidalObj (A : Mon C) :
    Discrete PUnit.{w + 1} ⥤ C := (Functor.const _).obj A.X

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
instance (A : Mon C) : (monToLaxMonoidalObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

@[to_additive (attr := simp) addMonToLaxMonoidalObj_ε]
/--
lemma `monToLaxMonoidalObj_ε` / 引理 `monToLaxMonoidalObj_ε`

English:
lemma monToLaxMonoidalObj_ε
  given: (A : Mon C)
  proof: rfl

@[to_additive (attr := simp) addMonToLaxMonoidalObj_μ]

中文:
引理 monToLaxMonoidalObj_ε
  条件: (A : 幺半群 C)
  证明: rfl

@[to_additive (attr := simp) addMonToLaxMonoidalObj_μ]
-/
lemma monToLaxMonoidalObj_ε (A : Mon C) :
    ε (monToLaxMonoidalObj A) = η[A.X] := rfl

@[to_additive (attr := simp) addMonToLaxMonoidalObj_μ]
/--
lemma `monToLaxMonoidalObj_μ` / 引理 `monToLaxMonoidalObj_μ`

English:
lemma monToLaxMonoidalObj_μ
  given: (A : Mon C) (X Y)
  proof: rfl

中文:
引理 monToLaxMonoidalObj_μ
  条件: (A : 幺半群 C) (X Y)
  证明: rfl
-/
lemma monToLaxMonoidalObj_μ (A : Mon C) (X Y) :
    «μ» (monToLaxMonoidalObj A) X Y = μ[A.X] := rfl

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps) addMonToLaxMonoidal
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/--
Definition of `monToLaxMonoidal` / `monToLaxMonoidal` 的定义

English:
definition monToLaxMonoidal
  signature: : Mon C ⥤ LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C where
  body: LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

中文:
定义 monToLaxMonoidal
  签名: : 幺半群 C ⥤ 松弛幺半群函子 (离散 命题单元.{w + 1}) C where
  定义体: LaxMonoidalFunctor.of (monToLaxMonoidalObj A)
  map f :=
    { hom := { app _ := f.hom }
      isMonoidal := { } }

Depends on / 依赖: LaxMonoidalFunctor, LaxMonoidalFunctor.of, monToLaxMonoidalObj
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
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: :
  body: NatIso.ofComponents
    (fun F => LaxMonoidalFunctor.isoOfComponents (fun _ => F.mapIso (eqToIso (by ext))))

#adaptation_note

中文:
定义 unitIso
  签名: :
  定义体: NatIso.ofComponents
    (fun F => LaxMonoidalFunctor.isoOfComponents (fun _ => F.mapIso (eqToIso (by ext))))

#adaptation_note

Depends on / 依赖: F.mapIso, LaxMonoidalFunctor, LaxMonoidalFunctor.isoOfComponents, NatIso, NatIso.ofComponents, eqToIso, isoOfComponents, mapIso, ofComponents
-/
def unitIso :
    𝟭 (LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C) ≅ laxMonoidalToMon C ⋙ monToLaxMonoidal C :=
  NatIso.ofComponents
    (fun F => LaxMonoidalFunctor.isoOfComponents (fun _ => F.mapIso (eqToIso (by ext))))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `counitIso`. -/
@[to_additive (attr := simps!) /-- Auxiliary definition for `counitIso`. -/]
/--
Definition of `counitIsoAux` / `counitIsoAux` 的定义

English:
definition counitIsoAux
  signature: (F : Mon C)
  body: Iso.refl _

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_zero]

中文:
定义 counitIsoAux
  签名: (F : 幺半群 C)
  定义体: Iso.refl _

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_zero]

Depends on / 依赖: Iso.refl
-/
def counitIsoAux (F : Mon C) :
    ((monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C).obj F).X ≅ ((𝟭 (Mon C)).obj F).X :=
  Iso.refl _

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_zero]
/--
theorem `monToLaxMonoidal_laxMonoidalToMon_obj_one` / 定理 `monToLaxMonoidal_laxMonoidalToMon_obj_one`

English:
theorem monToLaxMonoidal_laxMonoidalToMon_obj_one
  given: (F : Mon C)
  proof: rfl

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_add]

中文:
定理 monToLaxMonoidal_laxMonoidalToMon_obj_one
  条件: (F : 幺半群 C)
  证明: rfl

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_add]
-/
theorem monToLaxMonoidal_laxMonoidalToMon_obj_one (F : Mon C) :
    η[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = η[F.X] ≫ 𝟙 _ :=
  rfl

@[to_additive (attr := simp) addMonToLaxMonoidal_laxMonoidalToAddMon_obj_add]
/--
theorem `monToLaxMonoidal_laxMonoidalToMon_obj_mul` / 定理 `monToLaxMonoidal_laxMonoidalToMon_obj_mul`

English:
theorem monToLaxMonoidal_laxMonoidalToMon_obj_mul
  given: (F : Mon C)
  proof: rfl

中文:
定理 monToLaxMonoidal_laxMonoidalToMon_obj_mul
  条件: (F : 幺半群 C)
  证明: rfl
-/
theorem monToLaxMonoidal_laxMonoidalToMon_obj_mul (F : Mon C) :
    μ[((monToLaxMonoidal C ⋙ laxMonoidalToMon C).obj F).X] = μ[F.X] ≫ 𝟙 _ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `isMonHom_counitIsoAux` / 定理 `isMonHom_counitIsoAux`

English:
theorem isMonHom_counitIsoAux
  given: (F : Mon C)

中文:
定理 isMonHom_counitIsoAux
  条件: (F : 幺半群 C)
-/
theorem isMonHom_counitIsoAux (F : Mon C) :
    IsMonHom (counitIsoAux C F).hom where

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `Mon.equivLaxMonoidalFunctorPUnit`. -/
@[to_additive (attr := simps!)
/-- Implementation of `AddMon.equivLaxMonoidalFunctorPUnit`. -/]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon C)
  body: NatIso.ofComponents fun F =>
    letI : IsMonHom (counitIsoAux.{w} C F).hom := isMonHom_counitIsoAux C F
    mkIso (counitIsoAux.{w} C F)

中文:
定义 counitIso
  签名: : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (幺半群 C)
  定义体: NatIso.ofComponents fun F =>
    letI : IsMonHom (counitIsoAux.{w} C F).hom := isMonHom_counitIsoAux C F
    mkIso (counitIsoAux.{w} C F)

Depends on / 依赖: IsMonHom, NatIso, NatIso.ofComponents, counitIsoAux, isMonHom_counitIsoAux, ofComponents
-/
def counitIso : monToLaxMonoidal.{w} C ⋙ laxMonoidalToMon C ≅ 𝟭 (Mon C) :=
  NatIso.ofComponents fun F =>
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
/--
Definition of `equivLaxMonoidalFunctorPUnit` / `equivLaxMonoidalFunctorPUnit` 的定义

English:
definition equivLaxMonoidalFunctorPUnit
  signature: : LaxMonoidalFunctor (Discrete PUnit.{w + 1}) C ≌ Mon C where
  body: laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

中文:
定义 equivLaxMonoidalFunctorPUnit
  签名: : 松弛幺半群函子 (离散 命题单元.{w + 1}) C ≌ 幺半群 C where
  定义体: laxMonoidalToMon C
  inverse := monToLaxMonoidal C
  unitIso := unitIso C
  counitIso := counitIso C

Depends on / 依赖: laxMonoidalToMon
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
/--
Definition of `IsCommAddMonObj` / `IsCommAddMonObj` 的定义

English:
class IsCommAddMonObj
  parameters: (X : C) [AddMonObj X]
  axioms and operations (1):
    - add_comm((X)) : (β_ X X).hom ≫ σ = σ  [default: by cat_disch]

中文:
类 是交换加法MonObj
  参数: (X : C) [加法MonObj X]
  公理与运算 (1 个):
    - add_comm((X)) : (β_ X X).hom ≫ σ = σ  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class IsCommAddMonObj (X : C) [AddMonObj X] where
  add_comm (X) : (β_ X X).hom ≫ σ = σ := by cat_disch

/-- Predicate for a monoid object to be commutative. -/
@[to_additive]
/--
Definition of `IsCommMonObj` / `IsCommMonObj` 的定义

English:
class IsCommMonObj
  parameters: (X : C) [MonObj X]
  axioms and operations (1):
    - mul_comm((X)) : (β_ X X).hom ≫ μ = μ  [default: by cat_disch]

中文:
类 是交换MonObj
  参数: (X : C) [MonObj X]
  公理与运算 (1 个):
    - mul_comm((X)) : (β_ X X).hom ≫ μ = μ  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class IsCommMonObj (X : C) [MonObj X] where
  mul_comm (X) : (β_ X X).hom ≫ μ = μ := by cat_disch

open scoped MonObj

namespace IsCommMonObj

attribute [reassoc (attr := simp, mon_tauto)] mul_comm

variable (M) in
@[to_additive (attr := reassoc (attr := simp, mon_tauto))]
/--
lemma `mul_comm'` / 引理 `mul_comm'`

English:
lemma mul_comm'
  given: [IsCommMonObj M]
  statement: (β_ M M).inv ≫ μ = μ
  proof: by simp [← cancel_epi (β_ M M).hom]

@[to_additive]

中文:
引理 mul_comm'
  条件: [是交换MonObj M]
  结论: (β_ M M).inv ≫ μ = μ
  证明: by simp [← cancel_epi (β_ M M).hom]

@[to_additive]

Depends on / 依赖: cancel_epi
-/
lemma mul_comm' [IsCommMonObj M] : (β_ M M).inv ≫ μ = μ := by simp [← cancel_epi (β_ M M).hom]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCommMonObj (𝟙_ C)
  body: by dsimp; rw [braiding_leftUnitor, unitors_equal]

中文:
实例 :
  签名: 是交换MonObj (𝟙_ C)
  定义体: by dsimp; rw [braiding_leftUnitor, unitors_equal]

Depends on / 依赖: braiding_leftUnitor, unitors_equal
-/
instance : IsCommMonObj (𝟙_ C) where
  mul_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal]

end IsCommMonObj

variable (M) in
@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `MonObj.mul_mul_mul_comm` / 引理 `MonObj.mul_mul_mul_comm`

English:
lemma MonObj.mul_mul_mul_comm
  given: [IsCommMonObj M]
  proof: by simp only [mon_tauto]

中文:
引理 MonObj.mul_mul_mul_comm
  条件: [是交换MonObj M]
  证明: by simp only [mon_tauto]

Depends on / 依赖: mon_tauto
-/
lemma MonObj.mul_mul_mul_comm [IsCommMonObj M] :
    tensorμ M M M M ≫ (μ otimesₘ μ) ≫ μ = (μ otimesₘ μ) ≫ μ := by simp only [mon_tauto]

variable (M) in
@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `MonObj.mul_mul_mul_comm'` / 引理 `MonObj.mul_mul_mul_comm'`

English:
lemma MonObj.mul_mul_mul_comm'
  given: [IsCommMonObj M]
  proof: by simp only [mon_tauto]

中文:
引理 MonObj.mul_mul_mul_comm'
  条件: [是交换MonObj M]
  证明: by simp only [mon_tauto]

Depends on / 依赖: mon_tauto
-/
lemma MonObj.mul_mul_mul_comm' [IsCommMonObj M] :
    tensorδ M M M M ≫ (μ otimesₘ μ) ≫ μ = (μ otimesₘ μ) ≫ μ := by simp only [mon_tauto]

end

section SymmetricCategory
variable [SymmetricCategory C] {M N W X Y Z : C} [MonObj M] [MonObj N]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: M] [IsCommMonObj N] : IsCommMonObj (M otimes N) where
  body: by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, MonObj.tensorObj.mul_def,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]

中文:
实例 [是交换MonObj
  签名: M] [是交换MonObj N] : 是交换MonObj (M otimes N) where
  定义体: by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, MonObj.tensorObj.mul_def,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]

Depends on / 依赖: IsIso.inv_comp_eq, MonObj, MonObj.tensorObj.mul_def, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp_assoc, SymmetricCategory, SymmetricCategory.braiding_swap_eq_inv_braiding, associator_inv_naturality_left_assoc, associator_naturality_right_assoc, braiding_swap_eq_inv_braiding, inv_comp_eq, mul_def, tensorHom_def_assoc, tensorObj, tensor_whiskerLeft, whiskerLeft_comp, whiskerLeft_comp_assoc, whiskerRight_tensor
-/
instance [IsCommMonObj M] [IsCommMonObj N] : IsCommMonObj (M otimes N) where
  mul_comm := by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, MonObj.tensorObj.mul_def,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]

end SymmetricCategory
end CategoryTheory
