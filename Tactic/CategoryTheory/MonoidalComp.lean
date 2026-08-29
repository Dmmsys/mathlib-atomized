/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal composition `⊗≫` (composition up to associators)

We provide `f ⊗≫ g`, the `monoidalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

## Example

Suppose we have a braiding morphism `R X Y : X ⊗ Y ⟶ Y ⊗ X` in a monoidal category, and that we
want to define the morphism with the type `V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅ ⟶ V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅` that
transposes the second and third components by `R V₂ V₃`. How to do this? The first guess would be
to use the whiskering operators `◁` and `▷`, and define the morphism as `V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅`.
However, this morphism has the type `V₁ ⊗ ((V₂ ⊗ V₃) ⊗ V₄) ⊗ V₅ ⟶ V₁ ⊗ ((V₃ ⊗ V₂) ⊗ V₄) ⊗ V₅`,
which is not what we need. We should insert suitable associators. The desired associators can,
in principle, be defined by using the primitive three-components associator
`α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` as a building block, but writing down actual definitions
are quite tedious, and we usually don't want to see them.

The monoidal composition `⊗≫` is designed to solve such a problem. In this case, we can define the
desired morphism as `𝟙 _ ⊗≫ V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅ ⊗≫ 𝟙 _`, where the first and the second `𝟙 _`
are completed as `𝟙 (V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅)` and `𝟙 (V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅)`, respectively.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open scoped MonoidalCategory

-- We could likely turn this into a `Prop`-valued existential if that proves useful.
/--
Definition of `MonoidalCoherence` / `MonoidalCoherence` 的定义

English:
class MonoidalCoherence
  parameters: (X Y : C)
  axioms and operations (1):
    - iso : X ≅ Y

中文:
类 幺半群相干
  参数: (X Y : C)
  公理与运算 (1 个):
    - iso : X ≅ Y
-/
class MonoidalCoherence (X Y : C) where
  /-- A monoidal structural isomorphism between two objects. -/
  iso : X ≅ Y

/-- Notation for identities up to unitors and associators. -/
scoped[CategoryTheory.MonoidalCategory] notation " otimes𝟙 " =>
  MonoidalCoherence.iso -- type as \ot 𝟙

/--
Definition of `monoidalIso` / `monoidalIso` 的定义

English:
abbreviation monoidalIso
  signature: (X Y : C) [MonoidalCoherence X Y]
  body: MonoidalCoherence.iso

中文:
缩写 monoidalIso
  签名: (X Y : C) [幺半群相干 X Y]
  定义体: MonoidalCoherence.iso

Depends on / 依赖: MonoidalCoherence, MonoidalCoherence.iso
-/
abbrev monoidalIso (X Y : C) [MonoidalCoherence X Y] : X ≅ Y := MonoidalCoherence.iso

/--
Definition of `monoidalComp` / `monoidalComp` 的定义

English:
definition monoidalComp
  signature: {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z)
  body: f ≫ otimes𝟙.hom ≫ g

@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " otimes≫ " =>
  monoidalComp -- type as \ot \gg

中文:
定义 monoidalComp
  签名: {W X Y Z : C} [幺半群相干 X Y] (f : W ⟶ X) (g : Y ⟶ Z)
  定义体: f ≫ otimes𝟙.hom ≫ g

@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " otimes≫ " =>
  monoidalComp -- type as \ot \gg
-/
def monoidalComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ otimes𝟙.hom ≫ g

@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " otimes≫ " =>
  monoidalComp -- type as \ot \gg

/--
Definition of `monoidalIsoComp` / `monoidalIsoComp` 的定义

English:
definition monoidalIsoComp
  signature: {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z)
  body: f ≪≫ otimes𝟙 ≪≫ g

@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪otimes≫ " =>
  monoidalIsoComp -- type as \ll \ot \gg

中文:
定义 monoidalIsoComp
  签名: {W X Y Z : C} [幺半群相干 X Y] (f : W ≅ X) (g : Y ≅ Z)
  定义体: f ≪≫ otimes𝟙 ≪≫ g

@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪otimes≫ " =>
  monoidalIsoComp -- type as \ll \ot \gg
-/
def monoidalIsoComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ otimes𝟙 ≪≫ g

@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪otimes≫ " =>
  monoidalIsoComp -- type as \ll \ot \gg

namespace MonoidalCoherence

variable [MonoidalCategory C]

@[simps]
/--
Instance `refl` / 实例 `refl`

English:
instance refl
  signature: (X : C)
  body: ⟨Iso.refl _⟩

@[simps]

中文:
实例 refl
  签名: (X : C)
  定义体: ⟨Iso.refl _⟩

@[simps]

Depends on / 依赖: Iso.refl
-/
instance refl (X : C) : MonoidalCoherence X X := ⟨Iso.refl _⟩

@[simps]
/--
Instance `whiskerLeft` / 实例 `whiskerLeft`

English:
instance whiskerLeft
  signature: (X Y Z : C) [MonoidalCoherence Y Z]
  body: ⟨whiskerLeftIso X otimes𝟙⟩

@[simps]

中文:
实例 whiskerLeft
  签名: (X Y Z : C) [幺半群相干 Y Z]
  定义体: ⟨whiskerLeftIso X otimes𝟙⟩

@[simps]

Depends on / 依赖: whiskerLeftIso
-/
instance whiskerLeft (X Y Z : C) [MonoidalCoherence Y Z] :
    MonoidalCoherence (X otimes Y) (X otimes Z) :=
  ⟨whiskerLeftIso X otimes𝟙⟩

@[simps]
/--
Instance `whiskerRight` / 实例 `whiskerRight`

English:
instance whiskerRight
  signature: (X Y Z : C) [MonoidalCoherence X Y]
  body: ⟨whiskerRightIso otimes𝟙 Z⟩

@[simps]

中文:
实例 whiskerRight
  签名: (X Y Z : C) [幺半群相干 X Y]
  定义体: ⟨whiskerRightIso otimes𝟙 Z⟩

@[simps]

Depends on / 依赖: whiskerRightIso
-/
instance whiskerRight (X Y Z : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X otimes Z) (Y otimes Z) :=
  ⟨whiskerRightIso otimes𝟙 Z⟩

@[simps]
/--
Instance `tensor_right` / 实例 `tensor_right`

English:
instance tensor_right
  signature: (X Y : C) [MonoidalCoherence (𝟙_ C) Y]
  body: ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X otimes𝟙)⟩

@[simps]

中文:
实例 tensor_right
  签名: (X Y : C) [幺半群相干 (𝟙_ C) Y]
  定义体: ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X otimes𝟙)⟩

@[simps]

Depends on / 依赖: whiskerLeftIso
-/
instance tensor_right (X Y : C) [MonoidalCoherence (𝟙_ C) Y] :
    MonoidalCoherence X (X otimes Y) :=
  ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X otimes𝟙)⟩

@[simps]
/--
Instance `tensor_right'` / 实例 `tensor_right'`

English:
instance tensor_right'
  signature: (X Y : C) [MonoidalCoherence Y (𝟙_ C)]
  body: ⟨whiskerLeftIso X otimes𝟙 ≪≫ (ρ_ X)⟩

@[simps]

中文:
实例 tensor_right'
  签名: (X Y : C) [幺半群相干 Y (𝟙_ C)]
  定义体: ⟨whiskerLeftIso X otimes𝟙 ≪≫ (ρ_ X)⟩

@[simps]

Depends on / 依赖: whiskerLeftIso
-/
instance tensor_right' (X Y : C) [MonoidalCoherence Y (𝟙_ C)] :
    MonoidalCoherence (X otimes Y) X :=
  ⟨whiskerLeftIso X otimes𝟙 ≪≫ (ρ_ X)⟩

@[simps]
/--
Instance `left` / 实例 `left`

English:
instance left
  signature: (X Y : C) [MonoidalCoherence X Y]
  body: ⟨fun_ X ≪≫ otimes𝟙⟩

@[simps]

中文:
实例 left
  签名: (X Y : C) [幺半群相干 X Y]
  定义体: ⟨fun_ X ≪≫ otimes𝟙⟩

@[simps]

Depends on / 依赖: fun_
-/
instance left (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (𝟙_ C otimes X) Y :=
  ⟨fun_ X ≪≫ otimes𝟙⟩

@[simps]
/--
Instance `left'` / 实例 `left'`

English:
instance left'
  signature: (X Y : C) [MonoidalCoherence X Y]
  body: ⟨otimes𝟙 ≪≫ (fun_ Y).symm⟩

@[simps]

中文:
实例 left'
  签名: (X Y : C) [幺半群相干 X Y]
  定义体: ⟨otimes𝟙 ≪≫ (fun_ Y).symm⟩

@[simps]

Depends on / 依赖: fun_
-/
instance left' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (𝟙_ C otimes Y) :=
  ⟨otimes𝟙 ≪≫ (fun_ Y).symm⟩

@[simps]
/--
Instance `right` / 实例 `right`

English:
instance right
  signature: (X Y : C) [MonoidalCoherence X Y]
  body: ⟨ρ_ X ≪≫ otimes𝟙⟩

@[simps]

中文:
实例 right
  签名: (X Y : C) [幺半群相干 X Y]
  定义体: ⟨ρ_ X ≪≫ otimes𝟙⟩

@[simps]
-/
instance right (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X otimes 𝟙_ C) Y :=
  ⟨ρ_ X ≪≫ otimes𝟙⟩

@[simps]
/--
Instance `right'` / 实例 `right'`

English:
instance right'
  signature: (X Y : C) [MonoidalCoherence X Y]
  body: ⟨otimes𝟙 ≪≫ (ρ_ Y).symm⟩

@[simps]

中文:
实例 right'
  签名: (X Y : C) [幺半群相干 X Y]
  定义体: ⟨otimes𝟙 ≪≫ (ρ_ Y).symm⟩

@[simps]
-/
instance right' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (Y otimes 𝟙_ C) :=
  ⟨otimes𝟙 ≪≫ (ρ_ Y).symm⟩

@[simps]
/--
Instance `assoc` / 实例 `assoc`

English:
instance assoc
  signature: (X Y Z W : C) [MonoidalCoherence (X otimes (Y otimes Z)) W]
  body: ⟨α_ X Y Z ≪≫ otimes𝟙⟩

@[simps]

中文:
实例 assoc
  签名: (X Y Z W : C) [幺半群相干 (X otimes (Y otimes Z)) W]
  定义体: ⟨α_ X Y Z ≪≫ otimes𝟙⟩

@[simps]
-/
instance assoc (X Y Z W : C) [MonoidalCoherence (X otimes (Y otimes Z)) W] :
    MonoidalCoherence ((X otimes Y) otimes Z) W :=
  ⟨α_ X Y Z ≪≫ otimes𝟙⟩

@[simps]
/--
Instance `assoc'` / 实例 `assoc'`

English:
instance assoc'
  signature: (W X Y Z : C) [MonoidalCoherence W (X otimes (Y otimes Z))]
  body: ⟨otimes𝟙 ≪≫ (α_ X Y Z).symm⟩

中文:
实例 assoc'
  签名: (W X Y Z : C) [幺半群相干 W (X otimes (Y otimes Z))]
  定义体: ⟨otimes𝟙 ≪≫ (α_ X Y Z).symm⟩
-/
instance assoc' (W X Y Z : C) [MonoidalCoherence W (X otimes (Y otimes Z))] :
    MonoidalCoherence W ((X otimes Y) otimes Z) :=
  ⟨otimes𝟙 ≪≫ (α_ X Y Z).symm⟩

end MonoidalCoherence

/--
lemma `monoidalComp_refl` / 引理 `monoidalComp_refl`

English:
lemma monoidalComp_refl
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  simp [monoidalComp]

中文:
引理 monoidalComp_refl
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  simp [monoidalComp]
-/
@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f otimes≫ g = f ≫ g := by
  simp [monoidalComp]

end CategoryTheory
