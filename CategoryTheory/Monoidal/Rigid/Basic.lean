/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.Tactic.ApplyFun

/-!
# Rigid (autonomous) monoidal categories

This file defines rigid (autonomous) monoidal categories and the necessary theory about
exact pairings and duals.

## Main definitions

* `ExactPairing` of two objects of a monoidal category
* Type classes `HasLeftDual` and `HasRightDual` that capture that a pairing exists
* The `rightAdjointMate f` as a morphism `fᘁ : Yᘁ ⟶ Xᘁ` for a morphism `f : X ⟶ Y`
* The classes of `RightRigidCategory`, `LeftRigidCategory` and `RigidCategory`

## Main statements

* `comp_rightAdjointMate`: The adjoint mates of the composition is the composition of
  adjoint mates.

## Notation

* `η_` and `ε_` denote the coevaluation and evaluation morphism of an exact pairing.
* `Xᘁ` and `ᘁX` denote the right and left dual of an object, as well as the adjoint
  mate of a morphism.

## Future work

* Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.
* Show that the left adjoint mate of the right adjoint mate of a morphism is the morphism itself.
* Simplify constructions in the case where a symmetry or braiding is present.
* Show that `ᘁ` gives an equivalence of categories `C ≅ (Cᵒᵖ)ᴹᵒᵖ`.
* Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).

## Notes

Although we construct the adjunction `tensorLeft Y ⊣ tensorLeft X` from `ExactPairing X Y`,
this is not a bijective correspondence.
I think the correct statement is that `tensorLeft Y` and `tensorLeft X` are
module endofunctors of `C` as a right `C` module category,
and `ExactPairing X Y` is in bijection with adjunctions compatible with this right `C` action.

## References

* <https://ncatlab.org/nlab/show/rigid+monoidal+category>

## Tags

rigid category, monoidal category

-/

@[expose] public section


open CategoryTheory MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/--
Definition of `ExactPairing` / `ExactPairing` 的定义

English:
class ExactPairing
  parameters: (X Y : C)
  axioms and operations (4):
    - coevaluation' : 𝟙_ C ⟶ X otimes Y
    - evaluation' : Y otimes X ⟶ 𝟙_ C
    - coevaluation_evaluation' : Y ◁ coevaluation' ≫ (α_ _ _ _).inv ≫ evaluation' ▷ Y = (ρ_ Y).hom ≫ (fun_ Y).inv  [default: by cat_disch]
    - evaluation_coevaluation' : coevaluation' ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ evaluation' = (fun_ X).hom ≫ (ρ_ X).inv  [default: by cat_disch]

中文:
类 ExactPairing
  参数: (X Y : C)
  公理与运算 (4 个):
    - coevaluation' : 𝟙_ C ⟶ X otimes Y
    - evaluation' : Y otimes X ⟶ 𝟙_ C
    - coevaluation_evaluation' : Y ◁ coevaluation' ≫ (α_ _ _ _).inv ≫ evaluation' ▷ Y = (ρ_ Y).hom ≫ (fun_ Y).inv  [默认: by cat_disch]
    - evaluation_coevaluation' : coevaluation' ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ evaluation' = (fun_ X).hom ≫ (ρ_ X).inv  [默认: by cat_disch]

Depends on / 依赖: cat_disch, coevaluation, evaluation, evaluation_coevaluation, fun_
-/
class ExactPairing (X Y : C) where
  /-- Coevaluation of an exact pairing.

  Do not use directly. Use `ExactPairing.coevaluation` instead. -/
  coevaluation' : 𝟙_ C ⟶ X otimes Y
  /-- Evaluation of an exact pairing.

  Do not use directly. Use `ExactPairing.evaluation` instead. -/
  evaluation' : Y otimes X ⟶ 𝟙_ C
  coevaluation_evaluation' :
    Y ◁ coevaluation' ≫ (α_ _ _ _).inv ≫ evaluation' ▷ Y = (ρ_ Y).hom ≫ (fun_ Y).inv := by
    cat_disch
  evaluation_coevaluation' :
    coevaluation' ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ evaluation' = (fun_ X).hom ≫ (ρ_ X).inv := by
    cat_disch

namespace ExactPairing

-- Porting note: as there is no mechanism equivalent to `[]` in Lean 3 to make
-- arguments for class fields explicit,
-- we now repeat all the fields without primes.
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Making.20variable.20in.20class.20field.20explicit
variable (X Y : C)
variable [ExactPairing X Y]

/--
Definition of `coevaluation` / `coevaluation` 的定义

English:
definition coevaluation
  signature: : 𝟙_ C ⟶ X otimes Y
  body: @coevaluation' _ _ _ X Y _

中文:
定义 coevaluation
  签名: : 𝟙_ C ⟶ X otimes Y
  定义体: @coevaluation' _ _ _ X Y _

Depends on / 依赖: coevaluation
-/
def coevaluation : 𝟙_ C ⟶ X otimes Y := @coevaluation' _ _ _ X Y _

/--
Definition of `evaluation` / `evaluation` 的定义

English:
definition evaluation
  signature: : Y otimes X ⟶ 𝟙_ C
  body: @evaluation' _ _ _ X Y _

@[inherit_doc] notation "η_" => ExactPairing.coevaluation
@[inherit_doc] notation "ε_" => ExactPairing.evaluation

中文:
定义 evaluation
  签名: : Y otimes X ⟶ 𝟙_ C
  定义体: @evaluation' _ _ _ X Y _

@[inherit_doc] notation "η_" => ExactPairing.coevaluation
@[inherit_doc] notation "ε_" => ExactPairing.evaluation

Depends on / 依赖: evaluation
-/
def evaluation : Y otimes X ⟶ 𝟙_ C := @evaluation' _ _ _ X Y _

@[inherit_doc] notation "η_" => ExactPairing.coevaluation
@[inherit_doc] notation "ε_" => ExactPairing.evaluation

/--
lemma `coevaluation_evaluation` / 引理 `coevaluation_evaluation`

English:
lemma coevaluation_evaluation
  proof: coevaluation_evaluation'

中文:
引理 coevaluation_evaluation
  证明: coevaluation_evaluation'

Depends on / 依赖: coevaluation_evaluation
-/
lemma coevaluation_evaluation :
    Y ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ ε_ X _ ▷ Y = (ρ_ Y).hom ≫ (fun_ Y).inv :=
  coevaluation_evaluation'

/--
lemma `evaluation_coevaluation` / 引理 `evaluation_coevaluation`

English:
lemma evaluation_coevaluation
  proof: evaluation_coevaluation'

中文:
引理 evaluation_coevaluation
  证明: evaluation_coevaluation'

Depends on / 依赖: evaluation_coevaluation
-/
lemma evaluation_coevaluation :
    η_ _ _ ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε_ _ Y = (fun_ X).hom ≫ (ρ_ X).inv :=
  evaluation_coevaluation'

/--
lemma `coevaluation_evaluation''` / 引理 `coevaluation_evaluation''`

English:
lemma coevaluation_evaluation''
  proof: by
  convert! coevaluation_evaluation X Y <;> simp [monoidalComp]

中文:
引理 coevaluation_evaluation''
  证明: by
  convert! coevaluation_evaluation X Y <;> simp [monoidalComp]

Depends on / 依赖: coevaluation_evaluation, convert, monoidalComp
-/
lemma coevaluation_evaluation'' :
    Y ◁ η_ X Y otimes≫ ε_ X Y ▷ Y = otimes𝟙.hom := by
  convert! coevaluation_evaluation X Y <;> simp [monoidalComp]

/--
lemma `evaluation_coevaluation''` / 引理 `evaluation_coevaluation''`

English:
lemma evaluation_coevaluation''
  proof: by
  convert! evaluation_coevaluation X Y <;> simp [monoidalComp]

中文:
引理 evaluation_coevaluation''
  证明: by
  convert! evaluation_coevaluation X Y <;> simp [monoidalComp]

Depends on / 依赖: convert, evaluation_coevaluation, monoidalComp
-/
lemma evaluation_coevaluation'' :
    η_ X Y ▷ X otimes≫ X ◁ ε_ X Y = otimes𝟙.hom := by
  convert! evaluation_coevaluation X Y <;> simp [monoidalComp]

end ExactPairing

attribute [reassoc (attr := simp)] ExactPairing.coevaluation_evaluation
attribute [reassoc (attr := simp)] ExactPairing.evaluation_coevaluation

/--
Instance `exactPairingUnit` / 实例 `exactPairingUnit`

English:
instance exactPairingUnit
  signature: : ExactPairing (𝟙_ C) (𝟙_ C) where
  body: (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by monoidal_coherence
  evaluation_coevaluation' := by monoidal_coherence

中文:
实例 exactPairingUnit
  签名: : ExactPairing (𝟙_ C) (𝟙_ C) where
  定义体: (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by monoidal_coherence
  evaluation_coevaluation' := by monoidal_coherence
-/
instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation' := (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by monoidal_coherence
  evaluation_coevaluation' := by monoidal_coherence

/--
Instance `ExactPairing.tensor` / 实例 `ExactPairing.tensor`

English:
instance ExactPairing.tensor
  signature: {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]
  body: η_ X₁ Y₁ otimes≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫ 𝟙 _
  evaluation' := 𝟙 _ otimes≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) otimes≫ ε_ X₂ Y₂
  coevaluation_evaluation' := by
    calc
      _ = (Y₂ otimes Y₁) ◁ η_ X₁ Y₁ otimes≫
          (Y₂ otimes Y₁) ◁ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫
          (Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂)) ▷ (Y₂ ot

中文:
实例 ExactPairing.tensor
  签名: {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]
  定义体: η_ X₁ Y₁ otimes≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫ 𝟙 _
  evaluation' := 𝟙 _ otimes≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) otimes≫ ε_ X₂ Y₂
  coevaluation_evaluation' := by
    calc
      _ = (Y₂ otimes Y₁) ◁ η_ X₁ Y₁ otimes≫
          (Y₂ otimes Y₁) ◁ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫
          (Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂)) ▷ (Y₂ ot

Depends on / 依赖: otimes
-/
instance ExactPairing.tensor {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    ExactPairing (X₁ otimes X₂) (Y₂ otimes Y₁) where
  coevaluation' := η_ X₁ Y₁ otimes≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫ 𝟙 _
  evaluation' := 𝟙 _ otimes≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) otimes≫ ε_ X₂ Y₂
  coevaluation_evaluation' := by
    calc
      _ = (Y₂ otimes Y₁) ◁ η_ X₁ Y₁ otimes≫
          (Y₂ otimes Y₁) ◁ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫
          (Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂)) ▷ (Y₂ otimes Y₁) otimes≫
          ε_ X₂ Y₂ ▷ (Y₂ otimes Y₁) := by monoidal
      -- Group η₂ and ε₁ so they compose with ≫ (both act on the Y₁ ⊗ X₁ factor):
      --
      -- Y₂ Y₁ ╭── X₁ ────────────╮
      -- │ │ │ ╭── X₂ ───╮ │
      -- │ │ │ │ │ │
      -- │ ╰──ε₁──╯ │ │ │
      -- │ │ │ │
      -- ╰────── ε₂ ──────╯ │ │
      -- Y₂ Y₁
      --
      _ = (Y₂ otimes Y₁) ◁ η_ X₁ Y₁ otimes≫
          Y₂ ◁ ((Y₁ otimes X₁) ◁ η_ X₂ Y₂ ≫ ε_ X₁ Y₁ ▷ (X₂ otimes Y₂)) ▷ Y₁ otimes≫
          ε_ X₂ Y₂ ▷ (Y₂ otimes Y₁) := by monoidal
      -- Slide the η₂ cup past the ε₁ cap (whisker_exchange), separating the
      -- two zigzags into independent snakes:
      --
      -- Y₂ Y₁
      -- │ │ ╭─X₁──╮
      -- │ │ │ │
      -- │ ╰───╯ │ ← snake for (X₁, Y₁)
      -- │ │
      -- │ ╭─X₂──╮ │
      -- │ │ │ │
      -- ╰──╯ │ │ ← snake for (X₂, Y₂)
      -- Y₂ Y₁
      --
      _ = (Y₂ otimes Y₁) ◁ η_ X₁ Y₁ otimes≫
          Y₂ ◁ (ε_ X₁ Y₁ ▷ (𝟙_ C) ≫ (𝟙_ C) ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫
          ε_ X₂ Y₂ ▷ (Y₂ otimes Y₁) := by
        rw [whisker_exchange]
      -- Separate into two snakes and cancel each.
      _ = 𝟙 _ otimes≫ Y₂ ◁ (Y₁ ◁ η_ X₁ Y₁ otimes≫ ε_ X₁ Y₁ ▷ Y₁) otimes≫
          (Y₂ ◁ η_ X₂ Y₂ otimes≫ ε_ X₂ Y₂ ▷ Y₂) ▷ Y₁ otimes≫ 𝟙 _ := by monoidal
      _ = _ := by rw [coevaluation_evaluation'', coevaluation_evaluation'']; monoidal
  evaluation_coevaluation' := by
    calc
      _ = η_ X₁ Y₁ ▷ (X₁ otimes X₂) otimes≫
          (X₁ ◁ η_ X₂ Y₂) ▷ (Y₁ otimes X₁ otimes X₂) otimes≫
          (X₁ otimes X₂) ◁ (Y₂ ◁ ε_ X₁ Y₁ ▷ X₂) otimes≫
          (X₁ otimes X₂) ◁ ε_ X₂ Y₂ := by monoidal
      -- Group η₂ and ε₁ so they compose with ≫:
      --
      -- ╭── Y₁ ────────────╮ X₁ X₂
      -- │ ╭── Y₂ ───╮ │ │ │
      -- │ │ │ │ │ │
      -- │ │ │ ╰──ε₁───╯ │
      -- │ │ │ │
      -- │ │ ╰──────── ε₂ ────╯
      -- X₁ X₂
      --
      _ = η_ X₁ Y₁ ▷ (X₁ otimes X₂) otimes≫
          X₁ ◁ (η_ X₂ Y₂ ▷ (Y₁ otimes X₁) ≫ (X₂ otimes Y₂) ◁ ε_ X₁ Y₁) ▷ X₂ otimes≫
          (X₁ otimes X₂) ◁ ε_ X₂ Y₂ := by monoidal
      -- Slide the ε₁ cap past the η₂ cup (← whisker_exchange), separating the
      -- two zigzags into independent snakes:
      --
      -- X₁ X₂
      -- ╭──Y₁──╮ │ │
      -- │ │ │ │
      -- │ ╰──────╯ │ ← snake for (X₁, Y₁)
      -- │ │
      -- │ ╭──Y₂──╮ │
      -- │ │ │ │
      -- │ │ ╰───────╯ ← snake for (X₂, Y₂)
      -- X₁ X₂
      --
      _ = η_ X₁ Y₁ ▷ (X₁ otimes X₂) otimes≫
          X₁ ◁ ((𝟙_ C) ◁ ε_ X₁ Y₁ ≫ η_ X₂ Y₂ ▷ (𝟙_ C)) ▷ X₂ otimes≫
          (X₁ otimes X₂) ◁ ε_ X₂ Y₂ := by
        rw [← whisker_exchange]
      -- Separate into two snakes and cancel each.
      _ = 𝟙 _ otimes≫ (η_ X₁ Y₁ ▷ X₁ otimes≫ X₁ ◁ ε_ X₁ Y₁) ▷ X₂ otimes≫
          X₁ ◁ (η_ X₂ Y₂ ▷ X₂ otimes≫ X₂ ◁ ε_ X₂ Y₂) otimes≫ 𝟙 _ := by monoidal
      _ = _ := by rw [evaluation_coevaluation'', evaluation_coevaluation'']; monoidal

/--
lemma `ExactPairing.tensor_coevaluation` / 引理 `ExactPairing.tensor_coevaluation`

English:
lemma ExactPairing.tensor_coevaluation
  statement: {X₁ X₂ Y₁ Y₂ : C}
  proof: rfl

中文:
引理 ExactPairing.tensor_coevaluation
  结论: {X₁ X₂ Y₁ Y₂ : C}
  证明: rfl
-/
lemma ExactPairing.tensor_coevaluation {X₁ X₂ Y₁ Y₂ : C}
    [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    η_ (X₁ otimes X₂) (Y₂ otimes Y₁) = η_ X₁ Y₁ otimes≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ otimes≫ 𝟙 _ :=
  rfl

/--
lemma `ExactPairing.tensor_evaluation` / 引理 `ExactPairing.tensor_evaluation`

English:
lemma ExactPairing.tensor_evaluation
  statement: {X₁ X₂ Y₁ Y₂ : C}
  proof: rfl

中文:
引理 ExactPairing.tensor_evaluation
  结论: {X₁ X₂ Y₁ Y₂ : C}
  证明: rfl
-/
lemma ExactPairing.tensor_evaluation {X₁ X₂ Y₁ Y₂ : C}
    [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    ε_ (X₁ otimes X₂) (Y₂ otimes Y₁) = 𝟙 _ otimes≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) otimes≫ ε_ X₂ Y₂ :=
  rfl

/--
Definition of `HasRightDual` / `HasRightDual` 的定义

English:
class HasRightDual
  parameters: (X : C)
  axioms and operations (2):
    - rightDual : C
    - [exact : ExactPairing X rightDual]

中文:
类 有RightDual
  参数: (X : C)
  公理与运算 (2 个):
    - rightDual : C
    - [exact : ExactPairing X rightDual]
-/
class HasRightDual (X : C) where
  /-- The right dual of the object `X`. -/
  rightDual : C
  [exact : ExactPairing X rightDual]

/--
Definition of `HasLeftDual` / `HasLeftDual` 的定义

English:
class HasLeftDual
  parameters: (Y : C)
  axioms and operations (2):
    - leftDual : C
    - [exact : ExactPairing leftDual Y]

中文:
类 有LeftDual
  参数: (Y : C)
  公理与运算 (2 个):
    - leftDual : C
    - [exact : ExactPairing leftDual Y]
-/
class HasLeftDual (Y : C) where
  /-- The left dual of the object `X`. -/
  leftDual : C
  [exact : ExactPairing leftDual Y]

attribute [instance_reducible, instance] HasRightDual.exact
attribute [instance_reducible, instance] HasLeftDual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

#adaptation_note /-- https://github.com/leanprover/lean4/pull/4596
The overlapping notation for `leftDual` and `leftAdjointMate` become more problematic in
after https://github.com/leanprover/lean4/pull/4596, and we sometimes have to disambiguate with
e.g. `(ᘁX : C)` where previously just `ᘁX` was enough. -/

@[inherit_doc] prefix:1024 "ᘁ" => leftDual
@[inherit_doc] postfix:1024 "ᘁ" => rightDual

/--
Instance `hasRightDualUnit` / 实例 `hasRightDualUnit`

English:
instance hasRightDualUnit
  signature: : HasRightDual (𝟙_ C) where
  body: 𝟙_ C

中文:
实例 hasRightDualUnit
  签名: : 有RightDual (𝟙_ C) where
  定义体: 𝟙_ C
-/
instance hasRightDualUnit : HasRightDual (𝟙_ C) where
  rightDual := 𝟙_ C

/--
Instance `hasLeftDualUnit` / 实例 `hasLeftDualUnit`

English:
instance hasLeftDualUnit
  signature: : HasLeftDual (𝟙_ C) where
  body: 𝟙_ C

中文:
实例 hasLeftDualUnit
  签名: : 有LeftDual (𝟙_ C) where
  定义体: 𝟙_ C
-/
instance hasLeftDualUnit : HasLeftDual (𝟙_ C) where
  leftDual := 𝟙_ C

/--
Instance `hasRightDualLeftDual` / 实例 `hasRightDualLeftDual`

English:
instance hasRightDualLeftDual
  signature: {X : C} [HasLeftDual X]
  body: X

中文:
实例 hasRightDualLeftDual
  签名: {X : C} [有LeftDual X]
  定义体: X
-/
instance hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where
  rightDual := X

/--
Instance `hasLeftDualRightDual` / 实例 `hasLeftDualRightDual`

English:
instance hasLeftDualRightDual
  signature: {X : C} [HasRightDual X]
  body: X

中文:
实例 hasLeftDualRightDual
  签名: {X : C} [有RightDual X]
  定义体: X
-/
instance hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where
  leftDual := X

/-- The tensor product of two objects with right duals has a right dual,
given by the tensor product of the duals in the opposite order. -/
@[implicit_reducible]
/--
Definition of `hasRightDualTensor` / `hasRightDualTensor` 的定义

English:
definition hasRightDualTensor
  signature: {X Y : C} [HasRightDual X] [HasRightDual Y]
  body: Yᘁ otimes Xᘁ

中文:
定义 hasRightDualTensor
  签名: {X Y : C} [有RightDual X] [有RightDual Y]
  定义体: Yᘁ otimes Xᘁ

Depends on / 依赖: otimes
-/
def hasRightDualTensor {X Y : C} [HasRightDual X] [HasRightDual Y] :
    HasRightDual (X otimes Y) where
  rightDual := Yᘁ otimes Xᘁ

/-- The tensor product of two objects with left duals has a left dual,
given by the tensor product of the duals in the opposite order. -/
@[implicit_reducible]
/--
Definition of `hasLeftDualTensor` / `hasLeftDualTensor` 的定义

English:
definition hasLeftDualTensor
  signature: {X Y : C} [HasLeftDual X] [HasLeftDual Y]
  body: ᘁY otimes ᘁX

@[simp]

中文:
定义 hasLeftDualTensor
  签名: {X Y : C} [有LeftDual X] [有LeftDual Y]
  定义体: ᘁY otimes ᘁX

@[simp]

Depends on / 依赖: otimes
-/
def hasLeftDualTensor {X Y : C} [HasLeftDual X] [HasLeftDual Y] :
    HasLeftDual (X otimes Y) where
  leftDual := ᘁY otimes ᘁX

@[simp]
/--
theorem `leftDual_rightDual` / 定理 `leftDual_rightDual`

English:
theorem leftDual_rightDual
  given: {X : C} [HasRightDual X]
  statement: ᘁXᘁ = X
  proof: rfl

@[simp]

中文:
定理 leftDual_rightDual
  条件: {X : C} [有RightDual X]
  结论: ᘁXᘁ = X
  证明: rfl

@[simp]
-/
theorem leftDual_rightDual {X : C} [HasRightDual X] : ᘁXᘁ = X :=
  rfl

@[simp]
/--
theorem `rightDual_leftDual` / 定理 `rightDual_leftDual`

English:
theorem rightDual_leftDual
  given: {X : C} [HasLeftDual X]
  statement: (ᘁX)ᘁ = X
  proof: rfl

中文:
定理 rightDual_leftDual
  条件: {X : C} [有LeftDual X]
  结论: (ᘁX)ᘁ = X
  证明: rfl
-/
theorem rightDual_leftDual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X :=
  rfl

/--
Definition of `rightAdjointMate` / `rightAdjointMate` 的定义

English:
definition rightAdjointMate
  signature: {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y)
  body: (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (fun_ _).hom

中文:
定义 rightAdjointMate
  签名: {X Y : C} [有RightDual X] [有RightDual Y] (f : X ⟶ Y)
  定义体: (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (fun_ _).hom

Depends on / 依赖: fun_
-/
def rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (fun_ _).hom

/--
Definition of `leftAdjointMate` / `leftAdjointMate` 的定义

English:
definition leftAdjointMate
  signature: {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y)
  body: (fun_ _).inv ≫ η_ (ᘁX) X ▷ _ ≫ (_ ◁ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f
@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

@[simp]

中文:
定义 leftAdjointMate
  签名: {X Y : C} [有LeftDual X] [有LeftDual Y] (f : X ⟶ Y)
  定义体: (fun_ _).inv ≫ η_ (ᘁX) X ▷ _ ≫ (_ ◁ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f
@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

@[simp]

Depends on / 依赖: fun_
-/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (fun_ _).inv ≫ η_ (ᘁX) X ▷ _ ≫ (_ ◁ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f
@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

@[simp]
/--
theorem `rightAdjointMate_id` / 定理 `rightAdjointMate_id`

English:
theorem rightAdjointMate_id
  given: {X : C} [HasRightDual X]
  statement: (𝟙 X)ᘁ = 𝟙 (Xᘁ)
  proof: by
  simp [rightAdjointMate]

@[simp]

中文:
定理 rightAdjointMate_id
  条件: {X : C} [有RightDual X]
  结论: (𝟙 X)ᘁ = 𝟙 (Xᘁ)
  证明: by
  simp [rightAdjointMate]

@[simp]

Depends on / 依赖: rightAdjointMate
-/
theorem rightAdjointMate_id {X : C} [HasRightDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ) := by
  simp [rightAdjointMate]

@[simp]
/--
theorem `leftAdjointMate_id` / 定理 `leftAdjointMate_id`

English:
theorem leftAdjointMate_id
  given: {X : C} [HasLeftDual X]
  statement: (ᘁ(𝟙 X)) = 𝟙 (ᘁX)
  proof: by
  simp [leftAdjointMate]

中文:
定理 leftAdjointMate_id
  条件: {X : C} [有LeftDual X]
  结论: (ᘁ(𝟙 X)) = 𝟙 (ᘁX)
  证明: by
  simp [leftAdjointMate]

Depends on / 依赖: leftAdjointMate
-/
theorem leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX) := by
  simp [leftAdjointMate]

/--
theorem `rightAdjointMate_comp` / 定理 `rightAdjointMate_comp`

English:
theorem rightAdjointMate_comp
  statement: {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
  proof: calc
    _ = 𝟙 _ otimes≫ (Yᘁ : C) ◁ η_ X Xᘁ ≫ Yᘁ ◁ f ▷ Xᘁ otimes≫ (ε_ Y Yᘁ ▷ Xᘁ ≫ 𝟙_ C ◁ g) otimes≫ 𝟙 _ := by
      dsimp only [rightAdjointMate]; monoidal
    _ = _ := by
      rw [← whisker_exchange]; rw [tensorHom_def]; monoidal

中文:
定理 rightAdjointMate_comp
  结论: {X Y Z : C} [有RightDual X] [有RightDual Y] {f : X ⟶ Y}
  证明: calc
    _ = 𝟙 _ otimes≫ (Yᘁ : C) ◁ η_ X Xᘁ ≫ Yᘁ ◁ f ▷ Xᘁ otimes≫ (ε_ Y Yᘁ ▷ Xᘁ ≫ 𝟙_ C ◁ g) otimes≫ 𝟙 _ := by
      dsimp only [rightAdjointMate]; monoidal
    _ = _ := by
      rw [← whisker_exchange]; rw [tensorHom_def]; monoidal

Depends on / 依赖: monoidal, otimes, rightAdjointMate, tensorHom_def, whisker_exchange
-/
theorem rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
    {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g =
      (ρ_ (Yᘁ)).inv ≫
        _ ◁ η_ X (Xᘁ) ≫ _ ◁ (f otimesₘ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ ε_ Y (Yᘁ) ▷ _ ≫ (fun_ Z).hom :=
  calc
    _ = 𝟙 _ otimes≫ (Yᘁ : C) ◁ η_ X Xᘁ ≫ Yᘁ ◁ f ▷ Xᘁ otimes≫ (ε_ Y Yᘁ ▷ Xᘁ ≫ 𝟙_ C ◁ g) otimes≫ 𝟙 _ := by
      dsimp only [rightAdjointMate]; monoidal
    _ = _ := by
      rw [← whisker_exchange]; rw [tensorHom_def]; monoidal

/--
theorem `leftAdjointMate_comp` / 定理 `leftAdjointMate_comp`

English:
theorem leftAdjointMate_comp
  statement: {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
  proof: calc
    _ = 𝟙 _ otimes≫ η_ (ᘁX : C) X ▷ (ᘁY) otimes≫ (ᘁX) ◁ f ▷ (ᘁY) otimes≫ ((ᘁX) ◁ ε_ (ᘁY) Y ≫ g ▷ 𝟙_ C) otimes≫ 𝟙 _ := by
      dsimp only [leftAdjointMate]; monoidal
    _ = _ := by
      rw [whisker_exchange]; rw [tensorHom_def']; monoidal

中文:
定理 leftAdjointMate_comp
  结论: {X Y Z : C} [有LeftDual X] [有LeftDual Y] {f : X ⟶ Y}
  证明: calc
    _ = 𝟙 _ otimes≫ η_ (ᘁX : C) X ▷ (ᘁY) otimes≫ (ᘁX) ◁ f ▷ (ᘁY) otimes≫ ((ᘁX) ◁ ε_ (ᘁY) Y ≫ g ▷ 𝟙_ C) otimes≫ 𝟙 _ := by
      dsimp only [leftAdjointMate]; monoidal
    _ = _ := by
      rw [whisker_exchange]; rw [tensorHom_def']; monoidal

Depends on / 依赖: leftAdjointMate, monoidal, otimes, tensorHom_def, whisker_exchange
-/
theorem leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
    {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g =
      (fun_ _).inv ≫
        η_ (ᘁX : C) X ▷ _ ≫ (g otimesₘ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom :=
  calc
    _ = 𝟙 _ otimes≫ η_ (ᘁX : C) X ▷ (ᘁY) otimes≫ (ᘁX) ◁ f ▷ (ᘁY) otimes≫ ((ᘁX) ◁ ε_ (ᘁY) Y ≫ g ▷ 𝟙_ C) otimes≫ 𝟙 _ := by
      dsimp only [leftAdjointMate]; monoidal
    _ = _ := by
      rw [whisker_exchange]; rw [tensorHom_def']; monoidal

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
/--
theorem `comp_rightAdjointMate` / 定理 `comp_rightAdjointMate`

English:
theorem comp_rightAdjointMate
  statement: {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
  proof: by
  rw [rightAdjointMate_comp]
  simp only [rightAdjointMate, comp_whiskerRight]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]; congr 2
  symm
  calc
    _ = 𝟙 _ otimes≫ (η_ Y Yᘁ ▷ 𝟙_ C ≫ (Y otimes Yᘁ) ◁ η_ X Xᘁ) otimes≫ Y ◁ Yᘁ

中文:
定理 comp_rightAdjointMate
  结论: {X Y Z : C} [有RightDual X] [有RightDual Y] [有RightDual Z]
  证明: by
  rw [rightAdjointMate_comp]
  simp only [rightAdjointMate, comp_whiskerRight]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]; congr 2
  symm
  calc
    _ = 𝟙 _ otimes≫ (η_ Y Yᘁ ▷ 𝟙_ C ≫ (Y otimes Yᘁ) ◁ η_ X Xᘁ) otimes≫ Y ◁ Yᘁ

Depends on / 依赖: Category, Category.assoc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, monoidal, otimes, rightAdjointMate, rightAdjointMate_comp, tensorHom_def, whiskerLeft_comp
-/
theorem comp_rightAdjointMate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ := by
  rw [rightAdjointMate_comp]
  simp only [rightAdjointMate, comp_whiskerRight]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]; congr 2
  symm
  calc
    _ = 𝟙 _ otimes≫ (η_ Y Yᘁ ▷ 𝟙_ C ≫ (Y otimes Yᘁ) ◁ η_ X Xᘁ) otimes≫ Y ◁ Yᘁ ◁ f ▷ Xᘁ otimes≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ otimes≫ g ▷ Xᘁ otimes≫ 𝟙 _ := by
      rw [tensorHom_def']; monoidal
    _ = η_ X Xᘁ otimes≫ (η_ Y Yᘁ ▷ (X otimes Xᘁ) ≫ (Y otimes Yᘁ) ◁ f ▷ Xᘁ) otimes≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ otimes≫ g ▷ Xᘁ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ X Xᘁ otimes≫ f ▷ Xᘁ otimes≫ (η_ Y Yᘁ ▷ Y otimes≫ Y ◁ ε_ Y Yᘁ) ▷ Xᘁ otimes≫ g ▷ Xᘁ otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ g ▷ Xᘁ := by
      rw [evaluation_coevaluation'']; monoidal

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
/--
theorem `comp_leftAdjointMate` / 定理 `comp_leftAdjointMate`

English:
theorem comp_leftAdjointMate
  statement: {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y}
  proof: by
  rw [leftAdjointMate_comp]
  simp only [leftAdjointMate, MonoidalCategory.whiskerLeft_comp]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← comp_whiskerRight]; congr 2
  symm
  calc
    _ = 𝟙 _ otimes≫ ((𝟙_ C) ◁ η_ (ᘁY) Y ≫ η_ (ᘁX) X ▷ ((ᘁY) otimes Y)) otimes≫ 

中文:
定理 comp_leftAdjointMate
  结论: {X Y Z : C} [有LeftDual X] [有LeftDual Y] [有LeftDual Z] {f : X ⟶ Y}
  证明: by
  rw [leftAdjointMate_comp]
  simp only [leftAdjointMate, MonoidalCategory.whiskerLeft_comp]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← comp_whiskerRight]; congr 2
  symm
  calc
    _ = 𝟙 _ otimes≫ ((𝟙_ C) ◁ η_ (ᘁY) Y ≫ η_ (ᘁX) X ▷ ((ᘁY) otimes Y)) otimes≫ 

Depends on / 依赖: Category, Category.assoc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, leftAdjointMate, leftAdjointMate_comp, monoidal, otimes, tensorHom_def, whiskerLeft_comp
-/
theorem comp_leftAdjointMate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf := by
  rw [leftAdjointMate_comp]
  simp only [leftAdjointMate, MonoidalCategory.whiskerLeft_comp]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← comp_whiskerRight]; congr 2
  symm
  calc
    _ = 𝟙 _ otimes≫ ((𝟙_ C) ◁ η_ (ᘁY) Y ≫ η_ (ᘁX) X ▷ ((ᘁY) otimes Y)) otimes≫ (ᘁX) ◁ f ▷ (ᘁY) ▷ Y otimes≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y otimes≫ (ᘁX) ◁ g := by
      rw [tensorHom_def]; monoidal
    _ = η_ (ᘁX) X otimes≫ (((ᘁX) otimes X) ◁ η_ (ᘁY) Y ≫ ((ᘁX) ◁ f) ▷ ((ᘁY) otimes Y)) otimes≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y otimes≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; monoidal
    _ = η_ (ᘁX) X otimes≫ ((ᘁX) ◁ f) otimes≫ (ᘁX) ◁ (Y ◁ η_ (ᘁY) Y otimes≫ ε_ (ᘁY) Y ▷ Y) otimes≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; monoidal
    _ = η_ (ᘁX) X ≫ (ᘁX) ◁ f ≫ (ᘁX) ◁ g := by
      rw [coevaluation_evaluation'']; monoidal

/--
Definition of `tensorLeftHomEquiv` / `tensorLeftHomEquiv` 的定义

English:
definition tensorLeftHomEquiv
  signature: (X Y Y' Z : C) [ExactPairing Y Y']
  body: (fun_ _).inv ≫ η_ _ _ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ f
  invFun f := Y' ◁ f ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (fun_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ otimes≫ Y' ◁ η_ Y Y' ▷ X otimes≫ ((Y' otimes Y) ◁ f ≫ ε_ Y Y' ▷ Z) otimes≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ otimes≫ (Y' ◁ η_ Y Y' oti

中文:
定义 tensorLeftHomEquiv
  签名: (X Y Y' Z : C) [ExactPairing Y Y']
  定义体: (fun_ _).inv ≫ η_ _ _ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ f
  invFun f := Y' ◁ f ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (fun_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ otimes≫ Y' ◁ η_ Y Y' ▷ X otimes≫ ((Y' otimes Y) ◁ f ≫ ε_ Y Y' ▷ Z) otimes≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ otimes≫ (Y' ◁ η_ Y Y' oti

Depends on / 依赖: fun_
-/
def tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (Y' otimes X ⟶ Z) ≃ (X ⟶ Y otimes Z) where
  toFun f := (fun_ _).inv ≫ η_ _ _ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ f
  invFun f := Y' ◁ f ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (fun_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ otimes≫ Y' ◁ η_ Y Y' ▷ X otimes≫ ((Y' otimes Y) ◁ f ≫ ε_ Y Y' ▷ Z) otimes≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ otimes≫ (Y' ◁ η_ Y Y' otimes≫ ε_ Y Y' ▷ Y') ▷ X otimes≫ f := by
        rw [whisker_exchange]; monoidal
      _ = f := by
        rw [coevaluation_evaluation'']; monoidal
  right_inv f := by
    calc
      _ = 𝟙 _ otimes≫ (η_ Y Y' ▷ X ≫ (Y otimes Y') ◁ f) otimes≫ Y ◁ ε_ Y Y' ▷ Z otimes≫ 𝟙 _ := by
        monoidal
      _ = f otimes≫ (η_ Y Y' ▷ Y otimes≫ Y ◁ ε_ Y Y') ▷ Z otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = f := by
        rw [evaluation_coevaluation'']; monoidal

/--
Definition of `tensorRightHomEquiv` / `tensorRightHomEquiv` 的定义

English:
definition tensorRightHomEquiv
  signature: (X Y Y' Z : C) [ExactPairing Y Y']
  body: (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _
  invFun f := f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ otimes≫ X ◁ η_ Y Y' ▷ Y otimes≫ (f ▷ (Y' otimes Y) ≫ Z ◁ ε_ Y Y') otimes≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ otimes≫ X ◁ (η_ Y Y' ▷ Y otimes

中文:
定义 tensorRightHomEquiv
  签名: (X Y Y' Z : C) [ExactPairing Y Y']
  定义体: (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _
  invFun f := f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ otimes≫ X ◁ η_ Y Y' ▷ Y otimes≫ (f ▷ (Y' otimes Y) ≫ Z ◁ ε_ Y Y') otimes≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ otimes≫ X ◁ (η_ Y Y' ▷ Y otimes
-/
def tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (X otimes Y ⟶ Z) ≃ (X ⟶ Z otimes Y') where
  toFun f := (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _
  invFun f := f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ otimes≫ X ◁ η_ Y Y' ▷ Y otimes≫ (f ▷ (Y' otimes Y) ≫ Z ◁ ε_ Y Y') otimes≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ otimes≫ X ◁ (η_ Y Y' ▷ Y otimes≫ Y ◁ ε_ Y Y') otimes≫ f := by
        rw [← whisker_exchange]; monoidal
      _ = f := by
        rw [evaluation_coevaluation'']; monoidal
  right_inv f := by
    calc
      _ = 𝟙 _ otimes≫ (X ◁ η_ Y Y' ≫ f ▷ (Y otimes Y')) otimes≫ Z ◁ ε_ Y Y' ▷ Y' otimes≫ 𝟙 _ := by
        monoidal
      _ = f otimes≫ Z ◁ (Y' ◁ η_ Y Y' otimes≫ ε_ Y Y' ▷ Y') otimes≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = f := by
        rw [coevaluation_evaluation'']; monoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tensorLeftHomEquiv_naturality` / 定理 `tensorLeftHomEquiv_naturality`

English:
theorem tensorLeftHomEquiv_naturality
  statement: {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' otimes X ⟶ Z)
  proof: by
  simp [tensorLeftHomEquiv]

中文:
定理 tensorLeftHomEquiv_naturality
  结论: {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' otimes X ⟶ Z)
  证明: by
  simp [tensorLeftHomEquiv]

Depends on / 依赖: tensorLeftHomEquiv
-/
theorem tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' otimes X ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g := by
  simp [tensorLeftHomEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tensorLeftHomEquiv_symm_naturality` / 定理 `tensorLeftHomEquiv_symm_naturality`

English:
theorem tensorLeftHomEquiv_symm_naturality
  statement: {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
  proof: by
  simp [tensorLeftHomEquiv]

中文:
定理 tensorLeftHomEquiv_symm_naturality
  结论: {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
  证明: by
  simp [tensorLeftHomEquiv]

Depends on / 依赖: tensorLeftHomEquiv
-/
theorem tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Y otimes Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      _ ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g := by
  simp [tensorLeftHomEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tensorRightHomEquiv_naturality` / 定理 `tensorRightHomEquiv_naturality`

English:
theorem tensorRightHomEquiv_naturality
  statement: {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X otimes Y ⟶ Z)
  proof: by
  simp [tensorRightHomEquiv]

中文:
定理 tensorRightHomEquiv_naturality
  结论: {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X otimes Y ⟶ Z)
  证明: by
  simp [tensorRightHomEquiv]

Depends on / 依赖: tensorRightHomEquiv
-/
theorem tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X otimes Y ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y' := by
  simp [tensorRightHomEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tensorRightHomEquiv_symm_naturality` / 定理 `tensorRightHomEquiv_symm_naturality`

English:
theorem tensorRightHomEquiv_symm_naturality
  statement: {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
  proof: by
  simp [tensorRightHomEquiv]

中文:
定理 tensorRightHomEquiv_symm_naturality
  结论: {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
  证明: by
  simp [tensorRightHomEquiv]

Depends on / 依赖: tensorRightHomEquiv
-/
theorem tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Z otimes Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g := by
  simp [tensorRightHomEquiv]

/--
Definition of `tensorLeftAdjunction` / `tensorLeftAdjunction` 的定义

English:
definition tensorLeftAdjunction
  signature: (Y Y' : C) [ExactPairing Y Y']
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorLeftHomEquiv_naturality f g }

中文:
定义 tensorLeftAdjunction
  签名: (Y Y' : C) [ExactPairing Y Y']
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorLeftHomEquiv_naturality f g }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv, tensorLeftHomEquiv, tensorLeftHomEquiv_naturality, tensorLeftHomEquiv_symm_naturality
-/
def tensorLeftAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorLeft Y' ⊣ tensorLeft Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorLeftHomEquiv_naturality f g }

/--
Definition of `tensorRightAdjunction` / `tensorRightAdjunction` 的定义

English:
definition tensorRightAdjunction
  signature: (Y Y' : C) [ExactPairing Y Y']
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorRightHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorRightHomEquiv_naturality f g }

中文:
定义 tensorRightAdjunction
  签名: (Y Y' : C) [ExactPairing Y Y']
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorRightHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorRightHomEquiv_naturality f g }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv, tensorRightHomEquiv, tensorRightHomEquiv_naturality, tensorRightHomEquiv_symm_naturality
-/
def tensorRightAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorRight Y ⊣ tensorRight Y' :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorRightHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorRightHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorRightHomEquiv_naturality f g }

/--
If `Y` has a left dual `ᘁY`, then it is a closed object, with the internal hom functor `Y ⟶[C] -`
given by left tensoring by `ᘁY`.
This has to be a definition rather than an instance to avoid diamonds, for example between
`category_theory.monoidal_closed.functor_closed` and
`CategoryTheory.Monoidal.functorHasLeftDual`. Moreover, in concrete applications there is often
a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the closed
structure shouldn't come from `HasLeftDual` (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic).
-/
@[instance_reducible]
/--
Definition of `closedOfHasLeftDual` / `closedOfHasLeftDual` 的定义

English:
definition closedOfHasLeftDual
  signature: (Y : C) [HasLeftDual Y]
  body: tensorLeft (ᘁY)
  adj := tensorLeftAdjunction (ᘁY) Y

中文:
定义 closedOfHasLeftDual
  签名: (Y : C) [有LeftDual Y]
  定义体: tensorLeft (ᘁY)
  adj := tensorLeftAdjunction (ᘁY) Y

Depends on / 依赖: tensorLeft
-/
def closedOfHasLeftDual (Y : C) [HasLeftDual Y] : Closed Y where
  rightAdj := tensorLeft (ᘁY)
  adj := tensorLeftAdjunction (ᘁY) Y

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tensorLeftHomEquiv_tensor` / 定理 `tensorLeftHomEquiv_tensor`

English:
theorem tensorLeftHomEquiv_tensor
  statement: {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y otimes Z)
  proof: by
  simp [tensorLeftHomEquiv, tensorHom_def']

中文:
定理 tensorLeftHomEquiv_tensor
  结论: {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y otimes Z)
  证明: by
  simp [tensorLeftHomEquiv, tensorHom_def']

Depends on / 依赖: tensorHom_def, tensorLeftHomEquiv
-/
theorem tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y otimes Z)
    (g : X' ⟶ Z') :
    (tensorLeftHomEquiv (X otimes X') Y Y' (Z otimes Z')).symm ((f otimesₘ g) ≫ (α_ _ _ _).hom) =
      (α_ _ _ _).inv ≫ ((tensorLeftHomEquiv X Y Y' Z).symm f otimesₘ g) := by
  simp [tensorLeftHomEquiv, tensorHom_def']

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `tensorRightHomEquiv_tensor` / 定理 `tensorRightHomEquiv_tensor`

English:
theorem tensorRightHomEquiv_tensor
  statement: {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z otimes Y')
  proof: by
  simp [tensorRightHomEquiv, tensorHom_def]

中文:
定理 tensorRightHomEquiv_tensor
  结论: {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z otimes Y')
  证明: by
  simp [tensorRightHomEquiv, tensorHom_def]

Depends on / 依赖: tensorHom_def, tensorRightHomEquiv
-/
theorem tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z otimes Y')
    (g : X' ⟶ Z') :
    (tensorRightHomEquiv (X' otimes X) Y Y' (Z' otimes Z)).symm ((g otimesₘ f) ≫ (α_ _ _ _).inv) =
      (α_ _ _ _).hom ≫ (g otimesₘ (tensorRightHomEquiv X Y Y' Z).symm f) := by
  simp [tensorRightHomEquiv, tensorHom_def]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft` / 定理 `tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft`

English:
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft
  statement: {Y Y' Z : C} [ExactPairing Y Y']
  proof: by
  calc
    _ = Y' ◁ η_ Y Y' otimes≫ ((Y' otimes Y) ◁ f ≫ ε_ Y Y' ▷ Z) otimes≫ 𝟙 _ := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = (Y' ◁ η_ Y Y' otimes≫ ε_ Y Y' ▷ Y') otimes≫ f := by
      rw [whisker_exchange]; monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

中文:
定理 tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft
  结论: {Y Y' Z : C} [ExactPairing Y Y']
  证明: by
  calc
    _ = Y' ◁ η_ Y Y' otimes≫ ((Y' otimes Y) ◁ f ≫ ε_ Y Y' ▷ Z) otimes≫ 𝟙 _ := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = (Y' ◁ η_ Y Y' otimes≫ ε_ Y Y' ▷ Y') otimes≫ f := by
      rw [whisker_exchange]; monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

Depends on / 依赖: coevaluation_evaluation, monoidal, otimes, tensorLeftHomEquiv, whisker_exchange
-/
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ Y ◁ f) = (ρ_ _).hom ≫ f := by
  calc
    _ = Y' ◁ η_ Y Y' otimes≫ ((Y' otimes Y) ◁ f ≫ ε_ Y Y' ▷ Z) otimes≫ 𝟙 _ := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = (Y' ◁ η_ Y Y' otimes≫ ε_ Y Y' ▷ Y') otimes≫ f := by
      rw [whisker_exchange]; monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight` / 定理 `tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight`

English:
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight
  statement: {X Y : C} [HasRightDual X]
  proof: by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  simp

中文:
定理 tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight
  结论: {X Y : C} [有RightDual X]
  证明: by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  simp

Depends on / 依赖: rightAdjointMate, tensorLeftHomEquiv
-/
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight {X Y : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) :
    (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ f ▷ (Xᘁ)) = (ρ_ _).hom ≫ fᘁ := by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft` / 定理 `tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft`

English:
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft
  statement: {X Y : C} [HasLeftDual X]
  proof: by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  simp

中文:
定理 tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft
  结论: {X Y : C} [有LeftDual X]
  证明: by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  simp

Depends on / 依赖: leftAdjointMate, tensorRightHomEquiv
-/
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft {X Y : C} [HasLeftDual X]
    [HasLeftDual Y] (f : X ⟶ Y) :
    (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (ᘁX : C) X ≫ (ᘁX : C) ◁ f) = (fun_ _).hom ≫ ᘁf := by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight` / 定理 `tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight`

English:
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight
  statement: {Y Y' Z : C} [ExactPairing Y Y']
  proof: calc
    _ = η_ Y Y' ▷ Y otimes≫ (f ▷ (Y' otimes Y) ≫ Z ◁ ε_ Y Y') otimes≫ 𝟙 _ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = (η_ Y Y' ▷ Y otimes≫ Y ◁ ε_ Y Y') otimes≫ f := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

中文:
定理 tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight
  结论: {Y Y' Z : C} [ExactPairing Y Y']
  证明: calc
    _ = η_ Y Y' ▷ Y otimes≫ (f ▷ (Y' otimes Y) ≫ Z ◁ ε_ Y Y') otimes≫ 𝟙 _ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = (η_ Y Y' ▷ Y otimes≫ Y ◁ ε_ Y Y') otimes≫ f := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

Depends on / 依赖: evaluation_coevaluation, monoidal, otimes, tensorRightHomEquiv, whisker_exchange
-/
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ f ▷ Y') = (fun_ _).hom ≫ f :=
  calc
    _ = η_ Y Y' ▷ Y otimes≫ (f ▷ (Y' otimes Y) ≫ Z ◁ ε_ Y Y') otimes≫ 𝟙 _ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = (η_ Y Y' ▷ Y otimes≫ Y ◁ ε_ Y Y') otimes≫ f := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorLeftHomEquiv_whiskerLeft_comp_evaluation` / 定理 `tensorLeftHomEquiv_whiskerLeft_comp_evaluation`

English:
theorem tensorLeftHomEquiv_whiskerLeft_comp_evaluation
  given: {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ)
  proof: calc
    _ = 𝟙 _ otimes≫ (η_ (ᘁZ : C) Z ▷ Y ≫ ((ᘁZ) otimes Z) ◁ f) otimes≫ (ᘁZ) ◁ ε_ (ᘁZ) Z := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = f otimes≫ (η_ (ᘁZ) Z ▷ (ᘁZ) otimes≫ (ᘁZ) ◁ ε_ (ᘁZ) Z) := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation''

中文:
定理 tensorLeftHomEquiv_whiskerLeft_comp_evaluation
  条件: {Y Z : C} [有LeftDual Z] (f : Y ⟶ ᘁZ)
  证明: calc
    _ = 𝟙 _ otimes≫ (η_ (ᘁZ : C) Z ▷ Y ≫ ((ᘁZ) otimes Z) ◁ f) otimes≫ (ᘁZ) ◁ ε_ (ᘁZ) Z := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = f otimes≫ (η_ (ᘁZ) Z ▷ (ᘁZ) otimes≫ (ᘁZ) ◁ ε_ (ᘁZ) Z) := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation''

Depends on / 依赖: evaluation_coevaluation, monoidal, otimes, tensorLeftHomEquiv, whisker_exchange
-/
theorem tensorLeftHomEquiv_whiskerLeft_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) :
    (tensorLeftHomEquiv _ _ _ _) (Z ◁ f ≫ ε_ _ _) = f ≫ (ρ_ _).inv :=
  calc
    _ = 𝟙 _ otimes≫ (η_ (ᘁZ : C) Z ▷ Y ≫ ((ᘁZ) otimes Z) ◁ f) otimes≫ (ᘁZ) ◁ ε_ (ᘁZ) Z := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = f otimes≫ (η_ (ᘁZ) Z ▷ (ᘁZ) otimes≫ (ᘁZ) ◁ ε_ (ᘁZ) Z) := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

@[simp]
/--
theorem `tensorLeftHomEquiv_whiskerRight_comp_evaluation` / 定理 `tensorLeftHomEquiv_whiskerRight_comp_evaluation`

English:
theorem tensorLeftHomEquiv_whiskerRight_comp_evaluation
  statement: {X Y : C} [HasLeftDual X] [HasLeftDual Y]
  proof: by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  simp

@[simp]

中文:
定理 tensorLeftHomEquiv_whiskerRight_comp_evaluation
  结论: {X Y : C} [有LeftDual X] [有LeftDual Y]
  证明: by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  simp

@[simp]

Depends on / 依赖: leftAdjointMate, tensorLeftHomEquiv
-/
theorem tensorLeftHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) (f ▷ _ ≫ ε_ _ _) = (ᘁf) ≫ (ρ_ _).inv := by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  simp

@[simp]
/--
theorem `tensorRightHomEquiv_whiskerLeft_comp_evaluation` / 定理 `tensorRightHomEquiv_whiskerLeft_comp_evaluation`

English:
theorem tensorRightHomEquiv_whiskerLeft_comp_evaluation
  statement: {X Y : C} [HasRightDual X] [HasRightDual Y]
  proof: by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  simp

中文:
定理 tensorRightHomEquiv_whiskerLeft_comp_evaluation
  结论: {X Y : C} [有RightDual X] [有RightDual Y]
  证明: by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  simp

Depends on / 依赖: rightAdjointMate, tensorRightHomEquiv
-/
theorem tensorRightHomEquiv_whiskerLeft_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((Yᘁ : C) ◁ f ≫ ε_ _ _) = fᘁ ≫ (fun_ _).inv := by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorRightHomEquiv_whiskerRight_comp_evaluation` / 定理 `tensorRightHomEquiv_whiskerRight_comp_evaluation`

English:
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation
  given: {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ)
  proof: calc
    _ = 𝟙 _ otimes≫ (Y ◁ η_ X Xᘁ ≫ f ▷ (X otimes Xᘁ)) otimes≫ ε_ X Xᘁ ▷ Xᘁ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = f otimes≫ (Xᘁ ◁ η_ X Xᘁ otimes≫ ε_ X Xᘁ ▷ Xᘁ) := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [coevaluation_evaluation'']; monoidal

中文:
定理 tensorRightHomEquiv_whiskerRight_comp_evaluation
  条件: {X Y : C} [有RightDual X] (f : Y ⟶ Xᘁ)
  证明: calc
    _ = 𝟙 _ otimes≫ (Y ◁ η_ X Xᘁ ≫ f ▷ (X otimes Xᘁ)) otimes≫ ε_ X Xᘁ ▷ Xᘁ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = f otimes≫ (Xᘁ ◁ η_ X Xᘁ otimes≫ ε_ X Xᘁ ▷ Xᘁ) := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [coevaluation_evaluation'']; monoidal

Depends on / 依赖: coevaluation_evaluation, monoidal, otimes, tensorRightHomEquiv, whisker_exchange
-/
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ) :
    (tensorRightHomEquiv _ _ _ _) (f ▷ X ≫ ε_ X (Xᘁ)) = f ≫ (fun_ _).inv :=
  calc
    _ = 𝟙 _ otimes≫ (Y ◁ η_ X Xᘁ ≫ f ▷ (X otimes Xᘁ)) otimes≫ ε_ X Xᘁ ▷ Xᘁ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = f otimes≫ (Xᘁ ◁ η_ X Xᘁ otimes≫ ε_ X Xᘁ ▷ Xᘁ) := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [coevaluation_evaluation'']; monoidal

-- Next four lemmas passing `fᘁ` or `ᘁf` through (co)evaluations.
@[reassoc]
/--
theorem `coevaluation_comp_rightAdjointMate` / 定理 `coevaluation_comp_rightAdjointMate`

English:
theorem coevaluation_comp_rightAdjointMate
  given: {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y)
  proof: by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp

@[reassoc]

中文:
定理 coevaluation_comp_rightAdjointMate
  条件: {X Y : C} [有RightDual X] [有RightDual Y] (f : X ⟶ Y)
  证明: by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp

@[reassoc]

Depends on / 依赖: apply_fun, tensorLeftHomEquiv
-/
theorem coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ _ ◁ (fᘁ) = η_ _ _ ≫ f ▷ _ := by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp

@[reassoc]
/--
theorem `leftAdjointMate_comp_evaluation` / 定理 `leftAdjointMate_comp_evaluation`

English:
theorem leftAdjointMate_comp_evaluation
  given: {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y)
  proof: by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp

@[reassoc]

中文:
定理 leftAdjointMate_comp_evaluation
  条件: {X Y : C} [有LeftDual X] [有LeftDual Y] (f : X ⟶ Y)
  证明: by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp

@[reassoc]

Depends on / 依赖: apply_fun, tensorLeftHomEquiv
-/
theorem leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    X ◁ (ᘁf) ≫ ε_ _ _ = f ▷ _ ≫ ε_ _ _ := by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp

@[reassoc]
/--
theorem `coevaluation_comp_leftAdjointMate` / 定理 `coevaluation_comp_leftAdjointMate`

English:
theorem coevaluation_comp_leftAdjointMate
  given: {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y)
  proof: by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp

@[reassoc]

中文:
定理 coevaluation_comp_leftAdjointMate
  条件: {X Y : C} [有LeftDual X] [有LeftDual Y] (f : X ⟶ Y)
  证明: by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp

@[reassoc]

Depends on / 依赖: apply_fun, tensorRightHomEquiv
-/
theorem coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ (ᘁf) ▷ Y = η_ (ᘁX) X ≫ (ᘁX) ◁ f := by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp

@[reassoc]
/--
theorem `rightAdjointMate_comp_evaluation` / 定理 `rightAdjointMate_comp_evaluation`

English:
theorem rightAdjointMate_comp_evaluation
  given: {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y)
  proof: by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp

中文:
定理 rightAdjointMate_comp_evaluation
  条件: {X Y : C} [有RightDual X] [有RightDual Y] (f : X ⟶ Y)
  证明: by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp

Depends on / 依赖: apply_fun, tensorRightHomEquiv
-/
theorem rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ▷ X) ≫ ε_ X (Xᘁ) = ((Yᘁ) ◁ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp

/-- Transport an exact pairing across an isomorphism in the first argument. -/
@[instance_reducible]
/--
Definition of `exactPairingCongrLeft` / `exactPairingCongrLeft` 的定义

English:
definition exactPairingCongrLeft
  signature: {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X')
  body: Y ◁ i.hom ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ i.inv ▷ Y
  evaluation_coevaluation' :=
    calc
      _ = η_ X' Y ▷ X otimes≫ (i.inv ▷ (Y otimes X) ≫ X ◁ (Y ◁ i.hom)) otimes≫ X ◁ ε_ X' Y := by
        monoidal
      _ = 𝟙 _ otimes≫ (η_ X' Y ▷ X ≫ (X' otimes Y) ◁ i.hom) otimes≫
          (i.inv ▷ (Y 

中文:
定义 exactPairingCongrLeft
  签名: {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X')
  定义体: Y ◁ i.hom ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ i.inv ▷ Y
  evaluation_coevaluation' :=
    calc
      _ = η_ X' Y ▷ X otimes≫ (i.inv ▷ (Y otimes X) ≫ X ◁ (Y ◁ i.hom)) otimes≫ X ◁ ε_ X' Y := by
        monoidal
      _ = 𝟙 _ otimes≫ (η_ X' Y ▷ X ≫ (X' otimes Y) ◁ i.hom) otimes≫
          (i.inv ▷ (Y 

Depends on / 依赖: i.hom
-/
def exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : ExactPairing X Y where
  evaluation' := Y ◁ i.hom ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ i.inv ▷ Y
  evaluation_coevaluation' :=
    calc
      _ = η_ X' Y ▷ X otimes≫ (i.inv ▷ (Y otimes X) ≫ X ◁ (Y ◁ i.hom)) otimes≫ X ◁ ε_ X' Y := by
        monoidal
      _ = 𝟙 _ otimes≫ (η_ X' Y ▷ X ≫ (X' otimes Y) ◁ i.hom) otimes≫
          (i.inv ▷ (Y otimes X') ≫ X ◁ ε_ X' Y) otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = 𝟙 _ otimes≫ i.hom otimes≫ (η_ X' Y ▷ X' otimes≫ X' ◁ ε_ X' Y) otimes≫ i.inv otimes≫ 𝟙 _ := by
        rw [← whisker_exchange]; rw [← whisker_exchange]; monoidal
      _ = 𝟙 _ otimes≫ (i.hom ≫ i.inv) otimes≫ 𝟙 _ := by
        rw [evaluation_coevaluation'']; monoidal
      _ = (fun_ X).hom ≫ (ρ_ X).inv := by
        rw [Iso.hom_inv_id]
        monoidal
  coevaluation_evaluation' := by
    calc
      _ = Y ◁ η_ X' Y ≫ Y ◁ (i.inv ≫ i.hom) ▷ Y otimes≫ ε_ X' Y ▷ Y := by
        monoidal
      _ = Y ◁ η_ X' Y otimes≫ ε_ X' Y ▷ Y := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
        rw [coevaluation_evaluation'']
        simp

/-- Transport an exact pairing across an isomorphism in the second argument. -/
@[instance_reducible]
/--
Definition of `exactPairingCongrRight` / `exactPairingCongrRight` 的定义

English:
definition exactPairingCongrRight
  signature: {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y')
  body: i.hom ▷ X ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ X ◁ i.inv
  evaluation_coevaluation' := by
    calc
      _ = η_ X Y' ▷ X otimes≫ X ◁ (i.inv ≫ i.hom) ▷ X ≫ X ◁ ε_ X Y' := by
        monoidal
      _ = η_ X Y' ▷ X otimes≫ X ◁ ε_ X Y' := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
      

中文:
定义 exactPairingCongrRight
  签名: {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y')
  定义体: i.hom ▷ X ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ X ◁ i.inv
  evaluation_coevaluation' := by
    calc
      _ = η_ X Y' ▷ X otimes≫ X ◁ (i.inv ≫ i.hom) ▷ X ≫ X ◁ ε_ X Y' := by
        monoidal
      _ = η_ X Y' ▷ X otimes≫ X ◁ ε_ X Y' := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
      

Depends on / 依赖: i.hom
-/
def exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : ExactPairing X Y where
  evaluation' := i.hom ▷ X ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ X ◁ i.inv
  evaluation_coevaluation' := by
    calc
      _ = η_ X Y' ▷ X otimes≫ X ◁ (i.inv ≫ i.hom) ▷ X ≫ X ◁ ε_ X Y' := by
        monoidal
      _ = η_ X Y' ▷ X otimes≫ X ◁ ε_ X Y' := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
        rw [evaluation_coevaluation'']
        simp
  coevaluation_evaluation' :=
    calc
      _ = Y ◁ η_ X Y' otimes≫ (Y ◁ (X ◁ i.inv) ≫ i.hom ▷ (X otimes Y)) otimes≫ ε_ X Y' ▷ Y := by
        monoidal
      _ = 𝟙 _ otimes≫ (Y ◁ η_ X Y' ≫ i.hom ▷ (X otimes Y')) otimes≫
          ((Y' otimes X) ◁ i.inv ≫ ε_ X Y' ▷ Y) otimes≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = 𝟙 _ otimes≫ i.hom otimes≫ (Y' ◁ η_ X Y' otimes≫ ε_ X Y' ▷ Y') otimes≫ i.inv otimes≫ 𝟙 _ := by
        rw [whisker_exchange]; rw [whisker_exchange]; monoidal
      _ = 𝟙 _ otimes≫ (i.hom ≫ i.inv) otimes≫ 𝟙 _ := by
        rw [coevaluation_evaluation'']; monoidal
      _ = (ρ_ Y).hom ≫ (fun_ Y).inv := by
        rw [Iso.hom_inv_id]
        monoidal

/-- Transport an exact pairing across isomorphisms. -/
@[instance_reducible]
/--
Definition of `exactPairingCongr` / `exactPairingCongr` 的定义

English:
definition exactPairingCongr
  signature: {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y')
  body: haveI : ExactPairing X' Y := exactPairingCongrRight j
  exactPairingCongrLeft i

中文:
定义 exactPairingCongr
  签名: {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y')
  定义体: haveI : ExactPairing X' Y := exactPairingCongrRight j
  exactPairingCongrLeft i

Depends on / 依赖: ExactPairing, exactPairingCongrLeft, exactPairingCongrRight
-/
def exactPairingCongr {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y') :
    ExactPairing X Y :=
  haveI : ExactPairing X' Y := exactPairingCongrRight j
  exactPairingCongrLeft i

/--
Definition of `rightDualIso` / `rightDualIso` 的定义

English:
definition rightDualIso
  signature: {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂)
  body: @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_rightAdjointMate]; rw [Category.comp_id]; rw [@rightAdjointMate_id]
    r

中文:
定义 rightDualIso
  签名: {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂)
  定义体: @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_rightAdjointMate]; rw [Category.comp_id]; rw [@rightAdjointMate_id]
    r

Depends on / 依赖: rightAdjointMate
-/
def rightDualIso {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) : Y₁ ≅ Y₂ where
  hom := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_rightAdjointMate]; rw [Category.comp_id]; rw [@rightAdjointMate_id]
    rfl
  inv_hom_id := by
    rw [← @comp_rightAdjointMate]; rw [Category.comp_id]; rw [@rightAdjointMate_id]
    rfl

/--
Definition of `leftDualIso` / `leftDualIso` 的定义

English:
definition leftDualIso
  signature: {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y)
  body: @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_leftAdjointMate C]; rw [Category.comp_id]; rw [@leftAdjointMate_id]
    rfl

中文:
定义 leftDualIso
  签名: {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y)
  定义体: @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_leftAdjointMate C]; rw [Category.comp_id]; rw [@leftAdjointMate_id]
    rfl

Depends on / 依赖: leftAdjointMate
-/
def leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ where
  hom := @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_leftAdjointMate C]; rw [Category.comp_id]; rw [@leftAdjointMate_id]
    rfl
  inv_hom_id := by
    rw [← @comp_leftAdjointMate C]; rw [Category.comp_id]; rw [@leftAdjointMate_id]
    rfl

@[simp]
/--
theorem `rightDualIso_id` / 定理 `rightDualIso_id`

English:
theorem rightDualIso_id
  given: {X Y : C} (p : ExactPairing X Y)
  statement: rightDualIso p p = Iso.refl Y
  proof: by
  ext
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id]

@[simp]

中文:
定理 rightDualIso_id
  条件: {X Y : C} (p : ExactPairing X Y)
  结论: rightDualIso p p = 同构.refl Y
  证明: by
  ext
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id]

@[simp]

Depends on / 依赖: Iso.refl_hom, refl_hom, rightAdjointMate_id, rightDualIso
-/
theorem rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by
  ext
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id]

@[simp]
/--
theorem `leftDualIso_id` / 定理 `leftDualIso_id`

English:
theorem leftDualIso_id
  given: {X Y : C} (p : ExactPairing X Y)
  statement: leftDualIso p p = Iso.refl X
  proof: by
  ext
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id]

中文:
定理 leftDualIso_id
  条件: {X Y : C} (p : ExactPairing X Y)
  结论: leftDualIso p p = 同构.refl X
  证明: by
  ext
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id]

Depends on / 依赖: Iso.refl_hom, leftAdjointMate_id, leftDualIso, refl_hom
-/
theorem leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by
  ext
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id]

/--
Definition of `rightDualTensorIso` / `rightDualTensorIso` 的定义

English:
definition rightDualTensorIso
  signature: (X Y : C) [HasRightDual X] [HasRightDual Y]
  body: rightDualIso HasRightDual.exact ExactPairing.tensor

中文:
定义 rightDualTensorIso
  签名: (X Y : C) [有RightDual X] [有RightDual Y]
  定义体: rightDualIso HasRightDual.exact ExactPairing.tensor

Depends on / 依赖: ExactPairing, ExactPairing.tensor, HasRightDual, HasRightDual.exact, rightDualIso, tensor
-/
def rightDualTensorIso (X Y : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual (X otimes Y)] :
    (X otimes Y)ᘁ ≅ Yᘁ otimes Xᘁ :=
  rightDualIso HasRightDual.exact ExactPairing.tensor

/--
Definition of `leftDualTensorIso` / `leftDualTensorIso` 的定义

English:
definition leftDualTensorIso
  signature: (X Y : C) [HasLeftDual X] [HasLeftDual Y]
  body: leftDualIso HasLeftDual.exact ExactPairing.tensor

中文:
定义 leftDualTensorIso
  签名: (X Y : C) [有LeftDual X] [有LeftDual Y]
  定义体: leftDualIso HasLeftDual.exact ExactPairing.tensor

Depends on / 依赖: ExactPairing, ExactPairing.tensor, HasLeftDual, HasLeftDual.exact, leftDualIso, tensor
-/
def leftDualTensorIso (X Y : C) [HasLeftDual X] [HasLeftDual Y]
    [HasLeftDual (X otimes Y)] :
    leftDual (X otimes Y) ≅ leftDual Y otimes leftDual X :=
  leftDualIso HasLeftDual.exact ExactPairing.tensor

/--
Definition of `RightRigidCategory` / `RightRigidCategory` 的定义

English:
class RightRigidCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  axioms and operations (1):
    - [rightDual : forall X : C, HasRightDual X]

中文:
类 RightRigid范畴
  参数: (C : 类型u) [范畴.{v} C] [幺半群范畴.{v} C]
  公理与运算 (1 个):
    - [rightDual : 对任意 X : C, 有RightDual X]
-/
class RightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [rightDual : forall X : C, HasRightDual X]

/--
Definition of `LeftRigidCategory` / `LeftRigidCategory` 的定义

English:
class LeftRigidCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  axioms and operations (1):
    - [leftDual : forall X : C, HasLeftDual X]

中文:
类 LeftRigid范畴
  参数: (C : 类型u) [范畴.{v} C] [幺半群范畴.{v} C]
  公理与运算 (1 个):
    - [leftDual : 对任意 X : C, 有LeftDual X]
-/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : forall X : C, HasLeftDual X]

attribute [instance_reducible, instance 100] RightRigidCategory.rightDual
attribute [instance_reducible, instance 100] LeftRigidCategory.leftDual

/-- Any left rigid category is monoidal closed, with the internal hom `X ⟶[C] Y = ᘁX ⊗ Y`.
This has to be a definition rather than an instance to avoid diamonds, for example between
`category_theory.monoidal_closed.functor_category` and
`CategoryTheory.Monoidal.leftRigidFunctorCategory`. Moreover, in concrete applications there is
often a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case the monoidal
closed structure shouldn't come the rigid structure (e.g. in the category `FinVect k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even though these are
naturally isomorphic). -/
@[instance_reducible]
/--
Definition of `monoidalClosedOfLeftRigidCategory` / `monoidalClosedOfLeftRigidCategory` 的定义

English:
definition monoidalClosedOfLeftRigidCategory
  signature: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  body: closedOfHasLeftDual X

中文:
定义 monoidalClosedOfLeftRigidCategory
  签名: (C : 类型u) [范畴.{v} C] [幺半群范畴.{v} C]
  定义体: closedOfHasLeftDual X

Depends on / 依赖: closedOfHasLeftDual
-/
def monoidalClosedOfLeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [LeftRigidCategory C] : MonoidalClosed C where
  closed X := closedOfHasLeftDual X

/--
Definition of `RigidCategory` / `RigidCategory` 的定义

English:
class RigidCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  (no additional axioms)

中文:
类 Rigid范畴
  参数: (C : 类型u) [范畴.{v} C] [幺半群范畴.{v} C]
  (无附加公理)
-/
class RigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    RightRigidCategory C, LeftRigidCategory C

end CategoryTheory
