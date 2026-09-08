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

/-- An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities. -/
/-
**CategoryTheory.ExactPairing** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：ExactPairing (X Y : C) where /-- Coevaluation of an exact pairing.  Do not
 use directly. Use `ExactPairing.coevaluation` instead. -/ coevaluation' : 𝟙_ C 
⟶ X otimes Y /-- Evaluation of an exact pairing.  Do not use directly. Use `Exac
tPairing.evaluation` instead. -/ evaluation' : Y otimes X ⟶ 𝟙_ C coevaluation_ev
aluation' : Y ◁ coevaluation' ≫ (α_ _ _ _).inv ≫ evaluation' ▷ Y = (ρ_ Y).hom ≫ 
(fun_ Y).inv
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An exact pairing is a pair of objects `X Y : C` which admit
  a coevaluation and evaluation morphism which fulfill two triangle equalities.
-/
class ExactPairing (X Y : C) where
  /-- Coevaluation of an exact pairing.

  Do not use directly. Use `ExactPairing.coevaluation` instead. -/
  coevaluation' : 𝟙_ C ⟶ X ⊗ Y
  /-- Evaluation of an exact pairing.

  Do not use directly. Use `ExactPairing.evaluation` instead. -/
  evaluation' : Y ⊗ X ⟶ 𝟙_ C
  coevaluation_evaluation' :
    Y ◁ coevaluation' ≫ (α_ _ _ _).inv ≫ evaluation' ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv := by
    cat_disch
  evaluation_coevaluation' :
    coevaluation' ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ evaluation' = (λ_ X).hom ≫ (ρ_ X).inv := by
    cat_disch

namespace ExactPairing

-- Porting note: as there is no mechanism equivalent to `[]` in Lean 3 to make
-- arguments for class fields explicit,
-- we now repeat all the fields without primes.
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Making.20variable.20in.20class.20field.20explicit
variable (X Y : C)
variable [ExactPairing X Y]

/-- Coevaluation of an exact pairing. -/
/-
**CategoryTheory.ExactPairing.coevaluation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ExactPairing`。
形式化陈述：coevaluation : 𝟙_ C ⟶ X otimes Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coevaluation of an exact pairing.
-/
def coevaluation : 𝟙_ C ⟶ X ⊗ Y := @coevaluation' _ _ _ X Y _

/-- Evaluation of an exact pairing. -/
/-
**CategoryTheory.ExactPairing.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ExactPairing`。
形式化陈述：evaluation : Y otimes X ⟶ 𝟙_ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of an exact pairing.
-/
def evaluation : Y ⊗ X ⟶ 𝟙_ C := @evaluation' _ _ _ X Y _

@[inherit_doc] notation "η_" => ExactPairing.coevaluation
@[inherit_doc] notation "ε_" => ExactPairing.evaluation
/-
**CategoryTheory.ExactPairing.coevaluation_evaluation** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ExactPairing`。
形式化陈述：coevaluation_evaluation : Y ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ ε_ X _ ▷ Y = (ρ_ Y
).hom ≫ (fun_ Y).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ExactPairing.coevaluation_evaluation'`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C} {X Y : C}   [self : CategoryTheory.…
-/
lemma coevaluation_evaluation :
    Y ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ ε_ X _ ▷ Y = (ρ_ Y).hom ≫ (λ_ Y).inv :=
  coevaluation_evaluation'
/-
**CategoryTheory.ExactPairing.evaluation_coevaluation** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ExactPairing`。
形式化陈述：evaluation_coevaluation : η_ _ _ ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε_ _ Y = (fun_
 X).hom ≫ (ρ_ X).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ExactPairing.evaluation_coevaluation'`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C} {X Y : C}   [self : CategoryTheory.…
-/
lemma evaluation_coevaluation :
    η_ _ _ ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε_ _ Y = (λ_ X).hom ≫ (ρ_ X).inv :=
  evaluation_coevaluation'
/-
**CategoryTheory.ExactPairing.coevaluation_evaluation''** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ExactPairing`。
形式化陈述：coevaluation_evaluation'' : Y ◁ η_ X Y otimes≫ ε_ X Y ▷ Y = otimes𝟙.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerRightIso_refl`：whiskerRightIso_re
fl (X W : C) : whiskerRightIso (Iso.refl X) W = Iso.refl (X otimes W)
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ExactPairing.coevaluation_evaluation`：coevaluation_evalua
tion : Y ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ ε_ X _ ▷ Y = (ρ_ Y).hom ≫ (fun_ Y).inv
-/
lemma coevaluation_evaluation'' :
    Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y = ⊗𝟙.hom := by
  convert! coevaluation_evaluation X Y <;> simp [monoidalComp]
/-
**CategoryTheory.ExactPairing.evaluation_coevaluation''** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ExactPairing`。
形式化陈述：evaluation_coevaluation'' : η_ X Y ▷ X otimes≫ X ◁ ε_ X Y = otimes𝟙.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoidalCategory.whiskerRightIso_refl`：whiskerRightIso_re
fl (X W : C) : whiskerRightIso (Iso.refl X) W = Iso.refl (X otimes W)
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用引理 `CategoryTheory.ExactPairing.evaluation_coevaluation`：evaluation_coevalua
tion : η_ _ _ ▷ X ≫ (α_ _ _ _).hom ≫ X ◁ ε_ _ Y = (fun_ X).hom ≫ (ρ_ X).inv
-/
lemma evaluation_coevaluation'' :
    η_ X Y ▷ X ⊗≫ X ◁ ε_ X Y = ⊗𝟙.hom := by
  convert! evaluation_coevaluation X Y <;> simp [monoidalComp]

end ExactPairing

attribute [reassoc (attr := simp)] ExactPairing.coevaluation_evaluation
attribute [reassoc (attr := simp)] ExactPairing.evaluation_coevaluation

/-
**CategoryTheory.exactPairingUnit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where coevaluation'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance exactPairingUnit : ExactPairing (𝟙_ C) (𝟙_ C) where
  coevaluation' := (ρ_ _).inv
  evaluation' := (ρ_ _).hom
  coevaluation_evaluation' := by monoidal_coherence
  evaluation_coevaluation' := by monoidal_coherence

/-- The tensor product of exact pairings. Given exact pairings `(X₁, Y₁)` and `(X₂, Y₂)`,
we get an exact pairing `(X₁ ⊗ X₂, Y₂ ⊗ Y₁)`. Note the reversed order in the second factor. -/
/-
**CategoryTheory.ExactPairing.tensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.E
xactPairing`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {X₁ X₂ Y₁ Y₂ : C} →         [Cate
goryTheory.ExactPairing X₁ Y₁] →           [CategoryTheory.ExactPairing X₂ Y₂] →
             CategoryTheory.ExactPairing (CategoryTheory.MonoidalCategoryStruct.
tensorObj X₁ X₂)               (CategoryTheory.MonoidalCategoryStruct.tensorObj 
Y₂ Y₁)
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ X₂；CategoryTheory.Monoidal
CategoryStruct.tensorObj Y₂ Y₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of exact pairings. Given exact pairings `(X₁, Y₁)` and `(X₂, 
Y₂)`,
we get an exact pairing `(X₁ ⊗ X₂, Y₂ ⊗ Y₁)`. Note the reversed order in the sec
ond factor.
-/
instance ExactPairing.tensor {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    ExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) where
  coevaluation' := η_ X₁ Y₁ ⊗≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫ 𝟙 _
  evaluation' := 𝟙 _ ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ ε_ X₂ Y₂
  coevaluation_evaluation' := by
    calc
      _ = (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ⊗≫
          (Y₂ ⊗ Y₁) ◁ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫
          (Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂)) ▷ (Y₂ ⊗ Y₁) ⊗≫
          ε_ X₂ Y₂ ▷ (Y₂ ⊗ Y₁) := by monoidal
      -- Group η₂ and ε₁ so they compose with ≫ (both act on the Y₁ ⊗ X₁ factor):
      --
      --   Y₂  Y₁      ╭── X₁ ────────────╮
      --   │    │      │    ╭── X₂ ───╮   │
      --   │    │      │    │         │   │
      --   │    ╰──ε₁──╯    │         │   │
      --   │                │         │   │
      --   ╰────── ε₂ ──────╯         │   │
      --                              Y₂  Y₁
      --
      _ = (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ⊗≫
          Y₂ ◁ ((Y₁ ⊗ X₁) ◁ η_ X₂ Y₂ ≫ ε_ X₁ Y₁ ▷ (X₂ ⊗ Y₂)) ▷ Y₁ ⊗≫
          ε_ X₂ Y₂ ▷ (Y₂ ⊗ Y₁) := by monoidal
      -- Slide the η₂ cup past the ε₁ cap (whisker_exchange), separating the
      -- two zigzags into independent snakes:
      --
      --   Y₂   Y₁
      --   │    │   ╭─X₁──╮
      --   │    │   │     │
      --   │    ╰───╯     │       ← snake for (X₁, Y₁)
      --   │              │
      --   │  ╭─X₂──╮     │
      --   │  │     │     │
      --   ╰──╯     │     │       ← snake for (X₂, Y₂)
      --            Y₂    Y₁
      --
      _ = (Y₂ ⊗ Y₁) ◁ η_ X₁ Y₁ ⊗≫
          Y₂ ◁ (ε_ X₁ Y₁ ▷ (𝟙_ C) ≫ (𝟙_ C) ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫
          ε_ X₂ Y₂ ▷ (Y₂ ⊗ Y₁) := by
        rw [whisker_exchange]
      -- Separate into two snakes and cancel each.
      _ = 𝟙 _ ⊗≫ Y₂ ◁ (Y₁ ◁ η_ X₁ Y₁ ⊗≫ ε_ X₁ Y₁ ▷ Y₁) ⊗≫
          (Y₂ ◁ η_ X₂ Y₂ ⊗≫ ε_ X₂ Y₂ ▷ Y₂) ▷ Y₁ ⊗≫ 𝟙 _ := by monoidal
      _ = _ := by rw [coevaluation_evaluation'', coevaluation_evaluation'']; monoidal
  evaluation_coevaluation' := by
    calc
      _ = η_ X₁ Y₁ ▷ (X₁ ⊗ X₂) ⊗≫
          (X₁ ◁ η_ X₂ Y₂) ▷ (Y₁ ⊗ X₁ ⊗ X₂) ⊗≫
          (X₁ ⊗ X₂) ◁ (Y₂ ◁ ε_ X₁ Y₁ ▷ X₂) ⊗≫
          (X₁ ⊗ X₂) ◁ ε_ X₂ Y₂ := by monoidal
      -- Group η₂ and ε₁ so they compose with ≫:
      --
      --   ╭── Y₁ ────────────╮       X₁   X₂
      --   │    ╭── Y₂ ───╮   │       │    │
      --   │    │         │   │       │    │
      --   │    │         │   ╰──ε₁───╯    │
      --   │    │         │                │
      --   │    │         ╰──────── ε₂ ────╯
      --   X₁   X₂
      --
      _ = η_ X₁ Y₁ ▷ (X₁ ⊗ X₂) ⊗≫
          X₁ ◁ (η_ X₂ Y₂ ▷ (Y₁ ⊗ X₁) ≫ (X₂ ⊗ Y₂) ◁ ε_ X₁ Y₁) ▷ X₂ ⊗≫
          (X₁ ⊗ X₂) ◁ ε_ X₂ Y₂ := by monoidal
      -- Slide the ε₁ cap past the η₂ cup (← whisker_exchange), separating the
      -- two zigzags into independent snakes:
      --
      --                 X₁   X₂
      --   ╭──Y₁──╮      │    │
      --   │      │      │    │
      --   │      ╰──────╯    │       ← snake for (X₁, Y₁)
      --   │                  │
      --   │   ╭──Y₂──╮       │
      --   │   │      │       │
      --   │   │      ╰───────╯       ← snake for (X₂, Y₂)
      --   X₁  X₂
      --
      _ = η_ X₁ Y₁ ▷ (X₁ ⊗ X₂) ⊗≫
          X₁ ◁ ((𝟙_ C) ◁ ε_ X₁ Y₁ ≫ η_ X₂ Y₂ ▷ (𝟙_ C)) ▷ X₂ ⊗≫
          (X₁ ⊗ X₂) ◁ ε_ X₂ Y₂ := by
        rw [← whisker_exchange]
      -- Separate into two snakes and cancel each.
      _ = 𝟙 _ ⊗≫ (η_ X₁ Y₁ ▷ X₁ ⊗≫ X₁ ◁ ε_ X₁ Y₁) ▷ X₂ ⊗≫
          X₁ ◁ (η_ X₂ Y₂ ▷ X₂ ⊗≫ X₂ ◁ ε_ X₂ Y₂) ⊗≫ 𝟙 _ := by monoidal
      _ = _ := by rw [evaluation_coevaluation'', evaluation_coevaluation'']; monoidal
/-
**CategoryTheory.ExactPairing.tensor_coevaluation** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ExactPairing`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X₁ X₂ Y₁ Y₂ : C} [inst_2 : CategoryTheory.Exac
tPairing X₁ Y₁] [inst_3 : CategoryTheory.ExactPairing X₂ Y₂],   η_ (CategoryTheo
ry.MonoidalCategoryStruct.tensorObj X₁ X₂) (CategoryTheory.MonoidalCategoryStruc
t.tensorObj Y₂ Y₁) =     CategoryTheory.monoidalComp (η_ X₁ Y₁)       (CategoryT
heory.monoidalComp         (CategoryTheory.MonoidalCategoryStruct.whiskerRight  
         (CategoryTheory.MonoidalCategoryStruct.whiskerLeft X₁ (η_ X₂ Y₂)) Y₁)  
       (CategoryTheory.CategoryStruct.id           (CategoryTheory.MonoidalCateg
oryStruct.tensorObj (CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ X₂)     
        (CategoryTheory.MonoidalCategoryStruct.tensorObj Y₂ Y₁))))
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ X₂；CategoryTheory.Monoidal
CategoryStruct.tensorObj Y₂ Y₁；η_ X₁ Y₁；CategoryTheory.monoidalComp         (Cat
egoryTheory.MonoidalCategoryStruct.whiskerRight           (CategoryTheory.Monoid
alCategoryStruct.whiskerLeft X₁ (η_ X₂ Y₂)) Y₁)         (CategoryTheory.Category
Struct.id           (CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTh
eory.MonoidalCategoryStruct.tensorObj X₁ X₂)             (CategoryTheory.Monoida
lCategoryStruct.tensorObj Y₂ Y₁)))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ExactPairing.tensor_coevaluation {X₁ X₂ Y₁ Y₂ : C}
    [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    η_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = η_ X₁ Y₁ ⊗≫ (X₁ ◁ η_ X₂ Y₂) ▷ Y₁ ⊗≫ 𝟙 _ :=
  rfl
/-
**CategoryTheory.ExactPairing.tensor_evaluation** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.ExactPairing`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X₁ X₂ Y₁ Y₂ : C} [inst_2 : CategoryTheory.Exac
tPairing X₁ Y₁] [inst_3 : CategoryTheory.ExactPairing X₂ Y₂],   ε_ (CategoryTheo
ry.MonoidalCategoryStruct.tensorObj X₁ X₂) (CategoryTheory.MonoidalCategoryStruc
t.tensorObj Y₂ Y₁) =     CategoryTheory.monoidalComp       (CategoryTheory.Categ
oryStruct.id         (CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryT
heory.MonoidalCategoryStruct.tensorObj Y₂ Y₁)           (CategoryTheory.Monoidal
CategoryStruct.tensorObj X₁ X₂)))       (CategoryTheory.monoidalComp         (Ca
tegoryTheory.MonoidalCategoryStruct.whiskerLeft Y₂           (CategoryTheory.Mon
oidalCategoryStruct.whiskerRight (ε_ X₁ Y₁) X₂))         (ε_ X₂ Y₂))
参数：CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ X₂；CategoryTheory.Monoidal
CategoryStruct.tensorObj Y₂ Y₁；CategoryTheory.CategoryStruct.id         (Categor
yTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.MonoidalCategoryStruct.
tensorObj Y₂ Y₁)           (CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ X
₂))；CategoryTheory.monoidalComp         (CategoryTheory.MonoidalCategoryStruct.w
hiskerLeft Y₂           (CategoryTheory.MonoidalCategoryStruct.whiskerRight (ε_ 
X₁ Y₁) X₂))         (ε_ X₂ Y₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ExactPairing.tensor_evaluation {X₁ X₂ Y₁ Y₂ : C}
    [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = 𝟙 _ ⊗≫ Y₂ ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ ε_ X₂ Y₂ :=
  rfl

/-- A class of objects which have a right dual. -/
/-
**CategoryTheory.HasRightDual** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryThe
ory.MonoidalCategory C] → C → Type (max u₁ v₁)
参数：max u₁ v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of objects which have a right dual.
-/
class HasRightDual (X : C) where
  /-- The right dual of the object `X`. -/
  rightDual : C
  [exact : ExactPairing X rightDual]

/-- A class of objects which have a left dual. -/
/-
**CategoryTheory.HasLeftDual** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryThe
ory.MonoidalCategory C] → C → Type (max u₁ v₁)
参数：max u₁ v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of objects which have a left dual.
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
/-
**CategoryTheory.hasRightDualUnit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：hasRightDualUnit : HasRightDual (𝟙_ C) where rightDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
https://github.com/leanprover/lean4/pull/4596
The overlapping notation for `leftDual` and `leftAdjointMate` become more proble
matic in
after https://github.com/leanprover/lean4/pull/4596, and we sometimes have to di
sambiguate with
e.g. `(ᘁX : C)` where previously just `ᘁX` was enough.
-/
instance hasRightDualUnit : HasRightDual (𝟙_ C) where
  rightDual := 𝟙_ C
/-
**CategoryTheory.hasLeftDualUnit** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：hasLeftDualUnit : HasLeftDual (𝟙_ C) where leftDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLeftDualUnit : HasLeftDual (𝟙_ C) where
  leftDual := 𝟙_ C
/-
**CategoryTheory.hasRightDualLeftDual** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`
。
形式化陈述：hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where right
Dual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasRightDualLeftDual {X : C} [HasLeftDual X] : HasRightDual ᘁX where
  rightDual := X
/-
**CategoryTheory.hasLeftDualRightDual** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`
。
形式化陈述：hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where leftD
ual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLeftDualRightDual {X : C} [HasRightDual X] : HasLeftDual Xᘁ where
  leftDual := X

/-- The tensor product of two objects with right duals has a right dual,
given by the tensor product of the duals in the opposite order. -/
@[implicit_reducible]
/-
**CategoryTheory.hasRightDualTensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：hasRightDualTensor {X Y : C} [HasRightDual X] [HasRightDual Y] : HasRightD
ual (X otimes Y) where rightDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two objects with right duals has a right dual,
given by the tensor product of the duals in the opposite order.
-/
def hasRightDualTensor {X Y : C} [HasRightDual X] [HasRightDual Y] :
    HasRightDual (X ⊗ Y) where
  rightDual := Yᘁ ⊗ Xᘁ

/-- The tensor product of two objects with left duals has a left dual,
given by the tensor product of the duals in the opposite order. -/
@[implicit_reducible]
/-
**CategoryTheory.hasLeftDualTensor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：hasLeftDualTensor {X Y : C} [HasLeftDual X] [HasLeftDual Y] : HasLeftDual 
(X otimes Y) where leftDual
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two objects with left duals has a left dual,
given by the tensor product of the duals in the opposite order.
-/
def hasLeftDualTensor {X Y : C} [HasLeftDual X] [HasLeftDual Y] :
    HasLeftDual (X ⊗ Y) where
  leftDual := ᘁY ⊗ ᘁX

@[simp]
/-
**CategoryTheory.leftDual_rightDual** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：leftDual_rightDual {X : C} [HasRightDual X] : ᘁXᘁ = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDual_rightDual {X : C} [HasRightDual X] : ᘁXᘁ = X :=
  rfl

@[simp]
/-
**CategoryTheory.rightDual_leftDual** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：rightDual_leftDual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDual_leftDual {X : C} [HasLeftDual X] : (ᘁX)ᘁ = X :=
  rfl

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
/-
**CategoryTheory.rightAdjointMate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
 Yᘁ ⟶ Xᘁ
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`.
-/
def rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) : Yᘁ ⟶ Xᘁ :=
  (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ _ ◁ f ▷ _ ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (λ_ _).hom

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
/-
**CategoryTheory.leftAdjointMate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY
 ⟶ ᘁX
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`.
-/
def leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) : ᘁY ⟶ ᘁX :=
  (λ_ _).inv ≫ η_ (ᘁX) X ▷ _ ≫ (_ ◁ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f
@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

@[simp]
/-
**CategoryTheory.rightAdjointMate_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：rightAdjointMate_id {X : C} [HasRightDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ExactPairing.coevaluation_evaluation_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoidal
Category C] (X Y : C)   [inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightAdjointMate_id {X : C} [HasRightDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ) := by
  simp [rightAdjointMate]

@[simp]
/-
**CategoryTheory.leftAdjointMate_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.ExactPairing.evaluation_coevaluation_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoidal
Category C] (X Y : C)   [inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftAdjointMate_id {X : C} [HasLeftDual X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX) := by
  simp [leftAdjointMate]
/-
**CategoryTheory.rightAdjointMate_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X
 ⟶ Y} {g : Xᘁ ⟶ Z} : fᘁ ≫ g = (ρ_ (Yᘁ)).inv ≫ _ ◁ η_ X (Xᘁ) ≫ _ ◁ (f otimesₘ g) 
≫ (α_ (Yᘁ) Y Z).inv ≫ ε_ Y (Yᘁ) ▷ _ ≫ (fun_ Z).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_id`：evalWhiskerLeft_id {f g : C}
 {η : f ⟶ g} {η₁ : f ⟶ 𝟙_ C otimes g} {η₂ : 𝟙_ C otimes f ⟶ 𝟙_ C otimes g} (e_η₁
 : η ≫ (fun_ _).inv = η₁) (e_η₂ …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
-/
theorem rightAdjointMate_comp {X Y Z : C} [HasRightDual X] [HasRightDual Y] {f : X ⟶ Y}
    {g : Xᘁ ⟶ Z} :
    fᘁ ≫ g =
      (ρ_ (Yᘁ)).inv ≫
        _ ◁ η_ X (Xᘁ) ≫ _ ◁ (f ⊗ₘ g) ≫ (α_ (Yᘁ) Y Z).inv ≫ ε_ Y (Yᘁ) ▷ _ ≫ (λ_ Z).hom :=
  calc
    _ = 𝟙 _ ⊗≫ (Yᘁ : C) ◁ η_ X Xᘁ ≫ Yᘁ ◁ f ▷ Xᘁ ⊗≫ (ε_ Y Yᘁ ▷ Xᘁ ≫ 𝟙_ C ◁ g) ⊗≫ 𝟙 _ := by
      dsimp only [rightAdjointMate]; monoidal
    _ = _ := by
      rw [← whisker_exchange, tensorHom_def]; monoidal
/-
**CategoryTheory.leftAdjointMate_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ 
Y} {g : (ᘁX) ⟶ Z} : (ᘁf) ≫ g = (fun_ _).inv ≫ η_ (ᘁX : C) X ▷ _ ≫ (g otimesₘ f) 
▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
参数：ᘁX。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_whisker`：evalWhiskerRight_
cons_whisker {f g h i j k : C} {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i
 ⟶ j} {η₁ : h otimes k ⟶ i otimes k} {η₂ : …
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_id`：evalWhiskerRight_id {f g : 
C} {η : f ⟶ g} {η₁ : f ⟶ g otimes 𝟙_ C} {η₂ : f otimes 𝟙_ C ⟶ g otimes 𝟙_ C} (e_
η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ :…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
-/
theorem leftAdjointMate_comp {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] {f : X ⟶ Y}
    {g : (ᘁX) ⟶ Z} :
    (ᘁf) ≫ g =
      (λ_ _).inv ≫
        η_ (ᘁX : C) X ▷ _ ≫ (g ⊗ₘ f) ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom :=
  calc
    _ = 𝟙 _ ⊗≫ η_ (ᘁX : C) X ▷ (ᘁY) ⊗≫ (ᘁX) ◁ f ▷ (ᘁY) ⊗≫ ((ᘁX) ◁ ε_ (ᘁY) Y ≫ g ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by
      dsimp only [leftAdjointMate]; monoidal
    _ = _ := by
      rw [whisker_exchange, tensorHom_def']; monoidal

/-- The composition of right adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
/-
**CategoryTheory.comp_rightAdjointMate** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：comp_rightAdjointMate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRi
ghtDual Z] {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.rightAdjointMate_comp`：rightAdjointMate_comp {X Y Z : C} 
[HasRightDual X] [HasRightDual Y] {f : X ⟶ Y} {g : Xᘁ ⟶ Z} : fᘁ ≫ g = (ρ_ (Yᘁ)).
inv ≫ _ ◁ η_ X (Xᘁ) ≫ _ ◁ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_id`：evalWhiskerRight_id {f g : 
C} {η : f ⟶ g} {η₁ : f ⟶ g otimes 𝟙_ C} {η₂ : f otimes 𝟙_ C ⟶ g otimes 𝟙_ C} (e_
η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ :…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The composition of right adjoint mates is the adjoint mate of the composition.
-/
theorem comp_rightAdjointMate {X Y Z : C} [HasRightDual X] [HasRightDual Y] [HasRightDual Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g)ᘁ = gᘁ ≫ fᘁ := by
  rw [rightAdjointMate_comp]
  simp only [rightAdjointMate, comp_whiskerRight]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp]; congr 2
  symm
  calc
    _ = 𝟙 _ ⊗≫ (η_ Y Yᘁ ▷ 𝟙_ C ≫ (Y ⊗ Yᘁ) ◁ η_ X Xᘁ) ⊗≫ Y ◁ Yᘁ ◁ f ▷ Xᘁ ⊗≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [tensorHom_def']; monoidal
    _ = η_ X Xᘁ ⊗≫ (η_ Y Yᘁ ▷ (X ⊗ Xᘁ) ≫ (Y ⊗ Yᘁ) ◁ f ▷ Xᘁ) ⊗≫
        Y ◁ ε_ Y Yᘁ ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ X Xᘁ ⊗≫ f ▷ Xᘁ ⊗≫ (η_ Y Yᘁ ▷ Y ⊗≫ Y ◁ ε_ Y Yᘁ) ▷ Xᘁ ⊗≫ g ▷ Xᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ g ▷ Xᘁ := by
      rw [evaluation_coevaluation'']; monoidal

/-- The composition of left adjoint mates is the adjoint mate of the composition. -/
@[reassoc]
/-
**CategoryTheory.comp_leftAdjointMate** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：comp_leftAdjointMate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftD
ual Z] {f : X ⟶ Y} {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.leftAdjointMate_comp`：leftAdjointMate_comp {X Y Z : C} [H
asLeftDual X] [HasLeftDual Y] {f : X ⟶ Y} {g : (ᘁX) ⟶ Z} : (ᘁf) ≫ g = (fun_ _).i
nv ≫ η_ (ᘁX : C) X ▷ _ ≫ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_whisker`：evalWhiskerRight_
cons_whisker {f g h i j k : C} {α : g ≅ f otimes h} {η : h ⟶ i} {ηs : f otimes i
 ⟶ j} {η₁ : h otimes k ⟶ i otimes k} {η₂ : …
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_id`：evalWhiskerLeft_id {f g : C}
 {η : f ⟶ g} {η₁ : f ⟶ 𝟙_ C otimes g} {η₂ : 𝟙_ C otimes f ⟶ 𝟙_ C otimes g} (e_η₁
 : η ≫ (fun_ _).inv = η₁) (e_η₂ …
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The composition of left adjoint mates is the adjoint mate of the composition.
-/
theorem comp_leftAdjointMate {X Y Z : C} [HasLeftDual X] [HasLeftDual Y] [HasLeftDual Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} : (ᘁf ≫ g) = (ᘁg) ≫ ᘁf := by
  rw [leftAdjointMate_comp]
  simp only [leftAdjointMate, MonoidalCategory.whiskerLeft_comp]
  simp only [← Category.assoc]; congr 3; simp only [Category.assoc]
  simp only [← comp_whiskerRight]; congr 2
  symm
  calc
    _ = 𝟙 _ ⊗≫ ((𝟙_ C) ◁ η_ (ᘁY) Y ≫ η_ (ᘁX) X ▷ ((ᘁY) ⊗ Y)) ⊗≫ (ᘁX) ◁ f ▷ (ᘁY) ▷ Y ⊗≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y ⊗≫ (ᘁX) ◁ g := by
      rw [tensorHom_def]; monoidal
    _ = η_ (ᘁX) X ⊗≫ (((ᘁX) ⊗ X) ◁ η_ (ᘁY) Y ≫ ((ᘁX) ◁ f) ▷ ((ᘁY) ⊗ Y)) ⊗≫
        (ᘁX) ◁ ε_ (ᘁY) Y ▷ Y ⊗≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; monoidal
    _ = η_ (ᘁX) X ⊗≫ ((ᘁX) ◁ f) ⊗≫ (ᘁX) ◁ (Y ◁ η_ (ᘁY) Y ⊗≫ ε_ (ᘁY) Y ▷ Y) ⊗≫ (ᘁX) ◁ g := by
      rw [whisker_exchange]; monoidal
    _ = η_ (ᘁX) X ≫ (ᘁX) ◁ f ≫ (ᘁX) ◁ g := by
      rw [coevaluation_evaluation'']; monoidal

/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
by "pulling the string on the left" up or down.

This gives the adjunction `tensorLeftAdjunction Y Y' : tensorLeft Y' ⊣ tensorLeft Y`.

This adjunction is often referred to as "Frobenius reciprocity" in the
fusion categories / planar algebras / subfactors literature.
-/
/-
**CategoryTheory.tensorLeftHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (Y' otimes X ⟶ Z) 
≃ (X ⟶ Y otimes Z) where toFun f
参数：X Y Y' Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)`
by "pulling the string on the left" up or down.

This gives the adjunction `tensorLeftAdjunction Y Y' : tensorLeft Y' ⊣ tensorLef
t Y`.

This adjunction is often referred to as "Frobenius reciprocity" in the
fusion categories / planar algebras / subfactors literature.
-/
def tensorLeftHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z) where
  toFun f := (λ_ _).inv ≫ η_ _ _ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ f
  invFun f := Y' ◁ f ≫ (α_ _ _ _).inv ≫ ε_ _ _ ▷ _ ≫ (λ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ Y' ◁ η_ Y Y' ▷ X ⊗≫ ((Y' ⊗ Y) ◁ f ≫ ε_ Y Y' ▷ Z) ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ▷ X ⊗≫ f := by
        rw [whisker_exchange]; monoidal
      _ = f := by
        rw [coevaluation_evaluation'']; monoidal
  right_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ (η_ Y Y' ▷ X ≫ (Y ⊗ Y') ◁ f) ⊗≫ Y ◁ ε_ Y Y' ▷ Z ⊗≫ 𝟙 _ := by
        monoidal
      _ = f ⊗≫ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ▷ Z ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = f := by
        rw [evaluation_coevaluation'']; monoidal

/-- Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')`
by "pulling the string on the right" up or down.
-/
/-
**CategoryTheory.tensorRightHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (X otimes Y ⟶ Z) 
≃ (X ⟶ Z otimes Y') where toFun f
参数：X Y Y' Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an exact pairing on `Y Y'`,
we get a bijection on hom-sets `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')`
by "pulling the string on the right" up or down.
-/
def tensorRightHomEquiv (X Y Y' Z : C) [ExactPairing Y Y'] : (X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y') where
  toFun f := (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _
  invFun f := f ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ ε_ _ _ ≫ (ρ_ _).hom
  left_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ X ◁ η_ Y Y' ▷ Y ⊗≫ (f ▷ (Y' ⊗ Y) ≫ Z ◁ ε_ Y Y') ⊗≫ 𝟙 _ := by
        monoidal
      _ = 𝟙 _ ⊗≫ X ◁ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ f := by
        rw [← whisker_exchange]; monoidal
      _ = f := by
        rw [evaluation_coevaluation'']; monoidal
  right_inv f := by
    calc
      _ = 𝟙 _ ⊗≫ (X ◁ η_ Y Y' ≫ f ▷ (Y ⊗ Y')) ⊗≫ Z ◁ ε_ Y Y' ▷ Y' ⊗≫ 𝟙 _ := by
        monoidal
      _ = f ⊗≫ Z ◁ (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = f := by
        rw [coevaluation_evaluation'']; monoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.tensorLeftHomEquiv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y
' otimes X ⟶ Z) (g : Z ⟶ Z') : (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorL
eftHomEquiv X Y Y' Z) f ≫ Y ◁ g
参数：f : Y' otimes X ⟶ Z；g : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorLeftHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) = (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g := by
  simp [tensorLeftHomEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.tensorLeftHomEquiv_symm_naturality** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (
f : X ⟶ X') (g : X' ⟶ Y otimes Z) : (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
 _ ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g
参数：f : X ⟶ X'；g : X' ⟶ Y otimes Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorLeftHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      _ ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g := by
  simp [tensorLeftHomEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.tensorRightHomEquiv_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : 
X otimes Y ⟶ Z) (g : Z ⟶ Z') : (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensor
RightHomEquiv X Y Y' Z) f ≫ g ▷ Y'
参数：f : X otimes Y ⟶ Z；g : Z ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorRightHomEquiv_naturality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z)
    (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) = (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y' := by
  simp [tensorRightHomEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.tensorRightHomEquiv_symm_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] 
(f : X ⟶ X') (g : X' ⟶ Z otimes Y') : (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g
) = f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g
参数：f : X ⟶ X'；g : X' ⟶ Z otimes Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorRightHomEquiv_symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X')
    (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g := by
  simp [tensorRightHomEquiv]

/-- If `Y Y'` have an exact pairing,
then the functor `tensorLeft Y'` is left adjoint to `tensorLeft Y`.
-/
/-
**CategoryTheory.tensorLeftAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：tensorLeftAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorLeft Y' ⊣ tens
orLeft Y
参数：Y Y' : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.tensorLeftHomEquiv_symm_naturality`：tensorLeftHomEquiv_sy
mm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X') (g : X' ⟶ Y oti
mes Z) : (tensorLeftHomEquiv X Y Y' Z).…
· 使用定理 `CategoryTheory.tensorLeftHomEquiv_naturality`：tensorLeftHomEquiv_natural
ity {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' otimes X ⟶ Z) (g : Z ⟶ Z') : (
tensorLeftHomEquiv X Y Y' Z') (f ≫…

--- 原说明 ---
If `Y Y'` have an exact pairing,
then the functor `tensorLeft Y'` is left adjoint to `tensorLeft Y`.
-/
def tensorLeftAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorLeft Y' ⊣ tensorLeft Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Z => tensorLeftHomEquiv X Y Y' Z
      homEquiv_naturality_left_symm := fun f g => tensorLeftHomEquiv_symm_naturality f g
      homEquiv_naturality_right := fun f g => tensorLeftHomEquiv_naturality f g }

/-- If `Y Y'` have an exact pairing,
then the functor `tensor_right Y` is left adjoint to `tensor_right Y'`.
-/
/-
**CategoryTheory.tensorRightAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：tensorRightAdjunction (Y Y' : C) [ExactPairing Y Y'] : tensorRight Y ⊣ ten
sorRight Y'
参数：Y Y' : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.tensorRightHomEquiv_symm_naturality`：tensorRightHomEquiv_
symm_naturality {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X') (g : X' ⟶ Z o
times Y') : (tensorRightHomEquiv X Y Y' …
· 使用定理 `CategoryTheory.tensorRightHomEquiv_naturality`：tensorRightHomEquiv_natur
ality {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X otimes Y ⟶ Z) (g : Z ⟶ Z') : 
(tensorRightHomEquiv X Y Y' Z') (f …

--- 原说明 ---
If `Y Y'` have an exact pairing,
then the functor `tensor_right Y` is left adjoint to `tensor_right Y'`.
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
/-
**CategoryTheory.closedOfHasLeftDual** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：closedOfHasLeftDual (Y : C) [HasLeftDual Y] : Closed Y where rightAdj
参数：Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Y` has a left dual `ᘁY`, then it is a closed object, with the internal hom f
unctor `Y ⟶[C] -`
given by left tensoring by `ᘁY`.
This has to be a definition rather than an instance to avoid diamonds, for examp
le between
`category_theory.monoidal_closed.functor_closed` and
`CategoryTheory.Monoidal.functorHasLeftDual`. Moreover, in concrete applications
 there is often
a more useful definition of the internal hom object than `ᘁY ⊗ X`, in which case
 the closed
structure shouldn't come from `HasLeftDual` (e.g. in the category `FinVect k`, i
t is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even t
hough these are
naturally isomorphic).
-/
def closedOfHasLeftDual (Y : C) [HasLeftDual Y] : Closed Y where
  rightAdj := tensorLeft (ᘁY)
  adj := tensorLeftAdjunction (ᘁY) Y

set_option backward.isDefEq.respectTransparency.types false in
/-- `tensorLeftHomEquiv` commutes with tensoring on the right -/
/-
**CategoryTheory.tensorLeftHomEquiv_tensor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X 
⟶ Y otimes Z) (g : X' ⟶ Z') : (tensorLeftHomEquiv (X otimes X') Y Y' (Z otimes Z
')).symm ((f otimesₘ g) ≫ (α_ _ _ _).hom) = (α_ _ _ _).inv ≫ ((tensorLeftHomEqui
v X Y Y' Z).symm f otimesₘ g)
参数：f : X ⟶ Y otimes Z；g : X' ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_whiskerRight`：leftUnitor_whis
kerRight (X Y : C) : (fun_ X).hom ▷ Y = (α_ (𝟙_ C) X Y).hom ≫ (fun_ (X otimes Y)
).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`tensorLeftHomEquiv` commutes with tensoring on the right
-/
theorem tensorLeftHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Y ⊗ Z)
    (g : X' ⟶ Z') :
    (tensorLeftHomEquiv (X ⊗ X') Y Y' (Z ⊗ Z')).symm ((f ⊗ₘ g) ≫ (α_ _ _ _).hom) =
      (α_ _ _ _).inv ≫ ((tensorLeftHomEquiv X Y Y' Z).symm f ⊗ₘ g) := by
  simp [tensorLeftHomEquiv, tensorHom_def']

set_option backward.isDefEq.respectTransparency.types false in
/-- `tensorRightHomEquiv` commutes with tensoring on the left -/
/-
**CategoryTheory.tensorRightHomEquiv_tensor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X
 ⟶ Z otimes Y') (g : X' ⟶ Z') : (tensorRightHomEquiv (X' otimes X) Y Y' (Z' otim
es Z)).symm ((g otimesₘ f) ≫ (α_ _ _ _).inv) = (α_ _ _ _).hom ≫ (g otimesₘ (tens
orRightHomEquiv X Y Y' Z).symm f)
参数：f : X ⟶ Z otimes Y'；g : X' ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_hom_hom_hom_hom_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_rightUnitor`：whiskerLeft_rig
htUnitor (X Y : C) : X ◁ (ρ_ Y).hom = (α_ X Y (𝟙_ C)).inv ≫ (ρ_ (X otimes Y)).ho
m
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`tensorRightHomEquiv` commutes with tensoring on the left
-/
theorem tensorRightHomEquiv_tensor {X X' Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⟶ Z ⊗ Y')
    (g : X' ⟶ Z') :
    (tensorRightHomEquiv (X' ⊗ X) Y Y' (Z' ⊗ Z)).symm ((g ⊗ₘ f) ≫ (α_ _ _ _).inv) =
      (α_ _ _ _).hom ≫ (g ⊗ₘ (tensorRightHomEquiv X Y Y' Z).symm f) := by
  simp [tensorRightHomEquiv, tensorHom_def]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft {Y Y' Z : C} [ExactP
airing Y Y'] (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ Y ◁ f) =
 (ρ_ _).hom ≫ f
参数：f : Y' ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_id`：evalWhiskerLeft_id {f g : C}
 {η : f ⟶ g} {η₁ : f ⟶ 𝟙_ C otimes g} {η₂ : 𝟙_ C otimes f ⟶ 𝟙_ C otimes g} (e_η₁
 : η ≫ (fun_ _).inv = η₁) (e_η₂ …
· 使用引理 `CategoryTheory.ExactPairing.coevaluation_evaluation''`：coevaluation_eval
uation'' : Y ◁ η_ X Y otimes≫ ε_ X Y ▷ Y = otimes𝟙.hom
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
-/
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ Y ◁ f) = (ρ_ _).hom ≫ f := by
  calc
    _ = Y' ◁ η_ Y Y' ⊗≫ ((Y' ⊗ Y) ◁ f ≫ ε_ Y Y' ▷ Z) ⊗≫ 𝟙 _ := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ⊗≫ f := by
      rw [whisker_exchange]; monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight {X Y : C} [HasRight
Dual X] [HasRightDual Y] (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _
 ≫ f ▷ (Xᘁ)) = (ρ_ _).hom ≫ fᘁ
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight {X Y : C} [HasRightDual X]
    [HasRightDual Y] (f : X ⟶ Y) :
    (tensorLeftHomEquiv _ _ _ _).symm (η_ _ _ ≫ f ▷ (Xᘁ)) = (ρ_ _).hom ≫ fᘁ := by
  dsimp [tensorLeftHomEquiv, rightAdjointMate]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft {X Y : C} [HasLeftD
ual X] [HasLeftDual Y] (f : X ⟶ Y) : (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (
ᘁX : C) X ≫ (ᘁX : C) ◁ f) = (fun_ _).hom ≫ ᘁf
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft {X Y : C} [HasLeftDual X]
    [HasLeftDual Y] (f : X ⟶ Y) :
    (tensorRightHomEquiv _ (ᘁY) _ _).symm (η_ (ᘁX : C) X ≫ (ᘁX : C) ◁ f) = (λ_ _).hom ≫ ᘁf := by
  dsimp [tensorRightHomEquiv, leftAdjointMate]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight {Y Y' Z : C} [Exac
tPairing Y Y'] (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ f ▷ Y
') = (fun_ _).hom ≫ f
参数：f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_id`：evalWhiskerRight_id {f g : 
C} {η : f ⟶ g} {η₁ : f ⟶ g otimes 𝟙_ C} {η₂ : f otimes 𝟙_ C ⟶ g otimes 𝟙_ C} (e_
η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ :…
· 使用引理 `CategoryTheory.ExactPairing.evaluation_coevaluation''`：evaluation_coeval
uation'' : η_ X Y ▷ X otimes≫ X ◁ ε_ X Y = otimes𝟙.hom
（共 31 条，此处仅展示前 30 条）
-/
theorem tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight {Y Y' Z : C} [ExactPairing Y Y']
    (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η_ Y Y' ≫ f ▷ Y') = (λ_ _).hom ≫ f :=
  calc
    _ = η_ Y Y' ▷ Y ⊗≫ (f ▷ (Y' ⊗ Y) ≫ Z ◁ ε_ Y Y') ⊗≫ 𝟙 _ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫ f := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.tensorLeftHomEquiv_whiskerLeft_comp_evaluation** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorLeftHomEquiv_whiskerLeft_comp_evaluation {Y Z : C} [HasLeftDual Z] (
f : Y ⟶ ᘁZ) : (tensorLeftHomEquiv _ _ _ _) (Z ◁ f ≫ ε_ _ _) = f ≫ (ρ_ _).inv
参数：f : Y ⟶ ᘁZ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f g 
h i : C} {η : h ⟶ i} {η₁ : g otimes h ⟶ g otimes i} {η₂ : f otimes g otimes h ⟶ 
f otimes g otimes i} {η₃ : f otime…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_id`：evalWhiskerLeft_id {f g : C}
 {η : f ⟶ g} {η₁ : f ⟶ 𝟙_ C otimes g} {η₂ : 𝟙_ C otimes f ⟶ 𝟙_ C otimes g} (e_η₁
 : η ≫ (fun_ _).inv = η₁) (e_η₂ …
· 使用引理 `CategoryTheory.ExactPairing.evaluation_coevaluation''`：evaluation_coeval
uation'' : η_ X Y ▷ X otimes≫ X ◁ ε_ X Y = otimes𝟙.hom
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
-/
theorem tensorLeftHomEquiv_whiskerLeft_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) :
    (tensorLeftHomEquiv _ _ _ _) (Z ◁ f ≫ ε_ _ _) = f ≫ (ρ_ _).inv :=
  calc
    _ = 𝟙 _ ⊗≫ (η_ (ᘁZ : C) Z ▷ Y ≫ ((ᘁZ) ⊗ Z) ◁ f) ⊗≫ (ᘁZ) ◁ ε_ (ᘁZ) Z := by
      dsimp [tensorLeftHomEquiv]; monoidal
    _ = f ⊗≫ (η_ (ᘁZ) Z ▷ (ᘁZ) ⊗≫ (ᘁZ) ◁ ε_ (ᘁZ) Z) := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [evaluation_coevaluation'']; monoidal

@[simp]
/-
**CategoryTheory.tensorLeftHomEquiv_whiskerRight_comp_evaluation** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorLeftHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasLeftDual X] 
[HasLeftDual Y] (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) (f ▷ _ ≫ ε_ _ _) = (ᘁ
f) ≫ (ρ_ _).inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorLeftHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y]
    (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) (f ▷ _ ≫ ε_ _ _) = (ᘁf) ≫ (ρ_ _).inv := by
  dsimp [tensorLeftHomEquiv, leftAdjointMate]
  simp

@[simp]
/-
**CategoryTheory.tensorRightHomEquiv_whiskerLeft_comp_evaluation** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorRightHomEquiv_whiskerLeft_comp_evaluation {X Y : C} [HasRightDual X]
 [HasRightDual Y] (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((Yᘁ : C) ◁ f ≫ ε_
 _ _) = fᘁ ≫ (fun_ _).inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc`：whisker_assoc (X : C) {Y 
Y' : C} (f : Y ⟶ Y') (Z : C) : (X ◁ f) ▷ Z = (α_ X Y Z).hom ≫ X ◁ f ▷ Z ≫ (α_ X 
Y' Z).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorRightHomEquiv_whiskerLeft_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y]
    (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((Yᘁ : C) ◁ f ≫ ε_ _ _) = fᘁ ≫ (λ_ _).inv := by
  dsimp [tensorRightHomEquiv, rightAdjointMate]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.tensorRightHomEquiv_whiskerRight_comp_evaluation** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensorRightHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasRightDual X
] (f : Y ⟶ Xᘁ) : (tensorRightHomEquiv _ _ _ _) (f ▷ X ≫ ε_ X (Xᘁ)) = f ≫ (fun_ _
).inv
参数：f : Y ⟶ Xᘁ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Monoidal.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g ⟶ 
h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerLeft`：eval_whiskerLeft {f g h : C} {
η η' : g ⟶ h} {θ : f otimes g ⟶ f otimes h} (e_η : η = η') (e_θ : f ◁ η' = θ) : 
f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Monoidal.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _).
hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_cons
 {f g h i j : C} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f otimes i ⟶ f otimes
 j} (e_θ : f ◁ ηs = θ) : f ◁ (α.hom ≫…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : C)
 {g h : C} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f α).hom
· 使用定理 `Mathlib.Tactic.Monoidal.eval_whiskerRight`：eval_whiskerRight {f g h : C}
 {η η' : f ⟶ g} {θ : f otimes h ⟶ g otimes h} (e_η : η = η') (e_θ : η' ▷ h = θ) 
: η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_cons_of_of`：evalWhiskerRight_co
ns_of_of {f g h i j : C} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h otimes j 
⟶ i otimes j} {η₁ : g otimes j ⟶ h otimes…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_nil`：evalWhiskerRight_nil {f g 
: C} (α : f ≅ g) (h : C) : (whiskerRightIso α h).hom = (whiskerRightIso α h).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRightAux_of`：evalWhiskerRightAux_of {
f g : C} (η : f ⟶ g) (h : C) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso.refl _).h
om
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_cons`：evalComp_cons {f g h i j : C} (α 
: f ≅ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (
α.hom ≫ η ≫ ηs) ≫ θ = α.hom…
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_nil`：evalComp_nil_nil {f g h : C} (
α : f ≅ g) (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Monoidal.evalComp_nil_cons`：evalComp_nil_cons {f g h i j 
: C} (α : f ≅ g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs)
 = (α ≪≫ β).hom ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Monoidal.eval_monoidalComp`：eval_monoidalComp {η η' : f ⟶
 g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η = η') (e_θ : 
θ = θ') (e_αθ : α.hom ≫ θ' = αθ…
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_comp`：evalWhiskerRight_comp {f 
f' g h : C} {η : f ⟶ f'} {η₁ : f otimes g ⟶ f' otimes g} {η₂ : (f otimes g) otim
es h ⟶ (f' otimes g) otimes h} {η₃ …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Monoidal.mk_eq_of_naturality`：mk_eq_of_naturality {f g f'
 : C} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙_ C otimes f ≅ f') (η_g : 𝟙_ C otime
s g ≅ f') (η_hom : η'.hom = η) (Θ…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_comp`：naturality_comp {p f g h pf : C
} {η : f ≅ g} {θ : g ≅ h} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (η_h :
 p otimes h ≅ pf) (ih_η : p ◁…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_inv`：naturality_inv {p f g pf : C} {η
 : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf) (ih : p ◁ η ≪≫ η_g = η
_f) : p ◁ η.symm ≪≫ η_f = η_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_rightUnitor`：naturality_rightUnitor {
p f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = normalizeIsoComp η_f (
ρ_ pf)
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerLeft`：naturality_whiskerLeft {
p f g h pf pfg : C} {η : g ≅ h} (η_f : p otimes f ≅ pf) (η_fg : pf otimes g ≅ pf
g) (η_fh : (pf otimes h) ≅ pfg) (ih_…
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_id`：naturality_id {p f pf : C} (η_f :
 p otimes f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_associator`：naturality_associator {p 
f g h pf pfg pfgh : C} (η_f : p otimes f ≅ pf) (η_g : pf otimes g ≅ pfg) (η_h : 
pfg otimes h ≅ pfgh) : p ◁ (α_ f g …
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_whiskerRight`：naturality_whiskerRight
 {p f g h pf pfh : C} {η : f ≅ g} (η_f : p otimes f ≅ pf) (η_g : p otimes g ≅ pf
) (η_fh : (pf otimes h) ≅ pfh) (ih_η …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `Mathlib.Tactic.Monoidal.evalWhiskerRight_id`：evalWhiskerRight_id {f g : 
C} {η : f ⟶ g} {η₁ : f ⟶ g otimes 𝟙_ C} {η₂ : f otimes 𝟙_ C ⟶ g otimes 𝟙_ C} (e_
η₁ : η ≫ (ρ_ _).inv = η₁) (e_η₂ :…
· 使用引理 `CategoryTheory.ExactPairing.coevaluation_evaluation''`：coevaluation_eval
uation'' : Y ◁ η_ X Y otimes≫ ε_ X Y ▷ Y = otimes𝟙.hom
· 使用定理 `Mathlib.Tactic.Monoidal.naturality_leftUnitor`：naturality_leftUnitor {p 
f pf : C} (η_f : p otimes f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = normalizeIsoComp (ρ_ p
) η_f
-/
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ) :
    (tensorRightHomEquiv _ _ _ _) (f ▷ X ≫ ε_ X (Xᘁ)) = f ≫ (λ_ _).inv :=
  calc
    _ = 𝟙 _ ⊗≫ (Y ◁ η_ X Xᘁ ≫ f ▷ (X ⊗ Xᘁ)) ⊗≫ ε_ X Xᘁ ▷ Xᘁ := by
      dsimp [tensorRightHomEquiv]; monoidal
    _ = f ⊗≫ (Xᘁ ◁ η_ X Xᘁ ⊗≫ ε_ X Xᘁ ▷ Xᘁ) := by
      rw [whisker_exchange]; monoidal
    _ = _ := by
      rw [coevaluation_evaluation'']; monoidal

-- Next four lemmas passing `fᘁ` or `ᘁf` through (co)evaluations.
@[reassoc]
/-
**CategoryTheory.coevaluation_comp_rightAdjointMate** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDua
l Y] (f : X ⟶ Y) : η_ Y (Yᘁ) ≫ _ ◁ (fᘁ) = η_ _ _ ≫ f ▷ _
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft`：te
nsorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft {Y Y' Z : C} [ExactPairing Y
 Y'] (f : Y' ⟶ Z) : (tensorLeftHomEquiv _ _ _ _).symm (η_ …
· 使用定理 `CategoryTheory.tensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight`：t
ensorLeftHomEquiv_symm_coevaluation_comp_whiskerRight {X Y : C} [HasRightDual X]
 [HasRightDual Y] (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coevaluation_comp_rightAdjointMate {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    η_ Y (Yᘁ) ≫ _ ◁ (fᘁ) = η_ _ _ ≫ f ▷ _ := by
  apply_fun (tensorLeftHomEquiv _ Y (Yᘁ) _).symm
  simp

@[reassoc]
/-
**CategoryTheory.leftAdjointMate_comp_evaluation** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] 
(f : X ⟶ Y) : X ◁ (ᘁf) ≫ ε_ _ _ = f ▷ _ ≫ ε_ _ _
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.tensorLeftHomEquiv_whiskerLeft_comp_evaluation`：tensorLef
tHomEquiv_whiskerLeft_comp_evaluation {Y Z : C} [HasLeftDual Z] (f : Y ⟶ ᘁZ) : (
tensorLeftHomEquiv _ _ _ _) (Z ◁ f ≫ ε_ _ _) = f ≫ …
· 使用定理 `CategoryTheory.tensorLeftHomEquiv_whiskerRight_comp_evaluation`：tensorLe
ftHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y
] (f : X ⟶ Y) : (tensorLeftHomEquiv _ _ _ _) (f ▷ _ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftAdjointMate_comp_evaluation {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    X ◁ (ᘁf) ≫ ε_ _ _ = f ▷ _ ≫ ε_ _ _ := by
  apply_fun tensorLeftHomEquiv _ (ᘁX) X _
  simp

@[reassoc]
/-
**CategoryTheory.coevaluation_comp_leftAdjointMate** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y
] (f : X ⟶ Y) : η_ (ᘁY) Y ≫ (ᘁf) ▷ Y = η_ (ᘁX) X ≫ (ᘁX) ◁ f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight`：
tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight {Y Y' Z : C} [ExactPairi
ng Y Y'] (f : Y ⟶ Z) : (tensorRightHomEquiv _ Y _ _).symm (η…
· 使用定理 `CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft`：t
ensorRightHomEquiv_symm_coevaluation_comp_whiskerLeft {X Y : C} [HasLeftDual X] 
[HasLeftDual Y] (f : X ⟶ Y) : (tensorRightHomEquiv _ (ᘁY) _…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coevaluation_comp_leftAdjointMate {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    η_ (ᘁY) Y ≫ (ᘁf) ▷ Y = η_ (ᘁX) X ≫ (ᘁX) ◁ f := by
  apply_fun (tensorRightHomEquiv _ (ᘁY) Y _).symm
  simp

@[reassoc]
/-
**CategoryTheory.rightAdjointMate_comp_evaluation** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual 
Y] (f : X ⟶ Y) : (fᘁ ▷ X) ≫ ε_ X (Xᘁ) = ((Yᘁ) ◁ f) ≫ ε_ Y (Yᘁ)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.tensorRightHomEquiv_whiskerRight_comp_evaluation`：tensorR
ightHomEquiv_whiskerRight_comp_evaluation {X Y : C} [HasRightDual X] (f : Y ⟶ Xᘁ
) : (tensorRightHomEquiv _ _ _ _) (f ▷ X ≫ ε_ X (Xᘁ))…
· 使用定理 `CategoryTheory.tensorRightHomEquiv_whiskerLeft_comp_evaluation`：tensorRi
ghtHomEquiv_whiskerLeft_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual
 Y] (f : X ⟶ Y) : (tensorRightHomEquiv _ _ _ _) ((Yᘁ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightAdjointMate_comp_evaluation {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    (fᘁ ▷ X) ≫ ε_ X (Xᘁ) = ((Yᘁ) ◁ f) ≫ ε_ Y (Yᘁ) := by
  apply_fun tensorRightHomEquiv _ X (Xᘁ) _
  simp

/-- Transport an exact pairing across an isomorphism in the first argument. -/
@[instance_reducible]
/-
**CategoryTheory.exactPairingCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : Exac
tPairing X Y where evaluation'
参数：i : X ≅ X'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport an exact pairing across an isomorphism in the first argument.
-/
def exactPairingCongrLeft {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') : ExactPairing X Y where
  evaluation' := Y ◁ i.hom ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ i.inv ▷ Y
  evaluation_coevaluation' :=
    calc
      _ = η_ X' Y ▷ X ⊗≫ (i.inv ▷ (Y ⊗ X) ≫ X ◁ (Y ◁ i.hom)) ⊗≫ X ◁ ε_ X' Y := by
        monoidal
      _ = 𝟙 _ ⊗≫ (η_ X' Y ▷ X ≫ (X' ⊗ Y) ◁ i.hom) ⊗≫
          (i.inv ▷ (Y ⊗ X') ≫ X ◁ ε_ X' Y) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ i.hom ⊗≫ (η_ X' Y ▷ X' ⊗≫ X' ◁ ε_ X' Y) ⊗≫ i.inv ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, ← whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ (i.hom ≫ i.inv) ⊗≫ 𝟙 _ := by
        rw [evaluation_coevaluation'']; monoidal
      _ = (λ_ X).hom ≫ (ρ_ X).inv := by
        rw [Iso.hom_inv_id]
        monoidal
  coevaluation_evaluation' := by
    calc
      _ = Y ◁ η_ X' Y ≫ Y ◁ (i.inv ≫ i.hom) ▷ Y ⊗≫ ε_ X' Y ▷ Y := by
        monoidal
      _ = Y ◁ η_ X' Y ⊗≫ ε_ X' Y ▷ Y := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
        rw [coevaluation_evaluation'']
        simp

/-- Transport an exact pairing across an isomorphism in the second argument. -/
@[instance_reducible]
/-
**CategoryTheory.exactPairingCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : Exa
ctPairing X Y where evaluation'
参数：i : Y ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport an exact pairing across an isomorphism in the second argument.
-/
def exactPairingCongrRight {X Y Y' : C} [ExactPairing X Y'] (i : Y ≅ Y') : ExactPairing X Y where
  evaluation' := i.hom ▷ X ≫ ε_ _ _
  coevaluation' := η_ _ _ ≫ X ◁ i.inv
  evaluation_coevaluation' := by
    calc
      _ = η_ X Y' ▷ X ⊗≫ X ◁ (i.inv ≫ i.hom) ▷ X ≫ X ◁ ε_ X Y' := by
        monoidal
      _ = η_ X Y' ▷ X ⊗≫ X ◁ ε_ X Y' := by
        rw [Iso.inv_hom_id]; monoidal
      _ = _ := by
        rw [evaluation_coevaluation'']
        simp
  coevaluation_evaluation' :=
    calc
      _ = Y ◁ η_ X Y' ⊗≫ (Y ◁ (X ◁ i.inv) ≫ i.hom ▷ (X ⊗ Y)) ⊗≫ ε_ X Y' ▷ Y := by
        monoidal
      _ = 𝟙 _ ⊗≫ (Y ◁ η_ X Y' ≫ i.hom ▷ (X ⊗ Y')) ⊗≫
          ((Y' ⊗ X) ◁ i.inv ≫ ε_ X Y' ▷ Y) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ i.hom ⊗≫ (Y' ◁ η_ X Y' ⊗≫ ε_ X Y' ▷ Y') ⊗≫ i.inv ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, whisker_exchange]; monoidal
      _ = 𝟙 _ ⊗≫ (i.hom ≫ i.inv) ⊗≫ 𝟙 _ := by
        rw [coevaluation_evaluation'']; monoidal
      _ = (ρ_ Y).hom ≫ (λ_ Y).inv := by
        rw [Iso.hom_inv_id]
        monoidal

/-- Transport an exact pairing across isomorphisms. -/
@[instance_reducible]
/-
**CategoryTheory.exactPairingCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：exactPairingCongr {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y
 ≅ Y') : ExactPairing X Y
参数：i : X ≅ X'；j : Y ≅ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport an exact pairing across isomorphisms.
-/
def exactPairingCongr {X X' Y Y' : C} [ExactPairing X' Y'] (i : X ≅ X') (j : Y ≅ Y') :
    ExactPairing X Y :=
  haveI : ExactPairing X' Y := exactPairingCongrRight j
  exactPairingCongrLeft i

/-- Right duals are isomorphic. -/
/-
**CategoryTheory.rightDualIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：rightDualIso {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y
₂) : Y₁ ≅ Y₂ where hom
参数：p₁ : ExactPairing X Y₁；p₂ : ExactPairing X Y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right duals are isomorphic.
-/
def rightDualIso {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) : Y₁ ≅ Y₂ where
  hom := @rightAdjointMate C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  inv := @rightAdjointMate C _ _ X X ⟨Y₁⟩ ⟨Y₂⟩ (𝟙 X)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_rightAdjointMate, Category.comp_id, @rightAdjointMate_id]
    rfl
  inv_hom_id := by
    rw [← @comp_rightAdjointMate, Category.comp_id, @rightAdjointMate_id]
    rfl

/-- Left duals are isomorphic. -/
/-
**CategoryTheory.leftDualIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y
) : X₁ ≅ X₂ where hom
参数：p₁ : ExactPairing X₁ Y；p₂ : ExactPairing X₂ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left duals are isomorphic.
-/
def leftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) : X₁ ≅ X₂ where
  hom := @leftAdjointMate C _ _ Y Y ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y)
  inv := @leftAdjointMate C _ _ Y Y ⟨X₁⟩ ⟨X₂⟩ (𝟙 Y)
  hom_inv_id := by
    -- Make all arguments explicit, because we want to find them by unification not synthesis.
    rw [← @comp_leftAdjointMate C, Category.comp_id, @leftAdjointMate_id]
    rfl
  inv_hom_id := by
    rw [← @comp_leftAdjointMate C, Category.comp_id, @leftAdjointMate_id]
    rfl

@[simp]
/-
**CategoryTheory.rightDualIso_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.
refl Y
参数：p : ExactPairing X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.rightAdjointMate_id`：rightAdjointMate_id {X : C} [HasRigh
tDual X] : (𝟙 X)ᘁ = 𝟙 (Xᘁ)
· 使用定理 `CategoryTheory.Iso.mk.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (hom hom_1 : X ⟶ Y) (e_hom : hom = hom_1)   (inv in
v_1 : Y ⟶ X) (e_inv : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightDualIso_id {X Y : C} (p : ExactPairing X Y) : rightDualIso p p = Iso.refl Y := by
  ext
  simp only [rightDualIso, Iso.refl_hom, @rightAdjointMate_id]

@[simp]
/-
**CategoryTheory.leftDualIso_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.re
fl X
参数：p : ExactPairing X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.leftAdjointMate_id`：leftAdjointMate_id {X : C} [HasLeftDu
al X] : (ᘁ(𝟙 X)) = 𝟙 (ᘁX)
· 使用定理 `CategoryTheory.Iso.mk.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (hom hom_1 : X ⟶ Y) (e_hom : hom = hom_1)   (inv in
v_1 : Y ⟶ X) (e_inv : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftDualIso_id {X Y : C} (p : ExactPairing X Y) : leftDualIso p p = Iso.refl X := by
  ext
  simp only [leftDualIso, Iso.refl_hom, @leftAdjointMate_id]

/-- The right dual of a tensor product is isomorphic to the reversed tensor product of
the right duals. -/
/-
**CategoryTheory.rightDualTensorIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：rightDualTensorIso (X Y : C) [HasRightDual X] [HasRightDual Y] [HasRightDu
al (X otimes Y)] : (X otimes Y)ᘁ ≅ Yᘁ otimes Xᘁ
参数：X Y : C；X otimes Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right dual of a tensor product is isomorphic to the reversed tensor product 
of
the right duals.
-/
def rightDualTensorIso (X Y : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual (X ⊗ Y)] :
    (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ :=
  rightDualIso HasRightDual.exact ExactPairing.tensor

/-- The left dual of a tensor product is isomorphic to the reversed tensor product of
the left duals. -/
/-
**CategoryTheory.leftDualTensorIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：leftDualTensorIso (X Y : C) [HasLeftDual X] [HasLeftDual Y] [HasLeftDual (
X otimes Y)] : leftDual (X otimes Y) ≅ leftDual Y otimes leftDual X
参数：X Y : C；X otimes Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left dual of a tensor product is isomorphic to the reversed tensor product o
f
the left duals.
-/
def leftDualTensorIso (X Y : C) [HasLeftDual X] [HasLeftDual Y]
    [HasLeftDual (X ⊗ Y)] :
    leftDual (X ⊗ Y) ≅ leftDual Y ⊗ leftDual X :=
  leftDualIso HasLeftDual.exact ExactPairing.tensor

/-- A right rigid monoidal category is one in which every object has a right dual. -/
/-
**CategoryTheory.RightRigidCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`
。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.MonoidalCategory C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right rigid monoidal category is one in which every object has a right dual.
-/
class RightRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [rightDual : ∀ X : C, HasRightDual X]

/-- A left rigid monoidal category is one in which every object has a right dual. -/
/-
**CategoryTheory.LeftRigidCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.MonoidalCategory C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left rigid monoidal category is one in which every object has a right dual.
-/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : ∀ X : C, HasLeftDual X]

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
/-
**CategoryTheory.monoidalClosedOfLeftRigidCategory** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：monoidalClosedOfLeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalC
ategory.{v} C] [LeftRigidCategory C] : MonoidalClosed C where closed X
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any left rigid category is monoidal closed, with the internal hom `X ⟶[C] Y = ᘁX
 ⊗ Y`.
This has to be a definition rather than an instance to avoid diamonds, for examp
le between
`category_theory.monoidal_closed.functor_category` and
`CategoryTheory.Monoidal.leftRigidFunctorCategory`. Moreover, in concrete applic
ations there is
often a more useful definition of the internal hom object than `ᘁY ⊗ X`, in whic
h case the monoidal
closed structure shouldn't come the rigid structure (e.g. in the category `FinVe
ct k`, it is more
convenient to define the internal hom as `Y →ₗ[k] X` rather than `ᘁY ⊗ X` even t
hough these are
naturally isomorphic).
-/
def monoidalClosedOfLeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    [LeftRigidCategory C] : MonoidalClosed C where
  closed X := closedOfHasLeftDual X

/-- A rigid monoidal category is a monoidal category which is left rigid and right rigid. -/
/-
**CategoryTheory.RigidCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.MonoidalCategory C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rigid monoidal category is a monoidal category which is left rigid and right r
igid.
-/
class RigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    RightRigidCategory C, LeftRigidCategory C

end CategoryTheory

