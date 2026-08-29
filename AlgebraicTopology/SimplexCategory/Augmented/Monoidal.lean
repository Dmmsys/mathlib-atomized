/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal structure on the augmented simplex category

This file defines a monoidal structure on `AugmentedSimplexCategory`.
The tensor product of objects is characterized by the fact that the initial object `star` is
also the unit, and the fact that `⦋m⦌ ⊗ ⦋n⦌ = ⦋m + n + 1⦌` for `n m : ℕ`.

Through the (not in mathlib) equivalence between `AugmentedSimplexCategory` and the category
of finite ordinals, the tensor products corresponds to ordinal sum.

As the unit of this structure is an initial object, for every `x y : AugmentedSimplexCategory`,
there are maps `AugmentedSimplexCategory.inl x y : x ⟶ x ⊗ y` and
`AugmentedSimplexCategory.inr x y : y ⟶ x ⊗ y`. The main API for working with the tensor product
of maps is given by `AugmentedSimplexCategory.tensorObj_hom_ext`, which characterizes maps
`x ⊗ y ⟶ z` in terms of their composition with these two maps. We also characterize the behaviour
of the associator isomorphism with respect to these maps.

-/

@[expose] public section

namespace AugmentedSimplexCategory

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] CategoryTheory.WithInitial

open CategoryTheory MonoidalCategory
open scoped Simplicial

@[simp]
/--
lemma `eqToHom_toOrderHom` / 引理 `eqToHom_toOrderHom`

English:
lemma eqToHom_toOrderHom
  given: {x y : SimplexCategory} (h : WithInitial.of x = WithInitial.of y)
  proof: SimplexCategory.eqToHom_toOrderHom (by injection h)

中文:
引理 eqToHom_toOrderHom
  条件: {x y : 单纯形范畴} (h : WithInitial.of x = WithInitial.of y)
  证明: SimplexCategory.eqToHom_toOrderHom (by injection h)

Depends on / 依赖: SimplexCategory, SimplexCategory.eqToHom_toOrderHom, eqToHom_toOrderHom, injection
-/
lemma eqToHom_toOrderHom {x y : SimplexCategory} (h : WithInitial.of x = WithInitial.of y) :
    SimplexCategory.Hom.toOrderHom (WithInitial.down <| eqToHom h) =
      (Fin.castOrderIso
        (congrArg (fun t => t + 1) (by injection h with h; rw [h]))).toOrderEmbedding.toOrderHom :=
  SimplexCategory.eqToHom_toOrderHom (by injection h)

-- (Impl. note): This definition could easily be inlined in
-- the definition of `tensorObjOf` below, but having it type check directly as an element
-- of `SimplexCategory` avoids having to sprinkle `WithInitial.down` everywhere.
/--
Definition of `tensorObjOf` / `tensorObjOf` 的定义

English:
abbreviation tensorObjOf
  signature: (m n : SimplexCategory)
  body: .mk (m.len + n.len + 1)

中文:
缩写 tensorObjOf
  签名: (m n : 单纯形范畴)
  定义体: .mk (m.len + n.len + 1)

Depends on / 依赖: m.len, n.len
-/
abbrev tensorObjOf (m n : SimplexCategory) : SimplexCategory := .mk (m.len + n.len + 1)

/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
definition tensorObj
  signature: (m n : AugmentedSimplexCategory)
  body: match m, n with
| .of m, .of n => .of tensorObjOf m n
  | .star, x => x
  | x, .star => x

中文:
定义 tensorObj
  签名: (m n : AugmentedSimplexCategory)
  定义体: match m, n with
| .of m, .of n => .of tensorObjOf m n
  | .star, x => x
  | x, .star => x

Depends on / 依赖: tensorObjOf
-/
def tensorObj (m n : AugmentedSimplexCategory) : AugmentedSimplexCategory :=
  match m, n with
| .of m, .of n => .of tensorObjOf m n
  | .star, x => x
  | x, .star => x

/--
Definition of `tensorHomOf` / `tensorHomOf` 的定义

English:
definition tensorHomOf
  signature: {x₁ y₁ x₂ y₂ : SimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂)
  body: letI f₁ : Fin ((x₁.len + 1) + (x₂.len + 1)) ->o Fin ((y₁.len + 1) + (y₂.len + 1)) :=
    { toFun i :=
        Fin.addCases
          (motive := fun _ => Fin <| (y₁.len + 1) + (y₂.len + 1))
          (fun i => (f₁.toOrderHom i).castAdd _)
          (fun i => (f₂.toOrderHom i).natAdd _)
          i
      monotone' i j h := by
        cases i using Fin.addCases <;>
        cases j using Fin.addCases <;>
        rw [Fin.le_def] at h ⊢ <;>
        simp at h ⊢ <;>
        grind only [OrderHom.apply_mono] }
  (eqToHom (congrArg _ (Nat.succ_add _ _)).symm ≫ (SimplexCategory.mkHom f₁) ≫
    eqToHom (congrArg _ (Nat.succ_add _ _)) : _ ⟶ ⦋y₁.len + y₂.len + 1⦌)

中文:
定义 tensorHomOf
  签名: {x₁ y₁ x₂ y₂ : 单纯形范畴} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂)
  定义体: letI f₁ : Fin ((x₁.len + 1) + (x₂.len + 1)) ->o Fin ((y₁.len + 1) + (y₂.len + 1)) :=
    { toFun i :=
        Fin.addCases
          (motive := fun _ => Fin <| (y₁.len + 1) + (y₂.len + 1))
          (fun i => (f₁.toOrderHom i).castAdd _)
          (fun i => (f₂.toOrderHom i).natAdd _)
          i
      monotone' i j h := by
        cases i using Fin.addCases <;>
        cases j using Fin.addCases <;>
        rw [Fin.le_def] at h ⊢ <;>
        simp at h ⊢ <;>
        grind only [OrderHom.apply_mono] }
  (eqToHom (congrArg _ (Nat.succ_add _ _)).symm ≫ (SimplexCategory.mkHom f₁) ≫
    eqToHom (congrArg _ (Nat.succ_add _ _)) : _ ⟶ ⦋y₁.len + y₂.len + 1⦌)

Depends on / 依赖: Fin.addCases, Fin.le_def, Nat.succ_add, OrderHom, OrderHom.apply_mono, SimplexCategory, SimplexCategory.mkHom, addCases, apply_mono, castAdd, congrA, eqToHom, le_def, monotone, motive, natAdd, succ_add, toOrderHom
-/
def tensorHomOf {x₁ y₁ x₂ y₂ : SimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObjOf x₁ x₂ ⟶ tensorObjOf y₁ y₂ :=
  letI f₁ : Fin ((x₁.len + 1) + (x₂.len + 1)) ->o Fin ((y₁.len + 1) + (y₂.len + 1)) :=
    { toFun i :=
        Fin.addCases
          (motive := fun _ => Fin <| (y₁.len + 1) + (y₂.len + 1))
          (fun i => (f₁.toOrderHom i).castAdd _)
          (fun i => (f₂.toOrderHom i).natAdd _)
          i
      monotone' i j h := by
        cases i using Fin.addCases <;>
        cases j using Fin.addCases <;>
        rw [Fin.le_def] at h ⊢ <;>
        simp at h ⊢ <;>
        grind only [OrderHom.apply_mono] }
  (eqToHom (congrArg _ (Nat.succ_add _ _)).symm ≫ (SimplexCategory.mkHom f₁) ≫
    eqToHom (congrArg _ (Nat.succ_add _ _)) : _ ⟶ ⦋y₁.len + y₂.len + 1⦌)

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂)
  body: match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of _, .of _, .of _, .of _, f₁, f₂ => tensorHomOf f₁ f₂
  | .of _, .of y₁, .star, .of y₂, f₁, _ =>
    f₁ ≫ ((SimplexCategory.mkHom <| (Fin.castAddOrderEmb (y₂.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₁.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .of y₁, .of _, .of y₂, _, f₂ =>
    f₂ ≫ ((SimplexCategory.mkHom <| (Fin.natAddOrderEmb (y₁.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₂.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .star, .of _, .of _, _, f₂ => f₂
  | .of _, .of _, .star, .star, f₁, _ => f₁
  | .star, _, .star, _, _, _ => WithInitial.starInitial.to _

中文:
定义 tensorHom
  签名: {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂)
  定义体: match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of _, .of _, .of _, .of _, f₁, f₂ => tensorHomOf f₁ f₂
  | .of _, .of y₁, .star, .of y₂, f₁, _ =>
    f₁ ≫ ((SimplexCategory.mkHom <| (Fin.castAddOrderEmb (y₂.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₁.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .of y₁, .of _, .of y₂, _, f₂ =>
    f₂ ≫ ((SimplexCategory.mkHom <| (Fin.natAddOrderEmb (y₁.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₂.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .star, .of _, .of _, _, f₂ => f₂
  | .of _, .of _, .star, .star, f₁, _ => f₁
  | .star, _, .star, _, _, _ => WithInitial.starInitial.to _

Depends on / 依赖: Fin.castAddOrderEmb, Fin.natAddOrderEmb, Nat.succ_add, SimplexCategory, SimplexCategory.mkHom, castAddOrderEmb, eqToHom, natAddOrderEmb, succ_add, tensorHomOf, toOrderHom
-/
def tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObj x₁ x₂ ⟶ tensorObj y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of _, .of _, .of _, .of _, f₁, f₂ => tensorHomOf f₁ f₂
  | .of _, .of y₁, .star, .of y₂, f₁, _ =>
    f₁ ≫ ((SimplexCategory.mkHom <| (Fin.castAddOrderEmb (y₂.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₁.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .of y₁, .of _, .of y₂, _, f₂ =>
    f₂ ≫ ((SimplexCategory.mkHom <| (Fin.natAddOrderEmb (y₁.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₂.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .star, .of _, .of _, _, f₂ => f₂
  | .of _, .of _, .star, .star, f₁, _ => f₁
  | .star, _, .star, _, _, _ => WithInitial.starInitial.to _

/--
Definition of `tensorUnit` / `tensorUnit` 的定义

English:
abbreviation tensorUnit
  signature: : AugmentedSimplexCategory
  body: WithInitial.star

中文:
缩写 tensorUnit
  签名: : AugmentedSimplexCategory
  定义体: WithInitial.star

Depends on / 依赖: WithInitial, WithInitial.star
-/
abbrev tensorUnit : AugmentedSimplexCategory := WithInitial.star

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (x y z : AugmentedSimplexCategory)
  body: match x, y, z with
  | .of x, .of y, .of z =>
    eqToIso (congrArg (fun j => WithInitial.of <| SimplexCategory.mk j)
      (by simp +arith))
  | .star, .star, .star => Iso.refl _
  | .star, .of _, .star => Iso.refl _
  | .star, .star, .of _ => Iso.refl _
  | .star, .of _, .of _ => Iso.refl _
  | .of _, .star, .star => Iso.refl _
  | .of _, .star, .of _ => Iso.refl _
  | .of _, .of _, .star => Iso.refl _

中文:
定义 associator
  签名: (x y z : AugmentedSimplexCategory)
  定义体: match x, y, z with
  | .of x, .of y, .of z =>
    eqToIso (congrArg (fun j => WithInitial.of <| SimplexCategory.mk j)
      (by simp +arith))
  | .star, .star, .star => Iso.refl _
  | .star, .of _, .star => Iso.refl _
  | .star, .star, .of _ => Iso.refl _
  | .star, .of _, .of _ => Iso.refl _
  | .of _, .star, .star => Iso.refl _
  | .of _, .star, .of _ => Iso.refl _
  | .of _, .of _, .star => Iso.refl _

Depends on / 依赖: Iso.refl, SimplexCategory, SimplexCategory.mk, WithInitial, WithInitial.of, eqToIso
-/
def associator (x y z : AugmentedSimplexCategory) :
    tensorObj (tensorObj x y) z ≅ tensorObj x (tensorObj y z) :=
  match x, y, z with
  | .of x, .of y, .of z =>
    eqToIso (congrArg (fun j => WithInitial.of <| SimplexCategory.mk j)
      (by simp +arith))
  | .star, .star, .star => Iso.refl _
  | .star, .of _, .star => Iso.refl _
  | .star, .star, .of _ => Iso.refl _
  | .star, .of _, .of _ => Iso.refl _
  | .of _, .star, .star => Iso.refl _
  | .of _, .star, .of _ => Iso.refl _
  | .of _, .of _, .star => Iso.refl _

/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (x : AugmentedSimplexCategory)
  body: match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

中文:
定义 leftUnitor
  签名: (x : AugmentedSimplexCategory)
  定义体: match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

Depends on / 依赖: Iso.refl
-/
def leftUnitor (x : AugmentedSimplexCategory) :
    tensorObj tensorUnit x ≅ x :=
  match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (x : AugmentedSimplexCategory)
  body: match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

中文:
定义 rightUnitor
  签名: (x : AugmentedSimplexCategory)
  定义体: match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

Depends on / 依赖: Iso.refl
-/
def rightUnitor (x : AugmentedSimplexCategory) :
    tensorObj x tensorUnit ≅ x :=
  match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategoryStruct AugmentedSimplexCategory
  body: tensorObj
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft x _ _ f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)

@[local simp]

中文:
实例 :
  签名: 幺半群范畴结构 AugmentedSimplexCategory
  定义体: tensorObj
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft x _ _ f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)

@[local simp]

Depends on / 依赖: tensorObj
-/
instance : MonoidalCategoryStruct AugmentedSimplexCategory where
  tensorObj := tensorObj
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft x _ _ f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)

@[local simp]
/--
lemma `id_tensorHom` / 引理 `id_tensorHom`

English:
lemma id_tensorHom
  statement: (x : AugmentedSimplexCategory) {y₁ y₂ : AugmentedSimplexCategory}
  proof: rfl

@[local simp]

中文:
引理 id_tensorHom
  结论: (x : AugmentedSimplexCategory) {y₁ y₂ : AugmentedSimplexCategory}
  证明: rfl

@[local simp]
-/
lemma id_tensorHom (x : AugmentedSimplexCategory) {y₁ y₂ : AugmentedSimplexCategory}
    (f : y₁ ⟶ y₂) : 𝟙 x otimesₘ f = x ◁ f :=
  rfl

@[local simp]
/--
lemma `tensorHom_id` / 引理 `tensorHom_id`

English:
lemma tensorHom_id
  statement: {x₁ x₂ : AugmentedSimplexCategory} (y : AugmentedSimplexCategory)
  proof: rfl

@[local simp]

中文:
引理 tensorHom_id
  结论: {x₁ x₂ : AugmentedSimplexCategory} (y : AugmentedSimplexCategory)
  证明: rfl

@[local simp]
-/
lemma tensorHom_id {x₁ x₂ : AugmentedSimplexCategory} (y : AugmentedSimplexCategory)
    (f : x₁ ⟶ x₂) : f otimesₘ 𝟙 y = f ▷ y :=
  rfl

@[local simp]
/--
lemma `whiskerLeft_id_star` / 引理 `whiskerLeft_id_star`

English:
lemma whiskerLeft_id_star
  given: {x : AugmentedSimplexCategory}
  statement: x ◁ 𝟙 .star = 𝟙 _
  proof: by
  cases x <;>
  rfl

@[local simp]

中文:
引理 whiskerLeft_id_star
  条件: {x : AugmentedSimplexCategory}
  结论: x ◁ 𝟙 .star = 𝟙 _
  证明: by
  cases x <;>
  rfl

@[local simp]
-/
lemma whiskerLeft_id_star {x : AugmentedSimplexCategory} : x ◁ 𝟙 .star = 𝟙 _ := by
  cases x <;>
  rfl

@[local simp]
/--
lemma `id_star_whiskerRight` / 引理 `id_star_whiskerRight`

English:
lemma id_star_whiskerRight
  given: {x : AugmentedSimplexCategory}
  statement: 𝟙 WithInitial.star ▷ x = 𝟙 _
  proof: by
  cases x <;>
  rfl

中文:
引理 id_star_whiskerRight
  条件: {x : AugmentedSimplexCategory}
  结论: 𝟙 WithInitial.star ▷ x = 𝟙 _
  证明: by
  cases x <;>
  rfl
-/
lemma id_star_whiskerRight {x : AugmentedSimplexCategory} : 𝟙 WithInitial.star ▷ x = 𝟙 _ := by
  cases x <;>
  rfl

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: (x y : AugmentedSimplexCategory)
  body: (ρ_ x).inv ≫ _ ◁ (WithInitial.starInitial.to y)

中文:
定义 inl
  签名: (x y : AugmentedSimplexCategory)
  定义体: (ρ_ x).inv ≫ _ ◁ (WithInitial.starInitial.to y)

Depends on / 依赖: WithInitial, WithInitial.starInitial.to, starInitial
-/
def inl (x y : AugmentedSimplexCategory) : x ⟶ x otimes y :=
  (ρ_ x).inv ≫ _ ◁ (WithInitial.starInitial.to y)

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: (x y : AugmentedSimplexCategory)
  body: (fun_ y).inv ≫ (WithInitial.starInitial.to x) ▷ _

中文:
定义 inr
  签名: (x y : AugmentedSimplexCategory)
  定义体: (fun_ y).inv ≫ (WithInitial.starInitial.to x) ▷ _

Depends on / 依赖: WithInitial, WithInitial.starInitial.to, fun_, starInitial
-/
def inr (x y : AugmentedSimplexCategory) : y ⟶ x otimes y :=
  (fun_ y).inv ≫ (WithInitial.starInitial.to x) ▷ _

/--
Definition of `inl'` / `inl'` 的定义

English:
abbreviation inl'
  signature: (x y : SimplexCategory)
  body: WithInitial.down inl (.of x) (.of y)

中文:
缩写 inl'
  签名: (x y : 单纯形范畴)
  定义体: WithInitial.down inl (.of x) (.of y)

Depends on / 依赖: WithInitial, WithInitial.down
-/
abbrev inl' (x y : SimplexCategory) : x ⟶ tensorObjOf x y := WithInitial.down inl (.of x) (.of y)

/--
Definition of `inr'` / `inr'` 的定义

English:
abbreviation inr'
  signature: (x y : SimplexCategory)
  body: WithInitial.down inr (.of x) (.of y)

中文:
缩写 inr'
  签名: (x y : 单纯形范畴)
  定义体: WithInitial.down inr (.of x) (.of y)

Depends on / 依赖: WithInitial, WithInitial.down
-/
abbrev inr' (x y : SimplexCategory) : y ⟶ tensorObjOf x y := WithInitial.down inr (.of x) (.of y)

/--
lemma `inl'_eval` / 引理 `inl'_eval`

English:
lemma inl'_eval
  given: (x y : SimplexCategory) (i : Fin (x.len + 1))
  proof: by
  ext
  simp [inl', inl, MonoidalCategoryStruct.rightUnitor, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.tensorUnit, MonoidalCategoryStruct.tensorObj,
    tensorUnit, tensorHom, WithInitial.down, rightUnitor, tensorObj, CategoryStruct.id,
    CategoryStruct.comp, WithInitial.comp, WithInitial.id,
    OrderEmbedding.toOrderHom]

中文:
引理 inl'_eval
  条件: (x y : 单纯形范畴) (i : 有限集 (x.len + 1))
  证明: by
  ext
  simp [inl', inl, MonoidalCategoryStruct.rightUnitor, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.tensorUnit, MonoidalCategoryStruct.tensorObj,
    tensorUnit, tensorHom, WithInitial.down, rightUnitor, tensorObj, CategoryStruct.id,
    CategoryStruct.comp, WithInitial.comp, WithInitial.id,
    OrderEmbedding.toOrderHom]
-/
lemma inl'_eval (x y : SimplexCategory) (i : Fin (x.len + 1)) :
    (inl' x y).toOrderHom i = (i.castAdd _).cast (Nat.succ_add x.len (y.len + 1)) := by
  ext
  simp [inl', inl, MonoidalCategoryStruct.rightUnitor, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.tensorUnit, MonoidalCategoryStruct.tensorObj,
    tensorUnit, tensorHom, WithInitial.down, rightUnitor, tensorObj, CategoryStruct.id,
    CategoryStruct.comp, WithInitial.comp, WithInitial.id,
    OrderEmbedding.toOrderHom]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inr'_eval` / 引理 `inr'_eval`

English:
lemma inr'_eval
  given: (x y : SimplexCategory) (i : Fin (y.len + 1))
  proof: by
  dsimp [inr', inr, MonoidalCategoryStruct.leftUnitor, MonoidalCategoryStruct.whiskerRight,
    tensorHom, WithInitial.down, leftUnitor, tensorObj]
  ext
  simp [OrderEmbedding.toOrderHom]

中文:
引理 inr'_eval
  条件: (x y : 单纯形范畴) (i : 有限集 (y.len + 1))
  证明: by
  dsimp [inr', inr, MonoidalCategoryStruct.leftUnitor, MonoidalCategoryStruct.whiskerRight,
    tensorHom, WithInitial.down, leftUnitor, tensorObj]
  ext
  simp [OrderEmbedding.toOrderHom]
-/
lemma inr'_eval (x y : SimplexCategory) (i : Fin (y.len + 1)) :
    (inr' x y).toOrderHom i = (i.natAdd _).cast (Nat.succ_add x.len (y.len + 1)) := by
  dsimp [inr', inr, MonoidalCategoryStruct.leftUnitor, MonoidalCategoryStruct.whiskerRight,
    tensorHom, WithInitial.down, leftUnitor, tensorObj]
  ext
  simp [OrderEmbedding.toOrderHom]

/-- We can characterize morphisms out of a tensor product via their precomposition with `inl` and
`inr`. -/
@[ext]
/--
theorem `tensorObj_hom_ext` / 定理 `tensorObj_hom_ext`

English:
theorem tensorObj_hom_ext
  statement: {x y z : AugmentedSimplexCategory} (f g : x otimes y ⟶ z)
  proof: match x, y, z, f, g with
  | .of x, .of y, .of z, f, g => by
    change (tensorObjOf x y) ⟶ z at f g
    change inl' _ _ ≫ f = inl' _ _ ≫ g at h₁
    change inr' _ _ ≫ f = inr' _ _ ≫ g at h₂
    ext i
    let j : Fin ((x.len + 1) + (y.len + 1)) := i.cast (Nat.succ_add x.len (y.len + 1)).symm
    have : i = j.cast (Nat.succ_add x.len (y.len + 1)) := rfl
    rw [this]
    cases j using Fin.addCases (m := x.len + 1) (n := y.len + 1) with
    | left j =>
      rw [SimplexCategory.Hom.ext_iff]; rw [OrderHom.ext_iff] at h₁
      simpa [← inl'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₁ j
    | right j =>
      rw [SimplexCategory.Hom.ext_iff]; rw [OrderHom.ext_iff] at h₂
      simpa [← inr'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₂ j
  | .of x, .star, .of z, f, g => by
      simp only [inl, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        whiskerLeft_id_star] at h₁
      simpa [Category.id_comp f, Category.id_comp g] using h₁
  | .star, .of y, .of z, f, g => by
      simp only [inr, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        id_star_whiskerRight] at h₂
      simpa [Category.id_comp f, Category.id_comp g] using h₂
  | .star, .star, .of z, f, g => rfl
  | .star, .star, .star, f, g => rfl

中文:
定理 tensorObj_hom_ext
  结论: {x y z : AugmentedSimplexCategory} (f g : x otimes y ⟶ z)
  证明: match x, y, z, f, g with
  | .of x, .of y, .of z, f, g => by
    change (tensorObjOf x y) ⟶ z at f g
    change inl' _ _ ≫ f = inl' _ _ ≫ g at h₁
    change inr' _ _ ≫ f = inr' _ _ ≫ g at h₂
    ext i
    let j : Fin ((x.len + 1) + (y.len + 1)) := i.cast (Nat.succ_add x.len (y.len + 1)).symm
    have : i = j.cast (Nat.succ_add x.len (y.len + 1)) := rfl
    rw [this]
    cases j using Fin.addCases (m := x.len + 1) (n := y.len + 1) with
    | left j =>
      rw [SimplexCategory.Hom.ext_iff]; rw [OrderHom.ext_iff] at h₁
      simpa [← inl'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₁ j
    | right j =>
      rw [SimplexCategory.Hom.ext_iff]; rw [OrderHom.ext_iff] at h₂
      simpa [← inr'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₂ j
  | .of x, .star, .of z, f, g => by
      simp only [inl, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        whiskerLeft_id_star] at h₁
      simpa [Category.id_comp f, Category.id_comp g] using h₁
  | .star, .of y, .of z, f, g => by
      simp only [inr, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        id_star_whiskerRight] at h₂
      simpa [Category.id_comp f, Category.id_comp g] using h₂
  | .star, .star, .of z, f, g => rfl
  | .star, .star, .star, f, g => rfl

Depends on / 依赖: Fin.addCases, Nat.succ_add, OrderHom, OrderHom.ext_iff, SimplexCategory, SimplexCategory.Hom.ext_iff, _eval, addCases, ext_iff, i.cast, j.cast, succ_add, tensorObjOf, x.len, y.len
-/
theorem tensorObj_hom_ext {x y z : AugmentedSimplexCategory} (f g : x otimes y ⟶ z)
    (h₁ : inl _ _ ≫ f = inl _ _ ≫ g)
    (h₂ : inr _ _ ≫ f = inr _ _ ≫ g) : f = g :=
  match x, y, z, f, g with
  | .of x, .of y, .of z, f, g => by
    change (tensorObjOf x y) ⟶ z at f g
    change inl' _ _ ≫ f = inl' _ _ ≫ g at h₁
    change inr' _ _ ≫ f = inr' _ _ ≫ g at h₂
    ext i
    let j : Fin ((x.len + 1) + (y.len + 1)) := i.cast (Nat.succ_add x.len (y.len + 1)).symm
    have : i = j.cast (Nat.succ_add x.len (y.len + 1)) := rfl
    rw [this]
    cases j using Fin.addCases (m := x.len + 1) (n := y.len + 1) with
    | left j =>
      rw [SimplexCategory.Hom.ext_iff]; rw [OrderHom.ext_iff] at h₁
      simpa [← inl'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₁ j
    | right j =>
      rw [SimplexCategory.Hom.ext_iff]; rw [OrderHom.ext_iff] at h₂
      simpa [← inr'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₂ j
  | .of x, .star, .of z, f, g => by
      simp only [inl, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        whiskerLeft_id_star] at h₁
      simpa [Category.id_comp f, Category.id_comp g] using h₁
  | .star, .of y, .of z, f, g => by
      simp only [inr, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        id_star_whiskerRight] at h₂
      simpa [Category.id_comp f, Category.id_comp g] using h₂
  | .star, .star, .of z, f, g => rfl
  | .star, .star, .star, f, g => rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inl_comp_tensorHom` / 引理 `inl_comp_tensorHom`

English:
lemma inl_comp_tensorHom
  statement: {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
  proof: match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inl' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₁ ≫ inl' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inl'_eval x₁ x₂ i
have e₂ := inl'_eval y₁ y₂ (WithInitial.down f₁).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁]; rw [e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i => Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i => Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.castAdd (x₂.len + 1) i)
      rw [Fin.addCases_left]
    rfl
  | _, _, .star, _, f₁, f₂ => by cat_disch
  | .star, _, _, _, _, _ => rfl

中文:
引理 inl_comp_tensorHom
  结论: {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
  证明: match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inl' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₁ ≫ inl' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inl'_eval x₁ x₂ i
have e₂ := inl'_eval y₁ y₂ (WithInitial.down f₁).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁]; rw [e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i => Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i => Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.castAdd (x₂.len + 1) i)
      rw [Fin.addCases_left]
    rfl
  | _, _, .star, _, f₁, f₂ => by cat_disch
  | .star, _, _, _, _, _ => rfl

Depends on / 依赖: Fin.castOrderIso_apply, Fin.cast_cast, OrderEmbedding, OrderEmbedding.toOrderHom_coe, OrderIso, OrderIso.coe_toOrderEmbedding, SimplexCategory, SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk, WithInitial, WithInitial.down, _eval, castOrderIso_apply, cast_cast, coe_toOrderEmbedding, eqToHom_toOrderHom, len_mk, tensorHomOf, toOrderHom, toOrderHom_coe
-/
lemma inl_comp_tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : inl x₁ x₂ ≫ (f₁ otimesₘ f₂) = f₁ ≫ inl y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inl' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₁ ≫ inl' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inl'_eval x₁ x₂ i
have e₂ := inl'_eval y₁ y₂ (WithInitial.down f₁).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁]; rw [e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i => Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i => Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.castAdd (x₂.len + 1) i)
      rw [Fin.addCases_left]
    rfl
  | _, _, .star, _, f₁, f₂ => by cat_disch
  | .star, _, _, _, _, _ => rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inr_comp_tensorHom` / 引理 `inr_comp_tensorHom`

English:
lemma inr_comp_tensorHom
  statement: {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
  proof: match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inr' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₂ ≫ inr' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inr'_eval x₁ x₂ i
have e₂ := inr'_eval y₁ y₂ (WithInitial.down f₂).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁]; rw [e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      Nat.succ_eq_add_one, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i => Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i => Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.natAdd (x₁.len + 1) i)
      rw [Fin.addCases_right]
    rfl
  | .star, _, _, _, f₁, f₂ => by cat_disch
  | _, _, .star, _, _, _ => rfl

中文:
引理 inr_comp_tensorHom
  结论: {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
  证明: match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inr' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₂ ≫ inr' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inr'_eval x₁ x₂ i
have e₂ := inr'_eval y₁ y₂ (WithInitial.down f₂).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁]; rw [e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      Nat.succ_eq_add_one, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i => Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i => Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.natAdd (x₁.len + 1) i)
      rw [Fin.addCases_right]
    rfl
  | .star, _, _, _, f₁, f₂ => by cat_disch
  | _, _, .star, _, _, _ => rfl

Depends on / 依赖: Fin.castOrderIso, Nat.succ_eq_add_one, OrderEmbedding, OrderEmbedding.toOrderHom_coe, OrderIso, OrderIso.coe_toOrderEmbedding, SimplexCategory, SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk, WithInitial, WithInitial.down, _eval, castOrderIso, coe_toOrderEmbedding, eqToHom_toOrderHom, len_mk, succ_eq_add_one, tensorHomOf, toOrderHom, toOrderHom_coe
-/
lemma inr_comp_tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : inr x₁ x₂ ≫ (f₁ otimesₘ f₂) = f₂ ≫ inr y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inr' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₂ ≫ inr' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inr'_eval x₁ x₂ i
have e₂ := inr'_eval y₁ y₂ (WithInitial.down f₂).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁]; rw [e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      Nat.succ_eq_add_one, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i => Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i => Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.natAdd (x₁.len + 1) i)
      rw [Fin.addCases_right]
    rfl
  | .star, _, _, _, f₁, f₂ => by cat_disch
  | _, _, .star, _, _, _ => rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_comp_associator` / 引理 `inr_comp_associator`

English:
lemma inr_comp_associator
  given: (x y z : AugmentedSimplexCategory)
  proof: match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ WithInitial.down _ = inr' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    simp only [eqToHom_toOrderHom, SimplexCategory.len_mk, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
    have e₁ := inr'_eval (tensorObjOf x y) z i
    have e₂ := inr'_eval y z i
have e₃ := inr'_eval x (tensorObjOf y z)
Fin.cast (by simp +arith) i.natAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁]; rw [e₂]; rw [e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

中文:
引理 inr_comp_associator
  条件: (x y z : AugmentedSimplexCategory)
  证明: match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ WithInitial.down _ = inr' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    simp only [eqToHom_toOrderHom, SimplexCategory.len_mk, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
    have e₁ := inr'_eval (tensorObjOf x y) z i
    have e₂ := inr'_eval y z i
have e₃ := inr'_eval x (tensorObjOf y z)
Fin.cast (by simp +arith) i.natAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁]; rw [e₂]; rw [e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

Depends on / 依赖: Fin.cast, Fin.castOrderIso_apply, MonoidalCategoryStruct, MonoidalCategoryStruct.associator, OrderEmbedding, OrderEmbedding.toOrderHom_coe, OrderIso, OrderIso.coe_toOrderEmbedding, SimplexCategory, SimplexCategory.len_, SimplexCategory.len_mk, WithInitial, WithInitial.down, _eval, associator, castOrderIso_apply, coe_toOrderEmbedding, eqToHom_toOrderHom, i.natAdd, len_
-/
lemma inr_comp_associator (x y z : AugmentedSimplexCategory) :
    inr _ _ ≫ (α_ x y z).hom = inr _ _ ≫ inr _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ WithInitial.down _ = inr' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    simp only [eqToHom_toOrderHom, SimplexCategory.len_mk, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
    have e₁ := inr'_eval (tensorObjOf x y) z i
    have e₂ := inr'_eval y z i
have e₃ := inr'_eval x (tensorObjOf y z)
Fin.cast (by simp +arith) i.natAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁]; rw [e₂]; rw [e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_comp_inl_comp_associator` / 引理 `inl_comp_inl_comp_associator`

English:
lemma inl_comp_inl_comp_associator
  given: (x y z : AugmentedSimplexCategory)
  proof: match x, y, z with
  | .of x, .of y, .of z => by
    change inl' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval x y i
    have e₂ := inl'_eval x (tensorObjOf y z) i
have e₃ := inl'_eval (tensorObjOf x y) z Fin.cast (by simp +arith) i.castAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁]; rw [e₂]; rw [e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

中文:
引理 inl_comp_inl_comp_associator
  条件: (x y z : AugmentedSimplexCategory)
  证明: match x, y, z with
  | .of x, .of y, .of z => by
    change inl' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval x y i
    have e₂ := inl'_eval x (tensorObjOf y z) i
have e₃ := inl'_eval (tensorObjOf x y) z Fin.cast (by simp +arith) i.castAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁]; rw [e₂]; rw [e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

Depends on / 依赖: Fin.cast, MonoidalCategoryStruct, MonoidalCategoryStruct.associator, SimplexCategory, SimplexCategory.len_mk, WithInitial, WithInitial.down, _eval, associator, castAdd, cat_disch, i.castAdd, len_mk, tensorObjOf, y.len
-/
lemma inl_comp_inl_comp_associator (x y z : AugmentedSimplexCategory) :
    inl _ _ ≫ inl _ _ ≫ (α_ x y z).hom = inl _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change inl' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval x y i
    have e₂ := inl'_eval x (tensorObjOf y z) i
have e₃ := inl'_eval (tensorObjOf x y) z Fin.cast (by simp +arith) i.castAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁]; rw [e₂]; rw [e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_comp_inl_comp_associator` / 引理 `inr_comp_inl_comp_associator`

English:
lemma inr_comp_inl_comp_associator
  given: (x y z : AugmentedSimplexCategory)
  proof: match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval y z i
    have e₂ := inr'_eval x y i
have e₃ := inl'_eval (tensorObjOf x y) z Fin.cast (by simp +arith) i.natAdd (x.len + 1)
have e₄ := inr'_eval x (tensorObjOf y z) Fin.cast (by simp +arith) i.castAdd (z.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃ e₄
    rw [e₁]; rw [e₂]; rw [e₃]; rw [e₄]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

中文:
引理 inr_comp_inl_comp_associator
  条件: (x y z : AugmentedSimplexCategory)
  证明: match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval y z i
    have e₂ := inr'_eval x y i
have e₃ := inl'_eval (tensorObjOf x y) z Fin.cast (by simp +arith) i.natAdd (x.len + 1)
have e₄ := inr'_eval x (tensorObjOf y z) Fin.cast (by simp +arith) i.castAdd (z.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃ e₄
    rw [e₁]; rw [e₂]; rw [e₃]; rw [e₄]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

Depends on / 依赖: Fin.cast, MonoidalCategoryStruct, MonoidalCategoryStruct.associator, SimplexCategory, SimplexCategory.len_mk, WithInitial, WithInitial.down, _eval, associator, castAdd, i.castAdd, i.natAdd, len_mk, natAdd, tensorObjOf, x.len, z.len
-/
lemma inr_comp_inl_comp_associator (x y z : AugmentedSimplexCategory) :
    inr _ _ ≫ inl _ _ ≫ (α_ x y z).hom = inl _ _ ≫ inr _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval y z i
    have e₂ := inr'_eval x y i
have e₃ := inl'_eval (tensorObjOf x y) z Fin.cast (by simp +arith) i.natAdd (x.len + 1)
have e₄ := inr'_eval x (tensorObjOf y z) Fin.cast (by simp +arith) i.castAdd (z.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃ e₄
    rw [e₁]; rw [e₂]; rw [e₃]; rw [e₄]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

/--
theorem `tensorHom_comp_tensorHom` / 定理 `tensorHom_comp_tensorHom`

English:
theorem tensorHom_comp_tensorHom
  statement: {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory}
  proof: by
  cat_disch

中文:
定理 tensorHom_comp_tensorHom
  结论: {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem tensorHom_comp_tensorHom {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) (g₁ : y₁ ⟶ z₁) (g₂ : y₂ ⟶ z₂) :
    (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂) := by
  cat_disch

/--
theorem `tensor_id` / 定理 `tensor_id`

English:
theorem tensor_id
  given: (x y : AugmentedSimplexCategory)
  statement: (𝟙 x) otimesₘ (𝟙 y) = 𝟙 (x otimes y)
  proof: by
  ext
  · simpa [inl, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (𝟙 x) (WithInitial.starInitial.to y) (𝟙 x) (𝟙 y))
  · simpa [inr, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (WithInitial.starInitial.to x) (𝟙 y) (𝟙 x) (𝟙 y))

中文:
定理 tensor_id
  条件: (x y : AugmentedSimplexCategory)
  结论: (𝟙 x) otimesₘ (𝟙 y) = 𝟙 (x otimes y)
  证明: by
  ext
  · simpa [inl, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (𝟙 x) (WithInitial.starInitial.to y) (𝟙 x) (𝟙 y))
  · simpa [inr, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (WithInitial.starInitial.to x) (𝟙 y) (𝟙 x) (𝟙 y))

Depends on / 依赖: MonoidalCategoryStruct, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight, WithInitial, WithInitial.starInitial.to, starInitial, tensorHom_comp_tensorHom, whiskerLeft, whiskerRight
-/
theorem tensor_id (x y : AugmentedSimplexCategory) : (𝟙 x) otimesₘ (𝟙 y) = 𝟙 (x otimes y) := by
  ext
  · simpa [inl, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (𝟙 x) (WithInitial.starInitial.to y) (𝟙 x) (𝟙 y))
  · simpa [inr, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (WithInitial.starInitial.to x) (𝟙 y) (𝟙 x) (𝟙 y))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory AugmentedSimplexCategory
  body: MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (pentagon := fun w x y z => by ext <;> simp [-id_tensorHom, -tensorHom_id])

中文:
实例 :
  签名: 幺半群范畴 AugmentedSimplexCategory
  定义体: MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (pentagon := fun w x y z => by ext <;> simp [-id_tensorHom, -tensorHom_id])

Depends on / 依赖: MonoidalCategory, MonoidalCategory.ofTensorHom, id_tensorHom, id_tensorHom_id, ofTensorHom, pentagon, tensorHom_comp_tensorHom, tensorHom_id, tensor_id
-/
instance : MonoidalCategory AugmentedSimplexCategory :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (pentagon := fun w x y z => by ext <;> simp [-id_tensorHom, -tensorHom_id])

end AugmentedSimplexCategory
