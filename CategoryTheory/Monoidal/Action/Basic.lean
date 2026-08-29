/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!

# Actions from a monoidal category on a category

Given a monoidal category `C`, and a category `D`, we define a left action of
`C` on `D` as the data of an object `c ⊙ₗ d` of `D` for every
`c : C` and `d : D`, as well as the data required to turn `- ⊙ₗ -` into
a bifunctor, along with structure natural isomorphisms
`(- ⊗ -) ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -` and `𝟙_ C ⊙ₗ - ≅ -`, subject to coherence conditions.

We also define right actions, for these, the notation for the action of `c`
on `d` is `d ⊙ᵣ c`, and the structure isomorphisms are of the form
`- ⊙ᵣ (- ⊗ -) ≅ (- ⊙ᵣ -) ⊙ᵣ -` and `- ⊙ₗ 𝟙_ C ≅ -`.


## References
* [Janelidze, G, and Kelly, G.M., *A note on actions of a monoidal category*][JanelidzeKelly2001]

## TODOs/Projects
* Equivalence between actions of `C` on `D` and pseudofunctors from the
  classifying bicategory of `C` to `Cat`.
* Left/Right Modules in `D` over a monoid object in `C`.
  Equivalence with `Mod_` when `D` is `C`. Bimodules objects.
* Given a monad `M` on `C`, equivalence between `Algebra M`, and modules in `C`
  on `M.toMon : Mon (C ⥤ C)`.
* Canonical left action of `Type u` on `u`-small cocomplete categories via the
  copower.

-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category* C] [Category* D]
/--
Definition of `MonoidalLeftActionStruct` / `MonoidalLeftActionStruct` 的定义

English:
class MonoidalLeftActionStruct
  parameters: [MonoidalCategoryStruct C]
  axioms and operations (6):
    - actionObj : C -> D -> D
    - actionHomLeft({c c' : C} (f : c ⟶ c') (d : D)) : actionObj c d ⟶ actionObj c' d
    - actionHomRight((c : C) {d d' : D} (f : d ⟶ d')) : actionObj c d ⟶ actionObj c d'
    - actionHom({c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d')) : actionObj c d ⟶ actionObj c' d'  [default: actionHomLeft f d ≫ actionHomRight c' g]
    - actionAssocIso((c c' : C) (d : D)) : actionObj (c otimes c') d ≅ actionObj c (actionObj c' d)
    - actionUnitIso((d : D)) : actionObj (𝟙_ C) d ≅ d

中文:
类 MonoidalLeftActionStruct
  参数: [MonoidalCategoryStruct C]
  公理与运算 (6 个):
    - actionObj : C -> D -> D
    - actionHomLeft({c c' : C} (f : c ⟶ c') (d : D)) : actionObj c d ⟶ actionObj c' d
    - actionHomRight((c : C) {d d' : D} (f : d ⟶ d')) : actionObj c d ⟶ actionObj c d'
    - actionHom({c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d')) : actionObj c d ⟶ actionObj c' d'  [默认: actionHomLeft f d ≫ actionHomRight c' g]
    - actionAssocIso((c c' : C) (d : D)) : actionObj (c otimes c') d ≅ actionObj c (actionObj c' d)
    - actionUnitIso((d : D)) : actionObj (𝟙_ C) d ≅ d

Depends on / 依赖: actionHomLeft, actionHomRight
-/
class MonoidalLeftActionStruct [MonoidalCategoryStruct C] where
  /-- The left action on objects. This is denoted `c ⊙ₗ d`. -/
  actionObj : C -> D -> D
  /-- The left action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.map f).app d`. This is denoted `f ⊵ₗ d`. -/
  actionHomLeft {c c' : C} (f : c ⟶ c') (d : D) :
    actionObj c d ⟶ actionObj c' d
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.obj c).map f`. This is denoted `c ⊴ₗ f`. -/
  actionHomRight (c : C) {d d' : D} (f : d ⟶ d') :
    actionObj c d ⟶ actionObj c d'
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    actionObj c d ⟶ actionObj c' d' := actionHomLeft f d ≫ actionHomRight c' g
  /-- The structural isomorphism `(c ⊗ c') ⊙ₗ d ≅ c ⊙ₗ (c' ⊙ₗ d)`. -/
  actionAssocIso (c c' : C) (d : D) :
    actionObj (c otimes c') d ≅ actionObj c (actionObj c' d)
  /-- The structural isomorphism between `𝟙_ C ⊙ₗ d` and `d`. -/
  actionUnitIso (d : D) : actionObj (𝟙_ C) d ≅ d

namespace MonoidalLeftAction

export MonoidalLeftActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`. -/
scoped infixr:70 " ⊙ₗ " => MonoidalLeftActionStruct.actionObj

/-- Notation for `actionHomLeft`, the action of `C` on morphisms in `D`. -/
scoped infixr:81 " ⊵ₗ " => MonoidalLeftActionStruct.actionHomLeft

/-- Notation for `actionHomRight`, the action of morphism in `C` on `D`. -/
scoped infixr:81 " ⊴ₗ " => MonoidalLeftActionStruct.actionHomRight

/-- Notation for `actionHom`, the bifunctorial action of morphisms in `C` and
`D` on `- ⊙ₗ -`. -/
scoped infixr:70 " ⊙ₗₘ " => MonoidalLeftActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ⊗ - ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -`. -/
scoped notation "αₗ " => MonoidalLeftActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`. -/
scoped notation "funₗ " => MonoidalLeftActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`,
allowing one to specify the acting category. -/
scoped notation "funₗ["J"]" => MonoidalLeftActionStruct.actionUnitIso (C := J)

end MonoidalLeftAction

open scoped MonoidalLeftAction in
/--
Definition of `MonoidalLeftAction` / `MonoidalLeftAction` 的定义

English:
class MonoidalLeftAction
  parameters: [MonoidalCategory C]
  axioms and operations (11):
    - actionHom_def({c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d')) : f ⊙ₗₘ g = f ⊵ₗ d ≫ c' ⊴ₗ g  [default: by cat_disch]
    - actionHomRight_id((c : C) (d : D)) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d)  [default: by cat_disch]
    - id_actionHomLeft((c : C) (d : D)) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d)  [default: by cat_disch]
    - actionHom_comp({c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'') (g₁ : d ⟶ d') (g₂ : d' ⟶ d'')) : (f₁ ≫ f₂) ⊙ₗₘ (g₁ ≫ g₂) = (f₁ ⊙ₗₘ g₁) ≫ (f₂ ⊙ₗₘ g₂)  [default: by cat_disch]
    - actionAssocIso_hom_naturality({c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂)) : ((f otimesₘ g) ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).hom = (αₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗₘ g ⊙ₗₘ h)  [default: by cat_disch]
    - actionUnitIso_hom_naturality({d d' : D} (f : d ⟶ d')) : (funₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (funₗ d').hom  [default: by cat_disch]
    - whiskerLeft_actionHomLeft((c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D)) : (c ◁ f) ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (αₗ _ _ _).inv  [default: by cat_disch]
    - whiskerRight_actionHomLeft({c c' : C} (c'' : C) (f : c ⟶ c') (d : D)) : (f ▷ c'') ⊵ₗ d = (αₗ c c'' d).hom ≫ f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (αₗ c' c'' d).inv  [default: by cat_disch]
    - associator_actionHom((c₁ c₂ c₃ : C) (d : D)) : (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (αₗ c₁ (c₂ otimes c₃) d).hom ≫ c₁ ⊴ₗ (αₗ c₂ c₃ d).hom = (αₗ (c₁ otimes c₂ : C) c₃ d).hom ≫ (αₗ c₁ c₂ (c₃ ⊙ₗ d)).hom  [default: by cat_disch]
    - leftUnitor_actionHom((c : C) (d : D)) : (fun_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ (funₗ _).hom  [default: by cat_disch]
    - rightUnitor_actionHom((c : C) (d : D)) : (ρ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ (funₗ _).hom  [default: by cat_disch]

中文:
类 MonoidalLeftAction
  参数: [MonoidalCategory C]
  公理与运算 (11 个):
    - actionHom_def({c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d')) : f ⊙ₗₘ g = f ⊵ₗ d ≫ c' ⊴ₗ g  [默认: by cat_disch]
    - actionHomRight_id((c : C) (d : D)) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d)  [默认: by cat_disch]
    - id_actionHomLeft((c : C) (d : D)) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d)  [默认: by cat_disch]
    - actionHom_comp({c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'') (g₁ : d ⟶ d') (g₂ : d' ⟶ d'')) : (f₁ ≫ f₂) ⊙ₗₘ (g₁ ≫ g₂) = (f₁ ⊙ₗₘ g₁) ≫ (f₂ ⊙ₗₘ g₂)  [默认: by cat_disch]
    - actionAssocIso_hom_naturality({c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂)) : ((f otimesₘ g) ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).hom = (αₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗₘ g ⊙ₗₘ h)  [默认: by cat_disch]
    - actionUnitIso_hom_naturality({d d' : D} (f : d ⟶ d')) : (funₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (funₗ d').hom  [默认: by cat_disch]
    - whiskerLeft_actionHomLeft((c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D)) : (c ◁ f) ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (αₗ _ _ _).inv  [默认: by cat_disch]
    - whiskerRight_actionHomLeft({c c' : C} (c'' : C) (f : c ⟶ c') (d : D)) : (f ▷ c'') ⊵ₗ d = (αₗ c c'' d).hom ≫ f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (αₗ c' c'' d).inv  [默认: by cat_disch]
    - associator_actionHom((c₁ c₂ c₃ : C) (d : D)) : (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (αₗ c₁ (c₂ otimes c₃) d).hom ≫ c₁ ⊴ₗ (αₗ c₂ c₃ d).hom = (αₗ (c₁ otimes c₂ : C) c₃ d).hom ≫ (αₗ c₁ c₂ (c₃ ⊙ₗ d)).hom  [默认: by cat_disch]
    - leftUnitor_actionHom((c : C) (d : D)) : (fun_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ (funₗ _).hom  [默认: by cat_disch]
    - rightUnitor_actionHom((c : C) (d : D)) : (ρ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ (funₗ _).hom  [默认: by cat_disch]

Depends on / 依赖: actionAssocIso_hom_naturality, actionHomRight_id, actionHom_comp, cat_disch, id_actionHomLeft
-/
class MonoidalLeftAction [MonoidalCategory C] extends
    MonoidalLeftActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
      f ⊙ₗₘ g = f ⊵ₗ d ≫ c' ⊴ₗ g := by
    cat_disch
  actionHomRight_id (c : C) (d : D) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d) := by cat_disch
  id_actionHomLeft (c : C) (d : D) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d) := by cat_disch
  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'')
      (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
      (f₁ ≫ f₂) ⊙ₗₘ (g₁ ≫ g₂) = (f₁ ⊙ₗₘ g₁) ≫ (f₂ ⊙ₗₘ g₂) := by
    cat_disch
  actionAssocIso_hom_naturality
      {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
      ((f otimesₘ g) ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).hom =
        (αₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗₘ g ⊙ₗₘ h) := by
    cat_disch
  actionUnitIso_hom_naturality {d d' : D} (f : d ⟶ d') :
      (funₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (funₗ d').hom := by
    cat_disch
  whiskerLeft_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
      (c ◁ f) ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (αₗ _ _ _).inv := by
    cat_disch
  whiskerRight_actionHomLeft {c c' : C} (c'' : C) (f : c ⟶ c') (d : D) :
      (f ▷ c'') ⊵ₗ d = (αₗ c c'' d).hom ≫
        f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (αₗ c' c'' d).inv := by
    cat_disch
  associator_actionHom (c₁ c₂ c₃ : C) (d : D) :
      (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (αₗ c₁ (c₂ otimes c₃) d).hom ≫
        c₁ ⊴ₗ (αₗ c₂ c₃ d).hom =
      (αₗ (c₁ otimes c₂ : C) c₃ d).hom ≫ (αₗ c₁ c₂ (c₃ ⊙ₗ d)).hom := by
    cat_disch
  leftUnitor_actionHom (c : C) (d : D) :
      (fun_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ (funₗ _).hom := by
    cat_disch
  rightUnitor_actionHom (c : C) (d : D) :
      (ρ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ (funₗ _).hom := by
    cat_disch

attribute [reassoc] MonoidalLeftAction.actionHom_def
attribute [reassoc, simp] MonoidalLeftAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalLeftAction.actionHomRight_id
attribute [reassoc, simp] MonoidalLeftAction.whiskerLeft_actionHomLeft
attribute [simp, reassoc] MonoidalLeftAction.actionHom_comp
attribute [reassoc] MonoidalLeftAction.actionAssocIso_hom_naturality
attribute [reassoc] MonoidalLeftAction.actionUnitIso_hom_naturality
attribute [reassoc (attr := simp)] MonoidalLeftAction.associator_actionHom
attribute [simp, reassoc] MonoidalLeftAction.leftUnitor_actionHom
attribute [simp, reassoc] MonoidalLeftAction.rightUnitor_actionHom

/--
A monoidal category acts on itself on the left through the tensor product.
-/
@[simps!]
/--
Instance `selfLeftAction` / 实例 `selfLeftAction`

English:
instance selfLeftAction
  signature: [MonoidalCategory C]
  body: x otimes y
  actionHom f g := f otimesₘ g
  actionUnitIso x := fun_ x
  actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

中文:
实例 selfLeftAction
  签名: [MonoidalCategory C]
  定义体: x otimes y
  actionHom f g := f otimesₘ g
  actionUnitIso x := fun_ x
  actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

Depends on / 依赖: otimes
-/
instance selfLeftAction [MonoidalCategory C] : MonoidalLeftAction C C where
  actionObj x y := x otimes y
  actionHom f g := f otimesₘ g
  actionUnitIso x := fun_ x
  actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

namespace MonoidalLeftAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalLeftAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCategory`.

@[simp]
/--
lemma `id_actionHom` / 引理 `id_actionHom`

English:
lemma id_actionHom
  given: (c : C) {d d' : D} (f : d ⟶ d')
  proof: by
  simp [actionHom_def]

@[simp]

中文:
引理 id_actionHom
  条件: (c : C) {d d' : D} (f : d ⟶ d')
  证明: by
  simp [actionHom_def]

@[simp]

Depends on / 依赖: actionHom_def
-/
lemma id_actionHom (c : C) {d d' : D} (f : d ⟶ d') :
    (𝟙 c) ⊙ₗₘ f = c ⊴ₗ f := by
  simp [actionHom_def]

@[simp]
/--
lemma `actionHom_id` / 引理 `actionHom_id`

English:
lemma actionHom_id
  given: {c c' : C} (f : c ⟶ c') (d : D)
  proof: by
  simp [actionHom_def]

@[reassoc, simp]

中文:
引理 actionHom_id
  条件: {c c' : C} (f : c ⟶ c') (d : D)
  证明: by
  simp [actionHom_def]

@[reassoc, simp]

Depends on / 依赖: actionHom_def
-/
lemma actionHom_id {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊙ₗₘ (𝟙 d) = f ⊵ₗ d := by
  simp [actionHom_def]

@[reassoc, simp]
/--
theorem `actionHomRight_comp` / 定理 `actionHomRight_comp`

English:
theorem actionHomRight_comp
  given: (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z)
  proof: by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]

中文:
定理 actionHomRight_comp
  条件: (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z)
  证明: by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]

Depends on / 依赖: actionHom_comp, id_actionHom
-/
theorem actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ₗ (f ≫ g) = w ⊴ₗ f ≫ w ⊴ₗ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
/--
theorem `unit_actionHomRight` / 定理 `unit_actionHomRight`

English:
theorem unit_actionHomRight
  given: {x y : D} (f : x ⟶ y)
  proof: by
  rw [← Category.assoc]; rw [actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]

中文:
定理 unit_actionHomRight
  条件: {x y : D} (f : x ⟶ y)
  证明: by
  rw [← Category.assoc]; rw [actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]

Depends on / 依赖: Category, Category.assoc, actionUnitIso_hom_naturality
-/
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    (𝟙_ C) ⊴ₗ f = (funₗ x).hom ≫ f ≫ (funₗ y).inv := by
  rw [← Category.assoc]; rw [actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]
/--
theorem `tensor_actionHomRight` / 定理 `tensor_actionHomRight`

English:
theorem tensor_actionHomRight
  given: (x y : C) {z z' : D} (f : z ⟶ z')
  proof: by
  simp only [← id_actionHom]
  rw [← Category.assoc]; rw [← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]

中文:
定理 tensor_actionHomRight
  条件: (x y : C) {z z' : D} (f : z ⟶ z')
  证明: by
  simp only [← id_actionHom]
  rw [← Category.assoc]; rw [← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]

Depends on / 依赖: Category, Category.assoc, actionAssocIso_hom_naturality, id_actionHom
-/
theorem tensor_actionHomRight (x y : C) {z z' : D} (f : z ⟶ z') :
    (x otimes y) ⊴ₗ f = (αₗ x y z).hom ≫ x ⊴ₗ y ⊴ₗ f ≫ (αₗ x y z').inv := by
  simp only [← id_actionHom]
  rw [← Category.assoc]; rw [← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]
/--
theorem `comp_actionHomLeft` / 定理 `comp_actionHomLeft`

English:
theorem comp_actionHomLeft
  given: {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D)
  proof: by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]

中文:
定理 comp_actionHomLeft
  条件: {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D)
  证明: by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]

Depends on / 依赖: Category, Category.id_comp, actionHom_comp, actionHom_id, id_comp
-/
theorem comp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) :
    (f ≫ g) ⊵ₗ z = f ⊵ₗ z ≫ g ⊵ₗ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
/--
theorem `actionHomLeft_action` / 定理 `actionHomLeft_action`

English:
theorem actionHomLeft_action
  given: {x x' : C} (f : x ⟶ x') (y : C) (z : D)
  proof: by
  simp [whiskerRight_actionHomLeft]

@[reassoc]

中文:
定理 actionHomLeft_action
  条件: {x x' : C} (f : x ⟶ x') (y : C) (z : D)
  证明: by
  simp [whiskerRight_actionHomLeft]

@[reassoc]

Depends on / 依赖: whiskerRight_actionHomLeft
-/
theorem actionHomLeft_action {x x' : C} (f : x ⟶ x') (y : C) (z : D) :
    f ⊵ₗ (y ⊙ₗ z) = (αₗ x y z).inv ≫ (f ▷ y) ⊵ₗ z ≫ (αₗ x' y z).hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
/--
theorem `action_exchange` / 定理 `action_exchange`

English:
theorem action_exchange
  given: {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z)
  proof: by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]

中文:
定理 action_exchange
  条件: {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z)
  证明: by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]

Depends on / 依赖: actionHom_comp, actionHom_id, comp_id, id_actionHom, id_comp
-/
theorem action_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ₗ g ≫ f ⊵ₗ z = f ⊵ₗ y ≫ x ⊴ₗ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
/--
theorem `actionHom_def'` / 定理 `actionHom_def'`

English:
theorem actionHom_def'
  given: {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
  proof: action_exchange f g ▸ actionHom_def f g

@[reassoc]

中文:
定理 actionHom_def'
  条件: {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
  证明: action_exchange f g ▸ actionHom_def f g

@[reassoc]

Depends on / 依赖: actionHom_def, action_exchange
-/
theorem actionHom_def' {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ₗₘ g = x₁ ⊴ₗ g ≫ f ⊵ₗ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc]
/--
theorem `actionAssocIso_inv_naturality` / 定理 `actionAssocIso_inv_naturality`

English:
theorem actionAssocIso_inv_naturality
  proof: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Eq.comm]; rw [Iso.inv_comp_eq]; rw [actionAssocIso_hom_naturality]

@[reassoc]

中文:
定理 actionAssocIso_inv_naturality
  证明: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Eq.comm]; rw [Iso.inv_comp_eq]; rw [actionAssocIso_hom_naturality]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Eq.comm, Iso.comp_inv_eq, Iso.inv_comp_eq, actionAssocIso_hom_naturality, comp_inv_eq, inv_comp_eq
-/
theorem actionAssocIso_inv_naturality
    {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
    (f ⊙ₗₘ g ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).inv =
    (αₗ c₁ c₃ d₁).inv ≫ ((f otimesₘ g) ⊙ₗₘ h) := by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Eq.comm]; rw [Iso.inv_comp_eq]; rw [actionAssocIso_hom_naturality]

@[reassoc]
/--
theorem `actionUnitIso_inv_naturality` / 定理 `actionUnitIso_inv_naturality`

English:
theorem actionUnitIso_inv_naturality
  given: {d d' : D} (f : d ⟶ d')
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Eq.comm]; rw [Iso.comp_inv_eq]; rw [actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]

中文:
定理 actionUnitIso_inv_naturality
  条件: {d d' : D} (f : d ⟶ d')
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Eq.comm]; rw [Iso.comp_inv_eq]; rw [actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Eq.comm, Iso.comp_inv_eq, Iso.inv_comp_eq, actionUnitIso_hom_naturality, comp_inv_eq, inv_comp_eq
-/
theorem actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') :
      (funₗ d).inv ≫ (𝟙_ C) ⊴ₗ f = f ≫ (funₗ d').inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Eq.comm]; rw [Iso.comp_inv_eq]; rw [actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_hom_inv` / 定理 `actionHomRight_hom_inv`

English:
theorem actionHomRight_hom_inv
  given: (x : C) {y z : D} (f : y ≅ z)
  proof: by
  rw [← actionHomRight_comp]; rw [Iso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_hom_inv
  条件: (x : C) {y z : D} (f : y ≅ z)
  证明: by
  rw [← actionHomRight_comp]; rw [Iso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, actionHomRight_comp, actionHomRight_id, hom_inv_id
-/
theorem actionHomRight_hom_inv (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ₗ f.hom ≫ x ⊴ₗ f.inv = 𝟙 (x ⊙ₗ y : D) := by
  rw [← actionHomRight_comp]; rw [Iso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_actionHomLeft` / 定理 `hom_inv_actionHomLeft`

English:
theorem hom_inv_actionHomLeft
  given: {x y : C} (f : x ≅ y) (z : D)
  proof: by
  rw [← comp_actionHomLeft]; rw [Iso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_actionHomLeft
  条件: {x y : C} (f : x ≅ y) (z : D)
  证明: by
  rw [← comp_actionHomLeft]; rw [Iso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, comp_actionHomLeft, hom_inv_id, id_actionHomLeft
-/
theorem hom_inv_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.hom ⊵ₗ z ≫ f.inv ⊵ₗ z = 𝟙 (x ⊙ₗ z) := by
  rw [← comp_actionHomLeft]; rw [Iso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_inv_hom` / 定理 `actionHomRight_inv_hom`

English:
theorem actionHomRight_inv_hom
  given: (x : C) {y z : D} (f : y ≅ z)
  proof: by
  rw [← actionHomRight_comp]; rw [Iso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_inv_hom
  条件: (x : C) {y z : D} (f : y ≅ z)
  证明: by
  rw [← actionHomRight_comp]; rw [Iso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, actionHomRight_comp, actionHomRight_id, inv_hom_id
-/
theorem actionHomRight_inv_hom (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ₗ f.inv ≫ x ⊴ₗ f.hom = 𝟙 (x ⊙ₗ z) := by
  rw [← actionHomRight_comp]; rw [Iso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_actionHomLeft` / 定理 `inv_hom_actionHomLeft`

English:
theorem inv_hom_actionHomLeft
  given: {x y : C} (f : x ≅ y) (z : D)
  proof: by
  rw [← comp_actionHomLeft]; rw [Iso.inv_hom_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

中文:
定理 inv_hom_actionHomLeft
  条件: {x y : C} (f : x ≅ y) (z : D)
  证明: by
  rw [← comp_actionHomLeft]; rw [Iso.inv_hom_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, comp_actionHomLeft, id_actionHomLeft, inv_hom_id
-/
theorem inv_hom_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.inv ⊵ₗ z ≫ f.hom ⊵ₗ z = 𝟙 (y ⊙ₗ z) := by
  rw [← comp_actionHomLeft]; rw [Iso.inv_hom_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_hom_inv'` / 定理 `actionHomRight_hom_inv'`

English:
theorem actionHomRight_hom_inv'
  given: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  proof: by
  rw [← actionHomRight_comp]; rw [IsIso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_hom_inv'
  条件: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  证明: by
  rw [← actionHomRight_comp]; rw [IsIso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, actionHomRight_comp, actionHomRight_id, hom_inv_id
-/
theorem actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ₗ f ≫ x ⊴ₗ inv f = 𝟙 (x ⊙ₗ y) := by
  rw [← actionHomRight_comp]; rw [IsIso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_actionHomLeft'` / 定理 `hom_inv_actionHomLeft'`

English:
theorem hom_inv_actionHomLeft'
  given: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  proof: by
  rw [← comp_actionHomLeft]; rw [IsIso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_actionHomLeft'
  条件: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  证明: by
  rw [← comp_actionHomLeft]; rw [IsIso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, comp_actionHomLeft, hom_inv_id, id_actionHomLeft
-/
theorem hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    f ⊵ₗ z ≫ inv f ⊵ₗ z = 𝟙 (x ⊙ₗ z) := by
  rw [← comp_actionHomLeft]; rw [IsIso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_inv_hom'` / 定理 `actionHomRight_inv_hom'`

English:
theorem actionHomRight_inv_hom'
  given: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  proof: by
  rw [← actionHomRight_comp]; rw [IsIso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_inv_hom'
  条件: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  证明: by
  rw [← actionHomRight_comp]; rw [IsIso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.inv_hom_id, actionHomRight_comp, actionHomRight_id, inv_hom_id
-/
theorem actionHomRight_inv_hom' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ₗ inv f ≫ x ⊴ₗ f = 𝟙 (x ⊙ₗ z) := by
  rw [← actionHomRight_comp]; rw [IsIso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_actionHomLeft'` / 定理 `inv_hom_actionHomLeft'`

English:
theorem inv_hom_actionHomLeft'
  given: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  proof: by
  rw [← comp_actionHomLeft]; rw [IsIso.inv_hom_id]; rw [id_actionHomLeft]

中文:
定理 inv_hom_actionHomLeft'
  条件: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  证明: by
  rw [← comp_actionHomLeft]; rw [IsIso.inv_hom_id]; rw [id_actionHomLeft]

Depends on / 依赖: IsIso.inv_hom_id, comp_actionHomLeft, id_actionHomLeft, inv_hom_id
-/
theorem inv_hom_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv f ⊵ₗ z ≫ f ⊵ₗ z = 𝟙 (y ⊙ₗ z) := by
  rw [← comp_actionHomLeft]; rw [IsIso.inv_hom_id]; rw [id_actionHomLeft]

/--
Instance `isIso_actionHomRight` / 实例 `isIso_actionHomRight`

English:
instance isIso_actionHomRight
  signature: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  body: ⟨x ⊴ₗ inv f, by simp⟩

中文:
实例 isIso_actionHomRight
  签名: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  定义体: ⟨x ⊴ₗ inv f, by simp⟩
-/
instance isIso_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    IsIso (x ⊴ₗ f) :=
  ⟨x ⊴ₗ inv f, by simp⟩

/--
Instance `isIso_actionHomLeft` / 实例 `isIso_actionHomLeft`

English:
instance isIso_actionHomLeft
  signature: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  body: ⟨inv f ⊵ₗ z, by simp⟩

中文:
实例 isIso_actionHomLeft
  签名: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  定义体: ⟨inv f ⊵ₗ z, by simp⟩
-/
instance isIso_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    IsIso (f ⊵ₗ z) :=
  ⟨inv f ⊵ₗ z, by simp⟩

/--
Instance `isIso_actionHom` / 实例 `isIso_actionHom`

English:
instance isIso_actionHom
  signature: {x y : C} {x' y' : D}
  body: ⟨(inv f) ⊙ₗₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]

中文:
实例 isIso_actionHom
  签名: {x y : C} {x' y' : D}
  定义体: ⟨(inv f) ⊙ₗₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]

Depends on / 依赖: actionHom_comp
-/
instance isIso_actionHom {x y : C} {x' y' : D}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    IsIso (f ⊙ₗₘ g) :=
  ⟨(inv f) ⊙ₗₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]
/--
lemma `inv_actionHomLeft` / 引理 `inv_actionHomLeft`

English:
lemma inv_actionHomLeft
  given: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  proof: IsIso.inv_eq_of_hom_inv_id hom_inv_actionHomLeft' f z

@[simp]

中文:
引理 inv_actionHomLeft
  条件: {x y : C} (f : x ⟶ y) [IsIso f] (z : D)
  证明: IsIso.inv_eq_of_hom_inv_id hom_inv_actionHomLeft' f z

@[simp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, hom_inv_actionHomLeft, inv_eq_of_hom_inv_id
-/
lemma inv_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv (f ⊵ₗ z) = inv f ⊵ₗ z :=
IsIso.inv_eq_of_hom_inv_id hom_inv_actionHomLeft' f z

@[simp]
/--
lemma `inv_actionHomRight` / 引理 `inv_actionHomRight`

English:
lemma inv_actionHomRight
  given: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  proof: IsIso.inv_eq_of_hom_inv_id actionHomRight_hom_inv' x f

@[simp]

中文:
引理 inv_actionHomRight
  条件: (x : C) {y z : D} (f : y ⟶ z) [IsIso f]
  证明: IsIso.inv_eq_of_hom_inv_id actionHomRight_hom_inv' x f

@[simp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, actionHomRight_hom_inv, inv_eq_of_hom_inv_id
-/
lemma inv_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    inv (x ⊴ₗ f) = x ⊴ₗ inv f :=
IsIso.inv_eq_of_hom_inv_id actionHomRight_hom_inv' x f

@[simp]
/--
lemma `inv_actionHom` / 引理 `inv_actionHom`

English:
lemma inv_actionHom
  statement: {x y : C} {x' y' : D}
  proof: IsIso.inv_eq_of_hom_inv_id by simp [← actionHom_comp]

中文:
引理 inv_actionHom
  结论: {x y : C} {x' y' : D}
  证明: IsIso.inv_eq_of_hom_inv_id by simp [← actionHom_comp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, actionHom_comp, inv_eq_of_hom_inv_id
-/
lemma inv_actionHom {x y : C} {x' y' : D}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    inv (f ⊙ₗₘ g) = (inv f) ⊙ₗₘ (inv g) :=
IsIso.inv_eq_of_hom_inv_id by simp [← actionHom_comp]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
/--
Definition of `curriedAction` / `curriedAction` 的定义

English:
definition curriedAction
  signature: : C ⥤ D ⥤ D where
  body: { obj y := x ⊙ₗ y
      map f := x ⊴ₗ f }
  map f :=
    { app y := f ⊵ₗ y
      naturality _ _ _ := by simp [action_exchange] }

中文:
定义 curriedAction
  签名: : C ⥤ D ⥤ D where
  定义体: { obj y := x ⊙ₗ y
      map f := x ⊴ₗ f }
  map f :=
    { app y := f ⊵ₗ y
      naturality _ _ _ := by simp [action_exchange] }

Depends on / 依赖: action_exchange, naturality
-/
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := x ⊙ₗ y
      map f := x ⊴ₗ f }
  map f :=
    { app y := f ⊵ₗ y
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ c ⊙ₗ d` as a functor. -/
.obj c abbrev actionLeft (c : C) : D ⥤ D := curriedAction C D

variable {D} in
/-- Bundle `c ↦ c ⊙ₗ d` as a functor. -/
.flip.obj d abbrev actionRight (d : D) : C ⥤ D := curriedAction C D

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Bundle `αₗ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
/--
Definition of `actionAssocNatIso` / `actionAssocNatIso` 的定义

English:
definition actionAssocNatIso
  signature: :
  body: NatIso.ofComponents fun _ =>
    NatIso.ofComponents fun _ =>
     NatIso.ofComponents fun _ => αₗ _ _ _

中文:
定义 actionAssocNatIso
  签名: :
  定义体: NatIso.ofComponents fun _ =>
    NatIso.ofComponents fun _ =>
     NatIso.ofComponents fun _ => αₗ _ _ _

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def actionAssocNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) ≅
    bifunctorComp₂₃ (curriedAction C D) (curriedAction C D) :=
  NatIso.ofComponents fun _ =>
    NatIso.ofComponents fun _ =>
     NatIso.ofComponents fun _ => αₗ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Bundle `λₗ _` as an isomorphism of functors. -/
@[simps!]
/--
Definition of `actionUnitNatIso` / `actionUnitNatIso` 的定义

English:
definition actionUnitNatIso
  signature: : actionLeft D (𝟙_ C) ≅ 𝟭 D
  body: NatIso.ofComponents (funₗ ·)

中文:
定义 actionUnitNatIso
  签名: : actionLeft D (𝟙_ C) ≅ 𝟭 D
  定义体: NatIso.ofComponents (funₗ ·)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def actionUnitNatIso : actionLeft D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (funₗ ·)

end

end MonoidalLeftAction

/--
Definition of `MonoidalRightActionStruct` / `MonoidalRightActionStruct` 的定义

English:
class MonoidalRightActionStruct
  parameters: [MonoidalCategoryStruct C]
  axioms and operations (6):
    - actionObj : D -> C -> D
    - actionHomRight((d : D) {c c' : C} (f : c ⟶ c')) : actionObj d c ⟶ actionObj d c'
    - actionHomLeft({d d' : D} (f : d ⟶ d') (c : C)) : actionObj d c ⟶ actionObj d' c
    - actionHom({c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c')) : actionObj d c ⟶ actionObj d' c'  [default: actionHomLeft f c ≫ actionHomRight d' g]
    - actionAssocIso((d : D) (c c' : C)) : actionObj d (c otimes c') ≅ actionObj (actionObj d c) c'
    - actionUnitIso((d : D)) : actionObj d (𝟙_ C) ≅ d

中文:
类 MonoidalRightActionStruct
  参数: [MonoidalCategoryStruct C]
  公理与运算 (6 个):
    - actionObj : D -> C -> D
    - actionHomRight((d : D) {c c' : C} (f : c ⟶ c')) : actionObj d c ⟶ actionObj d c'
    - actionHomLeft({d d' : D} (f : d ⟶ d') (c : C)) : actionObj d c ⟶ actionObj d' c
    - actionHom({c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c')) : actionObj d c ⟶ actionObj d' c'  [默认: actionHomLeft f c ≫ actionHomRight d' g]
    - actionAssocIso((d : D) (c c' : C)) : actionObj d (c otimes c') ≅ actionObj (actionObj d c) c'
    - actionUnitIso((d : D)) : actionObj d (𝟙_ C) ≅ d

Depends on / 依赖: actionHomLeft, actionHomRight
-/
class MonoidalRightActionStruct [MonoidalCategoryStruct C] where
  /-- The right action on objects. This is denoted `d ⊙ᵣ c`. -/
  actionObj : D -> C -> D
  /-- The right action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.map f).app d`. This is denoted `d ⊴ᵣ f`. -/
  actionHomRight (d : D) {c c' : C} (f : c ⟶ c') :
    actionObj d c ⟶ actionObj d c'
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.obj c).map f`. This is denoted `f ⊵ᵣ c`. -/
  actionHomLeft {d d' : D} (f : d ⟶ d') (c : C) :
    actionObj d c ⟶ actionObj d' c
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') :
    actionObj d c ⟶ actionObj d' c' := actionHomLeft f c ≫ actionHomRight d' g
  /-- The structural isomorphism `d ⊙ᵣ (c ⊗ c') ≅ (d ⊙ᵣ c) ⊙ᵣ c'`. -/
  actionAssocIso (d : D) (c c' : C) :
    actionObj d (c otimes c') ≅ actionObj (actionObj d c) c'
  /-- The structural isomorphism between `d ⊙ᵣ 𝟙_ C` and `d`. -/
  actionUnitIso (d : D) : actionObj d (𝟙_ C) ≅ d

namespace MonoidalRightAction

export MonoidalRightActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`. -/
scoped infixr:70 " ⊙ᵣ " => MonoidalRightActionStruct.actionObj

/-- Notation for `actionHomLeft`, the action of `D` on morphisms in `C`. -/
scoped infixr:81 " ⊵ᵣ " => MonoidalRightActionStruct.actionHomLeft

/-- Notation for `actionHomRight`, the action of morphism in `D` on `C`. -/
scoped infixr:81 " ⊴ᵣ " => MonoidalRightActionStruct.actionHomRight

/-- Notation for `actionHom`, the bifunctorial action of morphisms in `C` and
`D` on `- ⊙ -`. -/
scoped infixr:70 " ⊙ᵣₘ " => MonoidalRightActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ⊙ᵣ (- ⊗ -) ≅ (- ⊙ᵣ -) ⊙ᵣ -`. -/
scoped notation "αᵣ " => MonoidalRightActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `- ⊙ᵣ 𝟙_ C ≅ -`. -/
scoped notation "ρᵣ " => MonoidalRightActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `- ⊙ᵣ 𝟙_ C ≅ -`,
allowing one to specify the acting category. -/
scoped notation "ρᵣ[" J "]" => MonoidalRightActionStruct.actionUnitIso (C := J)

end MonoidalRightAction

open scoped MonoidalRightAction in
/--
Definition of `MonoidalRightAction` / `MonoidalRightAction` 的定义

English:
class MonoidalRightAction
  parameters: [MonoidalCategory C]
  axioms and operations (11):
    - actionHom_def({c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c')) : f ⊙ᵣₘ g = f ⊵ᵣ c ≫ d' ⊴ᵣ g  [default: by cat_disch]
    - actionHomRight_id((c : C) (d : D)) : d ⊴ᵣ 𝟙 c = 𝟙 (d ⊙ᵣ c)  [default: by cat_disch]
    - id_actionHomLeft((c : C) (d : D)) : 𝟙 d ⊵ᵣ c = 𝟙 (d ⊙ᵣ c)  [default: by cat_disch]
    - actionHom_comp({c c' c'' : C} {d d' d'' : D} (f₁ : d ⟶ d') (f₂ : d' ⟶ d'') (g₁ : c ⟶ c') (g₂ : c' ⟶ c'')) : (f₁ ≫ f₂) ⊙ᵣₘ (g₁ ≫ g₂) = (f₁ ⊙ᵣₘ g₁) ≫ (f₂ ⊙ᵣₘ g₂)  [default: by cat_disch]
    - actionAssocIso_hom_naturality({d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄)) : (f ⊙ᵣₘ g otimesₘ h) ≫ (αᵣ d₂ c₂ c₄).hom = (αᵣ d₁ c₁ c₃).hom ≫ ((f ⊙ᵣₘ g) ⊙ᵣₘ h)  [default: by cat_disch]
    - actionUnitIso_hom_naturality({d d' : D} (f : d ⟶ d')) : (ρᵣ d).hom ≫ f = f ⊵ᵣ (𝟙_ C) ≫ (ρᵣ d').hom  [default: by cat_disch]
    - actionHomRight_whiskerRight({c' c'' : C} (f : c' ⟶ c'') (c : C) (d : D)) : d ⊴ᵣ (f ▷ c) = (αᵣ _ _ _).hom ≫ ((d ⊴ᵣ f) ⊵ᵣ c) ≫ (αᵣ _ _ _).inv  [default: by cat_disch]
    - whiskerRight_actionHomLeft((c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D)) : d ⊴ᵣ (c ◁ f) = (αᵣ d c c').hom ≫ (d ⊙ᵣ c) ⊴ᵣ f ≫ (αᵣ d c c'').inv  [default: by cat_disch]
    - actionHom_associator((c₁ c₂ c₃ : C) (d : D)) : d ⊴ᵣ (α_ c₁ c₂ c₃).hom ≫ (αᵣ d c₁ (c₂ otimes c₃)).hom ≫ (αᵣ (d ⊙ᵣ c₁ : D) c₂ c₃).hom = (αᵣ d (c₁ otimes c₂ : C) c₃).hom ≫ (αᵣ d c₁ c₂).hom ⊵ᵣ c₃  [default: by cat_disch]
    - actionHom_leftUnitor((c : C) (d : D)) : d ⊴ᵣ (fun_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom ⊵ᵣ c  [default: by cat_disch]
    - actionHom_rightUnitor((c : C) (d : D)) : d ⊴ᵣ (ρ_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom  [default: by cat_disch]

中文:
类 MonoidalRightAction
  参数: [MonoidalCategory C]
  公理与运算 (11 个):
    - actionHom_def({c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c')) : f ⊙ᵣₘ g = f ⊵ᵣ c ≫ d' ⊴ᵣ g  [默认: by cat_disch]
    - actionHomRight_id((c : C) (d : D)) : d ⊴ᵣ 𝟙 c = 𝟙 (d ⊙ᵣ c)  [默认: by cat_disch]
    - id_actionHomLeft((c : C) (d : D)) : 𝟙 d ⊵ᵣ c = 𝟙 (d ⊙ᵣ c)  [默认: by cat_disch]
    - actionHom_comp({c c' c'' : C} {d d' d'' : D} (f₁ : d ⟶ d') (f₂ : d' ⟶ d'') (g₁ : c ⟶ c') (g₂ : c' ⟶ c'')) : (f₁ ≫ f₂) ⊙ᵣₘ (g₁ ≫ g₂) = (f₁ ⊙ᵣₘ g₁) ≫ (f₂ ⊙ᵣₘ g₂)  [默认: by cat_disch]
    - actionAssocIso_hom_naturality({d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄)) : (f ⊙ᵣₘ g otimesₘ h) ≫ (αᵣ d₂ c₂ c₄).hom = (αᵣ d₁ c₁ c₃).hom ≫ ((f ⊙ᵣₘ g) ⊙ᵣₘ h)  [默认: by cat_disch]
    - actionUnitIso_hom_naturality({d d' : D} (f : d ⟶ d')) : (ρᵣ d).hom ≫ f = f ⊵ᵣ (𝟙_ C) ≫ (ρᵣ d').hom  [默认: by cat_disch]
    - actionHomRight_whiskerRight({c' c'' : C} (f : c' ⟶ c'') (c : C) (d : D)) : d ⊴ᵣ (f ▷ c) = (αᵣ _ _ _).hom ≫ ((d ⊴ᵣ f) ⊵ᵣ c) ≫ (αᵣ _ _ _).inv  [默认: by cat_disch]
    - whiskerRight_actionHomLeft((c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D)) : d ⊴ᵣ (c ◁ f) = (αᵣ d c c').hom ≫ (d ⊙ᵣ c) ⊴ᵣ f ≫ (αᵣ d c c'').inv  [默认: by cat_disch]
    - actionHom_associator((c₁ c₂ c₃ : C) (d : D)) : d ⊴ᵣ (α_ c₁ c₂ c₃).hom ≫ (αᵣ d c₁ (c₂ otimes c₃)).hom ≫ (αᵣ (d ⊙ᵣ c₁ : D) c₂ c₃).hom = (αᵣ d (c₁ otimes c₂ : C) c₃).hom ≫ (αᵣ d c₁ c₂).hom ⊵ᵣ c₃  [默认: by cat_disch]
    - actionHom_leftUnitor((c : C) (d : D)) : d ⊴ᵣ (fun_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom ⊵ᵣ c  [默认: by cat_disch]
    - actionHom_rightUnitor((c : C) (d : D)) : d ⊴ᵣ (ρ_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom  [默认: by cat_disch]

Depends on / 依赖: actionAssocIso_hom_naturality, actionHomRight_id, actionHom_comp, cat_disch, id_actionHomLeft
-/
class MonoidalRightAction [MonoidalCategory C] extends
    MonoidalRightActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') :
      f ⊙ᵣₘ g = f ⊵ᵣ c ≫ d' ⊴ᵣ g := by
    cat_disch
  actionHomRight_id (c : C) (d : D) : d ⊴ᵣ 𝟙 c = 𝟙 (d ⊙ᵣ c) := by cat_disch
  id_actionHomLeft (c : C) (d : D) : 𝟙 d ⊵ᵣ c = 𝟙 (d ⊙ᵣ c) := by cat_disch
  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : d ⟶ d') (f₂ : d' ⟶ d'')
      (g₁ : c ⟶ c') (g₂ : c' ⟶ c'') :
      (f₁ ≫ f₂) ⊙ᵣₘ (g₁ ≫ g₂) = (f₁ ⊙ᵣₘ g₁) ≫ (f₂ ⊙ᵣₘ g₂) := by
    cat_disch
  actionAssocIso_hom_naturality
      {d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄) :
      (f ⊙ᵣₘ g otimesₘ h) ≫ (αᵣ d₂ c₂ c₄).hom =
        (αᵣ d₁ c₁ c₃).hom ≫ ((f ⊙ᵣₘ g) ⊙ᵣₘ h) := by
    cat_disch
  actionUnitIso_hom_naturality {d d' : D} (f : d ⟶ d') :
      (ρᵣ d).hom ≫ f = f ⊵ᵣ (𝟙_ C) ≫ (ρᵣ d').hom := by
    cat_disch
  actionHomRight_whiskerRight {c' c'' : C} (f : c' ⟶ c'') (c : C) (d : D) :
     d ⊴ᵣ (f ▷ c) = (αᵣ _ _ _).hom ≫ ((d ⊴ᵣ f) ⊵ᵣ c) ≫ (αᵣ _ _ _).inv := by
    cat_disch
  whiskerRight_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
     d ⊴ᵣ (c ◁ f) = (αᵣ d c c').hom ≫ (d ⊙ᵣ c) ⊴ᵣ f ≫ (αᵣ d c c'').inv := by
    cat_disch
  actionHom_associator (c₁ c₂ c₃ : C) (d : D) :
      d ⊴ᵣ (α_ c₁ c₂ c₃).hom ≫ (αᵣ d c₁ (c₂ otimes c₃)).hom ≫
        (αᵣ (d ⊙ᵣ c₁ : D) c₂ c₃).hom =
      (αᵣ d (c₁ otimes c₂ : C) c₃).hom ≫ (αᵣ d c₁ c₂).hom ⊵ᵣ c₃ := by
    cat_disch
  actionHom_leftUnitor (c : C) (d : D) :
      d ⊴ᵣ (fun_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom ⊵ᵣ c := by
    cat_disch
  actionHom_rightUnitor (c : C) (d : D) :
      d ⊴ᵣ (ρ_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom := by
    cat_disch

attribute [reassoc] MonoidalRightAction.actionHom_def
attribute [reassoc, simp] MonoidalRightAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalRightAction.actionHomRight_id
attribute [reassoc, simp] MonoidalRightAction.actionHomRight_whiskerRight
attribute [simp, reassoc] MonoidalRightAction.actionHom_comp
attribute [reassoc] MonoidalRightAction.actionAssocIso_hom_naturality
attribute [reassoc] MonoidalRightAction.actionUnitIso_hom_naturality
attribute [reassoc (attr := simp)] MonoidalRightAction.actionHom_associator
attribute [simp, reassoc] MonoidalRightAction.actionHom_leftUnitor
attribute [simp, reassoc] MonoidalRightAction.actionHom_rightUnitor

/-- A monoidal category acts on itself through the tensor product. -/
@[simps!]
/--
Instance `selRightfAction` / 实例 `selRightfAction`

English:
instance selRightfAction
  signature: [MonoidalCategory C]
  body: x otimes y
  actionHom f g := f otimesₘ g
  actionUnitIso x := ρ_ x
.symm actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

中文:
实例 selRightfAction
  签名: [MonoidalCategory C]
  定义体: x otimes y
  actionHom f g := f otimesₘ g
  actionUnitIso x := ρ_ x
.symm actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

Depends on / 依赖: otimes
-/
instance selRightfAction [MonoidalCategory C] : MonoidalRightAction C C where
  actionObj x y := x otimes y
  actionHom f g := f otimesₘ g
  actionUnitIso x := ρ_ x
.symm actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

namespace MonoidalRightAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalRightAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCategory`.

@[simp]
/--
lemma `actionHom_id` / 引理 `actionHom_id`

English:
lemma actionHom_id
  given: {d d' : D} (f : d ⟶ d') (c : C)
  proof: by
  simp [actionHom_def]

@[simp]

中文:
引理 actionHom_id
  条件: {d d' : D} (f : d ⟶ d') (c : C)
  证明: by
  simp [actionHom_def]

@[simp]

Depends on / 依赖: actionHom_def
-/
lemma actionHom_id {d d' : D} (f : d ⟶ d') (c : C) :
    f ⊙ᵣₘ (𝟙 c) = f ⊵ᵣ c := by
  simp [actionHom_def]

@[simp]
/--
lemma `id_actionHom` / 引理 `id_actionHom`

English:
lemma id_actionHom
  given: (d : D) {c c' : C} (f : c ⟶ c')
  proof: by
  simp [actionHom_def]

@[reassoc, simp]

中文:
引理 id_actionHom
  条件: (d : D) {c c' : C} (f : c ⟶ c')
  证明: by
  simp [actionHom_def]

@[reassoc, simp]

Depends on / 依赖: actionHom_def
-/
lemma id_actionHom (d : D) {c c' : C} (f : c ⟶ c') :
    (𝟙 d) ⊙ᵣₘ f = d ⊴ᵣ f := by
  simp [actionHom_def]

@[reassoc, simp]
/--
theorem `actionHomRight_comp` / 定理 `actionHomRight_comp`

English:
theorem actionHomRight_comp
  given: (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  proof: by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]

中文:
定理 actionHomRight_comp
  条件: (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  证明: by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]

Depends on / 依赖: actionHom_comp, id_actionHom
-/
theorem actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ᵣ (f ≫ g) = w ⊴ᵣ f ≫ w ⊴ᵣ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
/--
theorem `unit_actionHomRight` / 定理 `unit_actionHomRight`

English:
theorem unit_actionHomRight
  given: {x y : D} (f : x ⟶ y)
  proof: by
  rw [← Category.assoc]; rw [actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]

中文:
定理 unit_actionHomRight
  条件: {x y : D} (f : x ⟶ y)
  证明: by
  rw [← Category.assoc]; rw [actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]

Depends on / 依赖: Category, Category.assoc, actionUnitIso_hom_naturality
-/
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    f ⊵ᵣ (𝟙_ C) = (ρᵣ x).hom ≫ f ≫ (ρᵣ y).inv := by
  rw [← Category.assoc]; rw [actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]
/--
theorem `actionHomLeft_tensor` / 定理 `actionHomLeft_tensor`

English:
theorem actionHomLeft_tensor
  given: {z z' : D} (f : z ⟶ z') (x y : C)
  proof: by
  simp only [← actionHom_id]
  rw [← Category.assoc]; rw [← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]

中文:
定理 actionHomLeft_tensor
  条件: {z z' : D} (f : z ⟶ z') (x y : C)
  证明: by
  simp only [← actionHom_id]
  rw [← Category.assoc]; rw [← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]

Depends on / 依赖: Category, Category.assoc, actionAssocIso_hom_naturality, actionHom_id
-/
theorem actionHomLeft_tensor {z z' : D} (f : z ⟶ z') (x y : C) :
    (f ⊵ᵣ (x otimes y)) = (αᵣ z x y).hom ≫ (f ⊵ᵣ x) ⊵ᵣ y ≫ (αᵣ z' x y).inv := by
  simp only [← actionHom_id]
  rw [← Category.assoc]; rw [← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]
/--
theorem `comp_actionHomLeft` / 定理 `comp_actionHomLeft`

English:
theorem comp_actionHomLeft
  given: {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C)
  proof: by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]

中文:
定理 comp_actionHomLeft
  条件: {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C)
  证明: by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]

Depends on / 依赖: Category, Category.id_comp, actionHom_comp, actionHom_id, id_comp
-/
theorem comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) :
    (f ≫ g) ⊵ᵣ z = f ⊵ᵣ z ≫ g ⊵ᵣ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
/--
theorem `action_actionHomRight` / 定理 `action_actionHomRight`

English:
theorem action_actionHomRight
  given: (y : D) (z : C) {x x' : C} (f : x ⟶ x')
  proof: by
  simp [whiskerRight_actionHomLeft]

@[reassoc]

中文:
定理 action_actionHomRight
  条件: (y : D) (z : C) {x x' : C} (f : x ⟶ x')
  证明: by
  simp [whiskerRight_actionHomLeft]

@[reassoc]

Depends on / 依赖: whiskerRight_actionHomLeft
-/
theorem action_actionHomRight (y : D) (z : C) {x x' : C} (f : x ⟶ x') :
    (y ⊙ᵣ z) ⊴ᵣ f = (αᵣ y z x).inv ≫ y ⊴ᵣ (z ◁ f) ≫ (αᵣ y z x').hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
/--
theorem `action_exchange` / 定理 `action_exchange`

English:
theorem action_exchange
  given: {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z)
  proof: by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]

中文:
定理 action_exchange
  条件: {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z)
  证明: by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]

Depends on / 依赖: actionHom_comp, actionHom_id, comp_id, id_actionHom, id_comp
-/
theorem action_exchange {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ᵣ g ≫ f ⊵ᵣ z = f ⊵ᵣ y ≫ x ⊴ᵣ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
/--
theorem `actionHom_def'` / 定理 `actionHom_def'`

English:
theorem actionHom_def'
  given: {x₁ y₁ : D} {x₂ y₂ : C} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
  proof: action_exchange f g ▸ actionHom_def f g

@[reassoc]

中文:
定理 actionHom_def'
  条件: {x₁ y₁ : D} {x₂ y₂ : C} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
  证明: action_exchange f g ▸ actionHom_def f g

@[reassoc]

Depends on / 依赖: actionHom_def, action_exchange
-/
theorem actionHom_def' {x₁ y₁ : D} {x₂ y₂ : C} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ᵣₘ g = x₁ ⊴ᵣ g ≫ f ⊵ᵣ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc]
/--
theorem `actionAssocIso_inv_naturality` / 定理 `actionAssocIso_inv_naturality`

English:
theorem actionAssocIso_inv_naturality
  proof: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Eq.comm]; rw [Iso.inv_comp_eq]; rw [actionAssocIso_hom_naturality]

@[reassoc]

中文:
定理 actionAssocIso_inv_naturality
  证明: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Eq.comm]; rw [Iso.inv_comp_eq]; rw [actionAssocIso_hom_naturality]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Eq.comm, Iso.comp_inv_eq, Iso.inv_comp_eq, actionAssocIso_hom_naturality, comp_inv_eq, inv_comp_eq
-/
theorem actionAssocIso_inv_naturality
    {d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄) :
    ((f ⊙ᵣₘ g) ⊙ᵣₘ h) ≫ (αᵣ d₂ c₂ c₄).inv =
    (αᵣ d₁ c₁ c₃).inv ≫ (f ⊙ᵣₘ g otimesₘ h) := by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Eq.comm]; rw [Iso.inv_comp_eq]; rw [actionAssocIso_hom_naturality]

@[reassoc]
/--
theorem `actionUnitIso_inv_naturality` / 定理 `actionUnitIso_inv_naturality`

English:
theorem actionUnitIso_inv_naturality
  given: {d d' : D} (f : d ⟶ d')
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Eq.comm]; rw [Iso.comp_inv_eq]; rw [actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]

中文:
定理 actionUnitIso_inv_naturality
  条件: {d d' : D} (f : d ⟶ d')
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Eq.comm]; rw [Iso.comp_inv_eq]; rw [actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Eq.comm, Iso.comp_inv_eq, Iso.inv_comp_eq, actionUnitIso_hom_naturality, comp_inv_eq, inv_comp_eq
-/
theorem actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') :
      (ρᵣ d).inv ≫ f ⊵ᵣ (𝟙_ C) = f ≫ (ρᵣ d').inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Eq.comm]; rw [Iso.comp_inv_eq]; rw [actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_hom_inv` / 定理 `actionHomRight_hom_inv`

English:
theorem actionHomRight_hom_inv
  given: (x : D) {y z : C} (f : y ≅ z)
  proof: by
  rw [← actionHomRight_comp]; rw [Iso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_hom_inv
  条件: (x : D) {y z : C} (f : y ≅ z)
  证明: by
  rw [← actionHomRight_comp]; rw [Iso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, actionHomRight_comp, actionHomRight_id, hom_inv_id
-/
theorem actionHomRight_hom_inv (x : D) {y z : C} (f : y ≅ z) :
    x ⊴ᵣ f.hom ≫ x ⊴ᵣ f.inv = 𝟙 (x ⊙ᵣ y : D) := by
  rw [← actionHomRight_comp]; rw [Iso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_actionHomLeft` / 定理 `hom_inv_actionHomLeft`

English:
theorem hom_inv_actionHomLeft
  given: {x y : D} (f : x ≅ y) (z : C)
  proof: by
  rw [← comp_actionHomLeft]; rw [Iso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_actionHomLeft
  条件: {x y : D} (f : x ≅ y) (z : C)
  证明: by
  rw [← comp_actionHomLeft]; rw [Iso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, comp_actionHomLeft, hom_inv_id, id_actionHomLeft
-/
theorem hom_inv_actionHomLeft {x y : D} (f : x ≅ y) (z : C) :
    f.hom ⊵ᵣ z ≫ f.inv ⊵ᵣ z = 𝟙 (x ⊙ᵣ z) := by
  rw [← comp_actionHomLeft]; rw [Iso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_inv_hom` / 定理 `actionHomRight_inv_hom`

English:
theorem actionHomRight_inv_hom
  given: (x : D) {y z : C} (f : y ≅ z)
  proof: by
  rw [← actionHomRight_comp]; rw [Iso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_inv_hom
  条件: (x : D) {y z : C} (f : y ≅ z)
  证明: by
  rw [← actionHomRight_comp]; rw [Iso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, actionHomRight_comp, actionHomRight_id, inv_hom_id
-/
theorem actionHomRight_inv_hom (x : D) {y z : C} (f : y ≅ z) :
    x ⊴ᵣ f.inv ≫ x ⊴ᵣ f.hom = 𝟙 (x ⊙ᵣ z) := by
  rw [← actionHomRight_comp]; rw [Iso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_actionHomLeft` / 定理 `inv_hom_actionHomLeft`

English:
theorem inv_hom_actionHomLeft
  given: {x y : D} (f : x ≅ y) (z : C)
  proof: by
  rw [← comp_actionHomLeft]; rw [Iso.inv_hom_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

中文:
定理 inv_hom_actionHomLeft
  条件: {x y : D} (f : x ≅ y) (z : C)
  证明: by
  rw [← comp_actionHomLeft]; rw [Iso.inv_hom_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, comp_actionHomLeft, id_actionHomLeft, inv_hom_id
-/
theorem inv_hom_actionHomLeft {x y : D} (f : x ≅ y) (z : C) :
    f.inv ⊵ᵣ z ≫ f.hom ⊵ᵣ z = 𝟙 (y ⊙ᵣ z) := by
  rw [← comp_actionHomLeft]; rw [Iso.inv_hom_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_hom_inv'` / 定理 `actionHomRight_hom_inv'`

English:
theorem actionHomRight_hom_inv'
  given: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  proof: by
  rw [← actionHomRight_comp]; rw [IsIso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_hom_inv'
  条件: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  证明: by
  rw [← actionHomRight_comp]; rw [IsIso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, actionHomRight_comp, actionHomRight_id, hom_inv_id
-/
theorem actionHomRight_hom_inv' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    x ⊴ᵣ f ≫ x ⊴ᵣ inv f = 𝟙 (x ⊙ᵣ y) := by
  rw [← actionHomRight_comp]; rw [IsIso.hom_inv_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `hom_inv_actionHomLeft'` / 定理 `hom_inv_actionHomLeft'`

English:
theorem hom_inv_actionHomLeft'
  given: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  proof: by
  rw [← comp_actionHomLeft]; rw [IsIso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

中文:
定理 hom_inv_actionHomLeft'
  条件: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  证明: by
  rw [← comp_actionHomLeft]; rw [IsIso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.hom_inv_id, comp_actionHomLeft, hom_inv_id, id_actionHomLeft
-/
theorem hom_inv_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    f ⊵ᵣ z ≫ inv f ⊵ᵣ z = 𝟙 (x ⊙ᵣ z) := by
  rw [← comp_actionHomLeft]; rw [IsIso.hom_inv_id]; rw [id_actionHomLeft]

@[reassoc (attr := simp)]
/--
theorem `actionHomRight_inv_hom'` / 定理 `actionHomRight_inv_hom'`

English:
theorem actionHomRight_inv_hom'
  given: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  proof: by
  rw [← actionHomRight_comp]; rw [IsIso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

中文:
定理 actionHomRight_inv_hom'
  条件: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  证明: by
  rw [← actionHomRight_comp]; rw [IsIso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.inv_hom_id, actionHomRight_comp, actionHomRight_id, inv_hom_id
-/
theorem actionHomRight_inv_hom' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    x ⊴ᵣ inv f ≫ x ⊴ᵣ f = 𝟙 (x ⊙ᵣ z) := by
  rw [← actionHomRight_comp]; rw [IsIso.inv_hom_id]; rw [actionHomRight_id]

@[reassoc (attr := simp)]
/--
theorem `inv_hom_actionHomLeft'` / 定理 `inv_hom_actionHomLeft'`

English:
theorem inv_hom_actionHomLeft'
  given: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  proof: by
  rw [← comp_actionHomLeft]; rw [IsIso.inv_hom_id]; rw [id_actionHomLeft]

中文:
定理 inv_hom_actionHomLeft'
  条件: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  证明: by
  rw [← comp_actionHomLeft]; rw [IsIso.inv_hom_id]; rw [id_actionHomLeft]

Depends on / 依赖: IsIso.inv_hom_id, comp_actionHomLeft, id_actionHomLeft, inv_hom_id
-/
theorem inv_hom_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    inv f ⊵ᵣ z ≫ f ⊵ᵣ z = 𝟙 (y ⊙ᵣ z) := by
  rw [← comp_actionHomLeft]; rw [IsIso.inv_hom_id]; rw [id_actionHomLeft]

/--
Instance `isIso_actionHomLeft` / 实例 `isIso_actionHomLeft`

English:
instance isIso_actionHomLeft
  signature: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  body: ⟨inv f ⊵ᵣ z, by simp⟩

中文:
实例 isIso_actionHomLeft
  签名: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  定义体: ⟨inv f ⊵ᵣ z, by simp⟩
-/
instance isIso_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    IsIso (f ⊵ᵣ z) :=
  ⟨inv f ⊵ᵣ z, by simp⟩

/--
Instance `isIso_actionHomRight` / 实例 `isIso_actionHomRight`

English:
instance isIso_actionHomRight
  signature: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  body: ⟨x ⊴ᵣ inv f, by simp⟩

中文:
实例 isIso_actionHomRight
  签名: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  定义体: ⟨x ⊴ᵣ inv f, by simp⟩
-/
instance isIso_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    IsIso (x ⊴ᵣ f) :=
  ⟨x ⊴ᵣ inv f, by simp⟩

/--
Instance `isIso_actionHom` / 实例 `isIso_actionHom`

English:
instance isIso_actionHom
  signature: {x y : D} {x' y' : C}
  body: ⟨(inv f) ⊙ᵣₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]

中文:
实例 isIso_actionHom
  签名: {x y : D} {x' y' : C}
  定义体: ⟨(inv f) ⊙ᵣₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]

Depends on / 依赖: actionHom_comp
-/
instance isIso_actionHom {x y : D} {x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    IsIso (f ⊙ᵣₘ g) :=
  ⟨(inv f) ⊙ᵣₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]
/--
lemma `inv_actionHomLeft` / 引理 `inv_actionHomLeft`

English:
lemma inv_actionHomLeft
  given: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  proof: IsIso.inv_eq_of_hom_inv_id hom_inv_actionHomLeft' f z

@[simp]

中文:
引理 inv_actionHomLeft
  条件: {x y : D} (f : x ⟶ y) [IsIso f] (z : C)
  证明: IsIso.inv_eq_of_hom_inv_id hom_inv_actionHomLeft' f z

@[simp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, hom_inv_actionHomLeft, inv_eq_of_hom_inv_id
-/
lemma inv_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    inv (f ⊵ᵣ z) = inv f ⊵ᵣ z :=
IsIso.inv_eq_of_hom_inv_id hom_inv_actionHomLeft' f z

@[simp]
/--
lemma `inv_actionHomRight` / 引理 `inv_actionHomRight`

English:
lemma inv_actionHomRight
  given: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  proof: IsIso.inv_eq_of_hom_inv_id actionHomRight_hom_inv' x f

@[simp]

中文:
引理 inv_actionHomRight
  条件: (x : D) {y z : C} (f : y ⟶ z) [IsIso f]
  证明: IsIso.inv_eq_of_hom_inv_id actionHomRight_hom_inv' x f

@[simp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, actionHomRight_hom_inv, inv_eq_of_hom_inv_id
-/
lemma inv_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    inv (x ⊴ᵣ f) = x ⊴ᵣ inv f :=
IsIso.inv_eq_of_hom_inv_id actionHomRight_hom_inv' x f

@[simp]
/--
lemma `inv_actionHom` / 引理 `inv_actionHom`

English:
lemma inv_actionHom
  proof: IsIso.inv_eq_of_hom_inv_id by simp [← actionHom_comp]

中文:
引理 inv_actionHom
  证明: IsIso.inv_eq_of_hom_inv_id by simp [← actionHom_comp]

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, actionHom_comp, inv_eq_of_hom_inv_id
-/
lemma inv_actionHom
    {x y : D} {x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    inv (f ⊙ᵣₘ g) = (inv f) ⊙ᵣₘ (inv g) :=
IsIso.inv_eq_of_hom_inv_id by simp [← actionHom_comp]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
/--
Definition of `curriedAction` / `curriedAction` 的定义

English:
definition curriedAction
  signature: : C ⥤ D ⥤ D where
  body: { obj y := y ⊙ᵣ x
      map f := f ⊵ᵣ x }
  map f :=
    { app y := y ⊴ᵣ f
      naturality _ _ _ := by simp [action_exchange] }

中文:
定义 curriedAction
  签名: : C ⥤ D ⥤ D where
  定义体: { obj y := y ⊙ᵣ x
      map f := f ⊵ᵣ x }
  map f :=
    { app y := y ⊴ᵣ f
      naturality _ _ _ := by simp [action_exchange] }

Depends on / 依赖: action_exchange, naturality
-/
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := y ⊙ᵣ x
      map f := f ⊵ᵣ x }
  map f :=
    { app y := y ⊴ᵣ f
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ d ⊙ᵣ c` as a functor. -/
.obj c abbrev actionRight (c : C) : D ⥤ D := curriedAction C D

variable {D} in
/-- Bundle `c ↦ d ⊙ᵣ c` as a functor. -/
.flip.obj d abbrev actionLeft (d : D) : C ⥤ D := curriedAction C D

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Bundle `αᵣ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
/--
Definition of `actionAssocNatIso` / `actionAssocNatIso` 的定义

English:
definition actionAssocNatIso
  signature: :
  body: NatIso.ofComponents fun _ =>
    NatIso.ofComponents fun _ =>
     NatIso.ofComponents fun _ => αᵣ _ _ _

中文:
定义 actionAssocNatIso
  签名: :
  定义体: NatIso.ofComponents fun _ =>
    NatIso.ofComponents fun _ =>
     NatIso.ofComponents fun _ => αᵣ _ _ _

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def actionAssocNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) ≅
    (bifunctorComp₂₃ (curriedAction C D) (curriedAction C D)).flip :=
  NatIso.ofComponents fun _ =>
    NatIso.ofComponents fun _ =>
     NatIso.ofComponents fun _ => αᵣ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Bundle `ρᵣ _` as an isomorphism of functors. -/
@[simps!]
/--
Definition of `actionUnitNatIso` / `actionUnitNatIso` 的定义

English:
definition actionUnitNatIso
  signature: : actionRight D (𝟙_ C) ≅ 𝟭 D
  body: NatIso.ofComponents (ρᵣ ·)

中文:
定义 actionUnitNatIso
  签名: : actionRight D (𝟙_ C) ≅ 𝟭 D
  定义体: NatIso.ofComponents (ρᵣ ·)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def actionUnitNatIso : actionRight D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (ρᵣ ·)

end

end MonoidalRightAction

end CategoryTheory.MonoidalCategory
