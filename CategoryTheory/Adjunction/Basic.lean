/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mkOfHomEquiv`
* `mk'`: construct an adjunction from the data of a hom set equivalence, unit and counit natural
  transformations together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit`
  relating them to each other.
* `leftAdjointOfEquiv` / `rightAdjointOfEquiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunctionOfEquivLeft` / `adjunctionOfEquivRight` witness that these constructions
  give adjunctions.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, which assert the
existence of an adjoint functor. Given `[F.IsLeftAdjoint]`, a chosen right
adjoint can be obtained as `F.rightAdjoint`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.

## Overview of the directory `CategoryTheory.Adjunction`

* Adjoint lifting theorems are in the directory `Lifting`.
* The file `AdjointFunctorTheorems` proves the adjoint functor theorems.
* The file `Additive` develops adjunctions between additive functors.
* The file `Comma` shows that for a functor `G : D ⥤ C` the data of an initial object in each
  `StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.
* The file `CompositionIso` derives compatibilities for compositions of left adjoints from the
  corresponding data on right adjoints.
* The file `Evaluation` shows that products and coproducts are adjoint to evaluation of functors.
* The file `FullyFaithful` characterizes when adjoints are full or faithful in terms of the unit
  and counit.
* The file `Limits` proves that left adjoints preserve colimits and right adjoints preserve limits.
* The file `Mates` establishes the bijection between the 2-cells
  ```
          L₁ R₁
        C --→ D C ←-- D
      G ↓ ↗ ↓ H G ↓ ↘ ↓ H
        E --→ F E ←-- F
          L₂ R₂
  ```
  where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. Specializing to a pair of adjoints `L₁ L₂ : C ⥤ D`,
  `R₁ R₂ : D ⥤ C`, it provides equivalences `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)` and `(L₂ ≅ L₁) ≃ (R₁ ≅ R₂)`.
* The file `Opposites` contains constructions to relate adjunctions of functors to adjunctions of
  their opposites.
* The file `Parametrized` defines adjunctions with a parameter.
* The file `PartialAdjoint` studies the domain of definition of partial adjoints (left/right).
* The file `Reflective` defines reflective functors, i.e. fully faithful right adjoints. Note that
  many facts about reflective functors are proved in the earlier file `FullyFaithful`.
* The file `Restrict` defines the restriction of an adjunction along fully faithful functors.
* The file `Triple` proves that in an adjoint triple, the left adjoint is fully faithful if and
  only if the right adjoint is.
* The file `Quadruple` bundles adjoint quadruples and compares induced natural transformations.
* The file `Unique` proves uniqueness of adjoints.
* The file `Whiskering` proves that functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
  `F ⊣ G`, induce adjunctions between the functor categories `C ⥤ D` and `C ⥤ E`,
  and the functor categories `E ⥤ C` and `D ⥤ C`.

## Other files related to adjunctions

* The file `Mathlib/CategoryTheory/Monad/Adjunction.lean` develops the basic relationship between
  adjunctions and (co)monads. There it is also shown that given an adjunction `L ⊣ R` and an
  isomorphism `L ⋙ R ≅ 𝟭 C`, the unit is an isomorphism, and similarly for the counit.
-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option linter.translate.warnInvalid false in
/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We use the unit-counit definition of an adjunction. There is a constructor `Adjunction.mk'`
which constructs an adjunction from the data of a hom set equivalence, a unit, and a counit,
together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit` relating them to each
other.

There is also a constructor `Adjunction.mkOfHomEquiv` which constructs an adjunction from a natural
hom set equivalence.

To construct adjoints to a given functor, there are constructors `leftAdjointOfEquiv` and
`adjunctionOfEquivLeft` (as well as their duals). -/
@[stacks 0037, to_dual self (reorder := C D, 2 4, F G)]
/--
Definition of `Adjunction` / `Adjunction` 的定义

English:
structure Adjunction
  parameters: (F : C ⥤ D) (G : D ⥤ C)
  axioms and operations (4):
    - unit : 𝟭 C ⟶ F.comp G
    - counit : G.comp F ⟶ 𝟭 D
    - left_triangle_components((X : C)) : dsimp% F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X)  [default: by cat_disch]
    - right_triangle_components((Y : D)) : dsimp% unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y)  [default: by cat_disch]

中文:
结构 伴随
  参数: (F : C ⥤ D) (G : D ⥤ C)
  公理与运算 (4 个):
    - unit : 𝟭 C ⟶ F.comp G
    - counit : G.comp F ⟶ 𝟭 D
    - left_triangle_components((X : C)) : dsimp% F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X)  [默认: by cat_disch]
    - right_triangle_components((Y : D)) : dsimp% unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit and counit with the identity `F ⟶ FGF ⟶ F = 𝟙` -/
  left_triangle_components (X : C) :
    dsimp% F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X) := by cat_disch
  /-- Equality of the composition of the unit and counit with the identity `G ⟶ GFG ⟶ G = 𝟙` -/
  right_triangle_components (Y : D) :
    dsimp% unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y) := by cat_disch

to_dual_name_hint Left Right

attribute [to_dual existing] Adjunction.unit Adjunction.left_triangle_components
attribute [to_dual self (reorder := C D, 2 4, F G,
  unit counit, left_triangle_components right_triangle_components)] Adjunction.mk
attribute [to_dual self (reorder := C D, 2 4, F G,
  mk (unit counit, left_triangle_components right_triangle_components))] Adjunction.casesOn

/-- The notation `F ⊣ G` stands for `Adjunction F G` representing that `F` is left adjoint to `G` -/
infixl:15 " ⊣ " => Adjunction

namespace Functor

/--
Definition of `IsLeftAdjoint` / `IsLeftAdjoint` 的定义

English:
class IsLeftAdjoint
  parameters: (left : C ⥤ D)
  axioms and operations (1):
    - exists_rightAdjoint : exists (right : D ⥤ C), Nonempty (left ⊣ right)

中文:
类 是左伴随
  参数: (left : C ⥤ D)
  公理与运算 (1 个):
    - exists_rightAdjoint : 存在 (right : D ⥤ C), 非空 (left ⊣ right)
-/
class IsLeftAdjoint (left : C ⥤ D) : Prop where
  exists_rightAdjoint : exists (right : D ⥤ C), Nonempty (left ⊣ right)

/-- A class asserting the existence of a left adjoint. -/
@[to_dual]
/--
Definition of `IsRightAdjoint` / `IsRightAdjoint` 的定义

English:
class IsRightAdjoint
  parameters: (right : D ⥤ C)
  axioms and operations (1):
    - exists_leftAdjoint : exists (left : C ⥤ D), Nonempty (left ⊣ right)

中文:
类 是右伴随
  参数: (right : D ⥤ C)
  公理与运算 (1 个):
    - exists_leftAdjoint : 存在 (left : C ⥤ D), 非空 (left ⊣ right)
-/
class IsRightAdjoint (right : D ⥤ C) : Prop where
  exists_leftAdjoint : exists (left : C ⥤ D), Nonempty (left ⊣ right)

/-- A chosen left adjoint to a functor that is a right adjoint. -/
@[to_dual /-- A chosen right adjoint to a functor that is a left adjoint. -/]
/--
Definition of `leftAdjoint` / `leftAdjoint` 的定义

English:
definition leftAdjoint
  signature: (R : D ⥤ C) [IsRightAdjoint R]
  body: (IsRightAdjoint.exists_leftAdjoint (right := R)).choose

中文:
定义 leftAdjoint
  签名: (R : D ⥤ C) [是右伴随 R]
  定义体: (IsRightAdjoint.exists_leftAdjoint (right := R)).choose

Depends on / 依赖: IsRightAdjoint, IsRightAdjoint.exists_leftAdjoint, exists_leftAdjoint
-/
noncomputable def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  (IsRightAdjoint.exists_leftAdjoint (right := R)).choose

end Functor

/-- The adjunction associated to a functor known to be a left adjoint. -/
@[to_dual /-- The adjunction associated to a functor known to be a right adjoint. -/]
/--
Definition of `Adjunction.ofIsLeftAdjoint` / `Adjunction.ofIsLeftAdjoint` 的定义

English:
definition Adjunction.ofIsLeftAdjoint
  signature: (left : C ⥤ D) [left.IsLeftAdjoint]
  body: IsLeftAdjoint.exists_rightAdjoint.choose_spec.some

中文:
定义 伴随.ofIsLeftAdjoint
  签名: (left : C ⥤ D) [left.是左伴随]
  定义体: IsLeftAdjoint.exists_rightAdjoint.choose_spec.some

Depends on / 依赖: IsLeftAdjoint, IsLeftAdjoint.exists_rightAdjoint.choose_spec.some, choose_spec, exists_rightAdjoint
-/
noncomputable def Adjunction.ofIsLeftAdjoint (left : C ⥤ D) [left.IsLeftAdjoint] :
    left ⊣ left.rightAdjoint :=
  IsLeftAdjoint.exists_rightAdjoint.choose_spec.some

namespace Adjunction

attribute [reassoc (attr := simp)] left_triangle_components right_triangle_components

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D)
  body: fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp]; rw [assoc]; rw [← Functor.comp_map]; rw [adj.counit.naturality]; rw [← assoc]
    simp
  right_inv := fun g => by
    simp only [Functor.comp_obj, Functor.map_co

中文:
定义 homEquiv
  签名: {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D)
  定义体: fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp]; rw [assoc]; rw [← Functor.comp_map]; rw [adj.counit.naturality]; rw [← assoc]
    simp
  right_inv := fun g => by
    simp only [Functor.comp_obj, Functor.map_co

Depends on / 依赖: G.map, adj.unit.app
-/
def homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) where
  toFun := fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp]; rw [assoc]; rw [← Functor.comp_map]; rw [adj.counit.naturality]; rw [← assoc]
    simp
  right_inv := fun g => by
    simp only [Functor.comp_obj, Functor.map_comp]
    rw [← assoc]; rw [← Functor.comp_map]; rw [← adj.unit.naturality]
    simp

/-- `homEquiv'` is the dual of `homEquiv`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing homEquiv]
/--
Definition of `homEquiv'` / `homEquiv'` 的定义

English:
abbreviation homEquiv'
  signature: {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) (X : C) (Y : D)
  body: (homEquiv adj Y X).symm

中文:
缩写 homEquiv'
  签名: {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) (X : C) (Y : D)
  定义体: (homEquiv adj Y X).symm

Depends on / 依赖: homEquiv
-/
abbrev homEquiv' {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) (X : C) (Y : D) :
    (Y ⟶ F.obj X) ≃ (G.obj Y ⟶ X) := (homEquiv adj Y X).symm

attribute [simps (attr := to_dual none) -isSimp] homEquiv

@[to_dual none] alias homEquiv_unit := homEquiv_apply
@[to_dual none] alias homEquiv_counit := homEquiv_symm_apply

-- These lemmas are not global simp lemmas because certain adjunctions
-- are constructed using `Adjunction.mkOfHomEquiv`, and we certainly
-- do not want `dsimp` to apply `homEquiv_unit` or `homEquiv_counit`
-- in that case. However, when proving general API results about adjunctions,
-- it may be advisable to add a local simp attribute to these lemmas.
attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

set_option linter.existingAttributeWarning false in
@[ext, to_dual ext_counit]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G}
  proof: by
  suffices h' : adj.counit = adj'.counit by cases adj; cases adj'; aesop
  ext X
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]; rw [Adjunction.homEquiv_unit]; rw [Adjunction.right_triangle_components]; rw [h]; rw [Adjunction.right_triangle_components]

中文:
引理 ext
  结论: {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G}
  证明: by
  suffices h' : adj.counit = adj'.counit by cases adj; cases adj'; aesop
  ext X
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]; rw [Adjunction.homEquiv_unit]; rw [Adjunction.right_triangle_components]; rw [h]; rw [Adjunction.right_triangle_components]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.right_triangle_components, adj.counit, adj.homEquiv, counit, homEquiv, homEquiv_unit, injective, right_triangle_components
-/
lemma ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G}
    (h : adj.unit = adj'.unit) : adj = adj' := by
  suffices h' : adj.counit = adj'.counit by cases adj; cases adj'; aesop
  ext X
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]; rw [Adjunction.homEquiv_unit]; rw [Adjunction.right_triangle_components]; rw [h]; rw [Adjunction.right_triangle_components]

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

@[to_dual]
/--
lemma `isLeftAdjoint` / 引理 `isLeftAdjoint`

English:
lemma isLeftAdjoint
  given: (adj : F ⊣ G)
  statement: F.IsLeftAdjoint
  proof: ⟨_, ⟨adj⟩⟩

@[to_dual]

中文:
引理 isLeftAdjoint
  条件: (adj : F ⊣ G)
  结论: F.是左伴随
  证明: ⟨_, ⟨adj⟩⟩

@[to_dual]
-/
lemma isLeftAdjoint (adj : F ⊣ G) : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

@[to_dual]
instance (R : D ⥤ C) [R.IsRightAdjoint] : R.leftAdjoint.IsLeftAdjoint :=
  (ofIsRightAdjoint R).isLeftAdjoint

variable {X' X : C} {Y Y' : D}

set_option backward.defeqAttrib.useBackward true in
@[to_dual none]
/--
theorem `homEquiv_id` / 定理 `homEquiv_id`

English:
theorem homEquiv_id
  given: (X : C)
  statement: adj.homEquiv X _ (𝟙 _) = adj.unit.app X
  proof: by simp

@[to_dual none]

中文:
定理 homEquiv_id
  条件: (X : C)
  结论: adj.homEquiv X _ (𝟙 _) = adj.unit.app X
  证明: by simp

@[to_dual none]
-/
theorem homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X := by simp

@[to_dual none]
/--
theorem `homEquiv_symm_id` / 定理 `homEquiv_symm_id`

English:
theorem homEquiv_symm_id
  given: (X : D)
  statement: (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X
  proof: by simp

@[simp, to_dual none]

中文:
定理 homEquiv_symm_id
  条件: (X : D)
  结论: (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X
  证明: by simp

@[simp, to_dual none]
-/
theorem homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by simp

@[simp, to_dual none]
/--
lemma `homEquiv_symm_unit` / 引理 `homEquiv_symm_unit`

English:
lemma homEquiv_symm_unit
  given: (X : C)
  statement: dsimp% (adj.homEquiv _ _).symm (adj.unit.app X) = 𝟙 _
  proof: by
  simp

@[to_dual none]

中文:
引理 homEquiv_symm_unit
  条件: (X : C)
  结论: dsimp% (adj.homEquiv _ _).symm (adj.unit.app X) = 𝟙 _
  证明: by
  simp

@[to_dual none]
-/
lemma homEquiv_symm_unit (X : C) : dsimp% (adj.homEquiv _ _).symm (adj.unit.app X) = 𝟙 _ := by
  simp

@[to_dual none]
/--
theorem `homEquiv_naturality_left_symm` / 定理 `homEquiv_naturality_left_symm`

English:
theorem homEquiv_naturality_left_symm
  given: (f : X' ⟶ X) (g : X ⟶ G.obj Y)
  proof: by
  simp

@[to_dual none]

中文:
定理 homEquiv_naturality_left_symm
  条件: (f : X' ⟶ X) (g : X ⟶ G.obj Y)
  证明: by
  simp

@[to_dual none]
-/
theorem homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  simp

@[to_dual none]
/--
theorem `homEquiv_naturality_left` / 定理 `homEquiv_naturality_left`

English:
theorem homEquiv_naturality_left
  given: (f : X' ⟶ X) (g : F.obj X ⟶ Y)
  proof: by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, homEquiv_naturality_left_symm]

中文:
定理 homEquiv_naturality_left
  条件: (f : X' ⟶ X) (g : F.obj X ⟶ Y)
  证明: by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, homEquiv_naturality_left_symm]

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.symm_apply_apply, eq_symm_apply, homEquiv_naturality_left_symm, symm_apply_apply
-/
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, homEquiv_naturality_left_symm]

set_option backward.defeqAttrib.useBackward true in
@[to_dual none]
/--
theorem `homEquiv_naturality_right` / 定理 `homEquiv_naturality_right`

English:
theorem homEquiv_naturality_right
  given: (f : F.obj X ⟶ Y) (g : Y ⟶ Y')
  proof: by
  simp

@[to_dual none]

中文:
定理 homEquiv_naturality_right
  条件: (f : F.obj X ⟶ Y) (g : Y ⟶ Y')
  证明: by
  simp

@[to_dual none]
-/
theorem homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  simp

@[to_dual none]
/--
theorem `homEquiv_naturality_right_symm` / 定理 `homEquiv_naturality_right_symm`

English:
theorem homEquiv_naturality_right_symm
  given: (f : X ⟶ G.obj Y) (g : Y ⟶ Y')
  proof: by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, Equiv.apply_symm_apply]

@[to_dual none, reassoc]

中文:
定理 homEquiv_naturality_right_symm
  条件: (f : X ⟶ G.obj Y) (g : Y ⟶ Y')
  证明: by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, Equiv.apply_symm_apply]

@[to_dual none, reassoc]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_eq, apply_symm_apply, homEquiv_naturality_right, symm_apply_eq
-/
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, Equiv.apply_symm_apply]

@[to_dual none, reassoc]
/--
theorem `homEquiv_naturality_left_square` / 定理 `homEquiv_naturality_left_square`

English:
theorem homEquiv_naturality_left_square
  statement: (f : X' ⟶ X) (g : F.obj X ⟶ Y')
  proof: by
  rw [← homEquiv_naturality_left]; rw [← homEquiv_naturality_right]; rw [w]

@[to_dual none, reassoc]

中文:
定理 homEquiv_naturality_left_square
  结论: (f : X' ⟶ X) (g : F.obj X ⟶ Y')
  证明: by
  rw [← homEquiv_naturality_left]; rw [← homEquiv_naturality_right]; rw [w]

@[to_dual none, reassoc]

Depends on / 依赖: homEquiv_naturality_left, homEquiv_naturality_right
-/
theorem homEquiv_naturality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) :
    f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k := by
  rw [← homEquiv_naturality_left]; rw [← homEquiv_naturality_right]; rw [w]

@[to_dual none, reassoc]
/--
theorem `homEquiv_naturality_right_square` / 定理 `homEquiv_naturality_right_square`

English:
theorem homEquiv_naturality_right_square
  statement: (f : X' ⟶ X) (g : X ⟶ G.obj Y')
  proof: by
  rw [← homEquiv_naturality_left_symm]; rw [← homEquiv_naturality_right_symm]; rw [w]

@[to_dual none]

中文:
定理 homEquiv_naturality_right_square
  结论: (f : X' ⟶ X) (g : X ⟶ G.obj Y')
  证明: by
  rw [← homEquiv_naturality_left_symm]; rw [← homEquiv_naturality_right_symm]; rw [w]

@[to_dual none]

Depends on / 依赖: homEquiv_naturality_left_symm, homEquiv_naturality_right_symm
-/
theorem homEquiv_naturality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) :
    F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k := by
  rw [← homEquiv_naturality_left_symm]; rw [← homEquiv_naturality_right_symm]; rw [w]

@[to_dual none]
/--
theorem `homEquiv_naturality_left_square_iff` / 定理 `homEquiv_naturality_left_square_iff`

English:
theorem homEquiv_naturality_left_square_iff
  statement: (f : X' ⟶ X) (g : F.obj X ⟶ Y')
  proof: ⟨fun w => by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩

@[to_dual none]

中文:
定理 homEquiv_naturality_left_square_iff
  结论: (f : X' ⟶ X) (g : F.obj X ⟶ Y')
  证明: ⟨fun w => by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩

@[to_dual none]

Depends on / 依赖: Equiv.symm_apply_apply, homEquiv_naturality_left_square, homEquiv_naturality_right_square, symm_apply_apply
-/
theorem homEquiv_naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') :
    (f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k) ↔
      (F.map f ≫ g = h ≫ k) :=
  ⟨fun w => by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩

@[to_dual none]
/--
theorem `homEquiv_naturality_right_square_iff` / 定理 `homEquiv_naturality_right_square_iff`

English:
theorem homEquiv_naturality_right_square_iff
  statement: (f : X' ⟶ X) (g : X ⟶ G.obj Y')
  proof: ⟨fun w => by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩

@[simp, to_dual none]

中文:
定理 homEquiv_naturality_right_square_iff
  结论: (f : X' ⟶ X) (g : X ⟶ G.obj Y')
  证明: ⟨fun w => by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩

@[simp, to_dual none]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, homEquiv_naturality_left_square, homEquiv_naturality_right_square
-/
theorem homEquiv_naturality_right_square_iff (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') :
    (F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k) ↔
      (f ≫ g = h ≫ G.map k) :=
  ⟨fun w => by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩

@[simp, to_dual none]
/--
theorem `left_triangle` / 定理 `left_triangle`

English:
theorem left_triangle
  proof: by
  ext; simp

@[simp, to_dual none]

中文:
定理 left_triangle
  证明: by
  ext; simp

@[simp, to_dual none]
-/
theorem left_triangle :
    whiskerRight adj.unit F ≫ (Functor.associator ..).hom ≫ whiskerLeft F adj.counit =
    F.leftUnitor.hom ≫ F.rightUnitor.inv := by
  ext; simp

@[simp, to_dual none]
/--
theorem `right_triangle` / 定理 `right_triangle`

English:
theorem right_triangle
  proof: by
  ext; simp

@[to_dual (attr := reassoc (attr := simp))]

中文:
定理 right_triangle
  证明: by
  ext; simp

@[to_dual (attr := reassoc (attr := simp))]
-/
theorem right_triangle :
    whiskerLeft G adj.unit ≫ (Functor.associator ..).inv ≫ whiskerRight adj.counit G =
    G.rightUnitor.hom ≫ G.leftUnitor.inv := by
  ext; simp

@[to_dual (attr := reassoc (attr := simp))]
/--
theorem `unit_naturality` / 定理 `unit_naturality`

English:
theorem unit_naturality
  given: {X Y : C} (f : X ⟶ Y)
  proof: (adj.unit.naturality f).symm

@[to_dual none]

中文:
定理 unit_naturality
  条件: {X Y : C} (f : X ⟶ Y)
  证明: (adj.unit.naturality f).symm

@[to_dual none]

Depends on / 依赖: adj.unit.naturality, naturality
-/
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm

@[to_dual none]
/--
lemma `unit_comp_map_eq_iff` / 引理 `unit_comp_map_eq_iff`

English:
lemma unit_comp_map_eq_iff
  given: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  proof: ⟨fun h => by simp [← h], fun h => by simp [h]⟩

@[to_dual none]

中文:
引理 unit_comp_map_eq_iff
  条件: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  证明: ⟨fun h => by simp [← h], fun h => by simp [h]⟩

@[to_dual none]
-/
lemma unit_comp_map_eq_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    dsimp% adj.unit.app A ≫ G.map f = g ↔ f = F.map g ≫ adj.counit.app B :=
  ⟨fun h => by simp [← h], fun h => by simp [h]⟩

@[to_dual none]
/--
lemma `eq_unit_comp_map_iff` / 引理 `eq_unit_comp_map_iff`

English:
lemma eq_unit_comp_map_iff
  given: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  proof: ⟨fun h => by simp [h], fun h => by simp [← h]⟩

@[to_dual none]

中文:
引理 eq_unit_comp_map_iff
  条件: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  证明: ⟨fun h => by simp [h], fun h => by simp [← h]⟩

@[to_dual none]
-/
lemma eq_unit_comp_map_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    dsimp% g = adj.unit.app A ≫ G.map f ↔ F.map g ≫ adj.counit.app B = f :=
  ⟨fun h => by simp [h], fun h => by simp [← h]⟩

@[to_dual none]
/--
theorem `homEquiv_apply_eq` / 定理 `homEquiv_apply_eq`

English:
theorem homEquiv_apply_eq
  given: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  proof: unit_comp_map_eq_iff adj f g

@[to_dual none]

中文:
定理 homEquiv_apply_eq
  条件: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  证明: unit_comp_map_eq_iff adj f g

@[to_dual none]

Depends on / 依赖: unit_comp_map_eq_iff
-/
theorem homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  unit_comp_map_eq_iff adj f g

@[to_dual none]
/--
theorem `eq_homEquiv_apply` / 定理 `eq_homEquiv_apply`

English:
theorem eq_homEquiv_apply
  given: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  proof: eq_unit_comp_map_iff adj f g

中文:
定理 eq_homEquiv_apply
  条件: {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B)
  证明: eq_unit_comp_map_iff adj f g

Depends on / 依赖: eq_unit_comp_map_iff
-/
theorem eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  eq_unit_comp_map_iff adj f g

/-- If `adj : F ⊣ G`, and `X : C`, then `F.obj X` corepresents `Y ↦ (X ⟶ G.obj Y)`. -/
@[simps]
/--
Definition of `corepresentableBy` / `corepresentableBy` 的定义

English:
definition corepresentableBy
  signature: (X : C)
  body: adj.homEquiv _ _
  homEquiv_comp := by simp

中文:
定义 corepresentableBy
  签名: (X : C)
  定义体: adj.homEquiv _ _
  homEquiv_comp := by simp

Depends on / 依赖: adj.homEquiv, homEquiv
-/
def corepresentableBy (X : C) :
    (G ⋙ coyoneda.obj (Opposite.op X)).CorepresentableBy (F.obj X) where
  homEquiv := adj.homEquiv _ _
  homEquiv_comp := by simp

/-- If `adj : F ⊣ G`, and `Y : D`, then `G.obj Y` represents `X ↦ (F.obj X ⟶ Y)`. -/
@[simps]
/--
Definition of `representableBy` / `representableBy` 的定义

English:
definition representableBy
  signature: (Y : D)
  body: (adj.homEquiv _ _).symm
  homEquiv_comp := by simp

中文:
定义 representableBy
  签名: (Y : D)
  定义体: (adj.homEquiv _ _).symm
  homEquiv_comp := by simp

Depends on / 依赖: adj.homEquiv, homEquiv
-/
def representableBy (Y : D) :
    (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) where
  homEquiv := (adj.homEquiv _ _).symm
  homEquiv_comp := by simp

end

/--
Definition of `CoreHomEquivUnitCounit` / `CoreHomEquivUnitCounit` 的定义

English:
structure CoreHomEquivUnitCounit
  parameters: (F : C ⥤ D) (G : D ⥤ C)
  axioms and operations (5):
    - homEquiv : forall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
    - unit : 𝟭 C ⟶ F ⋙ G
    - counit : G ⋙ F ⟶ 𝟭 D
    - homEquiv_unit : forall {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f  [default: by cat_disch]
    - homEquiv_counit : forall {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y  [default: by cat_disch]

中文:
结构 余reHomEquivUnitCounit
  参数: (F : C ⥤ D) (G : D ⥤ C)
  公理与运算 (5 个):
    - homEquiv : 对任意 X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
    - unit : 𝟭 C ⟶ F ⋙ G
    - counit : G ⋙ F ⟶ 𝟭 D
    - homEquiv_unit : 对任意 {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f  [默认: by cat_disch]
    - homEquiv_counit : 对任意 {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/
  homEquiv : forall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F ⋙ G
  /-- The counit of an adjunction -/
  counit : G ⋙ F ⟶ 𝟭 D
  /-- The relationship between the unit and hom set equivalence of an adjunction -/
  homEquiv_unit : forall {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f := by cat_disch
  /-- The relationship between the counit and hom set equivalence of an adjunction -/
  homEquiv_counit : forall {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by cat_disch

/--
Definition of `CoreHomEquiv` / `CoreHomEquiv` 的定义

English:
structure CoreHomEquiv
  parameters: (F : C ⥤ D) (G : D ⥤ C)
  axioms and operations (3):
    - homEquiv : forall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
    - homEquiv_naturality_left_symm : forall {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y), (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g  [default: by cat_disch]
    - homEquiv_naturality_right : forall {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'), (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g  [default: by cat_disch]

中文:
结构 核态射等价
  参数: (F : C ⥤ D) (G : D ⥤ C)
  公理与运算 (3 个):
    - homEquiv : 对任意 X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
    - homEquiv_naturality_left_symm : 对任意 {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y), (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g  [默认: by cat_disch]
    - homEquiv_naturality_right : 对任意 {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'), (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` -/
  homEquiv : forall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The property that describes how `homEquiv.symm` transforms compositions `X' ⟶ X ⟶ G Y` -/
  homEquiv_naturality_left_symm :
    forall {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g := by
    cat_disch
  /-- The property that describes how `homEquiv` transforms compositions `F X ⟶ Y ⟶ Y'` -/
  homEquiv_naturality_right :
    forall {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g := by
    cat_disch

namespace CoreHomEquiv

attribute [simp] homEquiv_naturality_left_symm homEquiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

/--
theorem `homEquiv_naturality_left` / 定理 `homEquiv_naturality_left`

English:
theorem homEquiv_naturality_left
  given: (f : X' ⟶ X) (g : F.obj X ⟶ Y)
  proof: by
  rw [← Equiv.eq_symm_apply]; simp

中文:
定理 homEquiv_naturality_left
  条件: (f : X' ⟶ X) (g : F.obj X ⟶ Y)
  证明: by
  rw [← Equiv.eq_symm_apply]; simp

Depends on / 依赖: Equiv.eq_symm_apply, eq_symm_apply
-/
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]; simp

/--
theorem `homEquiv_naturality_right_symm` / 定理 `homEquiv_naturality_right_symm`

English:
theorem homEquiv_naturality_right_symm
  given: (f : X ⟶ G.obj Y) (g : Y ⟶ Y')
  proof: by
  rw [Equiv.symm_apply_eq]; simp

中文:
定理 homEquiv_naturality_right_symm
  条件: (f : X ⟶ G.obj Y) (g : Y ⟶ Y')
  证明: by
  rw [Equiv.symm_apply_eq]; simp

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]; simp

end CoreHomEquiv

/--
Definition of `CoreUnitCounit` / `CoreUnitCounit` 的定义

English:
structure CoreUnitCounit
  parameters: (F : C ⥤ D) (G : D ⥤ C)
  axioms and operations (4):
    - unit : 𝟭 C ⟶ F.comp G
    - counit : G.comp F ⟶ 𝟭 D
    - left_triangle : whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit = NatTrans.id (𝟭 C ⋙ F)  [default: by cat_disch]
    - right_triangle : whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G = NatTrans.id (G ⋙ 𝟭 C)  [default: by cat_disch]

中文:
结构 余reUnitCounit
  参数: (F : C ⥤ D) (G : D ⥤ C)
  公理与运算 (4 个):
    - unit : 𝟭 C ⟶ F.comp G
    - counit : G.comp F ⟶ 𝟭 D
    - left_triangle : whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit = 自然变换.id (𝟭 C ⋙ F)  [默认: by cat_disch]
    - right_triangle : whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G = 自然变换.id (G ⋙ 𝟭 C)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction between `F` and `G` -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction between `F` and `G` -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `F ⟶ (F G) F ⟶ F (G F) ⟶ F = NatTrans.id F` -/
  left_triangle :
    whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit =
      NatTrans.id (𝟭 C ⋙ F) := by
    cat_disch
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `G ⟶ G (F G) ⟶ (F G) F ⟶ G = NatTrans.id G` -/
  right_triangle :
    whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G =
      NatTrans.id (G ⋙ 𝟭 C) := by
    cat_disch

namespace CoreUnitCounit

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

attribute [local simp] CoreHomEquivUnitCounit.homEquiv_unit CoreHomEquivUnitCounit.homEquiv_counit

/--
Construct an adjunction from the data of a `CoreHomEquivUnitCounit`, i.e. a hom set
equivalence, unit and counit natural transformations together with proofs of the equalities
`homEquiv_unit` and `homEquiv_counit` relating them to each other.
-/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (adj : CoreHomEquivUnitCounit F G)
  body: adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit]; rw [(adj.homEquiv _ _).symm_apply_eq]; rw [adj.homEquiv_unit]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit]; rw [← (adj.homEquiv _ _).eq_symm_apply]; rw [adj.homEquiv_counit

中文:
定义 mk'
  签名: (adj : 余reHomEquivUnitCounit F G)
  定义体: adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit]; rw [(adj.homEquiv _ _).symm_apply_eq]; rw [adj.homEquiv_unit]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit]; rw [← (adj.homEquiv _ _).eq_symm_apply]; rw [adj.homEquiv_counit

Depends on / 依赖: adj.unit
-/
def mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit]; rw [(adj.homEquiv _ _).symm_apply_eq]; rw [adj.homEquiv_unit]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit]; rw [← (adj.homEquiv _ _).eq_symm_apply]; rw [adj.homEquiv_counit]
    simp

/--
lemma `mk'_homEquiv` / 引理 `mk'_homEquiv`

English:
lemma mk'_homEquiv
  given: (adj : CoreHomEquivUnitCounit F G)
  statement: (mk' adj).homEquiv = adj.homEquiv
  proof: by
  ext
  rw [homEquiv_unit]; rw [adj.homEquiv_unit]; rw [mk'_unit]

中文:
引理 mk'_homEquiv
  条件: (adj : 余reHomEquivUnitCounit F G)
  结论: (mk' adj).homEquiv = adj.homEquiv
  证明: by
  ext
  rw [homEquiv_unit]; rw [adj.homEquiv_unit]; rw [mk'_unit]
-/
lemma mk'_homEquiv (adj : CoreHomEquivUnitCounit F G) : (mk' adj).homEquiv = adj.homEquiv := by
  ext
  rw [homEquiv_unit]; rw [adj.homEquiv_unit]; rw [mk'_unit]

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps!]
/--
Definition of `mkOfHomEquiv` / `mkOfHomEquiv` 的定义

English:
definition mkOfHomEquiv
  signature: (adj : CoreHomEquiv F G)
  body: mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        natura

中文:
定义 mkOfHomEquiv
  签名: (adj : 核态射等价 F G)
  定义体: mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        natura

Depends on / 依赖: F.obj, G.obj, adj.homEqui, adj.homEquiv, adj.homEquiv_naturality_left, adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right, adj.homEquiv_naturality_right_symm, counit, homEqui, homEquiv, homEquiv_counit, homEquiv_naturality_left, homEquiv_naturality_left_symm, homEquiv_naturality_right, homEquiv_naturality_right_symm, homEquiv_unit, intros, invFun, naturality
-/
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm] }
    homEquiv := adj.homEquiv
    homEquiv_unit := fun {X Y f} => by simp [← adj.homEquiv_naturality_right]
    homEquiv_counit := fun {X Y f} => by simp [← adj.homEquiv_naturality_left_symm] }

@[simp]
/--
lemma `mkOfHomEquiv_homEquiv` / 引理 `mkOfHomEquiv_homEquiv`

English:
lemma mkOfHomEquiv_homEquiv
  given: (adj : CoreHomEquiv F G)
  proof: by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]

中文:
引理 mkOfHomEquiv_homEquiv
  条件: (adj : 核态射等价 F G)
  证明: by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]

Depends on / 依赖: adj.homEquiv_naturality_right, homEquiv_naturality_right, mkOfHomEquiv
-/
lemma mkOfHomEquiv_homEquiv (adj : CoreHomEquiv F G) :
    (mkOfHomEquiv adj).homEquiv = adj.homEquiv := by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps!]
/--
Definition of `mkOfUnitCounit` / `mkOfUnitCounit` 的定义

English:
definition mkOfUnitCounit
  signature: (adj : CoreUnitCounit F G)
  body: adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff]; rw [funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff]; rw 

中文:
定义 mkOfUnitCounit
  签名: (adj : 余reUnitCounit F G)
  定义体: adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff]; rw [funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff]; rw 

Depends on / 依赖: adj.unit
-/
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff]; rw [funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff]; rw [funext_iff] at this
    simpa [-CoreUnitCounit.right_triangle] using this Y

/-- The adjunction between the identity functor on a category and itself. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : 𝟭 C ⊣ 𝟭 C where
  body: 𝟙 _
  counit := 𝟙 _

中文:
定义 id
  签名: : 𝟭 C ⊣ 𝟭 C where
  定义体: 𝟙 _
  counit := 𝟙 _
-/
def id : 𝟭 C ⊣ 𝟭 C where
  unit := 𝟙 _
  counit := 𝟙 _

-- Satisfy the inhabited linter.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Adjunction (𝟭 C) (𝟭 C))
  body: ⟨id⟩

中文:
实例 :
  签名: 可居 (伴随 (𝟭 C) (𝟭 C))
  定义体: ⟨id⟩
-/
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[to_dual (attr := simps)
/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/]
/--
Definition of `equivHomsetLeftOfNatIso` / `equivHomsetLeftOfNatIso` 的定义

English:
definition equivHomsetLeftOfNatIso
  signature: {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D}
  body: iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp

中文:
定义 equivHomsetLeftOf自然数Iso
  签名: {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D}
  定义体: iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp

Depends on / 依赖: iso.inv.app
-/
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
    (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun f := iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp

set_option linter.translate.warnInvalid false in
/-- Transport an adjunction along a natural isomorphism on the left. -/
@[to_dual (attr := simps)
/-- Transport an adjunction along a natural isomorphism on the right. -/]
/--
Definition of `ofNatIsoLeft` / `ofNatIsoLeft` 的定义

English:
definition ofNatIsoLeft
  signature: {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
  body: adj.unit ≫ Functor.whiskerRight iso.hom _
  counit := Functor.whiskerLeft _ iso.inv ≫ adj.counit
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.map_comp, Functor.whiskerLeft_app, Category.assoc, NatTrans.

中文:
定义 of自然数IsoLeft
  签名: {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
  定义体: adj.unit ≫ Functor.whiskerRight iso.hom _
  counit := Functor.whiskerLeft _ iso.inv ≫ adj.counit
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.map_comp, Functor.whiskerLeft_app, Category.assoc, NatTrans.

Depends on / 依赖: Functor, Functor.whiskerRight, adj.unit, iso.hom, whiskerRight
-/
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H where
  unit := adj.unit ≫ Functor.whiskerRight iso.hom _
  counit := Functor.whiskerLeft _ iso.inv ≫ adj.counit
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.map_comp, Functor.whiskerLeft_app, Category.assoc, NatTrans.naturality_assoc]
    simp [← Functor.comp_map]
  right_triangle_components := by simp [← Functor.map_comp]

attribute [to_dual existing] ofNatIsoLeft_unit ofNatIsoLeft_counit

@[to_dual none]
/--
lemma `homEquiv_ofNatIsoLeft_apply` / 引理 `homEquiv_ofNatIsoLeft_apply`

English:
lemma homEquiv_ofNatIsoLeft_apply
  statement: {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
  proof: by
  simp

@[to_dual none]

中文:
引理 homEquiv_of自然数IsoLeft_apply
  结论: {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
  证明: by
  simp

@[to_dual none]
-/
lemma homEquiv_ofNatIsoLeft_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
    {X : C} {Y : D} (f : G.obj X ⟶ Y) :
    (ofNatIsoLeft adj iso).homEquiv X Y f = adj.homEquiv _ _ (iso.hom.app _ ≫ f) := by
  simp

@[to_dual none]
/--
lemma `homEquiv_ofNatIsoLeft_symm_apply` / 引理 `homEquiv_ofNatIsoLeft_symm_apply`

English:
lemma homEquiv_ofNatIsoLeft_symm_apply
  statement: {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
  proof: by
  simp

@[to_dual none]

中文:
引理 homEquiv_of自然数IsoLeft_symm_apply
  结论: {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
  证明: by
  simp

@[to_dual none]
-/
lemma homEquiv_ofNatIsoLeft_symm_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
    {X : C} {Y : D} (f : X ⟶ H.obj Y) :
    ((ofNatIsoLeft adj iso).homEquiv X Y).symm f = iso.inv.app _ ≫ (adj.homEquiv _ _).symm f := by
  simp

@[to_dual none]
/--
lemma `homEquiv_ofNatIsoRight_apply` / 引理 `homEquiv_ofNatIsoRight_apply`

English:
lemma homEquiv_ofNatIsoRight_apply
  statement: {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
  proof: by
  simp

@[to_dual none]

中文:
引理 homEquiv_of自然数IsoRight_apply
  结论: {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
  证明: by
  simp

@[to_dual none]
-/
lemma homEquiv_ofNatIsoRight_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (ofNatIsoRight adj iso).homEquiv X Y f = adj.homEquiv _ _ f ≫ iso.hom.app _ := by
  simp

@[to_dual none]
/--
lemma `homEquiv_ofNatIsoRight_symm_apply` / 引理 `homEquiv_ofNatIsoRight_symm_apply`

English:
lemma homEquiv_ofNatIsoRight_symm_apply
  statement: {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
  proof: by
  simp

中文:
引理 homEquiv_of自然数IsoRight_symm_apply
  结论: {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
  证明: by
  simp
-/
lemma homEquiv_ofNatIsoRight_symm_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
    {X : C} {Y : D} (f : X ⟶ H.obj Y) :
    ((ofNatIsoRight adj iso).homEquiv X Y).symm f =
      (adj.homEquiv _ _).symm (f ≫ iso.inv.app _) := by
  simp

/-- The isomorphism which an adjunction `F ⊣ G` induces on `G ⋙ yoneda`. This states that
`Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
/--
Definition of `compYonedaIso` / `compYonedaIso` 的定义

English:
definition compYonedaIso
  signature: {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
  body: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv Y.unop X).toIso.symm

中文:
定义 compYonedaIso
  签名: {C : 类型u₁} [范畴.{v₁} C] {D : 类型u₂} [范畴.{v₁} D]
  定义体: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv Y.unop X).toIso.symm

Depends on / 依赖: NatIso, NatIso.ofComponents, Y.unop, adj.homEquiv, homEquiv, ofComponents, toIso.symm
-/
def compYonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    G ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv Y.unop X).toIso.symm

/-- The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ coyoneda`. This states that
`Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
/--
Definition of `compCoyonedaIso` / `compCoyonedaIso` 的定义

English:
definition compCoyonedaIso
  signature: {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
  body: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv X.unop Y).toIso

中文:
定义 compCoyonedaIso
  签名: {C : 类型u₁} [范畴.{v₁} C] {D : 类型u₂} [范畴.{v₁} D]
  定义体: NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv X.unop Y).toIso

Depends on / 依赖: NatIso, NatIso.ofComponents, X.unop, adj.homEquiv, homEquiv, ofComponents
-/
def compCoyonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    F.op ⋙ coyoneda ≅ coyoneda ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv X.unop Y).toIso

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ uliftCoyoneda`.
This states that `Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
/--
Definition of `compUliftCoyonedaIso` / `compUliftCoyonedaIso` 的定义

English:
definition compUliftCoyonedaIso
  signature: (adj : F ⊣ G)
  body: NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans
      ((adj.homEquiv X.unop Y).trans Equiv.ulift.symm)).toIso))

中文:
定义 compUliftCoyonedaIso
  签名: (adj : F ⊣ G)
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans
      ((adj.homEquiv X.unop Y).trans Equiv.ulift.symm)).toIso))

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, NatIso, NatIso.ofComponents, X.unop, adj.homEquiv, homEquiv, ofComponents
-/
def compUliftCoyonedaIso (adj : F ⊣ G) :
    F.op ⋙ uliftCoyoneda.{max w v₁} ≅
      uliftCoyoneda.{max w v₂} ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans
      ((adj.homEquiv X.unop Y).trans Equiv.ulift.symm)).toIso))

section

variable {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
  (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)

/-- Composition of adjunctions. -/
@[to_dual self (reorder := C E, 2 6, F I, G H, adj₁ adj₂), simps! -isSimp unit counit, stacks 0DV0]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : F ⋙ H ⊣ I ⋙ G
  body: mk' {
    homEquiv := fun _ _ => Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ whiskerRight (F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫
      (associator _ _ _).inv) G ≫ (associator _ _ _).hom
    counit := (associator _ _ _).inv ≫ whiskerRight ((associator _ _ _).ho

中文:
定义 comp
  签名: : F ⋙ H ⊣ I ⋙ G
  定义体: mk' {
    homEquiv := fun _ _ => Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ whiskerRight (F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫
      (associator _ _ _).inv) G ≫ (associator _ _ _).hom
    counit := (associator _ _ _).inv ≫ whiskerRight ((associator _ _ _).ho

Depends on / 依赖: Equiv.trans, F.rightUnitor.inv, I.rightUnitor.hom, associator, counit, homEquiv, rightUnitor, whiskerLeft, whiskerRight
-/
def comp : F ⋙ H ⊣ I ⋙ G :=
  mk' {
    homEquiv := fun _ _ => Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ whiskerRight (F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫
      (associator _ _ _).inv) G ≫ (associator _ _ _).hom
    counit := (associator _ _ _).inv ≫ whiskerRight ((associator _ _ _).hom ≫
      whiskerLeft _ adj₁.counit ≫ I.rightUnitor.hom) _ ≫ adj₂.counit }

/--
lemma `comp_unit_app` / 引理 `comp_unit_app`

English:
lemma comp_unit_app
  given: (X : C)
  statement: dsimp%
  proof: by
  simp [Adjunction.comp]

@[to_dual existing (attr := simp, reassoc)]

中文:
引理 comp_unit_app
  条件: (X : C)
  结论: dsimp%
  证明: by
  simp [Adjunction.comp]

@[to_dual existing (attr := simp, reassoc)]

Depends on / 依赖: Adjunction, Adjunction.comp
-/
lemma comp_unit_app (X : C) : dsimp%
    (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) := by
  simp [Adjunction.comp]

@[to_dual existing (attr := simp, reassoc)]
/--
lemma `comp_counit_app` / 引理 `comp_counit_app`

English:
lemma comp_counit_app
  given: (X : E)
  statement: dsimp%
  proof: by
  simp [Adjunction.comp]

中文:
引理 comp_counit_app
  条件: (X : E)
  结论: dsimp%
  证明: by
  simp [Adjunction.comp]

Depends on / 依赖: Adjunction, Adjunction.comp
-/
lemma comp_counit_app (X : E) : dsimp%
    (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X := by
  simp [Adjunction.comp]

/--
lemma `comp_homEquiv` / 引理 `comp_homEquiv`

English:
lemma comp_homEquiv
  statement: (adj₁.comp adj₂).homEquiv =
  proof: mk'_homEquiv _

中文:
引理 comp_homEquiv
  结论: (adj₁.comp adj₂).homEquiv =
  证明: mk'_homEquiv _

Depends on / 依赖: _homEquiv
-/
lemma comp_homEquiv : (adj₁.comp adj₂).homEquiv =
    fun _ _ => Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _) :=
  mk'_homEquiv _

end

section ConstructLeft

-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variable {F_obj : C -> D}
variable (e : forall X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `rightAdjointOfEquiv`. -/
@[implicit_reducible, simps!]
/--
Definition of `leftAdjointOfEquiv` / `leftAdjointOfEquiv` 的定义

English:
definition leftAdjointOfEquiv
  signature: (he : forall X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
  body: F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq]; rw [he]; rw [Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc]; rw [← he]; rw [id_comp]; rw [Equiv.apply_symm_apply]
    simp

中文:
定义 leftAdjointOfEquiv
  签名: (he : 对任意 X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
  定义体: F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq]; rw [he]; rw [Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc]; rw [← he]; rw [id_comp]; rw [Equiv.apply_symm_apply]
    simp

Depends on / 依赖: F_obj
-/
def leftAdjointOfEquiv (he : forall X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g) : C ⥤ D where
  obj := F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq]; rw [he]; rw [Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc]; rw [← he]; rw [id_comp]; rw [Equiv.apply_symm_apply]
    simp

variable (he : forall X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

/-- Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G`. Dual
to `adjunctionOfEquivRight`. -/
@[simps!]
/--
Definition of `adjunctionOfEquivLeft` / `adjunctionOfEquivLeft` 的定义

English:
definition adjunctionOfEquivLeft
  signature: : leftAdjointOfEquiv e he ⊣ G
  body: mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq]; rw [he]; simp
        simp [← thi

中文:
定义 adjunctionOfEquivLeft
  签名: : leftAdjointOfEquiv e he ⊣ G
  定义体: mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq]; rw [he]; simp
        simp [← thi

Depends on / 依赖: Equiv.symm_apply_eq, G.map, G.obj, homEquiv, homEquiv_naturality_left_symm, mkOfHomEquiv, symm_apply_eq
-/
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq]; rw [he]; simp
        simp [← this, ← he] }

end ConstructLeft

section ConstructRight

-- Construction of a right adjoint, analogous to the above.
variable {G_obj : D -> C}
variable (e : forall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))

/--
theorem `he''` / 定理 `he''`

English:
theorem he''
  statement: (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
  proof: by
  rw [Equiv.eq_symm_apply]; rw [he]; simp

中文:
定理 he''
  结论: (he : 对任意 X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
  证明: by
  rw [Equiv.eq_symm_apply]; rw [he]; simp
-/
private theorem he'' (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
    {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  rw [Equiv.eq_symm_apply]; rw [he]; simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `leftAdjointOfEquiv`. -/
@[implicit_reducible, simps!]
/--
Definition of `rightAdjointOfEquiv` / `rightAdjointOfEquiv` 的定义

English:
definition rightAdjointOfEquiv
  signature: (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
  body: G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply]; rw [← he'' e he]; rw [Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc]; rw [he'' e he]; rw [comp_id]; rw [Equiv.symm_apply_apply]
  

中文:
定义 rightAdjointOfEquiv
  签名: (he : 对任意 X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
  定义体: G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply]; rw [← he'' e he]; rw [Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc]; rw [he'' e he]; rw [comp_id]; rw [Equiv.symm_apply_apply]
  

Depends on / 依赖: G_obj
-/
def rightAdjointOfEquiv (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) : D ⥤ C where
  obj := G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply]; rw [← he'' e he]; rw [Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc]; rw [he'' e he]; rw [comp_id]; rw [Equiv.symm_apply_apply]
    simp

/-- Show that the functor given by `rightAdjointOfEquiv` is indeed right adjoint to `F`. Dual
to `adjunctionOfEquivLeft`. -/
@[simps!]
/--
Definition of `adjunctionOfEquivRight` / `adjunctionOfEquivRight` 的定义

English:
definition adjunctionOfEquivRight
  signature: (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
  body: mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }

中文:
定义 adjunctionOfEquivRight
  签名: (he : 对任意 X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
  定义体: mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }

Depends on / 依赖: Equiv.symm_apply_eq, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv, reassoc_of, symm_apply_eq
-/
def adjunctionOfEquivRight (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) :
    F ⊣ (rightAdjointOfEquiv e he) :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }

end ConstructRight

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps!]
/--
Definition of `toEquivalence` / `toEquivalence` 的定义

English:
definition toEquivalence
  signature: (adj : F ⊣ G) [forall X, IsIso (adj.unit.app X)]
  body: F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)

中文:
定义 toEquivalence
  签名: (adj : F ⊣ G) [对任意 X, 是同构 (adj.unit.app X)]
  定义体: F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)
-/
noncomputable def toEquivalence (adj : F ⊣ G) [forall X, IsIso (adj.unit.app X)]
    [forall Y, IsIso (adj.counit.app Y)] : C ≌ D where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)

/--
lemma `map_comp_bijective_iff` / 引理 `map_comp_bijective_iff`

English:
lemma map_comp_bijective_iff
  given: (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D)
  proof: by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]; rw [← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp

中文:
引理 map_comp_bijective_iff
  条件: (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D)
  证明: by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]; rw [← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, adj.homEquiv, bijective, homEquiv, of_comp_iff, symm.bijective
-/
lemma map_comp_bijective_iff (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D) :
    Function.Bijective (fun (g : F.obj Y ⟶ Z) => F.map f ≫ g) ↔
      Function.Bijective (fun (g : Y ⟶ G.obj Z) => f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]; rw [← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp

/--
lemma `comp_map_bijective_iff` / 引理 `comp_map_bijective_iff`

English:
lemma comp_map_bijective_iff
  given: (adj : F ⊣ G) {X Y : D} (g : X ⟶ Y) (Z : C)
  proof: by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]; rw [← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  simp

中文:
引理 comp_map_bijective_iff
  条件: (adj : F ⊣ G) {X Y : D} (g : X ⟶ Y) (Z : C)
  证明: by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]; rw [← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  simp

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, adj.homEquiv, bijective, homEquiv, of_comp_iff, symm.bijective
-/
lemma comp_map_bijective_iff (adj : F ⊣ G) {X Y : D} (g : X ⟶ Y) (Z : C) :
    Function.Bijective (fun (f : Z ⟶ G.obj X) => f ≫ G.map g) ↔
      Function.Bijective (fun (f : F.obj Z ⟶ X) => f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]; rw [← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  simp

end Adjunction

open Adjunction

/--
lemma `Functor.isEquivalence_of_isRightAdjoint` / 引理 `Functor.isEquivalence_of_isRightAdjoint`

English:
lemma Functor.isEquivalence_of_isRightAdjoint
  statement: (G : C ⥤ D) [IsRightAdjoint G]
  proof: (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse

中文:
引理 函子.isEquivalence_of_isRightAdjoint
  结论: (G : C ⥤ D) [是右伴随 G]
  证明: (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, isEquivalence_inverse, ofIsRightAdjoint, toEquivalence, toEquivalence.isEquivalence_inverse
-/
lemma Functor.isEquivalence_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G]
    [forall X, IsIso ((Adjunction.ofIsRightAdjoint G).unit.app X)]
    [forall Y, IsIso ((Adjunction.ofIsRightAdjoint G).counit.app Y)] : G.IsEquivalence :=
  (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse

namespace Equivalence

variable (e : C ≌ D)

/--
Definition of `toAdjunction` / `toAdjunction` 的定义

English:
definition toAdjunction
  signature: : e.functor ⊣ e.inverse where
  body: e.unit
  counit := e.counit

中文:
定义 toAdjunction
  签名: : e.functor ⊣ e.inverse where
  定义体: e.unit
  counit := e.counit

Depends on / 依赖: e.unit
-/
def toAdjunction : e.functor ⊣ e.inverse where
  unit := e.unit
  counit := e.counit

/-- `toAdjunction'` is the dual of `ToAdjunction`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing toAdjunction]
/--
Definition of `toAdjunction'` / `toAdjunction'` 的定义

English:
abbreviation toAdjunction'
  signature: : e.inverse ⊣ e.functor
  body: e.symm.toAdjunction

中文:
缩写 toAdjunction'
  签名: : e.inverse ⊣ e.functor
  定义体: e.symm.toAdjunction

Depends on / 依赖: e.symm.toAdjunction, toAdjunction
-/
abbrev toAdjunction' : e.inverse ⊣ e.functor := e.symm.toAdjunction

attribute [simps (attr := to_dual none)] toAdjunction

@[to_dual]
/--
lemma `isLeftAdjoint_functor` / 引理 `isLeftAdjoint_functor`

English:
lemma isLeftAdjoint_functor
  statement: e.functor.IsLeftAdjoint where
  proof: ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual]

中文:
引理 isLeftAdjoint_functor
  结论: e.functor.是左伴随 where
  证明: ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual]

Depends on / 依赖: e.toAdjunction, toAdjunction
-/
lemma isLeftAdjoint_functor : e.functor.IsLeftAdjoint where
  exists_rightAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual]
/--
lemma `isRightAdjoint_inverse` / 引理 `isRightAdjoint_inverse`

English:
lemma isRightAdjoint_inverse
  statement: e.inverse.IsRightAdjoint where
  proof: ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual none]

中文:
引理 isRightAdjoint_inverse
  结论: e.inverse.是右伴随 where
  证明: ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual none]

Depends on / 依赖: e.toAdjunction, toAdjunction
-/
lemma isRightAdjoint_inverse : e.inverse.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual none]
/--
lemma `refl_toAdjunction` / 引理 `refl_toAdjunction`

English:
lemma refl_toAdjunction
  statement: (refl (C := C)).toAdjunction = Adjunction.id
  proof: rfl

中文:
引理 refl_toAdjunction
  结论: (refl (C := C)).toAdjunction = 伴随.id
  证明: rfl

Depends on / 依赖: Adjunction, Adjunction.id, toAdjunction
-/
lemma refl_toAdjunction : (refl (C := C)).toAdjunction = Adjunction.id := rfl

/--
lemma `trans_toAdjunction` / 引理 `trans_toAdjunction`

English:
lemma trans_toAdjunction
  given: {E : Type*} [Category* E] (e' : D ≌ E)
  proof: rfl

中文:
引理 trans_toAdjunction
  条件: {E : 类型} [范畴* E] (e' : D ≌ E)
  证明: rfl
-/
lemma trans_toAdjunction {E : Type*} [Category* E] (e' : D ≌ E) :
    (e.trans e').toAdjunction = e.toAdjunction.comp e'.toAdjunction := rfl

end Equivalence

namespace Functor

/--
Instance `isLeftAdjoint_comp` / 实例 `isLeftAdjoint_comp`

English:
instance isLeftAdjoint_comp
  signature: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  body: ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩

中文:
实例 isLeftAdjoint_comp
  签名: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  定义体: ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, ofIsLeftAdjoint
-/
instance isLeftAdjoint_comp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] : (F ⋙ G).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩

/--
Instance `isRightAdjoint_comp` / 实例 `isRightAdjoint_comp`

English:
instance isRightAdjoint_comp
  signature: {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
  body: ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩

中文:
实例 isRightAdjoint_comp
  签名: {E : 类型u₃} [范畴.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
  定义体: ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint
-/
instance isRightAdjoint_comp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
    [IsRightAdjoint F] [IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where
  exists_leftAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩

/-- Transport being a right adjoint along a natural isomorphism. -/
@[to_dual /-- Transport being a left adjoint along a natural isomorphism. -/]
/--
lemma `isRightAdjoint_of_iso` / 引理 `isRightAdjoint_of_iso`

English:
lemma isRightAdjoint_of_iso
  given: {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint]
  proof: ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩

中文:
引理 isRightAdjoint_of_iso
  条件: {F G : C ⥤ D} (h : F ≅ G) [F.是右伴随]
  证明: ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint, ofNatIsoRight
-/
lemma isRightAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] :
    IsRightAdjoint G where
  exists_leftAdjoint := ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: (E : C ⥤ D) [IsEquivalence E]
  body: E.asEquivalence.toAdjunction

中文:
定义 adjunction
  签名: (E : C ⥤ D) [是等价 E]
  定义体: E.asEquivalence.toAdjunction

Depends on / 依赖: E.asEquivalence.toAdjunction, asEquivalence, toAdjunction
-/
noncomputable def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
@[to_dual /-- If `F` is an equivalence, it's a right adjoint. -/]
instance (priority := 10) isLeftAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsLeftAdjoint F :=
  F.asEquivalence.isLeftAdjoint_functor

/--
lemma `isLeftAdjoint_comp_iff_right` / 引理 `isLeftAdjoint_comp_iff_right`

English:
lemma isLeftAdjoint_comp_iff_right
  statement: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isLeftAdjoint_of_iso iso.symm

中文:
引理 isLeftAdjoint_comp_iff_right
  结论: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isLeftAdjoint_of_iso iso.symm

Depends on / 依赖: F.asEquivalence.counitIso, F.asEquivalence.inverse, Functor, Functor.associator, Functor.isoWhiskerRight, Functor.leftUnitor, asEquivalence, associator, counitIso, inverse, isLeftAdjoint_of_iso, iso.symm, isoWhiskerRight, leftUnitor
-/
lemma isLeftAdjoint_comp_iff_right {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsEquivalence] :
    (F ⋙ G).IsLeftAdjoint ↔ G.IsLeftAdjoint := by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isLeftAdjoint_of_iso iso.symm

/--
lemma `isRightAdjoint_comp_iff_right` / 引理 `isRightAdjoint_comp_iff_right`

English:
lemma isRightAdjoint_comp_iff_right
  statement: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isRightAdjoint_of_iso iso.symm

中文:
引理 isRightAdjoint_comp_iff_right
  结论: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isRightAdjoint_of_iso iso.symm

Depends on / 依赖: F.asEquivalence.counitIso, F.asEquivalence.inverse, Functor, Functor.associator, Functor.isoWhiskerRight, Functor.leftUnitor, asEquivalence, associator, counitIso, inverse, isRightAdjoint_of_iso, iso.symm, isoWhiskerRight, leftUnitor
-/
lemma isRightAdjoint_comp_iff_right {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsEquivalence] :
    (F ⋙ G).IsRightAdjoint ↔ G.IsRightAdjoint := by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isRightAdjoint_of_iso iso.symm

/--
lemma `isLeftAdjoint_comp_iff_left` / 引理 `isLeftAdjoint_comp_iff_left`

English:
lemma isLeftAdjoint_comp_iff_left
  statement: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isLeftAdjoint_of_iso iso.symm

中文:
引理 isLeftAdjoint_comp_iff_left
  结论: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isLeftAdjoint_of_iso iso.symm

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.rightUnitor, G.asEquivalence.inverse, G.asEquivalence.unitIso, asEquivalence, associator, inverse, isLeftAdjoint_of_iso, iso.symm, isoWhiskerLeft, rightUnitor, unitIso
-/
lemma isLeftAdjoint_comp_iff_left {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [G.IsEquivalence] :
    (F ⋙ G).IsLeftAdjoint ↔ F.IsLeftAdjoint := by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isLeftAdjoint_of_iso iso.symm

/--
lemma `isRightAdjoint_comp_iff_left` / 引理 `isRightAdjoint_comp_iff_left`

English:
lemma isRightAdjoint_comp_iff_left
  statement: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isRightAdjoint_of_iso iso.symm

中文:
引理 isRightAdjoint_comp_iff_left
  结论: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isRightAdjoint_of_iso iso.symm

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.rightUnitor, G.asEquivalence.inverse, G.asEquivalence.unitIso, asEquivalence, associator, inverse, isRightAdjoint_of_iso, iso.symm, isoWhiskerLeft, rightUnitor, unitIso
-/
lemma isRightAdjoint_comp_iff_left {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [G.IsEquivalence] :
    (F ⋙ G).IsRightAdjoint ↔ F.IsRightAdjoint := by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isRightAdjoint_of_iso iso.symm

end Functor

end CategoryTheory
