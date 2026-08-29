/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
public import Mathlib.Tactic.CategoryTheory.BicategoricalComp

/-!
# Adjunctions in bicategories

For 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjunction between `f` and `g`
consists of a pair of 2-morphisms `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategory.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.Equivalence.mkOfAdjointifyCounit`: construct an adjoint equivalence from
  2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.
* `Pseudofunctor.mapAdjunction`: a pseudofunctor `F` carries an adjunction `f ⊣ g`
  between 1-morphisms to an adjunction `F.map f ⊣ F.map g`. An analogous definition is given
  for `StrictPseudofunctor`.

## TODO

* `Bicategory.Equivalence.mkOfAdjointifyUnit`: construct an adjoint equivalence from
  2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.
-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

namespace Bicategory

/--
Definition of `leftZigzag` / `leftZigzag` 的定义

English:
abbreviation leftZigzag
  signature: (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
  body: η ▷ f otimes≫ f ◁ ε

中文:
缩写 leftZigzag
  签名: (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
  定义体: η ▷ f otimes≫ f ◁ ε

Depends on / 依赖: otimes
-/
abbrev leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  η ▷ f otimes≫ f ◁ ε

/--
Definition of `rightZigzag` / `rightZigzag` 的定义

English:
abbreviation rightZigzag
  signature: (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
  body: g ◁ η otimes≫ ε ▷ g

中文:
缩写 rightZigzag
  签名: (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
  定义体: g ◁ η otimes≫ ε ▷ g

Depends on / 依赖: otimes
-/
abbrev rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η otimes≫ ε ▷ g

/--
theorem `rightZigzag_idempotent_of_left_triangle` / 定理 `rightZigzag_idempotent_of_left_triangle`

English:
theorem rightZigzag_idempotent_of_left_triangle
  proof: by
  dsimp only [rightZigzag]
  calc
    _ = g ◁ η otimes≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) otimes≫ ε ▷ g := by
      bicategory
    _ = 𝟙 _ otimes≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) otimes≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = g ◁ η otimes≫ g ◁ leftZigzag η ε ▷ g otimes≫ ε ▷ g := by
      rw [← whisker_exchange]; rw [← whisker_exchange]; rw [leftZigzag]; bicategory
    _ = g ◁ η otimes≫ ε ▷ g := by
      rw [h]; bicategory

中文:
定理 rightZigzag_idempotent_of_left_triangle
  证明: by
  dsimp only [rightZigzag]
  calc
    _ = g ◁ η otimes≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) otimes≫ ε ▷ g := by
      bicategory
    _ = 𝟙 _ otimes≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) otimes≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = g ◁ η otimes≫ g ◁ leftZigzag η ε ▷ g otimes≫ ε ▷ g := by
      rw [← whisker_exchange]; rw [← whisker_exchange]; rw [leftZigzag]; bicategory
    _ = g ◁ η otimes≫ ε ▷ g := by
      rw [h]; bicategory

Depends on / 依赖: bicategory, leftZigzag, otimes, rightZigzag, whisker_exchange
-/
theorem rightZigzag_idempotent_of_left_triangle
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) (h : leftZigzag η ε = (fun_ _).hom ≫ (ρ_ _).inv) :
    rightZigzag η ε otimes≫ rightZigzag η ε = rightZigzag η ε := by
  dsimp only [rightZigzag]
  calc
    _ = g ◁ η otimes≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) otimes≫ ε ▷ g := by
      bicategory
    _ = 𝟙 _ otimes≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) otimes≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = g ◁ η otimes≫ g ◁ leftZigzag η ε ▷ g otimes≫ ε ▷ g := by
      rw [← whisker_exchange]; rw [← whisker_exchange]; rw [leftZigzag]; bicategory
    _ = g ◁ η otimes≫ ε ▷ g := by
      rw [h]; bicategory

/-- Adjunction between two 1-morphisms. -/
@[ext]
/--
Definition of `Adjunction` / `Adjunction` 的定义

English:
structure Adjunction
  parameters: (f : a ⟶ b) (g : b ⟶ a)
  axioms and operations (4):
    - unit : 𝟙 a ⟶ f ≫ g
    - counit : g ≫ f ⟶ 𝟙 b
    - left_triangle : leftZigzag unit counit = (fun_ _).hom ≫ (ρ_ _).inv  [default: by cat_disch]
    - right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (fun_ _).inv  [default: by cat_disch]

中文:
结构 伴随
  参数: (f : a ⟶ b) (g : b ⟶ a)
  公理与运算 (4 个):
    - unit : 𝟙 a ⟶ f ≫ g
    - counit : g ≫ f ⟶ 𝟙 b
    - left_triangle : leftZigzag unit counit = (fun_ _).hom ≫ (ρ_ _).inv  [默认: by cat_disch]
    - right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (fun_ _).inv  [默认: by cat_disch]

Depends on / 依赖: Groupoid, cat_disch
-/
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  /-- The unit of an adjunction. -/
  unit : 𝟙 a ⟶ f ≫ g
  /-- The counit of an adjunction. -/
  counit : g ≫ f ⟶ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzag unit counit = (fun_ _).hom ≫ (ρ_ _).inv := by cat_disch
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (fun_ _).inv := by cat_disch

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (a : B)
  body: (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by bicategory_coherence
  right_triangle := by bicategory_coherence

中文:
定义 id
  签名: (a : B)
  定义体: (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by bicategory_coherence
  right_triangle := by bicategory_coherence
-/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by bicategory_coherence
  right_triangle := by bicategory_coherence

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Adjunction (𝟙 a) (𝟙 a))
  body: ⟨id a⟩

中文:
实例 :
  签名: 可居 (伴随 (𝟙 a) (𝟙 a))
  定义体: ⟨id a⟩
-/
instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
/--
Definition of `compUnit` / `compUnit` 的定义

English:
definition compUnit
  signature: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  body: adj₁.unit otimes≫ f₁ ◁ adj₂.unit ▷ g₁ otimes≫ 𝟙 _

中文:
定义 compUnit
  签名: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  定义体: adj₁.unit otimes≫ f₁ ◁ adj₂.unit ▷ g₁ otimes≫ 𝟙 _

Depends on / 依赖: otimes
-/
def compUnit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
  adj₁.unit otimes≫ f₁ ◁ adj₂.unit ▷ g₁ otimes≫ 𝟙 _

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
/--
Definition of `compCounit` / `compCounit` 的定义

English:
definition compCounit
  signature: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  body: 𝟙 _ otimes≫ g₂ ◁ adj₁.counit ▷ f₂ otimes≫ adj₂.counit

中文:
定义 compCounit
  签名: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  定义体: 𝟙 _ otimes≫ g₂ ◁ adj₁.counit ▷ f₂ otimes≫ adj₂.counit

Depends on / 依赖: counit, otimes
-/
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ otimes≫ g₂ ◁ adj₁.counit ▷ f₂ otimes≫ adj₂.counit

/--
theorem `comp_left_triangle_aux` / 定理 `comp_left_triangle_aux`

English:
theorem comp_left_triangle_aux
  given: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  proof: by
  calc
    _ = 𝟙 _ otimes≫
          adj₁.unit ▷ (f₁ ≫ f₂) otimes≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ otimes≫
              (f₁ ≫ f₂) ◁ adj₂.counit otimes≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ otimes≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ otimes≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [left_triangle]; bicategory

中文:
定理 comp_left_triangle_aux
  条件: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  证明: by
  calc
    _ = 𝟙 _ otimes≫
          adj₁.unit ▷ (f₁ ≫ f₂) otimes≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ otimes≫
              (f₁ ≫ f₂) ◁ adj₂.counit otimes≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ otimes≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ otimes≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [left_triangle]; bicategory

Depends on / 依赖: bicategory, compCounit, compUnit, counit, leftZigzag, left_triangle, otimes, simp_rw, whisker_exchange
-/
theorem comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    leftZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (fun_ _).hom ≫ (ρ_ _).inv := by
  calc
    _ = 𝟙 _ otimes≫
          adj₁.unit ▷ (f₁ ≫ f₂) otimes≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ otimes≫
              (f₁ ≫ f₂) ◁ adj₂.counit otimes≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ otimes≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ otimes≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) otimes≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [left_triangle]; bicategory

/--
theorem `comp_right_triangle_aux` / 定理 `comp_right_triangle_aux`

English:
theorem comp_right_triangle_aux
  given: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  proof: by
  calc
    _ = 𝟙 _ otimes≫
          (g₂ ≫ g₁) ◁ adj₁.unit otimes≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ otimes≫
              adj₂.counit ▷ (g₂ ≫ g₁) otimes≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ otimes≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) otimes≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ otimes≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [right_triangle]; bicategory

中文:
定理 comp_right_triangle_aux
  条件: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  证明: by
  calc
    _ = 𝟙 _ otimes≫
          (g₂ ≫ g₁) ◁ adj₁.unit otimes≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ otimes≫
              adj₂.counit ▷ (g₂ ≫ g₁) otimes≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ otimes≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) otimes≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ otimes≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [right_triangle]; bicategory

Depends on / 依赖: bicategory, compCounit, compUnit, counit, otimes, rightZigzag, right_triangle, simp_rw, whisker_exchange
-/
theorem comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    rightZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (fun_ _).inv := by
  calc
    _ = 𝟙 _ otimes≫
          (g₂ ≫ g₁) ◁ adj₁.unit otimes≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ otimes≫
              adj₂.counit ▷ (g₂ ≫ g₁) otimes≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ otimes≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) otimes≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ otimes≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [right_triangle]; bicategory

/-- Composition of adjunctions. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  body: compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

中文:
定义 comp
  签名: (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
  定义体: compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

Depends on / 依赖: compUnit
-/
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
  unit := compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

end Composition

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

/--
Definition of `leftZigzagIso` / `leftZigzagIso` 的定义

English:
abbreviation leftZigzagIso
  signature: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  body: whiskerRightIso η f ≪otimes≫ whiskerLeftIso f ε

中文:
缩写 leftZigzagIso
  签名: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  定义体: whiskerRightIso η f ≪otimes≫ whiskerLeftIso f ε

Depends on / 依赖: otimes, whiskerLeftIso, whiskerRightIso
-/
abbrev leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪otimes≫ whiskerLeftIso f ε

/--
Definition of `rightZigzagIso` / `rightZigzagIso` 的定义

English:
abbreviation rightZigzagIso
  signature: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  body: whiskerLeftIso g η ≪otimes≫ whiskerRightIso ε g

@[simp]

中文:
缩写 rightZigzagIso
  签名: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  定义体: whiskerLeftIso g η ≪otimes≫ whiskerRightIso ε g

@[simp]

Depends on / 依赖: otimes, whiskerLeftIso, whiskerRightIso
-/
abbrev rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪otimes≫ whiskerRightIso ε g

@[simp]
/--
theorem `leftZigzagIso_hom` / 定理 `leftZigzagIso_hom`

English:
theorem leftZigzagIso_hom
  statement: (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom
  proof: rfl

@[simp]

中文:
定理 leftZigzagIso_hom
  结论: (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom
  证明: rfl

@[simp]
-/
theorem leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom :=
  rfl

@[simp]
/--
theorem `rightZigzagIso_hom` / 定理 `rightZigzagIso_hom`

English:
theorem rightZigzagIso_hom
  statement: (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom
  proof: rfl

@[simp]

中文:
定理 rightZigzagIso_hom
  结论: (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom
  证明: rfl

@[simp]
-/
theorem rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom :=
  rfl

@[simp]
/--
theorem `leftZigzagIso_inv` / 定理 `leftZigzagIso_inv`

English:
theorem leftZigzagIso_inv
  statement: (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv
  proof: by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]

中文:
定理 leftZigzagIso_inv
  结论: (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv
  证明: by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]

Depends on / 依赖: bicategoricalComp, bicategoricalIsoComp
-/
theorem leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
/--
theorem `rightZigzagIso_inv` / 定理 `rightZigzagIso_inv`

English:
theorem rightZigzagIso_inv
  statement: (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv
  proof: by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]

中文:
定理 rightZigzagIso_inv
  结论: (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv
  证明: by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]

Depends on / 依赖: bicategoricalComp, bicategoricalIsoComp
-/
theorem rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
/--
theorem `leftZigzagIso_symm` / 定理 `leftZigzagIso_symm`

English:
theorem leftZigzagIso_symm
  statement: (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm
  proof: Iso.ext (leftZigzagIso_inv η ε)

@[simp]

中文:
定理 leftZigzagIso_symm
  结论: (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm
  证明: Iso.ext (leftZigzagIso_inv η ε)

@[simp]

Depends on / 依赖: Iso.ext, leftZigzagIso_inv
-/
theorem leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm :=
  Iso.ext (leftZigzagIso_inv η ε)

@[simp]
/--
theorem `rightZigzagIso_symm` / 定理 `rightZigzagIso_symm`

English:
theorem rightZigzagIso_symm
  statement: (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm
  proof: Iso.ext (rightZigzagIso_inv η ε)

中文:
定理 rightZigzagIso_symm
  结论: (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm
  证明: Iso.ext (rightZigzagIso_inv η ε)

Depends on / 依赖: Iso.ext, rightZigzagIso_inv
-/
theorem rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm :=
  Iso.ext (rightZigzagIso_inv η ε)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (leftZigzag η.hom ε.hom)
  body: inferInstanceAs IsIso (leftZigzagIso η ε).hom

中文:
实例 :
  签名: 是同构 (leftZigzag η.hom ε.hom)
  定义体: inferInstanceAs IsIso (leftZigzagIso η ε).hom

Depends on / 依赖: leftZigzagIso
-/
instance : IsIso (leftZigzag η.hom ε.hom) := inferInstanceAs IsIso (leftZigzagIso η ε).hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (rightZigzag η.hom ε.hom)
  body: inferInstanceAs IsIso (rightZigzagIso η ε).hom

中文:
实例 :
  签名: 是同构 (rightZigzag η.hom ε.hom)
  定义体: inferInstanceAs IsIso (rightZigzagIso η ε).hom

Depends on / 依赖: rightZigzagIso
-/
instance : IsIso (rightZigzag η.hom ε.hom) := inferInstanceAs IsIso (rightZigzagIso η ε).hom

/--
theorem `right_triangle_of_left_triangle` / 定理 `right_triangle_of_left_triangle`

English:
theorem right_triangle_of_left_triangle
  given: (h : leftZigzag η.hom ε.hom = (fun_ f).hom ≫ (ρ_ f).inv)
  proof: by
  rw [← cancel_epi (rightZigzag η.hom ε.hom ≫ (fun_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzag η.hom ε.hom otimes≫ rightZigzag η.hom ε.hom := by bicategory
    _ = rightZigzag η.hom ε.hom := rightZigzag_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

中文:
定理 right_triangle_of_left_triangle
  条件: (h : leftZigzag η.hom ε.hom = (fun_ f).hom ≫ (ρ_ f).inv)
  证明: by
  rw [← cancel_epi (rightZigzag η.hom ε.hom ≫ (fun_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzag η.hom ε.hom otimes≫ rightZigzag η.hom ε.hom := by bicategory
    _ = rightZigzag η.hom ε.hom := rightZigzag_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

Depends on / 依赖: bicategory, cancel_epi, fun_, otimes, rightZigzag, rightZigzag_idempotent_of_left_triangle
-/
theorem right_triangle_of_left_triangle (h : leftZigzag η.hom ε.hom = (fun_ f).hom ≫ (ρ_ f).inv) :
    rightZigzag η.hom ε.hom = (ρ_ g).hom ≫ (fun_ g).inv := by
  rw [← cancel_epi (rightZigzag η.hom ε.hom ≫ (fun_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzag η.hom ε.hom otimes≫ rightZigzag η.hom ε.hom := by bicategory
    _ = rightZigzag η.hom ε.hom := rightZigzag_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

/--
Definition of `adjointifyCounit` / `adjointifyCounit` 的定义

English:
definition adjointifyCounit
  signature: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  body: whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ fun_ f) ≪≫ ε

中文:
定义 adjointifyCounit
  签名: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  定义体: whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ fun_ f) ≪≫ ε

Depends on / 依赖: fun_, rightZigzagIso, whiskerLeftIso
-/
def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ fun_ f) ≪≫ ε

set_option backward.defeqAttrib.useBackward true in
/--
theorem `adjointifyCounit_left_triangle` / 定理 `adjointifyCounit_left_triangle`

English:
theorem adjointifyCounit_left_triangle
  given: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  proof: by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ otimes≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) otimes≫
          f ◁ g ◁ η.inv ▷ f otimes≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 _ otimes≫ f ◁ ε.inv otimes≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f otimes≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; bicategory
    _ = 𝟙 _ otimes≫ f ◁ ε.inv otimes≫ (η.inv ≫ η.hom) ▷ f otimes≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; bicategory
    _ = 𝟙 _ otimes≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]; bicategory

中文:
定理 adjointifyCounit_left_triangle
  条件: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  证明: by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ otimes≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) otimes≫
          f ◁ g ◁ η.inv ▷ f otimes≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 _ otimes≫ f ◁ ε.inv otimes≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f otimes≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; bicategory
    _ = 𝟙 _ otimes≫ f ◁ ε.inv otimes≫ (η.inv ≫ η.hom) ▷ f otimes≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; bicategory
    _ = 𝟙 _ otimes≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]; bicategory

Depends on / 依赖: Iso.ext, adjointifyCounit, bicategoricalIsoComp, bicategory, otimes, whisker_exchange
-/
theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso η (adjointifyCounit η ε) = fun_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ otimes≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) otimes≫
          f ◁ g ◁ η.inv ▷ f otimes≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 _ otimes≫ f ◁ ε.inv otimes≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f otimes≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; bicategory
    _ = 𝟙 _ otimes≫ f ◁ ε.inv otimes≫ (η.inv ≫ η.hom) ▷ f otimes≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; bicategory
    _ = 𝟙 _ otimes≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]; bicategory

/--
Definition of `Equivalence` / `Equivalence` 的定义

English:
structure Equivalence
  parameters: (a b : B)
  axioms and operations (5):
    - hom : a ⟶ b
    - inv : b ⟶ a
    - unit : 𝟙 a ≅ hom ≫ inv
    - counit : inv ≫ hom ≅ 𝟙 b
    - left_triangle : leftZigzagIso unit counit = fun_ hom ≪≫ (ρ_ hom).symm  [default: by cat_disch]

中文:
结构 等价
  参数: (a b : B)
  公理与运算 (5 个):
    - hom : a ⟶ b
    - inv : b ⟶ a
    - unit : 𝟙 a ≅ hom ≫ inv
    - counit : inv ≫ hom ≅ 𝟙 b
    - left_triangle : leftZigzagIso unit counit = fun_ hom ≪≫ (ρ_ hom).symm  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Equivalence (a b : B) where
  /-- A 1-morphism in one direction. -/
  hom : a ⟶ b
  /-- A 1-morphism in the other direction. -/
  inv : b ⟶ a
  /-- The composition `hom ≫ inv` is isomorphic to the identity. -/
  unit : 𝟙 a ≅ hom ≫ inv
  /-- The composition `inv ≫ hom` is isomorphic to the identity. -/
  counit : inv ≫ hom ≅ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagIso unit counit = fun_ hom ≪≫ (ρ_ hom).symm := by cat_disch

@[inherit_doc] scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (a : B)
  body: ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

中文:
定义 id
  签名: (a : B)
  定义体: ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

Depends on / 依赖: bicategoricalIsoComp
-/
def id (a : B) : a ≌ a := ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Equivalence a a)
  body: ⟨id a⟩

中文:
实例 :
  签名: 可居 (等价 a a)
  定义体: ⟨id a⟩
-/
instance : Inhabited (Equivalence a a) := ⟨id a⟩

/--
theorem `left_triangle_hom` / 定理 `left_triangle_hom`

English:
theorem left_triangle_hom
  given: (e : a ≌ b)
  proof: congrArg Iso.hom e.left_triangle

中文:
定理 left_triangle_hom
  条件: (e : a ≌ b)
  证明: congrArg Iso.hom e.left_triangle

Depends on / 依赖: Iso.hom, e.left_triangle, left_triangle
-/
theorem left_triangle_hom (e : a ≌ b) :
    leftZigzag e.unit.hom e.counit.hom = (fun_ e.hom).hom ≫ (ρ_ e.hom).inv :=
  congrArg Iso.hom e.left_triangle

/--
theorem `right_triangle` / 定理 `right_triangle`

English:
theorem right_triangle
  given: (e : a ≌ b)
  proof: Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)

中文:
定理 right_triangle
  条件: (e : a ≌ b)
  证明: Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)

Depends on / 依赖: Iso.ext, counit, e.counit, e.left_triangle_hom, e.unit, left_triangle_hom, right_triangle_of_left_triangle
-/
theorem right_triangle (e : a ≌ b) :
    rightZigzagIso e.unit e.counit = ρ_ e.inv ≪≫ (fun_ e.inv).symm :=
  Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)

/--
theorem `right_triangle_hom` / 定理 `right_triangle_hom`

English:
theorem right_triangle_hom
  given: (e : a ≌ b)
  proof: congrArg Iso.hom e.right_triangle

中文:
定理 right_triangle_hom
  条件: (e : a ≌ b)
  证明: congrArg Iso.hom e.right_triangle

Depends on / 依赖: Iso.hom, e.right_triangle, right_triangle
-/
theorem right_triangle_hom (e : a ≌ b) :
    rightZigzag e.unit.hom e.counit.hom = (ρ_ e.inv).hom ≫ (fun_ e.inv).inv :=
  congrArg Iso.hom e.right_triangle

/--
Definition of `mkOfAdjointifyCounit` / `mkOfAdjointifyCounit` 的定义

English:
definition mkOfAdjointifyCounit
  signature: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  body: f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

中文:
定义 mkOfAdjointifyCounit
  签名: (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
  定义体: f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε
-/
def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

end Equivalence

end

noncomputable
section

/--
Definition of `RightAdjoint` / `RightAdjoint` 的定义

English:
structure RightAdjoint
  parameters: (left : a ⟶ b)
  axioms and operations (2):
    - right : b ⟶ a
    - adj : left ⊣ right

中文:
结构 右伴随
  参数: (left : a ⟶ b)
  公理与运算 (2 个):
    - right : b ⟶ a
    - adj : left ⊣ right
-/
structure RightAdjoint (left : a ⟶ b) where
  /-- The right adjoint to `left`. -/
  right : b ⟶ a
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/--
Definition of `IsLeftAdjoint` / `IsLeftAdjoint` 的定义

English:
class IsLeftAdjoint
  parameters: (left : a ⟶ b)
  (no additional axioms)

中文:
类 是左伴随
  参数: (left : a ⟶ b)
  (无附加公理)
-/
class IsLeftAdjoint (left : a ⟶ b) : Prop where mk' ::
  nonempty : Nonempty (RightAdjoint left)

/--
theorem `IsLeftAdjoint.mk` / 定理 `IsLeftAdjoint.mk`

English:
theorem IsLeftAdjoint.mk
  given: (adj : f ⊣ g)
  statement: IsLeftAdjoint f
  proof: ⟨⟨g, adj⟩⟩

中文:
定理 是左伴随.mk
  条件: (adj : f ⊣ g)
  结论: 是左伴随 f
  证明: ⟨⟨g, adj⟩⟩
-/
theorem IsLeftAdjoint.mk (adj : f ⊣ g) : IsLeftAdjoint f :=
  ⟨⟨g, adj⟩⟩

/--
Definition of `getRightAdjoint` / `getRightAdjoint` 的定义

English:
definition getRightAdjoint
  signature: (f : a ⟶ b) [IsLeftAdjoint f]
  body: Classical.choice IsLeftAdjoint.nonempty

中文:
定义 getRightAdjoint
  签名: (f : a ⟶ b) [是左伴随 f]
  定义体: Classical.choice IsLeftAdjoint.nonempty

Depends on / 依赖: Classical, Classical.choice, IsLeftAdjoint, IsLeftAdjoint.nonempty, choice, nonempty
-/
def getRightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : RightAdjoint f :=
  Classical.choice IsLeftAdjoint.nonempty

/--
Definition of `rightAdjoint` / `rightAdjoint` 的定义

English:
definition rightAdjoint
  signature: (f : a ⟶ b) [IsLeftAdjoint f]
  body: (getRightAdjoint f).right

中文:
定义 rightAdjoint
  签名: (f : a ⟶ b) [是左伴随 f]
  定义体: (getRightAdjoint f).right

Depends on / 依赖: getRightAdjoint
-/
def rightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : b ⟶ a :=
  (getRightAdjoint f).right

/--
Definition of `Adjunction.ofIsLeftAdjoint` / `Adjunction.ofIsLeftAdjoint` 的定义

English:
definition Adjunction.ofIsLeftAdjoint
  signature: (f : a ⟶ b) [IsLeftAdjoint f]
  body: (getRightAdjoint f).adj

中文:
定义 伴随.ofIsLeftAdjoint
  签名: (f : a ⟶ b) [是左伴随 f]
  定义体: (getRightAdjoint f).adj

Depends on / 依赖: guitartExact_of_isEquivalence_of_isIso
-/
def Adjunction.ofIsLeftAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : f ⊣ rightAdjoint f :=
  (getRightAdjoint f).adj

/--
Definition of `LeftAdjoint` / `LeftAdjoint` 的定义

English:
structure LeftAdjoint
  parameters: (right : b ⟶ a)
  axioms and operations (2):
    - left : a ⟶ b
    - adj : left ⊣ right

中文:
结构 左伴随
  参数: (right : b ⟶ a)
  公理与运算 (2 个):
    - left : a ⟶ b
    - adj : left ⊣ right
-/
structure LeftAdjoint (right : b ⟶ a) where
  /-- The left adjoint to `right`. -/
  left : a ⟶ b
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/--
Definition of `IsRightAdjoint` / `IsRightAdjoint` 的定义

English:
class IsRightAdjoint
  parameters: (right : b ⟶ a)
  (no additional axioms)

中文:
类 是右伴随
  参数: (right : b ⟶ a)
  (无附加公理)
-/
class IsRightAdjoint (right : b ⟶ a) : Prop where mk' ::
  nonempty : Nonempty (LeftAdjoint right)

/--
theorem `IsRightAdjoint.mk` / 定理 `IsRightAdjoint.mk`

English:
theorem IsRightAdjoint.mk
  given: (adj : f ⊣ g)
  statement: IsRightAdjoint g
  proof: ⟨⟨f, adj⟩⟩

中文:
定理 是右伴随.mk
  条件: (adj : f ⊣ g)
  结论: 是右伴随 g
  证明: ⟨⟨f, adj⟩⟩
-/
theorem IsRightAdjoint.mk (adj : f ⊣ g) : IsRightAdjoint g :=
  ⟨⟨f, adj⟩⟩

/--
Definition of `getLeftAdjoint` / `getLeftAdjoint` 的定义

English:
definition getLeftAdjoint
  signature: (f : b ⟶ a) [IsRightAdjoint f]
  body: Classical.choice IsRightAdjoint.nonempty

中文:
定义 getLeftAdjoint
  签名: (f : b ⟶ a) [是右伴随 f]
  定义体: Classical.choice IsRightAdjoint.nonempty

Depends on / 依赖: Classical, Classical.choice, IsRightAdjoint, IsRightAdjoint.nonempty, choice, nonempty
-/
def getLeftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : LeftAdjoint f :=
  Classical.choice IsRightAdjoint.nonempty

/--
Definition of `leftAdjoint` / `leftAdjoint` 的定义

English:
definition leftAdjoint
  signature: (f : b ⟶ a) [IsRightAdjoint f]
  body: (getLeftAdjoint f).left

中文:
定义 leftAdjoint
  签名: (f : b ⟶ a) [是右伴随 f]
  定义体: (getLeftAdjoint f).left

Depends on / 依赖: getLeftAdjoint
-/
def leftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : a ⟶ b :=
  (getLeftAdjoint f).left

/--
Definition of `Adjunction.ofIsRightAdjoint` / `Adjunction.ofIsRightAdjoint` 的定义

English:
definition Adjunction.ofIsRightAdjoint
  signature: (f : b ⟶ a) [IsRightAdjoint f]
  body: (getLeftAdjoint f).adj

中文:
定义 伴随.ofIsRightAdjoint
  签名: (f : b ⟶ a) [是右伴随 f]
  定义体: (getLeftAdjoint f).adj

Depends on / 依赖: getLeftAdjoint
-/
def Adjunction.ofIsRightAdjoint (f : b ⟶ a) [IsRightAdjoint f] : leftAdjoint f ⊣ f :=
  (getLeftAdjoint f).adj

end

end Bicategory

namespace Pseudofunctor

variable (F : Pseudofunctor B C) (adj : f ⊣ g)

/--
lemma `leftZigzag_map` / 引理 `leftZigzag_map`

English:
lemma leftZigzag_map
  proof: by
  simp [leftZigzag, bicategoricalComp]

中文:
引理 leftZigzag_map
  证明: by
  simp [leftZigzag, bicategoricalComp]

Depends on / 依赖: bicategoricalComp, leftZigzag
-/
lemma leftZigzag_map :
    leftZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom)
      ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) =
    (F.mapId a).inv ▷ F.map f otimes≫ (F.mapComp (𝟙 a) f).inv ≫
      F.map₂ (leftZigzag adj.unit adj.counit) ≫
        (F.mapComp f (𝟙 b)).hom otimes≫ F.map f ◁ (F.mapId b).hom := by
  simp [leftZigzag, bicategoricalComp]

/--
lemma `rightZigzag_map` / 引理 `rightZigzag_map`

English:
lemma rightZigzag_map
  proof: by
  simp [rightZigzag, bicategoricalComp, F.map₂_iso_inv]

中文:
引理 rightZigzag_map
  证明: by
  simp [rightZigzag, bicategoricalComp, F.map₂_iso_inv]

Depends on / 依赖: F.map, bicategoricalComp, rightZigzag
-/
lemma rightZigzag_map :
    rightZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom)
      ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) =
    F.map g ◁ (F.mapId a).inv otimes≫ (F.mapComp g (𝟙 a)).inv ≫
      F.map₂ (rightZigzag adj.unit adj.counit) ≫
        (F.mapComp (𝟙 b) g).hom otimes≫ (F.mapId b).hom ▷ F.map g := by
  simp [rightZigzag, bicategoricalComp, F.map₂_iso_inv]

/-- A pseudofunctor carries an adjunction `f ⊣ g` to an adjunction `F.map f ⊣ F.map g`. -/
@[simps]
/--
Definition of `mapAdjunction` / `mapAdjunction` 的定义

English:
definition mapAdjunction
  signature: : F.map f ⊣ F.map g where
  body: (F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom
  counit := (F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom
  left_triangle := by simp [leftZigzag_map, bicategoricalComp, F.map₂_iso_inv]
  right_triangle := by simp [rightZigzag_map, bicategoricalComp, F.map₂_iso_inv]

中文:
定义 mapAdjunction
  签名: : F.map f ⊣ F.map g where
  定义体: (F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom
  counit := (F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom
  left_triangle := by simp [leftZigzag_map, bicategoricalComp, F.map₂_iso_inv]
  right_triangle := by simp [rightZigzag_map, bicategoricalComp, F.map₂_iso_inv]

Depends on / 依赖: F.map, F.mapComp, F.mapId, adj.unit, mapComp
-/
def mapAdjunction : F.map f ⊣ F.map g where
  unit := (F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom
  counit := (F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom
  left_triangle := by simp [leftZigzag_map, bicategoricalComp, F.map₂_iso_inv]
  right_triangle := by simp [rightZigzag_map, bicategoricalComp, F.map₂_iso_inv]

end Pseudofunctor

namespace StrictPseudofunctor

variable (F : StrictPseudofunctor B C) (adj : f ⊣ g)

/-- A strict pseudofunctor carries an adjunction `f ⊣ g` to an adjunction
`F.map f ⊣ F.map g`. -/
@[simps!]
/--
Definition of `mapAdjunction` / `mapAdjunction` 的定义

English:
definition mapAdjunction
  signature: : F.map f ⊣ F.map g
  body: F.toPseudofunctor.mapAdjunction adj

中文:
定义 mapAdjunction
  签名: : F.map f ⊣ F.map g
  定义体: F.toPseudofunctor.mapAdjunction adj

Depends on / 依赖: F.toPseudofunctor.mapAdjunction, mapAdjunction, toPseudofunctor
-/
def mapAdjunction : F.map f ⊣ F.map g := F.toPseudofunctor.mapAdjunction adj

/--
lemma `mapAdjunction_unit'` / 引理 `mapAdjunction_unit'`

English:
lemma mapAdjunction_unit'
  proof: by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

中文:
引理 mapAdjunction_unit'
  证明: by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

Depends on / 依赖: F.mapComp_eq_eqToIso, F.mapId_eq_eqToIso, mapComp_eq_eqToIso, mapId_eq_eqToIso
-/
lemma mapAdjunction_unit' :
    (F.mapAdjunction adj).unit =
      eqToHom (F.map_id a).symm ≫ F.map₂ adj.unit ≫ eqToHom (F.map_comp f g) := by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

/--
lemma `mapAdjunction_counit'` / 引理 `mapAdjunction_counit'`

English:
lemma mapAdjunction_counit'
  proof: by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

中文:
引理 mapAdjunction_counit'
  证明: by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

Depends on / 依赖: F.mapComp_eq_eqToIso, F.mapId_eq_eqToIso, mapComp_eq_eqToIso, mapId_eq_eqToIso
-/
lemma mapAdjunction_counit' :
    (F.mapAdjunction adj).counit =
      eqToHom (F.map_comp g f).symm ≫ F.map₂ adj.counit ≫ eqToHom (F.map_id b) := by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

end StrictPseudofunctor

end CategoryTheory
