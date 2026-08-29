/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).

satisfying various axioms. This is implemented as a typeclass `F.LaxMonoidal`.

Similarly, we define the typeclass `F.OplaxMonoidal`. For these oplax monoidal functors,
we have similar data `η` and `δ`, but with morphisms in the opposite direction.

A monoidal functor (`F.Monoidal`) is defined here as the combination of `F.LaxMonoidal`
and `F.OplaxMonoidal`, with the additional conditions that `ε`/`η` and `μ`/`δ` are
inverse isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See `Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean` for monoidal natural
transformations.

We show in `Mathlib.CategoryTheory.Monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/

@[expose] public section


universe v₁ v₂ v₃ v₁' u₁ u₂ u₃ u₁'

namespace CategoryTheory

open Category CategoryTheory.Functor MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
  {C' : Type u₁'} [Category.{v₁'} C']

namespace Functor

-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
/-- A functor `F : C ⥤ D` between monoidal categories is lax monoidal if it is
equipped with morphisms `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`,
satisfying the appropriate coherences. -/
@[ext]
/--
Definition of `LaxMonoidal` / `LaxMonoidal` 的定义

English:
class LaxMonoidal
  parameters: (F : C ⥤ D)
  axioms and operations (7):
    - ε((F)) : 𝟙_ D ⟶ F.obj (𝟙_ C)
    - μ((F)) : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)
    - μ_natural_left((F)) : forall {X Y : C} (f : X ⟶ Y) (X' : C), F.map f ▷ F.obj X' ≫ μ Y X' = μ X X' ≫ F.map (f ▷ X')  [default: by cat_disch]
    - μ_natural_right((F)) : forall {X Y : C} (X' : C) (f : X ⟶ Y), F.obj X' ◁ F.map f ≫ μ X' Y = μ X' X ≫ F.map (X' ◁ f)  [default: by cat_disch]
    - associativity((F)) : forall X Y Z : C, μ X Y ▷ F.obj Z ≫ μ (X otimes Y) Z ≫ F.map (α_ X Y Z).hom = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ Y Z ≫ μ X (Y otimes Z)  [default: by cat_disch]
    - left_unitality((F)) : forall X : C, (fun_ (F.obj X)).hom = ε ▷ F.obj X ≫ μ (𝟙_ C) X ≫ F.map (fun_ X).hom  [default: by cat_disch]
    - right_unitality((F)) : forall X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ ε ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom  [default: by cat_disch]

中文:
类 LaxMonoidal
  参数: (F : C ⥤ D)
  公理与运算 (7 个):
    - ε((F)) : 𝟙_ D ⟶ F.obj (𝟙_ C)
    - μ((F)) : 对任意 X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)
    - μ_natural_left((F)) : 对任意 {X Y : C} (f : X ⟶ Y) (X' : C), F.map f ▷ F.obj X' ≫ μ Y X' = μ X X' ≫ F.map (f ▷ X')  [默认: by cat_disch]
    - μ_natural_right((F)) : 对任意 {X Y : C} (X' : C) (f : X ⟶ Y), F.obj X' ◁ F.map f ≫ μ X' Y = μ X' X ≫ F.map (X' ◁ f)  [默认: by cat_disch]
    - associativity((F)) : 对任意 X Y Z : C, μ X Y ▷ F.obj Z ≫ μ (X otimes Y) Z ≫ F.map (α_ X Y Z).hom = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ Y Z ≫ μ X (Y otimes Z)  [默认: by cat_disch]
    - left_unitality((F)) : 对任意 X : C, (fun_ (F.obj X)).hom = ε ▷ F.obj X ≫ μ (𝟙_ C) X ≫ F.map (fun_ X).hom  [默认: by cat_disch]
    - right_unitality((F)) : 对任意 X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ ε ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom  [默认: by cat_disch]

Depends on / 依赖: F.map, F.obj, cat_disch
-/
class LaxMonoidal (F : C ⥤ D) where
  /-- the unit morphism of a lax monoidal functor -/
  ε (F) : 𝟙_ D ⟶ F.obj (𝟙_ C)
  /-- the tensorator of a lax monoidal functor -/
  μ (F) : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)
  μ_natural_left (F) :
    forall {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ μ Y X' = μ X X' ≫ F.map (f ▷ X') := by
    cat_disch
  μ_natural_right (F) :
    forall {X Y : C} (X' : C) (f : X ⟶ Y),
      F.obj X' ◁ F.map f ≫ μ X' Y = μ X' X ≫ F.map (X' ◁ f) := by
    cat_disch
  /-- associativity of the tensorator -/
  associativity (F) :
    forall X Y Z : C,
      μ X Y ▷ F.obj Z ≫ μ (X otimes Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ Y Z ≫ μ X (Y otimes Z) := by
    cat_disch
  -- unitality
  left_unitality (F) :
    forall X : C, (fun_ (F.obj X)).hom = ε ▷ F.obj X ≫ μ (𝟙_ C) X ≫ F.map (fun_ X).hom := by
      cat_disch
  right_unitality (F) :
    forall X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ ε ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
    cat_disch

namespace LaxMonoidal

attribute [reassoc (attr := simp)] μ_natural_left μ_natural_right
  associativity

attribute [simp, reassoc] right_unitality left_unitality

section

variable (F : C ⥤ D) [F.LaxMonoidal]

@[reassoc (attr := simp)]
/--
theorem `μ_natural` / 定理 `μ_natural`

English:
theorem μ_natural
  given: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  proof: by
  simp [tensorHom_def]

@[reassoc (attr := simp)]

中文:
定理 μ_natural
  条件: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  证明: by
  simp [tensorHom_def]

@[reassoc (attr := simp)]

Depends on / 依赖: tensorHom_def
-/
theorem μ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f otimesₘ F.map g) ≫ μ F Y Y' = μ F X X' ≫ F.map (f otimesₘ g) := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
/--
theorem `left_unitality_inv` / 定理 `left_unitality_inv`

English:
theorem left_unitality_inv
  given: (X : C)
  proof: by
  rw [Iso.inv_comp_eq]; rw [left_unitality]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc (attr := simp)]

中文:
定理 left_unitality_inv
  条件: (X : C)
  证明: by
  rw [Iso.inv_comp_eq]; rw [left_unitality]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, F.map_comp, F.map_id, Iso.hom_inv_id, Iso.inv_comp_eq, comp_id, hom_inv_id, inv_comp_eq, left_unitality, map_comp, map_id
-/
theorem left_unitality_inv (X : C) :
    (fun_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X = F.map (fun_ X).inv := by
  rw [Iso.inv_comp_eq]; rw [left_unitality]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc (attr := simp)]
/--
theorem `right_unitality_inv` / 定理 `right_unitality_inv`

English:
theorem right_unitality_inv
  given: (X : C)
  proof: by
  rw [Iso.inv_comp_eq]; rw [right_unitality]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc (attr := simp)]

中文:
定理 right_unitality_inv
  条件: (X : C)
  证明: by
  rw [Iso.inv_comp_eq]; rw [right_unitality]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, F.map_comp, F.map_id, Iso.hom_inv_id, Iso.inv_comp_eq, comp_id, hom_inv_id, inv_comp_eq, map_comp, map_id, right_unitality
-/
theorem right_unitality_inv (X : C) :
    (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (𝟙_ C) = F.map (ρ_ X).inv := by
  rw [Iso.inv_comp_eq]; rw [right_unitality]; rw [Category.assoc]; rw [Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc (attr := simp)]
/--
theorem `associativity_inv` / 定理 `associativity_inv`

English:
theorem associativity_inv
  given: (X Y Z : C)
  proof: by
  rw [Iso.eq_inv_comp]; rw [← associativity_assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc]

中文:
定理 associativity_inv
  条件: (X Y Z : C)
  证明: by
  rw [Iso.eq_inv_comp]; rw [← associativity_assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc]

Depends on / 依赖: F.map_comp, F.map_id, Iso.eq_inv_comp, Iso.hom_inv_id, associativity_assoc, comp_id, eq_inv_comp, hom_inv_id, map_comp, map_id
-/
theorem associativity_inv (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X otimes Y) Z := by
  rw [Iso.eq_inv_comp]; rw [← associativity_assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [comp_id]

@[reassoc]
/--
lemma `ε_tensorHom_comp_μ` / 引理 `ε_tensorHom_comp_μ`

English:
lemma ε_tensorHom_comp_μ
  given: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  proof: by
  simp [tensorHom_def']

@[reassoc]

中文:
引理 ε_tensorHom_comp_μ
  条件: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  证明: by
  simp [tensorHom_def']

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
lemma ε_tensorHom_comp_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (ε F otimesₘ f) ≫ μ F (𝟙_ C) X = 𝟙_ D ◁ f ≫ (fun_ (F.obj X)).hom ≫ F.map (fun_ X).inv := by
  simp [tensorHom_def']

@[reassoc]
/--
lemma `tensorHom_ε_comp_μ` / 引理 `tensorHom_ε_comp_μ`

English:
lemma tensorHom_ε_comp_μ
  given: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  proof: by
  simp [tensorHom_def]

@[reassoc]

中文:
引理 tensorHom_ε_comp_μ
  条件: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  证明: by
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
lemma tensorHom_ε_comp_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (f otimesₘ ε F) ≫ μ F X (𝟙_ C) = f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
  simp [tensorHom_def]

@[reassoc]
/--
lemma `tensorUnit_whiskerLeft_comp_leftUnitor_hom` / 引理 `tensorUnit_whiskerLeft_comp_leftUnitor_hom`

English:
lemma tensorUnit_whiskerLeft_comp_leftUnitor_hom
  given: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  proof: by
  simp [tensorHom_def']

@[reassoc]

中文:
引理 tensorUnit_whiskerLeft_comp_leftUnitor_hom
  条件: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  证明: by
  simp [tensorHom_def']

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
lemma tensorUnit_whiskerLeft_comp_leftUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    𝟙_ D ◁ f ≫ (fun_ (F.obj X)).hom = (ε F otimesₘ f) ≫ μ F (𝟙_ C) X ≫ F.map (fun_ X).hom := by
  simp [tensorHom_def']

@[reassoc]
/--
lemma `whiskerRight_tensorUnit_comp_rightUnitor_hom` / 引理 `whiskerRight_tensorUnit_comp_rightUnitor_hom`

English:
lemma whiskerRight_tensorUnit_comp_rightUnitor_hom
  given: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  proof: by
  simp [tensorHom_def]

@[reassoc]

中文:
引理 whiskerRight_tensorUnit_comp_rightUnitor_hom
  条件: {X : C} {Y : D} (f : Y ⟶ F.obj X)
  证明: by
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
lemma whiskerRight_tensorUnit_comp_rightUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom = (f otimesₘ ε F) ≫ μ F X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  simp [tensorHom_def]

@[reassoc]
/--
lemma `μ_whiskerRight_comp_μ` / 引理 `μ_whiskerRight_comp_μ`

English:
lemma μ_whiskerRight_comp_μ
  given: (X Y Z : C)
  proof: by
  rw [← associativity_assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [map_id]; rw [Category.comp_id]

@[reassoc]

中文:
引理 μ_whiskerRight_comp_μ
  条件: (X Y Z : C)
  证明: by
  rw [← associativity_assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [map_id]; rw [Category.comp_id]

@[reassoc]

Depends on / 依赖: Category, Category.comp_id, F.map_comp, Iso.hom_inv_id, associativity_assoc, comp_id, hom_inv_id, map_comp, map_id
-/
lemma μ_whiskerRight_comp_μ (X Y Z : C) :
    μ F X Y ▷ F.obj Z ≫ μ F (X otimes Y) Z = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) ≫ F.map (α_ X Y Z).inv := by
  rw [← associativity_assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [map_id]; rw [Category.comp_id]

@[reassoc]
/--
lemma `whiskerLeft_μ_comp_μ` / 引理 `whiskerLeft_μ_comp_μ`

English:
lemma whiskerLeft_μ_comp_μ
  given: (X Y Z : C)
  proof: by
  rw [associativity]; rw [Iso.inv_hom_id_assoc]

中文:
引理 whiskerLeft_μ_comp_μ
  条件: (X Y Z : C)
  证明: by
  rw [associativity]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, associativity, inv_hom_id_assoc
-/
lemma whiskerLeft_μ_comp_μ (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) = (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
      μ F X Y ▷ F.obj Z ≫ μ F (X otimes Y) Z ≫ F.map (α_ X Y Z).hom := by
  rw [associativity]; rw [Iso.inv_hom_id_assoc]

/-- Copy of a lax monoidal structure with new `ε` and `μ` fields equal to the old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {F : C ⥤ D} (hF : F.LaxMonoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  body: ε'
  μ := μ'

中文:
定义 copy
  签名: {F : C ⥤ D} (hF : F.LaxMonoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  定义体: ε'
  μ := μ'

Depends on / 依赖: F.LaxMonoidal, LaxMonoidal, cat_disch
-/
def copy {F : C ⥤ D} (hF : F.LaxMonoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y))
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch) : F.LaxMonoidal where
  ε := ε'
  μ := μ'

end

section

variable {F : C ⥤ D}
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator -/
    (μ : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y))
    (μ_natural :
      forall {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (F.map f otimesₘ F.map g) ≫ μ Y Y' = μ X X' ≫ F.map (f otimesₘ g) := by
      cat_disch)
    /- associativity of the tensorator -/
    (associativity :
      forall X Y Z : C,
        (μ X Y otimesₘ 𝟙 (F.obj Z)) ≫ μ (X otimes Y) Z ≫ F.map (α_ X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) otimesₘ μ Y Z) ≫ μ X (Y otimes Z) := by
      cat_disch)
    /- unitality -/
    (left_unitality :
      forall X : C, (fun_ (F.obj X)).hom = (ε otimesₘ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (fun_ X).hom := by
        cat_disch)
    (right_unitality :
      forall X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) otimesₘ ε) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
        cat_disch)

set_option backward.privateInPublic true in
/--
A constructor for lax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
@[instance_reducible]
/--
Definition of `ofTensorHom` / `ofTensorHom` 的定义

English:
definition ofTensorHom
  signature: : F.LaxMonoidal where
  body: ε
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← tensorHom_id, ← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← id_tensorHom, ← F.map_id, μ_natural]
  associativity := fun X Y Z => by
    simp_rw [← tensorHom_id, ← id_tensorHom, associativity]
  left_unitality :=

中文:
定义 ofTensorHom
  签名: : F.LaxMonoidal where
  定义体: ε
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← tensorHom_id, ← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← id_tensorHom, ← F.map_id, μ_natural]
  associativity := fun X Y Z => by
    simp_rw [← tensorHom_id, ← id_tensorHom, associativity]
  left_unitality :=
-/
def ofTensorHom : F.LaxMonoidal where
  ε := ε
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← tensorHom_id, ← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← id_tensorHom, ← F.map_id, μ_natural]
  associativity := fun X Y Z => by
    simp_rw [← tensorHom_id, ← id_tensorHom, associativity]
  left_unitality := fun X => by
    simp_rw [← tensorHom_id, left_unitality]
  right_unitality := fun X => by
    simp_rw [← id_tensorHom, right_unitality]

end

@[simps]
/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : (𝟭 C).LaxMonoidal where
  body: 𝟙 _
  μ _ _ := 𝟙 _

中文:
实例 id
  签名: : (𝟭 C).LaxMonoidal where
  定义体: 𝟙 _
  μ _ _ := 𝟙 _
-/
instance id : (𝟭 C).LaxMonoidal where
  ε := 𝟙 _
  μ _ _ := 𝟙 _

section

variable (F : C ⥤ D) (G : D ⥤ E)

variable [F.LaxMonoidal] [G.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: : (F ⋙ G).LaxMonoidal where
  body: ε G ≫ G.map (ε F)
  μ X Y := μ G _ _ ≫ G.map (μ F X Y)
  μ_natural_left _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
  μ_natural_right _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]


中文:
实例 comp
  签名: : (F ⋙ G).LaxMonoidal where
  定义体: ε G ≫ G.map (ε F)
  μ X Y := μ G _ _ ≫ G.map (μ F X Y)
  μ_natural_left _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
  μ_natural_right _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]


Depends on / 依赖: G.map
-/
instance comp : (F ⋙ G).LaxMonoidal where
  ε := ε G ≫ G.map (ε F)
  μ X Y := μ G _ _ ≫ G.map (μ F X Y)
  μ_natural_left _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
  μ_natural_right _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]
  associativity _ _ _ := by
    dsimp
    simp_rw [comp_whiskerRight, assoc, μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
      assoc, μ_natural_right_assoc, ← associativity_assoc, ← G.map_comp, associativity]

end

end LaxMonoidal

/-- A functor `F : C ⥤ D` between monoidal categories is oplax monoidal if it is
equipped with morphisms `η : F.obj (𝟙_ C) ⟶ 𝟙 _D` and `δ X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y`,
satisfying the appropriate coherences. -/
@[ext]
/--
Definition of `OplaxMonoidal` / `OplaxMonoidal` 的定义

English:
class OplaxMonoidal
  parameters: (F : C ⥤ D)
  axioms and operations (7):
    - η((F)) : F.obj (𝟙_ C) ⟶ 𝟙_ D
    - δ((F)) : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y
    - δ_natural_left((F)) : forall {X Y : C} (f : X ⟶ Y) (X' : C), δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X'  [default: by cat_disch]
    - δ_natural_right((F)) : forall {X Y : C} (X' : C) (f : X ⟶ Y), δ X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ X' Y  [default: by cat_disch]
    - oplax_associativity((F)) : forall X Y Z : C, δ (X otimes Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom = F.map (α_ X Y Z).hom ≫ δ X (Y otimes Z) ≫ F.obj X ◁ δ Y Z  [default: by cat_disch]
    - oplax_left_unitality((F)) : forall X : C, (fun_ (F.obj X)).inv = F.map (fun_ X).inv ≫ δ (𝟙_ C) X ≫ η ▷ F.obj X  [default: by cat_disch]
    - oplax_right_unitality((F)) : forall X : C, (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ η  [default: by cat_disch]

中文:
类 OplaxMonoidal
  参数: (F : C ⥤ D)
  公理与运算 (7 个):
    - η((F)) : F.obj (𝟙_ C) ⟶ 𝟙_ D
    - δ((F)) : 对任意 X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y
    - δ_natural_left((F)) : 对任意 {X Y : C} (f : X ⟶ Y) (X' : C), δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X'  [默认: by cat_disch]
    - δ_natural_right((F)) : 对任意 {X Y : C} (X' : C) (f : X ⟶ Y), δ X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ X' Y  [默认: by cat_disch]
    - oplax_associativity((F)) : 对任意 X Y Z : C, δ (X otimes Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom = F.map (α_ X Y Z).hom ≫ δ X (Y otimes Z) ≫ F.obj X ◁ δ Y Z  [默认: by cat_disch]
    - oplax_left_unitality((F)) : 对任意 X : C, (fun_ (F.obj X)).inv = F.map (fun_ X).inv ≫ δ (𝟙_ C) X ≫ η ▷ F.obj X  [默认: by cat_disch]
    - oplax_right_unitality((F)) : 对任意 X : C, (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ η  [默认: by cat_disch]

Depends on / 依赖: F.map, F.obj, cat_disch
-/
class OplaxMonoidal (F : C ⥤ D) where
  /-- the counit morphism of a lax monoidal functor -/
  η (F) : F.obj (𝟙_ C) ⟶ 𝟙_ D
  /-- the cotensorator of an oplax monoidal functor -/
  δ (F) : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y
  δ_natural_left (F) :
    forall {X Y : C} (f : X ⟶ Y) (X' : C),
      δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X' := by
    cat_disch
  δ_natural_right (F) :
    forall {X Y : C} (X' : C) (f : X ⟶ Y),
      δ X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ X' Y := by
    cat_disch
  /-- associativity of the tensorator -/
  oplax_associativity (F) :
    forall X Y Z : C,
      δ (X otimes Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ δ X (Y otimes Z) ≫ F.obj X ◁ δ Y Z := by
    cat_disch
  -- unitality
  oplax_left_unitality (F) :
    forall X : C, (fun_ (F.obj X)).inv = F.map (fun_ X).inv ≫ δ (𝟙_ C) X ≫ η ▷ F.obj X := by
      cat_disch
  oplax_right_unitality (F) :
    forall X : C, (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ η := by
      cat_disch

namespace OplaxMonoidal

attribute [reassoc (attr := simp)] δ_natural_left δ_natural_right

@[reassoc (attr := simp)]
alias associativity := oplax_associativity

@[simp, reassoc]
alias left_unitality := oplax_left_unitality

@[simp, reassoc]
alias right_unitality := oplax_right_unitality

section

variable (F : C ⥤ D) [F.OplaxMonoidal]

@[reassoc (attr := simp)]
/--
theorem `δ_natural` / 定理 `δ_natural`

English:
theorem δ_natural
  given: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  proof: by
  simp [tensorHom_def]

@[reassoc (attr := simp)]

中文:
定理 δ_natural
  条件: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  证明: by
  simp [tensorHom_def]

@[reassoc (attr := simp)]

Depends on / 依赖: tensorHom_def
-/
theorem δ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    δ F X X' ≫ (F.map f otimesₘ F.map g) = F.map (f otimesₘ g) ≫ δ F Y Y' := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
/--
theorem `left_unitality_hom` / 定理 `left_unitality_hom`

English:
theorem left_unitality_hom
  given: (X : C)
  proof: by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [left_unitality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [id_comp]

@[reassoc (attr := simp)]

中文:
定理 left_unitality_hom
  条件: (X : C)
  证明: by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [left_unitality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [id_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, F.map_comp, F.map_id, Iso.eq_comp_inv, Iso.hom_inv_id, eq_comp_inv, hom_inv_id, id_comp, left_unitality, map_comp, map_id
-/
theorem left_unitality_hom (X : C) :
    δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (fun_ (F.obj X)).hom = F.map (fun_ X).hom := by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [left_unitality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [id_comp]

@[reassoc (attr := simp)]
/--
theorem `right_unitality_hom` / 定理 `right_unitality_hom`

English:
theorem right_unitality_hom
  given: (X : C)
  proof: by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [right_unitality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [id_comp]

@[reassoc (attr := simp)]

中文:
定理 right_unitality_hom
  条件: (X : C)
  证明: by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [right_unitality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [id_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, F.map_comp, F.map_id, Iso.eq_comp_inv, Iso.hom_inv_id, eq_comp_inv, hom_inv_id, id_comp, map_comp, map_id, right_unitality
-/
theorem right_unitality_hom (X : C) :
    δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [right_unitality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.hom_inv_id]; rw [F.map_id]; rw [id_comp]

@[reassoc (attr := simp)]
/--
theorem `associativity_inv` / 定理 `associativity_inv`

English:
theorem associativity_inv
  given: (X Y Z : C)
  proof: by
  rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Category.assoc]; rw [associativity]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.inv_hom_id]; rw [F.map_id]; rw [id_comp]

@[reassoc]

中文:
定理 associativity_inv
  条件: (X Y Z : C)
  证明: by
  rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Category.assoc]; rw [associativity]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.inv_hom_id]; rw [F.map_id]; rw [id_comp]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, F.map_comp, F.map_id, Iso.comp_inv_eq, Iso.inv_hom_id, associativity, comp_inv_eq, id_comp, inv_hom_id, map_comp, map_id
-/
theorem associativity_inv (X Y Z : C) :
    δ F X (Y otimes Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.map (α_ X Y Z).inv ≫ δ F (X otimes Y) Z ≫ δ F X Y ▷ F.obj Z := by
  rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Category.assoc]; rw [associativity]; rw [← Category.assoc]; rw [← F.map_comp]; rw [Iso.inv_hom_id]; rw [F.map_id]; rw [id_comp]

@[reassoc]
/--
lemma `δ_comp_η_tensorHom` / 引理 `δ_comp_η_tensorHom`

English:
lemma δ_comp_η_tensorHom
  given: {X : C} {Y : D} (f : F.obj X ⟶ Y)
  proof: by
  simp [tensorHom_def]

@[reassoc]

中文:
引理 δ_comp_η_tensorHom
  条件: {X : C} {Y : D} (f : F.obj X ⟶ Y)
  证明: by
  simp [tensorHom_def]

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
lemma δ_comp_η_tensorHom {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F (𝟙_ C) X ≫ (η F otimesₘ f) = F.map (fun_ X).hom ≫ (fun_ (F.obj X)).inv ≫ 𝟙_ D ◁ f := by
  simp [tensorHom_def]

@[reassoc]
/--
lemma `δ_comp_tensorHom_η` / 引理 `δ_comp_tensorHom_η`

English:
lemma δ_comp_tensorHom_η
  given: {X : C} {Y : D} (f : F.obj X ⟶ Y)
  proof: by
  simp [tensorHom_def']

@[reassoc]

中文:
引理 δ_comp_tensorHom_η
  条件: {X : C} {Y : D} (f : F.obj X ⟶ Y)
  证明: by
  simp [tensorHom_def']

@[reassoc]

Depends on / 依赖: tensorHom_def
-/
lemma δ_comp_tensorHom_η {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F X (𝟙_ C) ≫ (f otimesₘ η F) = F.map (ρ_ X).hom ≫ (ρ_ (F.obj X)).inv ≫ f ▷ 𝟙_ D := by
  simp [tensorHom_def']

@[reassoc]
/--
lemma `δ_comp_δ_whiskerRight` / 引理 `δ_comp_δ_whiskerRight`

English:
lemma δ_comp_δ_whiskerRight
  given: (X Y Z : C)
  proof: by
  rw [← associativity_assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

@[reassoc]

中文:
引理 δ_comp_δ_whiskerRight
  条件: (X Y Z : C)
  证明: by
  rw [← associativity_assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

@[reassoc]

Depends on / 依赖: Category, Category.comp_id, Iso.hom_inv_id, associativity_assoc, comp_id, hom_inv_id, infer_instance
-/
lemma δ_comp_δ_whiskerRight (X Y Z : C) :
    δ F (X otimes Y) Z ≫ δ F X Y ▷ F.obj Z = F.map (α_ X Y Z).hom ≫
      δ F X (Y otimes Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  rw [← associativity_assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

@[reassoc]
/--
lemma `δ_comp_whiskerLeft_δ` / 引理 `δ_comp_whiskerLeft_δ`

English:
lemma δ_comp_whiskerLeft_δ
  given: (X Y Z : C)
  proof: by
  rw [associativity]; rw [← F.map_comp_assoc]; rw [Iso.inv_hom_id]; rw [Functor.map_id]; rw [Category.id_comp]

中文:
引理 δ_comp_whiskerLeft_δ
  条件: (X Y Z : C)
  证明: by
  rw [associativity]; rw [← F.map_comp_assoc]; rw [Iso.inv_hom_id]; rw [Functor.map_id]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, F.map_comp_assoc, Functor, Functor.map_id, Iso.inv_hom_id, associativity, id_comp, inv_hom_id, map_comp_assoc, map_id
-/
lemma δ_comp_whiskerLeft_δ (X Y Z : C) :
    δ F X (Y otimes Z) ≫ F.obj X ◁ δ F Y Z = F.map (α_ X Y Z).inv ≫
      δ F (X otimes Y) Z ≫ δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  rw [associativity]; rw [← F.map_comp_assoc]; rw [Iso.inv_hom_id]; rw [Functor.map_id]; rw [Category.id_comp]

end

/-- Copy of an oplax monoidal structure on a functor `F` with new `η` and `δ` fields equal to the
old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {F : C ⥤ D} (hF : F.OplaxMonoidal) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
  body: η'
  δ := δ'

@[simps]

中文:
定义 copy
  签名: {F : C ⥤ D} (hF : F.OplaxMonoidal) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
  定义体: η'
  δ := δ'

@[simps]

Depends on / 依赖: F.OplaxMonoidal, OplaxMonoidal, cat_disch
-/
def copy {F : C ⥤ D} (hF : F.OplaxMonoidal) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (δ' : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y)
    (hη : η' = η F := by cat_disch) (hδ : δ' = δ F := by cat_disch) : F.OplaxMonoidal where
  η := η'
  δ := δ'

@[simps]
/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : (𝟭 C).OplaxMonoidal where
  body: 𝟙 _
  δ _ _ := 𝟙 _

中文:
实例 id
  签名: : (𝟭 C).OplaxMonoidal where
  定义体: 𝟙 _
  δ _ _ := 𝟙 _
-/
instance id : (𝟭 C).OplaxMonoidal where
  η := 𝟙 _
  δ _ _ := 𝟙 _

section

variable (F : C ⥤ D) (G : D ⥤ E) [F.OplaxMonoidal] [G.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: : (F ⋙ G).OplaxMonoidal where
  body: G.map (η F) ≫ η G
  δ X Y := G.map (δ F X Y) ≫ δ G _ _
  δ_natural_left {X Y} f X' := by
    dsimp
    rw [assoc]; rw [δ_natural_left]; rw [← G.map_comp_assoc]; rw [δ_natural_left]; rw [map_comp]; rw [assoc]
  δ_natural_right _ _ := by
    dsimp
    rw [assoc]; rw [δ_natural_right]; rw [← G.map_comp

中文:
实例 comp
  签名: : (F ⋙ G).OplaxMonoidal where
  定义体: G.map (η F) ≫ η G
  δ X Y := G.map (δ F X Y) ≫ δ G _ _
  δ_natural_left {X Y} f X' := by
    dsimp
    rw [assoc]; rw [δ_natural_left]; rw [← G.map_comp_assoc]; rw [δ_natural_left]; rw [map_comp]; rw [assoc]
  δ_natural_right _ _ := by
    dsimp
    rw [assoc]; rw [δ_natural_right]; rw [← G.map_comp

Depends on / 依赖: G.map
-/
instance comp : (F ⋙ G).OplaxMonoidal where
  η := G.map (η F) ≫ η G
  δ X Y := G.map (δ F X Y) ≫ δ G _ _
  δ_natural_left {X Y} f X' := by
    dsimp
    rw [assoc]; rw [δ_natural_left]; rw [← G.map_comp_assoc]; rw [δ_natural_left]; rw [map_comp]; rw [assoc]
  δ_natural_right _ _ := by
    dsimp
    rw [assoc]; rw [δ_natural_right]; rw [← G.map_comp_assoc]; rw [δ_natural_right]; rw [map_comp]; rw [assoc]
  oplax_associativity X Y Z := by
    dsimp
    rw [comp_whiskerRight]; rw [assoc]; rw [assoc]; rw [assoc]; rw [δ_natural_left_assoc]; rw [associativity]; rw [← G.map_comp_assoc]; rw [← G.map_comp_assoc]; rw [assoc]; rw [associativity]; rw [map_comp]; rw [map_comp]; rw [assoc]; rw [assoc]; rw [MonoidalCategory.whiskerLeft_comp]; rw [δ_natural_right_assoc]

end

end OplaxMonoidal

open LaxMonoidal OplaxMonoidal

/-- A functor between monoidal categories is monoidal if it is lax and oplax monoidals,
and both data give inverse isomorphisms. -/
@[ext]
/--
Definition of `Monoidal` / `Monoidal` 的定义

English:
class Monoidal
  parameters: (F : C ⥤ D)
  extends: F.LaxMonoidal, F.OplaxMonoidal
  axioms and operations (4):
    - ε_η((F)) : ε ≫ η = 𝟙 _  [default: by cat_disch]
    - η_ε((F)) : η ≫ ε = 𝟙 _  [default: by cat_disch]
    - μ_δ((F) (X Y : C)) : μ X Y ≫ δ X Y = 𝟙 _  [default: by cat_disch]
    - δ_μ((F) (X Y : C)) : δ X Y ≫ μ X Y = 𝟙 _  [default: by cat_disch]

中文:
类 Monoidal
  参数: (F : C ⥤ D)
  继承: F.LaxMonoidal, F.OplaxMonoidal
  公理与运算 (4 个):
    - ε_η((F)) : ε ≫ η = 𝟙 _  [默认: by cat_disch]
    - η_ε((F)) : η ≫ ε = 𝟙 _  [默认: by cat_disch]
    - μ_δ((F) (X Y : C)) : μ X Y ≫ δ X Y = 𝟙 _  [默认: by cat_disch]
    - δ_μ((F) (X Y : C)) : δ X Y ≫ μ X Y = 𝟙 _  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class Monoidal (F : C ⥤ D) extends F.LaxMonoidal, F.OplaxMonoidal where
  ε_η (F) : ε ≫ η = 𝟙 _ := by cat_disch
  η_ε (F) : η ≫ ε = 𝟙 _ := by cat_disch
  μ_δ (F) (X Y : C) : μ X Y ≫ δ X Y = 𝟙 _ := by cat_disch
  δ_μ (F) (X Y : C) : δ X Y ≫ μ X Y = 𝟙 _ := by cat_disch

namespace Monoidal

attribute [reassoc (attr := simp)] ε_η η_ε μ_δ δ_μ

section

variable (F : C ⥤ D) [F.Monoidal]

/-- The isomorphism `𝟙_ D ≅ F.obj (𝟙_ C)` when `F` is a monoidal functor. -/
@[simps]
/--
Definition of `εIso` / `εIso` 的定义

English:
definition εIso
  signature: : 𝟙_ D ≅ F.obj (𝟙_ C) where
  body: ε F
  inv := η F

中文:
定义 εIso
  签名: : 𝟙_ D ≅ F.obj (𝟙_ C) where
  定义体: ε F
  inv := η F
-/
def εIso : 𝟙_ D ≅ F.obj (𝟙_ C) where
  hom := ε F
  inv := η F

/-- The isomorphism `F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)` when `F` is a monoidal functor. -/
@[simps]
/--
Definition of `μIso` / `μIso` 的定义

English:
definition μIso
  signature: (X Y : C)
  body: μ F X Y
  inv := δ F X Y

中文:
定义 μIso
  签名: (X Y : C)
  定义体: μ F X Y
  inv := δ F X Y
-/
def μIso (X Y : C) : F.obj X otimes F.obj Y ≅ F.obj (X otimes Y) where
  hom := μ F X Y
  inv := δ F X Y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (ε F)
  body: (εIso F).isIso_hom

中文:
实例 :
  签名: IsIso (ε F)
  定义体: (εIso F).isIso_hom

Depends on / 依赖: isIso_hom
-/
instance : IsIso (ε F) := (εIso F).isIso_hom
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (η F)
  body: (εIso F).isIso_inv

中文:
实例 :
  签名: IsIso (η F)
  定义体: (εIso F).isIso_inv

Depends on / 依赖: isIso_inv
-/
instance : IsIso (η F) := (εIso F).isIso_inv
instance (X Y : C) : IsIso (μ F X Y) := (μIso F X Y).isIso_hom
instance (X Y : C) : IsIso (δ F X Y) := (μIso F X Y).isIso_inv

@[reassoc (attr := simp)]
/--
lemma `map_ε_η` / 引理 `map_ε_η`

English:
lemma map_ε_η
  given: (G : D ⥤ C')
  statement: G.map (ε F) ≫ G.map (η F) = 𝟙 _
  proof: (εIso F).map_hom_inv_id G

@[reassoc (attr := simp)]

中文:
引理 map_ε_η
  条件: (G : D ⥤ C')
  结论: G.map (ε F) ≫ G.map (η F) = 𝟙 _
  证明: (εIso F).map_hom_inv_id G

@[reassoc (attr := simp)]

Depends on / 依赖: map_hom_inv_id
-/
lemma map_ε_η (G : D ⥤ C') : G.map (ε F) ≫ G.map (η F) = 𝟙 _ :=
  (εIso F).map_hom_inv_id G

@[reassoc (attr := simp)]
/--
lemma `map_η_ε` / 引理 `map_η_ε`

English:
lemma map_η_ε
  given: (G : D ⥤ C')
  statement: G.map (η F) ≫ G.map (ε F) = 𝟙 _
  proof: (εIso F).map_inv_hom_id G

@[reassoc (attr := simp)]

中文:
引理 map_η_ε
  条件: (G : D ⥤ C')
  结论: G.map (η F) ≫ G.map (ε F) = 𝟙 _
  证明: (εIso F).map_inv_hom_id G

@[reassoc (attr := simp)]

Depends on / 依赖: map_inv_hom_id
-/
lemma map_η_ε (G : D ⥤ C') : G.map (η F) ≫ G.map (ε F) = 𝟙 _ :=
  (εIso F).map_inv_hom_id G

@[reassoc (attr := simp)]
/--
lemma `map_μ_δ` / 引理 `map_μ_δ`

English:
lemma map_μ_δ
  given: (G : D ⥤ C') (X Y : C)
  statement: G.map (μ F X Y) ≫ G.map (δ F X Y) = 𝟙 _
  proof: (μIso F X Y).map_hom_inv_id G

@[reassoc (attr := simp)]

中文:
引理 map_μ_δ
  条件: (G : D ⥤ C') (X Y : C)
  结论: G.map (μ F X Y) ≫ G.map (δ F X Y) = 𝟙 _
  证明: (μIso F X Y).map_hom_inv_id G

@[reassoc (attr := simp)]

Depends on / 依赖: map_hom_inv_id
-/
lemma map_μ_δ (G : D ⥤ C') (X Y : C) : G.map (μ F X Y) ≫ G.map (δ F X Y) = 𝟙 _ :=
  (μIso F X Y).map_hom_inv_id G

@[reassoc (attr := simp)]
/--
lemma `map_δ_μ` / 引理 `map_δ_μ`

English:
lemma map_δ_μ
  given: (G : D ⥤ C') (X Y : C)
  statement: G.map (δ F X Y) ≫ G.map (μ F X Y) = 𝟙 _
  proof: (μIso F X Y).map_inv_hom_id G

@[reassoc (attr := simp)]

中文:
引理 map_δ_μ
  条件: (G : D ⥤ C') (X Y : C)
  结论: G.map (δ F X Y) ≫ G.map (μ F X Y) = 𝟙 _
  证明: (μIso F X Y).map_inv_hom_id G

@[reassoc (attr := simp)]

Depends on / 依赖: map_inv_hom_id
-/
lemma map_δ_μ (G : D ⥤ C') (X Y : C) : G.map (δ F X Y) ≫ G.map (μ F X Y) = 𝟙 _ :=
  (μIso F X Y).map_inv_hom_id G

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_ε_η` / 引理 `whiskerRight_ε_η`

English:
lemma whiskerRight_ε_η
  given: (T : D)
  statement: ε F ▷ T ≫ η F ▷ T = 𝟙 _
  proof: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [ε_η]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_ε_η
  条件: (T : D)
  结论: ε F ▷ T ≫ η F ▷ T = 𝟙 _
  证明: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [ε_η]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.comp_whiskerRight, comp_whiskerRight, id_whiskerRight
-/
lemma whiskerRight_ε_η (T : D) : ε F ▷ T ≫ η F ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [ε_η]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_η_ε` / 引理 `whiskerRight_η_ε`

English:
lemma whiskerRight_η_ε
  given: (T : D)
  statement: η F ▷ T ≫ ε F ▷ T = 𝟙 _
  proof: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [η_ε]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_η_ε
  条件: (T : D)
  结论: η F ▷ T ≫ ε F ▷ T = 𝟙 _
  证明: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [η_ε]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.comp_whiskerRight, comp_whiskerRight, id_whiskerRight
-/
lemma whiskerRight_η_ε (T : D) : η F ▷ T ≫ ε F ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [η_ε]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_μ_δ` / 引理 `whiskerRight_μ_δ`

English:
lemma whiskerRight_μ_δ
  given: (X Y : C) (T : D)
  statement: μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _
  proof: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [μ_δ]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_μ_δ
  条件: (X Y : C) (T : D)
  结论: μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _
  证明: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [μ_δ]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.comp_whiskerRight, comp_whiskerRight, id_whiskerRight
-/
lemma whiskerRight_μ_δ (X Y : C) (T : D) : μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [μ_δ]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_δ_μ` / 引理 `whiskerRight_δ_μ`

English:
lemma whiskerRight_δ_μ
  given: (X Y : C) (T : D)
  statement: δ F X Y ▷ T ≫ μ F X Y ▷ T = 𝟙 _
  proof: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [δ_μ]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_δ_μ
  条件: (X Y : C) (T : D)
  结论: δ F X Y ▷ T ≫ μ F X Y ▷ T = 𝟙 _
  证明: by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [δ_μ]; rw [id_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.comp_whiskerRight, comp_whiskerRight, id_whiskerRight
-/
lemma whiskerRight_δ_μ (X Y : C) (T : D) : δ F X Y ▷ T ≫ μ F X Y ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight]; rw [δ_μ]; rw [id_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_ε_η` / 引理 `whiskerLeft_ε_η`

English:
lemma whiskerLeft_ε_η
  given: (T : D)
  statement: T ◁ ε F ≫ T ◁ η F = 𝟙 _
  proof: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [ε_η]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_ε_η
  条件: (T : D)
  结论: T ◁ ε F ≫ T ◁ η F = 𝟙 _
  证明: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [ε_η]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id, whiskerLeft_comp, whiskerLeft_id
-/
lemma whiskerLeft_ε_η (T : D) : T ◁ ε F ≫ T ◁ η F = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [ε_η]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_η_ε` / 引理 `whiskerLeft_η_ε`

English:
lemma whiskerLeft_η_ε
  given: (T : D)
  statement: T ◁ η F ≫ T ◁ ε F = 𝟙 _
  proof: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [η_ε]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_η_ε
  条件: (T : D)
  结论: T ◁ η F ≫ T ◁ ε F = 𝟙 _
  证明: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [η_ε]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id, whiskerLeft_comp, whiskerLeft_id
-/
lemma whiskerLeft_η_ε (T : D) : T ◁ η F ≫ T ◁ ε F = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [η_ε]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_μ_δ` / 引理 `whiskerLeft_μ_δ`

English:
lemma whiskerLeft_μ_δ
  given: (X Y : C) (T : D)
  statement: T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _
  proof: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [μ_δ]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_μ_δ
  条件: (X Y : C) (T : D)
  结论: T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _
  证明: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [μ_δ]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id, whiskerLeft_comp, whiskerLeft_id
-/
lemma whiskerLeft_μ_δ (X Y : C) (T : D) : T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [μ_δ]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_δ_μ` / 引理 `whiskerLeft_δ_μ`

English:
lemma whiskerLeft_δ_μ
  given: (X Y : C) (T : D)
  statement: T ◁ δ F X Y ≫ T ◁ μ F X Y = 𝟙 _
  proof: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [δ_μ]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc]

中文:
引理 whiskerLeft_δ_μ
  条件: (X Y : C) (T : D)
  结论: T ◁ δ F X Y ≫ T ◁ μ F X Y = 𝟙 _
  证明: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [δ_μ]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_id, whiskerLeft_comp, whiskerLeft_id
-/
lemma whiskerLeft_δ_μ (X Y : C) (T : D) : T ◁ δ F X Y ≫ T ◁ μ F X Y = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [δ_μ]; rw [MonoidalCategory.whiskerLeft_id]

@[reassoc]
/--
theorem `map_tensor` / 定理 `map_tensor`

English:
theorem map_tensor
  given: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  proof: by simp

@[reassoc]

中文:
定理 map_tensor
  条件: {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
  证明: by simp

@[reassoc]
-/
theorem map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f otimesₘ g) = δ F X X' ≫ (F.map f otimesₘ F.map g) ≫ μ F Y Y' := by simp

@[reassoc]
/--
theorem `map_whiskerLeft` / 定理 `map_whiskerLeft`

English:
theorem map_whiskerLeft
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  proof: by simp

@[reassoc]

中文:
定理 map_whiskerLeft
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  证明: by simp

@[reassoc]
-/
theorem map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) = δ F X Y ≫ F.obj X ◁ F.map f ≫ μ F X Z := by simp

@[reassoc]
/--
theorem `map_whiskerRight` / 定理 `map_whiskerRight`

English:
theorem map_whiskerRight
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: by simp

@[reassoc]

中文:
定理 map_whiskerRight
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: by simp

@[reassoc]
-/
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) = δ F X Z ≫ F.map f ▷ F.obj Z ≫ μ F Y Z := by simp

@[reassoc]
/--
theorem `map_associator` / 定理 `map_associator`

English:
theorem map_associator
  given: (X Y Z : C)
  proof: by
  rw [← LaxMonoidal.associativity F]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ_assoc]

@[reassoc]

中文:
定理 map_associator
  条件: (X Y Z : C)
  证明: by
  rw [← LaxMonoidal.associativity F]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ_assoc]

@[reassoc]

Depends on / 依赖: LaxMonoidal, LaxMonoidal.associativity, associativity
-/
theorem map_associator (X Y Z : C) :
    F.map (α_ X Y Z).hom =
      δ F (X otimes Y) Z ≫ δ F X Y ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) := by
  rw [← LaxMonoidal.associativity F]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ_assoc]

@[reassoc]
/--
theorem `map_associator_inv` / 定理 `map_associator_inv`

English:
theorem map_associator_inv
  given: (X Y Z : C)
  proof: by
  rw [← cancel_epi (F.map (α_ X Y Z).hom)]; rw [Iso.map_hom_inv_id]; rw [map_associator]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [OplaxMonoidal.associativity_inv_assoc]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ]; rw [comp_id]; rw [LaxMonoidal.associativity_inv]; rw [Iso.hom_inv_id_assoc];

中文:
定理 map_associator_inv
  条件: (X Y Z : C)
  证明: by
  rw [← cancel_epi (F.map (α_ X Y Z).hom)]; rw [Iso.map_hom_inv_id]; rw [map_associator]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [OplaxMonoidal.associativity_inv_assoc]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ]; rw [comp_id]; rw [LaxMonoidal.associativity_inv]; rw [Iso.hom_inv_id_assoc];

Depends on / 依赖: F.map, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id, LaxMonoidal, LaxMonoidal.associativity_inv, OplaxMonoidal, OplaxMonoidal.associativity_inv_assoc, associativity_inv, associativity_inv_assoc, cancel_epi, comp_id, hom_inv_id_assoc, map_associator, map_hom_inv_id
-/
theorem map_associator_inv (X Y Z : C) :
    F.map (α_ X Y Z).inv =
      δ F X (Y otimes Z) ≫ F.obj X ◁ δ F Y Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X otimes Y) Z := by
  rw [← cancel_epi (F.map (α_ X Y Z).hom)]; rw [Iso.map_hom_inv_id]; rw [map_associator]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [OplaxMonoidal.associativity_inv_assoc]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ]; rw [comp_id]; rw [LaxMonoidal.associativity_inv]; rw [Iso.hom_inv_id_assoc]; rw [whiskerRight_δ_μ_assoc]; rw [δ_μ]

@[reassoc]
/--
theorem `map_associator'` / 定理 `map_associator'`

English:
theorem map_associator'
  given: (X Y Z : C)
  proof: by
  simp

@[reassoc]

中文:
定理 map_associator'
  条件: (X Y Z : C)
  证明: by
  simp

@[reassoc]
-/
theorem map_associator' (X Y Z : C) :
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      μ F X Y ▷ F.obj Z ≫ μ F (X otimes Y) Z ≫ F.map (α_ X Y Z).hom ≫
        δ F X (Y otimes Z) ≫ F.obj X ◁ δ F Y Z := by
  simp

@[reassoc]
/--
theorem `map_associator_inv'` / 定理 `map_associator_inv'`

English:
theorem map_associator_inv'
  given: (X Y Z : C)
  proof: by
  rw [← cancel_epi (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom]; rw [map_associator']
  simp

@[reassoc]

中文:
定理 map_associator_inv'
  条件: (X Y Z : C)
  证明: by
  rw [← cancel_epi (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom]; rw [map_associator']
  simp

@[reassoc]

Depends on / 依赖: F.obj, cancel_epi, map_associator
-/
theorem map_associator_inv' (X Y Z : C) :
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) ≫ F.map (α_ X Y Z).inv ≫
        δ F (X otimes Y) Z ≫ δ F X Y ▷ F.obj Z := by
  rw [← cancel_epi (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom]; rw [map_associator']
  simp

@[reassoc]
/--
theorem `map_leftUnitor` / 定理 `map_leftUnitor`

English:
theorem map_leftUnitor
  given: (X : C)
  proof: by simp

@[reassoc]

中文:
定理 map_leftUnitor
  条件: (X : C)
  证明: by simp

@[reassoc]
-/
theorem map_leftUnitor (X : C) :
    F.map (fun_ X).hom = δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (fun_ (F.obj X)).hom := by simp

@[reassoc]
/--
theorem `map_leftUnitor_inv` / 定理 `map_leftUnitor_inv`

English:
theorem map_leftUnitor_inv
  given: (X : C)
  proof: by simp

@[reassoc]

中文:
定理 map_leftUnitor_inv
  条件: (X : C)
  证明: by simp

@[reassoc]
-/
theorem map_leftUnitor_inv (X : C) :
    F.map (fun_ X).inv = (fun_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X := by simp

@[reassoc]
/--
theorem `map_rightUnitor` / 定理 `map_rightUnitor`

English:
theorem map_rightUnitor
  given: (X : C)
  proof: by simp

@[reassoc]

中文:
定理 map_rightUnitor
  条件: (X : C)
  证明: by simp

@[reassoc]
-/
theorem map_rightUnitor (X : C) :
    F.map (ρ_ X).hom = δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom := by simp

@[reassoc]
/--
theorem `map_rightUnitor_inv` / 定理 `map_rightUnitor_inv`

English:
theorem map_rightUnitor_inv
  given: (X : C)
  proof: by simp

中文:
定理 map_rightUnitor_inv
  条件: (X : C)
  证明: by simp
-/
theorem map_rightUnitor_inv (X : C) :
    F.map (ρ_ X).inv = (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (𝟙_ C) := by simp

/--
lemma `inv_η` / 引理 `inv_η`

English:
lemma inv_η
  statement: CategoryTheory.inv (η F) = ε F
  proof: by
  rw [← εIso_hom]; rw [← Iso.comp_inv_eq_id]; rw [εIso_inv]; rw [IsIso.inv_hom_id]

中文:
引理 inv_η
  结论: CategoryTheory.inv (η F) = ε F
  证明: by
  rw [← εIso_hom]; rw [← Iso.comp_inv_eq_id]; rw [εIso_inv]; rw [IsIso.inv_hom_id]
-/
@[simp] lemma inv_η : CategoryTheory.inv (η F) = ε F := by
  rw [← εIso_hom]; rw [← Iso.comp_inv_eq_id]; rw [εIso_inv]; rw [IsIso.inv_hom_id]

/--
lemma `inv_ε` / 引理 `inv_ε`

English:
lemma inv_ε
  statement: CategoryTheory.inv (ε F) = η F
  proof: by simp [← inv_η]

中文:
引理 inv_ε
  结论: CategoryTheory.inv (ε F) = η F
  证明: by simp [← inv_η]
-/
@[simp] lemma inv_ε : CategoryTheory.inv (ε F) = η F := by simp [← inv_η]

/--
lemma `inv_μ` / 引理 `inv_μ`

English:
lemma inv_μ
  given: (X Y : C)
  statement: CategoryTheory.inv (μ F X Y) = δ F X Y
  proof: by
  rw [← Monoidal.μIso_inv]; rw [← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]

中文:
引理 inv_μ
  条件: (X Y : C)
  结论: CategoryTheory.inv (μ F X Y) = δ F X Y
  证明: by
  rw [← Monoidal.μIso_inv]; rw [← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]
-/
@[simp] lemma inv_μ (X Y : C) : CategoryTheory.inv (μ F X Y) = δ F X Y := by
  rw [← Monoidal.μIso_inv]; rw [← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]

/--
lemma `inv_δ` / 引理 `inv_δ`

English:
lemma inv_δ
  given: (X Y : C)
  statement: CategoryTheory.inv (δ F X Y) = μ F X Y
  proof: by simp [← inv_μ]

中文:
引理 inv_δ
  条件: (X Y : C)
  结论: CategoryTheory.inv (δ F X Y) = μ F X Y
  证明: by simp [← inv_μ]
-/
@[simp] lemma inv_δ (X Y : C) : CategoryTheory.inv (δ F X Y) = μ F X Y := by simp [← inv_μ]

set_option backward.defeqAttrib.useBackward true in
/-- The tensorator as a natural isomorphism. -/
@[simps!]
/--
Definition of `μNatIso` / `μNatIso` 的定义

English:
definition μNatIso
  signature: :
  body: NatIso.ofComponents (fun _ => μIso F _ _)

中文:
定义 μNatIso
  签名: :
  定义体: NatIso.ofComponents (fun _ => μIso F _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def μNatIso :
    Functor.prod F F ⋙ tensor D ≅ tensor C ⋙ F :=
  NatIso.ofComponents (fun _ => μIso F _ _)

set_option backward.defeqAttrib.useBackward true in
/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
/--
Definition of `commTensorLeft` / `commTensorLeft` 的定义

English:
definition commTensorLeft
  signature: (X : C)
  body: NatIso.ofComponents (fun Y => μIso F X Y)

中文:
定义 commTensorLeft
  签名: (X : C)
  定义体: NatIso.ofComponents (fun Y => μIso F X Y)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def commTensorLeft (X : C) :
    F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F X Y)

set_option backward.defeqAttrib.useBackward true in
/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
/--
Definition of `commTensorRight` / `commTensorRight` 的定义

English:
definition commTensorRight
  signature: (X : C)
  body: NatIso.ofComponents (fun Y => μIso F Y X)

中文:
定义 commTensorRight
  签名: (X : C)
  定义体: NatIso.ofComponents (fun Y => μIso F Y X)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def commTensorRight (X : C) :
    F ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F Y X)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟭 C).Monoidal

中文:
实例 :
  签名: (𝟭 C).Monoidal
-/
instance : (𝟭 C).Monoidal where

variable (F : C ⥤ D) (G : D ⥤ E)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Monoidal]
  signature: [G.Monoidal]
  body: by simp
  η_ε := by simp
  μ_δ _ _ := by simp
  δ_μ _ _ := by simp

中文:
实例 [F.Monoidal]
  签名: [G.Monoidal]
  定义体: by simp
  η_ε := by simp
  μ_δ _ _ := by simp
  δ_μ _ _ := by simp
-/
instance [F.Monoidal] [G.Monoidal] : (F ⋙ G).Monoidal where
  ε_η := by simp
  η_ε := by simp
  μ_δ _ _ := by simp
  δ_μ _ _ := by simp

/--
lemma `toLaxMonoidal_injective` / 引理 `toLaxMonoidal_injective`

English:
lemma toLaxMonoidal_injective
  statement: Function.Injective
  proof: by
  intro a b eq
  ext1
  · exact congr(($eq).ε)
  · exact congr(($eq).μ)
  · rw [← cancel_epi (εIso _).hom]
    rw [εIso_hom]; rw [ε_η]; rw [← @ε_η _ _ _ _ _ _ _ a]; rw [← εIso_hom]
    exact congr(($eq.symm).ε ≫ _)
  · ext
    rw [← cancel_epi (μIso F _ _).hom]
    rw [μIso_hom]; rw [μ_δ]; rw [← 

中文:
引理 toLaxMonoidal_injective
  结论: Function.Injective
  证明: by
  intro a b eq
  ext1
  · exact congr(($eq).ε)
  · exact congr(($eq).μ)
  · rw [← cancel_epi (εIso _).hom]
    rw [εIso_hom]; rw [ε_η]; rw [← @ε_η _ _ _ _ _ _ _ a]; rw [← εIso_hom]
    exact congr(($eq.symm).ε ≫ _)
  · ext
    rw [← cancel_epi (μIso F _ _).hom]
    rw [μIso_hom]; rw [μ_δ]; rw [← 

Depends on / 依赖: cancel_epi, eq.symm
-/
lemma toLaxMonoidal_injective : Function.Injective
    (@Monoidal.toLaxMonoidal _ _ _ _ _ _ _ : F.Monoidal -> F.LaxMonoidal) := by
  intro a b eq
  ext1
  · exact congr(($eq).ε)
  · exact congr(($eq).μ)
  · rw [← cancel_epi (εIso _).hom]
    rw [εIso_hom]; rw [ε_η]; rw [← @ε_η _ _ _ _ _ _ _ a]; rw [← εIso_hom]
    exact congr(($eq.symm).ε ≫ _)
  · ext
    rw [← cancel_epi (μIso F _ _).hom]
    rw [μIso_hom]; rw [μ_δ]; rw [← @μ_δ _ _ _ _ _ _ _ a]; rw [← μIso_hom]
    exact congr(($eq.symm).μ _ _ ≫ _)

/--
lemma `toOplaxMonoidal_injective` / 引理 `toOplaxMonoidal_injective`

English:
lemma toOplaxMonoidal_injective
  statement: Function.Injective
  proof: by
  intro a b eq
  ext1
  · rw [← cancel_mono (εIso _).inv]
    rw [εIso_inv]; rw [ε_η]; rw [← @ε_η _ _ _ _ _ _ _ a]; rw [← εIso_inv]
    exact congr(_ ≫ ($eq.symm).η)
  · ext
    rw [← cancel_mono (μIso F _ _).inv]
    rw [μIso_inv]; rw [μ_δ]; rw [← @μ_δ _ _ _ _ _ _ _ a]; rw [← μIso_inv]
    exact

中文:
引理 toOplaxMonoidal_injective
  结论: Function.Injective
  证明: by
  intro a b eq
  ext1
  · rw [← cancel_mono (εIso _).inv]
    rw [εIso_inv]; rw [ε_η]; rw [← @ε_η _ _ _ _ _ _ _ a]; rw [← εIso_inv]
    exact congr(_ ≫ ($eq.symm).η)
  · ext
    rw [← cancel_mono (μIso F _ _).inv]
    rw [μIso_inv]; rw [μ_δ]; rw [← @μ_δ _ _ _ _ _ _ _ a]; rw [← μIso_inv]
    exact

Depends on / 依赖: Unique, cancel_mono, eq.symm
-/
lemma toOplaxMonoidal_injective : Function.Injective
    (@Monoidal.toOplaxMonoidal _ _ _ _ _ _ _ : F.Monoidal -> F.OplaxMonoidal) := by
  intro a b eq
  ext1
  · rw [← cancel_mono (εIso _).inv]
    rw [εIso_inv]; rw [ε_η]; rw [← @ε_η _ _ _ _ _ _ _ a]; rw [← εIso_inv]
    exact congr(_ ≫ ($eq.symm).η)
  · ext
    rw [← cancel_mono (μIso F _ _).inv]
    rw [μIso_inv]; rw [μ_δ]; rw [← @μ_δ _ _ _ _ _ _ _ a]; rw [← μIso_inv]
    exact congr(_ ≫ ($eq.symm).δ _ _)
  · exact congr(($eq).η)
  · exact congr(($eq).δ)

/-- Copy of a monoidal structure on a functor `F` with new `ε`, `μ`, `η` and `δ` fields equal to the
old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {F : C ⥤ D} (hF : F.Monoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  body: hF.toLaxMonoidal.copy ε' μ' hε hμ
  __ := hF.toOplaxMonoidal.copy η' δ' hη hδ

中文:
定义 copy
  签名: {F : C ⥤ D} (hF : F.Monoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
  定义体: hF.toLaxMonoidal.copy ε' μ' hε hμ
  __ := hF.toOplaxMonoidal.copy η' δ' hη hδ

Depends on / 依赖: F.Monoidal, Monoidal, cat_disch, hF.toLaxMonoidal.copy, hF.toOplaxMonoidal.copy, toLaxMonoidal, toOplaxMonoidal
-/
def copy {F : C ⥤ D} (hF : F.Monoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (δ' : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y)
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch)
    (hη : η' = η F := by cat_disch) (hδ : δ' = δ F := by cat_disch) : F.Monoidal where
  __ := hF.toLaxMonoidal.copy ε' μ' hε hμ
  __ := hF.toOplaxMonoidal.copy η' δ' hη hδ

end Monoidal

variable (F : C ⥤ D)
/--
Definition of `CoreMonoidal` / `CoreMonoidal` 的定义

English:
structure CoreMonoidal
  parameters: where
  axioms and operations (7):
    - εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
    - μIso : forall X Y : C, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y)
    - μIso_hom_natural_left : forall {X Y : C} (f : X ⟶ Y) (X' : C), F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X')  [default: by cat_disch]
    - μIso_hom_natural_right : forall {X Y : C} (X' : C) (f : X ⟶ Y), F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f)  [default: by cat_disch]
    - associativity : forall X Y Z : C, (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X otimes Y) Z).hom ≫ F.map (α_ X Y Z).hom = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫ (μIso X (Y otimes Z)).hom  [default: by cat_disch]
    - left_unitality : forall X : C, (fun_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (fun_ X).hom  [default: by cat_disch]
    - right_unitality : forall X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom  [default: by cat_disch]

中文:
结构 CoreMonoidal
  参数: where
  公理与运算 (7 个):
    - εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
    - μIso : 对任意 X Y : C, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y)
    - μIso_hom_natural_left : 对任意 {X Y : C} (f : X ⟶ Y) (X' : C), F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X')  [默认: by cat_disch]
    - μIso_hom_natural_right : 对任意 {X Y : C} (X' : C) (f : X ⟶ Y), F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f)  [默认: by cat_disch]
    - associativity : 对任意 X Y Z : C, (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X otimes Y) Z).hom ≫ F.map (α_ X Y Z).hom = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫ (μIso X (Y otimes Z)).hom  [默认: by cat_disch]
    - left_unitality : 对任意 X : C, (fun_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (fun_ X).hom  [默认: by cat_disch]
    - right_unitality : 对任意 X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom  [默认: by cat_disch]

Depends on / 依赖: F.map, F.obj, cat_disch
-/
structure CoreMonoidal where
  /-- unit morphism -/
  εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
  /-- tensorator -/
  μIso : forall X Y : C, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y)
  μIso_hom_natural_left :
    forall {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X') := by
    cat_disch
  μIso_hom_natural_right :
    forall {X Y : C} (X' : C) (f : X ⟶ Y),
      F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f) := by
    cat_disch
  /-- associativity of the tensorator -/
  associativity :
    forall X Y Z : C,
      (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X otimes Y) Z).hom ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
          (μIso X (Y otimes Z)).hom := by
    cat_disch
  -- unitality
  left_unitality :
    forall X : C, (fun_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (fun_ X).hom := by
      cat_disch
  right_unitality :
    forall X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by
    cat_disch

namespace CoreMonoidal

attribute [reassoc (attr := simp)] μIso_hom_natural_left
  μIso_hom_natural_right associativity

attribute [reassoc] left_unitality right_unitality

variable {F}

/-- Alternative constructor for `CoreMonoidal`, for which the axioms are stated
in terms on the inverses of `εIso` and `μIso`. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
  body: εIso
  μIso := μIso
  μIso_hom_natural_left {X Y} f X' := by
    simp [← cancel_epi (μIso X X').inv, reassoc_of% μIso_inv_natural_left f X']
  μIso_hom_natural_right {X Y} X' g := by
    simp [← cancel_mono (μIso X' Y).inv, ← (μIso_inv_natural_right X' g)]
  associativity X Y Z := by
    rw [← cance

中文:
定义 mk'
  签名: (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
  定义体: εIso
  μIso := μIso
  μIso_hom_natural_left {X Y} f X' := by
    simp [← cancel_epi (μIso X X').inv, reassoc_of% μIso_inv_natural_left f X']
  μIso_hom_natural_right {X Y} X' g := by
    simp [← cancel_mono (μIso X' Y).inv, ← (μIso_inv_natural_right X' g)]
  associativity X Y Z := by
    rw [← cance

Depends on / 依赖: F.map, F.obj, cat_disch, fun_, oplax_associativity, oplax_left_unitality, otimes
-/
def mk' (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μIso : forall X Y : C, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y))
    (μIso_inv_natural_left : forall {X Y : C} (f : X ⟶ Y) (X' : C),
      (μIso X X').inv ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ (μIso Y X').inv := by cat_disch)
    (μIso_inv_natural_right : forall {X Y : C} (X' : C) (f : X ⟶ Y),
      (μIso X' X).inv ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ (μIso X' Y).inv := by cat_disch)
    (oplax_associativity : forall X Y Z : C,
      (μIso (X otimes Y) Z).inv ≫ (μIso X Y).inv ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ (μIso X (Y otimes Z)).inv ≫ F.obj X ◁ (μIso Y Z).inv := by cat_disch)
    (oplax_left_unitality : forall X : C, (fun_ (F.obj X)).inv =
      F.map (fun_ X).inv ≫ (μIso (𝟙_ C) X).inv ≫ εIso.inv ▷ F.obj X := by cat_disch)
    (oplax_right_unitality : forall X : C, (ρ_ (F.obj X)).inv =
      F.map (ρ_ X).inv ≫ (μIso X (𝟙_ C)).inv ≫ F.obj X ◁ εIso.inv := by cat_disch) :
    F.CoreMonoidal where
  εIso := εIso
  μIso := μIso
  μIso_hom_natural_left {X Y} f X' := by
    simp [← cancel_epi (μIso X X').inv, reassoc_of% μIso_inv_natural_left f X']
  μIso_hom_natural_right {X Y} X' g := by
    simp [← cancel_mono (μIso X' Y).inv, ← (μIso_inv_natural_right X' g)]
  associativity X Y Z := by
    rw [← cancel_epi ((μIso X Y).inv ▷ F.obj Z)]; rw [← cancel_epi (μIso (X otimes Y) Z).inv]; rw [reassoc_of% oplax_associativity]
    simp
  left_unitality X := by
    rw [← cancel_mono (fun_ (F.obj X)).inv]; rw [Iso.hom_inv_id]; rw [oplax_left_unitality]
    simp
  right_unitality X := by
    rw [← cancel_mono (ρ_ (F.obj X)).inv]; rw [Iso.hom_inv_id]; rw [oplax_right_unitality]
    simp

variable (h : F.CoreMonoidal)

/-- The lax monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `toLaxMonoidal` / `toLaxMonoidal` 的定义

English:
definition toLaxMonoidal
  signature: : F.LaxMonoidal where
  body: h.εIso.hom
  μ X Y := (h.μIso X Y).hom
  left_unitality := h.left_unitality
  right_unitality := h.right_unitality

中文:
定义 toLaxMonoidal
  签名: : F.LaxMonoidal where
  定义体: h.εIso.hom
  μ X Y := (h.μIso X Y).hom
  left_unitality := h.left_unitality
  right_unitality := h.right_unitality

Depends on / 依赖: Iso.hom
-/
def toLaxMonoidal : F.LaxMonoidal where
  ε := h.εIso.hom
  μ X Y := (h.μIso X Y).hom
  left_unitality := h.left_unitality
  right_unitality := h.right_unitality

/-- The oplax monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `toOplaxMonoidal` / `toOplaxMonoidal` 的定义

English:
definition toOplaxMonoidal
  signature: : F.OplaxMonoidal where
  body: h.εIso.inv
  δ X Y := (h.μIso X Y).inv
  δ_natural_left _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom]; rw [Iso.hom_inv_id_assoc]; rw [← h.μIso_hom_natural_left_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  δ_natural_right _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom]; rw [Iso.hom_inv_id_assoc]; 

中文:
定义 toOplaxMonoidal
  签名: : F.OplaxMonoidal where
  定义体: h.εIso.inv
  δ X Y := (h.μIso X Y).inv
  δ_natural_left _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom]; rw [Iso.hom_inv_id_assoc]; rw [← h.μIso_hom_natural_left_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  δ_natural_right _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom]; rw [Iso.hom_inv_id_assoc]; 

Depends on / 依赖: Iso.inv
-/
def toOplaxMonoidal : F.OplaxMonoidal where
  η := h.εIso.inv
  δ X Y := (h.μIso X Y).inv
  δ_natural_left _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom]; rw [Iso.hom_inv_id_assoc]; rw [← h.μIso_hom_natural_left_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  δ_natural_right _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom]; rw [Iso.hom_inv_id_assoc]; rw [← h.μIso_hom_natural_right_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]
  oplax_associativity X Y Z := by
    rw [← cancel_epi (h.μIso (X otimes Y) Z).hom]; rw [Iso.hom_inv_id_assoc]; rw [← cancel_epi ((h.μIso X Y).hom ▷ F.obj Z)]; rw [hom_inv_whiskerRight_assoc]; rw [associativity_assoc]; rw [Iso.hom_inv_id_assoc]; rw [whiskerLeft_hom_inv]; rw [comp_id]
  oplax_left_unitality _ := by
    rw [← cancel_epi (fun_ _).hom]; rw [Iso.hom_inv_id]; rw [h.left_unitality]; rw [assoc]; rw [assoc]; rw [Iso.map_hom_inv_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [hom_inv_whiskerRight]
  oplax_right_unitality _ := by
    rw [← cancel_epi (ρ_ _).hom]; rw [Iso.hom_inv_id]; rw [h.right_unitality]; rw [assoc]; rw [assoc]; rw [Iso.map_hom_inv_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [whiskerLeft_hom_inv]

attribute [local simp] toLaxMonoidal_ε toLaxMonoidal_μ toOplaxMonoidal_η toOplaxMonoidal_δ in
/-- The monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps! toLaxMonoidal toOplaxMonoidal, instance_reducible]
/--
Definition of `toMonoidal` / `toMonoidal` 的定义

English:
definition toMonoidal
  signature: : F.Monoidal where
  body: h.toLaxMonoidal
  toOplaxMonoidal := h.toOplaxMonoidal

中文:
定义 toMonoidal
  签名: : F.Monoidal where
  定义体: h.toLaxMonoidal
  toOplaxMonoidal := h.toOplaxMonoidal

Depends on / 依赖: h.toLaxMonoidal, toLaxMonoidal
-/
def toMonoidal : F.Monoidal where
  toLaxMonoidal := h.toLaxMonoidal
  toOplaxMonoidal := h.toOplaxMonoidal

variable (F)

/--
Definition of `ofLaxMonoidal` / `ofLaxMonoidal` 的定义

English:
definition ofLaxMonoidal
  signature: [F.LaxMonoidal] [IsIso (ε F)] [forall X Y, IsIso (μ F X Y)]
  body: asIso (ε F)
  μIso X Y := asIso (μ F X Y)

中文:
定义 ofLaxMonoidal
  签名: [F.LaxMonoidal] [IsIso (ε F)] [对任意 X Y, IsIso (μ F X Y)]
  定义体: asIso (ε F)
  μIso X Y := asIso (μ F X Y)
-/
noncomputable def ofLaxMonoidal [F.LaxMonoidal] [IsIso (ε F)] [forall X Y, IsIso (μ F X Y)] :
    F.CoreMonoidal where
  εIso := asIso (ε F)
  μIso X Y := asIso (μ F X Y)

/-- The `Functor.CoreMonoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms. -/
@[simps]
/--
Definition of `ofOplaxMonoidal` / `ofOplaxMonoidal` 的定义

English:
definition ofOplaxMonoidal
  signature: [F.OplaxMonoidal] [IsIso (η F)] [forall X Y, IsIso (δ F X Y)]
  body: (asIso (η F)).symm
  μIso X Y := (asIso (δ F X Y)).symm
  associativity X Y Z := by
    simp [← cancel_epi (δ F X Y ▷ F.obj Z), ← cancel_epi (δ F (X otimes Y) Z)]
  left_unitality X := by simp [← cancel_epi (fun_ (F.obj X)).inv]
  right_unitality X := by simp [← cancel_epi (ρ_ (F.obj X)).inv]

中文:
定义 ofOplaxMonoidal
  签名: [F.OplaxMonoidal] [IsIso (η F)] [对任意 X Y, IsIso (δ F X Y)]
  定义体: (asIso (η F)).symm
  μIso X Y := (asIso (δ F X Y)).symm
  associativity X Y Z := by
    simp [← cancel_epi (δ F X Y ▷ F.obj Z), ← cancel_epi (δ F (X otimes Y) Z)]
  left_unitality X := by simp [← cancel_epi (fun_ (F.obj X)).inv]
  right_unitality X := by simp [← cancel_epi (ρ_ (F.obj X)).inv]
-/
noncomputable def ofOplaxMonoidal [F.OplaxMonoidal] [IsIso (η F)] [forall X Y, IsIso (δ F X Y)] :
    F.CoreMonoidal where
  εIso := (asIso (η F)).symm
  μIso X Y := (asIso (δ F X Y)).symm
  associativity X Y Z := by
    simp [← cancel_epi (δ F X Y ▷ F.obj Z), ← cancel_epi (δ F (X otimes Y) Z)]
  left_unitality X := by simp [← cancel_epi (fun_ (F.obj X)).inv]
  right_unitality X := by simp [← cancel_epi (ρ_ (F.obj X)).inv]

end CoreMonoidal

/-- The `Functor.Monoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms. -/
@[instance_reducible]
/--
Definition of `Monoidal.ofLaxMonoidal` / `Monoidal.ofLaxMonoidal` 的定义

English:
definition Monoidal.ofLaxMonoidal
  body: (CoreMonoidal.ofLaxMonoidal F).toMonoidal

中文:
定义 Monoidal.ofLaxMonoidal
  定义体: (CoreMonoidal.ofLaxMonoidal F).toMonoidal

Depends on / 依赖: CoreMonoidal, CoreMonoidal.ofLaxMonoidal, ofLaxMonoidal, toMonoidal
-/
noncomputable def Monoidal.ofLaxMonoidal
    [F.LaxMonoidal] [IsIso (ε F)] [forall X Y, IsIso (μ F X Y)] :=
  (CoreMonoidal.ofLaxMonoidal F).toMonoidal

/-- The `Functor.Monoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms. -/
@[instance_reducible]
/--
Definition of `Monoidal.ofOplaxMonoidal` / `Monoidal.ofOplaxMonoidal` 的定义

English:
definition Monoidal.ofOplaxMonoidal
  body: (CoreMonoidal.ofOplaxMonoidal F).toMonoidal

中文:
定义 Monoidal.ofOplaxMonoidal
  定义体: (CoreMonoidal.ofOplaxMonoidal F).toMonoidal

Depends on / 依赖: CoreMonoidal, CoreMonoidal.ofOplaxMonoidal, ofOplaxMonoidal, toMonoidal
-/
noncomputable def Monoidal.ofOplaxMonoidal
    [F.OplaxMonoidal] [IsIso (η F)] [forall X Y, IsIso (δ F X Y)] :=
  (CoreMonoidal.ofOplaxMonoidal F).toMonoidal

section Prod

open scoped CategoryTheory.Prod

variable (F : C ⥤ D) (G : E ⥤ C') [MonoidalCategory C']

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (prod F G).LaxMonoidal
  body: ε F ×ₘ ε G
  μ X Y := μ F _ _ ×ₘ μ G _ _

中文:
实例 :
  签名: (prod F G).LaxMonoidal
  定义体: ε F ×ₘ ε G
  μ X Y := μ F _ _ ×ₘ μ G _ _
-/
instance : (prod F G).LaxMonoidal where
  ε := ε F ×ₘ ε G
  μ X Y := μ F _ _ ×ₘ μ G _ _

/--
lemma `prod_ε_fst` / 引理 `prod_ε_fst`

English:
lemma prod_ε_fst
  statement: (ε (prod F G)).1 = ε F
  proof: rfl

中文:
引理 prod_ε_fst
  结论: (ε (prod F G)).1 = ε F
  证明: rfl
-/
@[simp] lemma prod_ε_fst : (ε (prod F G)).1 = ε F := rfl
/--
lemma `prod_ε_snd` / 引理 `prod_ε_snd`

English:
lemma prod_ε_snd
  statement: (ε (prod F G)).2 = ε G
  proof: rfl

中文:
引理 prod_ε_snd
  结论: (ε (prod F G)).2 = ε G
  证明: rfl
-/
@[simp] lemma prod_ε_snd : (ε (prod F G)).2 = ε G := rfl
/--
lemma `prod_μ_fst` / 引理 `prod_μ_fst`

English:
lemma prod_μ_fst
  given: (X Y : C × E)
  statement: (μ (prod F G) X Y).1 = μ F _ _
  proof: rfl

中文:
引理 prod_μ_fst
  条件: (X Y : C × E)
  结论: (μ (prod F G) X Y).1 = μ F _ _
  证明: rfl
-/
@[simp] lemma prod_μ_fst (X Y : C × E) : (μ (prod F G) X Y).1 = μ F _ _ := rfl
/--
lemma `prod_μ_snd` / 引理 `prod_μ_snd`

English:
lemma prod_μ_snd
  given: (X Y : C × E)
  statement: (μ (prod F G) X Y).2 = μ G _ _
  proof: rfl

中文:
引理 prod_μ_snd
  条件: (X Y : C × E)
  结论: (μ (prod F G) X Y).2 = μ G _ _
  证明: rfl
-/
@[simp] lemma prod_μ_snd (X Y : C × E) : (μ (prod F G) X Y).2 = μ G _ _ := rfl

end

section


variable [F.OplaxMonoidal] [G.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (prod F G).OplaxMonoidal
  body: η F ×ₘ η G
  δ X Y := δ F _ _ ×ₘ δ G _ _

中文:
实例 :
  签名: (prod F G).OplaxMonoidal
  定义体: η F ×ₘ η G
  δ X Y := δ F _ _ ×ₘ δ G _ _
-/
instance : (prod F G).OplaxMonoidal where
  η := η F ×ₘ η G
  δ X Y := δ F _ _ ×ₘ δ G _ _

/--
lemma `prod_η_fst` / 引理 `prod_η_fst`

English:
lemma prod_η_fst
  statement: (η (prod F G)).1 = η F
  proof: rfl

中文:
引理 prod_η_fst
  结论: (η (prod F G)).1 = η F
  证明: rfl
-/
@[simp] lemma prod_η_fst : (η (prod F G)).1 = η F := rfl
/--
lemma `prod_η_snd` / 引理 `prod_η_snd`

English:
lemma prod_η_snd
  statement: (η (prod F G)).2 = η G
  proof: rfl

中文:
引理 prod_η_snd
  结论: (η (prod F G)).2 = η G
  证明: rfl
-/
@[simp] lemma prod_η_snd : (η (prod F G)).2 = η G := rfl
/--
lemma `prod_δ_fst` / 引理 `prod_δ_fst`

English:
lemma prod_δ_fst
  given: (X Y : C × E)
  statement: (δ (prod F G) X Y).1 = δ F _ _
  proof: rfl

中文:
引理 prod_δ_fst
  条件: (X Y : C × E)
  结论: (δ (prod F G) X Y).1 = δ F _ _
  证明: rfl
-/
@[simp] lemma prod_δ_fst (X Y : C × E) : (δ (prod F G) X Y).1 = δ F _ _ := rfl
/--
lemma `prod_δ_snd` / 引理 `prod_δ_snd`

English:
lemma prod_δ_snd
  given: (X Y : C × E)
  statement: (δ (prod F G) X Y).2 = δ G _ _
  proof: rfl

中文:
引理 prod_δ_snd
  条件: (X Y : C × E)
  结论: (δ (prod F G) X Y).2 = δ G _ _
  证明: rfl
-/
@[simp] lemma prod_δ_snd (X Y : C × E) : (δ (prod F G) X Y).2 = δ G _ _ := rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Monoidal]
  signature: [G.Monoidal]
  body: by ext <;> apply Monoidal.ε_η
  η_ε := by ext <;> apply Monoidal.η_ε
  μ_δ _ _ := by ext <;> apply Monoidal.μ_δ
  δ_μ _ _ := by ext <;> apply Monoidal.δ_μ

中文:
实例 [F.Monoidal]
  签名: [G.Monoidal]
  定义体: by ext <;> apply Monoidal.ε_η
  η_ε := by ext <;> apply Monoidal.η_ε
  μ_δ _ _ := by ext <;> apply Monoidal.μ_δ
  δ_μ _ _ := by ext <;> apply Monoidal.δ_μ

Depends on / 依赖: Monoidal
-/
instance [F.Monoidal] [G.Monoidal] : (prod F G).Monoidal where
  ε_η := by ext <;> apply Monoidal.ε_η
  η_ε := by ext <;> apply Monoidal.η_ε
  μ_δ _ _ := by ext <;> apply Monoidal.μ_δ
  δ_μ _ _ := by ext <;> apply Monoidal.δ_μ

end Prod

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (diag C).Monoidal
  body: CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 :
  签名: (diag C).Monoidal
  定义体: CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (diag C).Monoidal :=
  CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

/--
lemma `diag_ε` / 引理 `diag_ε`

English:
lemma diag_ε
  statement: ε (diag C) = 𝟙 _
  proof: rfl

中文:
引理 diag_ε
  结论: ε (diag C) = 𝟙 _
  证明: rfl
-/
@[simp] lemma diag_ε : ε (diag C) = 𝟙 _ := rfl
/--
lemma `diag_η` / 引理 `diag_η`

English:
lemma diag_η
  statement: η (diag C) = 𝟙 _
  proof: rfl

中文:
引理 diag_η
  结论: η (diag C) = 𝟙 _
  证明: rfl

Depends on / 依赖: _root_, _root_.id
-/
@[simp] lemma diag_η : η (diag C) = 𝟙 _ := rfl
/--
lemma `diag_μ` / 引理 `diag_μ`

English:
lemma diag_μ
  given: (X Y : C)
  statement: μ (diag C) X Y = 𝟙 _
  proof: rfl

中文:
引理 diag_μ
  条件: (X Y : C)
  结论: μ (diag C) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma diag_μ (X Y : C) : μ (diag C) X Y = 𝟙 _ := rfl
/--
lemma `diag_δ` / 引理 `diag_δ`

English:
lemma diag_δ
  given: (X Y : C)
  statement: δ (diag C) X Y = 𝟙 _
  proof: rfl

中文:
引理 diag_δ
  条件: (X Y : C)
  结论: δ (diag C) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma diag_δ (X Y : C) : δ (diag C) X Y = 𝟙 _ := rfl

section Prod'

variable (F : C ⥤ D) (G : C ⥤ E)

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

/--
Instance `LaxMonoidal.prod'` / 实例 `LaxMonoidal.prod'`

English:
instance LaxMonoidal.prod'
  signature: : (prod' F G).LaxMonoidal
  body: inferInstanceAs (diag C ⋙ prod F G).LaxMonoidal

中文:
实例 LaxMonoidal.prod'
  签名: : (prod' F G).LaxMonoidal
  定义体: inferInstanceAs (diag C ⋙ prod F G).LaxMonoidal

Depends on / 依赖: LaxMonoidal, cat_disch
-/
instance LaxMonoidal.prod' : (prod' F G).LaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).LaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_ε_fst` / 引理 `prod'_ε_fst`

English:
lemma prod'_ε_fst
  statement: (ε (prod' F G)).1 = ε F
  proof: by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

中文:
引理 prod'_ε_fst
  结论: (ε (prod' F G)).1 = ε F
  证明: by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

Depends on / 依赖: Hom.ext
-/
@[simp] lemma prod'_ε_fst : (ε (prod' F G)).1 = ε F := by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_ε_snd` / 引理 `prod'_ε_snd`

English:
lemma prod'_ε_snd
  statement: (ε (prod' F G)).2 = ε G
  proof: by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

中文:
引理 prod'_ε_snd
  结论: (ε (prod' F G)).2 = ε G
  证明: by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl
-/
@[simp] lemma prod'_ε_snd : (ε (prod' F G)).2 = ε G := by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_μ_fst` / 引理 `prod'_μ_fst`

English:
lemma prod'_μ_fst
  given: (X Y : C)
  statement: (μ (prod' F G) X Y).1 = μ F X Y
  proof: by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

中文:
引理 prod'_μ_fst
  条件: (X Y : C)
  结论: (μ (prod' F G) X Y).1 = μ F X Y
  证明: by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl
-/
@[simp] lemma prod'_μ_fst (X Y : C) : (μ (prod' F G) X Y).1 = μ F X Y := by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_μ_snd` / 引理 `prod'_μ_snd`

English:
lemma prod'_μ_snd
  given: (X Y : C)
  statement: (μ (prod' F G) X Y).2 = μ G X Y
  proof: by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

中文:
引理 prod'_μ_snd
  条件: (X Y : C)
  结论: (μ (prod' F G) X Y).2 = μ G X Y
  证明: by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl
-/
@[simp] lemma prod'_μ_snd (X Y : C) : (μ (prod' F G) X Y).2 = μ G X Y := by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id]; rw [Category.comp_id]
  rfl

end

section

variable [F.OplaxMonoidal] [G.OplaxMonoidal]

/--
Instance `OplaxMonoidal.prod'` / 实例 `OplaxMonoidal.prod'`

English:
instance OplaxMonoidal.prod'
  signature: : (prod' F G).OplaxMonoidal
  body: inferInstanceAs (diag C ⋙ prod F G).OplaxMonoidal

中文:
实例 OplaxMonoidal.prod'
  签名: : (prod' F G).OplaxMonoidal
  定义体: inferInstanceAs (diag C ⋙ prod F G).OplaxMonoidal

Depends on / 依赖: OplaxMonoidal
-/
instance OplaxMonoidal.prod' : (prod' F G).OplaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).OplaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_η_fst` / 引理 `prod'_η_fst`

English:
lemma prod'_η_fst
  statement: (η (prod' F G)).1 = η F
  proof: by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

中文:
引理 prod'_η_fst
  结论: (η (prod' F G)).1 = η F
  证明: by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl
-/
@[simp] lemma prod'_η_fst : (η (prod' F G)).1 = η F := by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_η_snd` / 引理 `prod'_η_snd`

English:
lemma prod'_η_snd
  statement: (η (prod' F G)).2 = η G
  proof: by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

中文:
引理 prod'_η_snd
  结论: (η (prod' F G)).2 = η G
  证明: by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

Depends on / 依赖: Category, Category.assoc, e.hom.s, e.inv.h, eqToHom, eqToHom_naturality, eqToHom_refl, eqToHom_trans
-/
@[simp] lemma prod'_η_snd : (η (prod' F G)).2 = η G := by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_δ_fst` / 引理 `prod'_δ_fst`

English:
lemma prod'_δ_fst
  given: (X Y : C)
  statement: (δ (prod' F G) X Y).1 = δ F X Y
  proof: by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

中文:
引理 prod'_δ_fst
  条件: (X Y : C)
  结论: (δ (prod' F G) X Y).1 = δ F X Y
  证明: by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

Depends on / 依赖: of_isIso_fac_right
-/
@[simp] lemma prod'_δ_fst (X Y : C) : (δ (prod' F G) X Y).1 = δ F X Y := by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `prod'_δ_snd` / 引理 `prod'_δ_snd`

English:
lemma prod'_δ_snd
  given: (X Y : C)
  statement: (δ (prod' F G) X Y).2 = δ G X Y
  proof: by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

中文:
引理 prod'_δ_snd
  条件: (X Y : C)
  结论: (δ (prod' F G) X Y).2 = δ G X Y
  证明: by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl
-/
@[simp] lemma prod'_δ_snd (X Y : C) : (δ (prod' F G) X Y).2 = δ G X Y := by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id]; rw [Category.id_comp]
  rfl

end

-- TODO: when clearing these deprecations, remove the `CategoryTheory.` in the proof below.

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `Monoidal.prod'` / 实例 `Monoidal.prod'`

English:
instance Monoidal.prod'
  signature: [F.Monoidal] [G.Monoidal]
  body: by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, ε_η,
        prodMonoidal_tensorUnit, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, ε_η,
        prodMonoidal_tensorUnit, prod_id]
  η_ε := by
    ext
    · simp only [CategoryTheo

中文:
实例 Monoidal.prod'
  签名: [F.Monoidal] [G.Monoidal]
  定义体: by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, ε_η,
        prodMonoidal_tensorUnit, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, ε_η,
        prodMonoidal_tensorUnit, prod_id]
  η_ε := by
    ext
    · simp only [CategoryTheo

Depends on / 依赖: CategoryTheory, CategoryTheory.prod_comp_fst, CategoryTheory.prod_comp_snd, _obj, prodMonoidal_tensorUnit, prod_comp_fst, prod_comp_snd, prod_id
-/
instance Monoidal.prod' [F.Monoidal] [G.Monoidal] :
    (prod' F G).Monoidal where
  -- automation should work, but it is terribly slow
  ε_η := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, ε_η,
        prodMonoidal_tensorUnit, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, ε_η,
        prodMonoidal_tensorUnit, prod_id]
  η_ε := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, η_ε,
        prod_id, prod'_obj]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, η_ε,
        prod_id, prod'_obj]
  μ_δ _ _ := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_μ_fst, prod'_δ_fst, μ_δ,
        prod'_obj, prodMonoidal_tensorObj, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_μ_snd, prod'_δ_snd, μ_δ,
        prod'_obj, prodMonoidal_tensorObj, prod_id]
  δ_μ _ _ := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_μ_fst, prod'_δ_fst, δ_μ,
        prod'_obj, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_μ_snd, prod'_δ_snd, δ_μ,
        prod'_obj, prod_id]

end Prod'

end Functor

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.OplaxMonoidal Functor.LaxMonoidal

section LaxMonoidal
variable [F.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- The right adjoint of an oplax monoidal functor is lax monoidal. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `rightAdjointLaxMonoidal` / `rightAdjointLaxMonoidal` 的定义

English:
definition rightAdjointLaxMonoidal
  signature: : G.LaxMonoidal where
  body: adj.homEquiv _ _ (η F)
  μ X Y := adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y))
  μ_natural_left {X Y} f X' := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp, assoc,
      ← δ_natural_left_assoc F]
    suffices F.map (G.map f) ▷ F.ob

中文:
定义 rightAdjointLaxMonoidal
  签名: : G.LaxMonoidal where
  定义体: adj.homEquiv _ _ (η F)
  μ X Y := adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y))
  μ_natural_left {X Y} f X' := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp, assoc,
      ← δ_natural_left_assoc F]
    suffices F.map (G.map f) ▷ F.ob

Depends on / 依赖: adj.homEquiv, homEquiv
-/
def rightAdjointLaxMonoidal : G.LaxMonoidal where
  ε := adj.homEquiv _ _ (η F)
  μ X Y := adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y))
  μ_natural_left {X Y} f X' := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp, assoc,
      ← δ_natural_left_assoc F]
    suffices F.map (G.map f) ▷ F.obj (G.obj X') ≫ _ =
      (adj.counit.app X otimesₘ adj.counit.app X') ≫ _ by rw [this]
    simpa using NatTrans.whiskerRight_app_tensor_app adj.counit adj.counit (f := f) X'
  μ_natural_right {X' Y'} X g := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp,
      assoc, ← δ_natural_right_assoc F]
    suffices F.obj (G.obj X) ◁ F.map (G.map g) ≫ _ =
      (adj.counit.app X otimesₘ adj.counit.app X') ≫ _ by rw [this]
    simpa using NatTrans.whiskerLeft_app_tensor_app adj.counit adj.counit (f := g) _
  associativity X Y Z := (adj.homEquiv _ _).symm.injective (by
    simp only [homEquiv_unit, comp_obj, map_comp, comp_whiskerRight, assoc, homEquiv_counit,
      counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
      MonoidalCategory.whiskerLeft_comp]
    rw [← δ_natural_left_assoc]; rw [← δ_natural_left_assoc]; rw [← δ_natural_left_assoc]
    have := @NatTrans.whiskerRight_app_tensor_app_assoc _ _ _ _ _ _ _ _ _ adj.counit adj.counit
    dsimp only [id_obj, comp_obj, Functor.comp_map, Functor.id_map] at this
    rw [this]; rw [this]; rw [tensorHom_def]; rw [assoc]; rw [← comp_whiskerRight_assoc]; rw [left_triangle_components]; rw [id_whiskerRight]; rw [id_comp]; rw [whisker_exchange_assoc]; rw [whisker_exchange_assoc]; rw [← tensorHom_def_assoc]; rw [associator_naturality]; rw [OplaxMonoidal.associativity_assoc]
    rw [← δ_natural_right_assoc]; rw [← δ_natural_right_assoc]; rw [← δ_natural_right_assoc]
    nth_rw 4 [tensorHom_def]
    rw [← whisker_exchange]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [assoc]; rw [assoc]; rw [counit_naturality]; rw [counit_naturality_assoc]; rw [left_triangle_components_assoc]; rw [MonoidalCategory.whiskerLeft_comp]; rw [assoc]; rw [tensorHom_def]; rw [whisker_exchange])
  left_unitality X := (adj.homEquiv _ _).symm.injective (by
    rw [homEquiv_counit]; rw [homEquiv_counit]; rw [homEquiv_unit]; rw [homEquiv_unit]; rw [comp_whiskerRight]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [counit_naturality]; rw [counit_naturality_assoc]; rw [counit_naturality_assoc]; rw [left_triangle_components_assoc]; rw [← δ_natural_left_assoc]; rw [← δ_natural_left_assoc]; rw [tensorHom_def]; rw [assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [assoc]; rw [counit_naturality]; rw [left_triangle_components_assoc]; rw [id_whiskerLeft]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [left_unitality_hom_assoc])
  right_unitality X := (adj.homEquiv _ _).symm.injective (by
    rw [homEquiv_counit]; rw [homEquiv_unit]; rw [MonoidalCategory.whiskerLeft_comp]; rw [homEquiv_unit]; rw [homEquiv_counit]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [map_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [counit_naturality]; rw [counit_naturality_assoc]; rw [counit_naturality_assoc]; rw [left_triangle_components_assoc]; rw [← δ_natural_right_assoc]; rw [← δ_natural_right_assoc]; rw [tensorHom_def]; rw [assoc]; rw [← whisker_exchange_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [assoc]; rw [counit_naturality]; rw [left_triangle_components_assoc]; rw [MonoidalCategory.whiskerRight_id]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [right_unitality_hom_assoc])

/--
Definition of `IsMonoidal` / `IsMonoidal` 的定义

English:
class IsMonoidal
  parameters: [G.LaxMonoidal]
  axioms and operations (2):
    - leftAdjoint_ε : ε G = adj.unit.app _ ≫ G.map (η F)  [default: by cat_disch]
    - leftAdjoint_μ((X Y : D)) : μ G X Y = adj.unit.app _ ≫ G.map (δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y))  [default: by cat_disch]

中文:
类 IsMonoidal
  参数: [G.LaxMonoidal]
  公理与运算 (2 个):
    - leftAdjoint_ε : ε G = adj.unit.app _ ≫ G.map (η F)  [默认: by cat_disch]
    - leftAdjoint_μ((X Y : D)) : μ G X Y = adj.unit.app _ ≫ G.map (δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y))  [默认: by cat_disch]

Depends on / 依赖: G.map, adj.counit.app, adj.unit.app, cat_disch, counit
-/
class IsMonoidal [G.LaxMonoidal] : Prop where
  leftAdjoint_ε : ε G = adj.unit.app _ ≫ G.map (η F) := by cat_disch
  leftAdjoint_μ (X Y : D) : μ G X Y =
    adj.unit.app _ ≫ G.map (δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y)) := by cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: adj.rightAdjointLaxMonoidal
    adj.IsMonoidal := by
  let := adj.rightAdjointLaxMonoidal
  constructor
  · rfl
  · intro _ _
    rfl

中文:
实例 :
  定义体: adj.rightAdjointLaxMonoidal
    adj.IsMonoidal := by
  let := adj.rightAdjointLaxMonoidal
  constructor
  · rfl
  · intro _ _
    rfl

Depends on / 依赖: adj.rightAdjointLaxMonoidal, rightAdjointLaxMonoidal
-/
instance :
    letI := adj.rightAdjointLaxMonoidal
    adj.IsMonoidal := by
  let := adj.rightAdjointLaxMonoidal
  constructor
  · rfl
  · intro _ _
    rfl

variable [G.LaxMonoidal] [adj.IsMonoidal]

@[reassoc]
/--
lemma `unit_app_unit_comp_map_η` / 引理 `unit_app_unit_comp_map_η`

English:
lemma unit_app_unit_comp_map_η
  statement: adj.unit.app (𝟙_ C) ≫ G.map (η F) = ε G
  proof: Adjunction.IsMonoidal.leftAdjoint_ε.symm

中文:
引理 unit_app_unit_comp_map_η
  结论: adj.unit.app (𝟙_ C) ≫ G.map (η F) = ε G
  证明: Adjunction.IsMonoidal.leftAdjoint_ε.symm

Depends on / 依赖: Adjunction, Adjunction.IsMonoidal.leftAdjoint_, IsMonoidal
-/
lemma unit_app_unit_comp_map_η : adj.unit.app (𝟙_ C) ≫ G.map (η F) = ε G :=
  Adjunction.IsMonoidal.leftAdjoint_ε.symm

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `unit_app_tensor_comp_map_δ` / 引理 `unit_app_tensor_comp_map_δ`

English:
lemma unit_app_tensor_comp_map_δ
  given: (X Y : C)
  proof: by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj), ← adj.unit_naturality_assoc,
    ← Functor.map_comp, ← δ_natural_assoc]

中文:
引理 unit_app_tensor_comp_map_δ
  条件: (X Y : C)
  证明: by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj), ← adj.unit_naturality_assoc,
    ← Functor.map_comp, ← δ_natural_assoc]

Depends on / 依赖: Functor, Functor.map_comp, IsMonoidal, IsMonoidal.leftAdjoint_, adj.unit_naturality_assoc, map_comp, unit_naturality_assoc
-/
lemma unit_app_tensor_comp_map_δ (X Y : C) :
    adj.unit.app (X otimes Y) ≫ G.map (δ F X Y) = (adj.unit.app X otimesₘ adj.unit.app Y) ≫ μ G _ _ := by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj), ← adj.unit_naturality_assoc,
    ← Functor.map_comp, ← δ_natural_assoc]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `map_ε_comp_counit_app_unit` / 引理 `map_ε_comp_counit_app_unit`

English:
lemma map_ε_comp_counit_app_unit
  statement: F.map (ε G) ≫ adj.counit.app (𝟙_ D) = η F
  proof: by
  simp [IsMonoidal.leftAdjoint_ε (adj := adj)]

中文:
引理 map_ε_comp_counit_app_unit
  结论: F.map (ε G) ≫ adj.counit.app (𝟙_ D) = η F
  证明: by
  simp [IsMonoidal.leftAdjoint_ε (adj := adj)]

Depends on / 依赖: IsMonoidal, IsMonoidal.leftAdjoint_
-/
lemma map_ε_comp_counit_app_unit : F.map (ε G) ≫ adj.counit.app (𝟙_ D) = η F := by
  simp [IsMonoidal.leftAdjoint_ε (adj := adj)]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `map_μ_comp_counit_app_tensor` / 引理 `map_μ_comp_counit_app_tensor`

English:
lemma map_μ_comp_counit_app_tensor
  given: (X Y : D)
  proof: by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj)]

中文:
引理 map_μ_comp_counit_app_tensor
  条件: (X Y : D)
  证明: by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj)]

Depends on / 依赖: IsMonoidal, IsMonoidal.leftAdjoint_
-/
lemma map_μ_comp_counit_app_tensor (X Y : D) :
    F.map (μ G X Y) ≫ adj.counit.app (X otimes Y) =
      δ F _ _ ≫ (adj.counit.app X otimesₘ adj.counit.app Y) := by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj)]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Adjunction.id (C := C)).IsMonoidal

中文:
实例 :
  签名: (Adjunction.id (C := C)).IsMonoidal

Depends on / 依赖: IsMonoidal
-/
instance : (Adjunction.id (C := C)).IsMonoidal where

set_option backward.defeqAttrib.useBackward true in
/--
Instance `isMonoidal_comp` / 实例 `isMonoidal_comp`

English:
instance isMonoidal_comp
  signature: {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
  body: by
    simp [IsMonoidal.leftAdjoint_ε (adj := adj'), IsMonoidal.leftAdjoint_ε (adj := adj),
      ← map_comp, ← adj'.unit_naturality_assoc]
  leftAdjoint_μ X Y := by
    simp only [comp_obj, comp_μ, IsMonoidal.leftAdjoint_μ (adj := adj), id_obj,
      IsMonoidal.leftAdjoint_μ (adj := adj'), assoc, ←

中文:
实例 isMonoidal_comp
  签名: {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
  定义体: by
    simp [IsMonoidal.leftAdjoint_ε (adj := adj'), IsMonoidal.leftAdjoint_ε (adj := adj),
      ← map_comp, ← adj'.unit_naturality_assoc]
  leftAdjoint_μ X Y := by
    simp only [comp_obj, comp_μ, IsMonoidal.leftAdjoint_μ (adj := adj), id_obj,
      IsMonoidal.leftAdjoint_μ (adj := adj'), assoc, ←

Depends on / 依赖: Functor, Functor.comp_map, IsMonoidal, IsMonoidal.leftAdjoint_, comp_counit_app, comp_map, comp_obj, comp_unit_app, id_obj, map_comp, tensorHom_comp_tensorHom, unit_naturality_assoc
-/
instance isMonoidal_comp {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
    [F'.OplaxMonoidal] [G'.LaxMonoidal] [adj'.IsMonoidal] : (adj.comp adj').IsMonoidal where
  leftAdjoint_ε := by
    simp [IsMonoidal.leftAdjoint_ε (adj := adj'), IsMonoidal.leftAdjoint_ε (adj := adj),
      ← map_comp, ← adj'.unit_naturality_assoc]
  leftAdjoint_μ X Y := by
    simp only [comp_obj, comp_μ, IsMonoidal.leftAdjoint_μ (adj := adj), id_obj,
      IsMonoidal.leftAdjoint_μ (adj := adj'), assoc, ← map_comp, comp_unit_app, comp_δ,
      comp_counit_app, ← tensorHom_comp_tensorHom, δ_natural_assoc, Functor.comp_map]
    simp

end LaxMonoidal

section OplaxMonoidal
variable [G.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- The left adjoint of a lax monoidal functor is oplax monoidal. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `leftAdjointOplaxMonoidal` / `leftAdjointOplaxMonoidal` 的定义

English:
definition leftAdjointOplaxMonoidal
  signature: : F.OplaxMonoidal where
  body: (adj.homEquiv _ _).symm (ε G)
  δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X otimesₘ adj.unit.app Y) ≫ μ G _ _)
  δ_natural_left _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm]; rw [← Adjunction.homEquiv_naturality_left_symm]; rw [assoc]; rw [← μ_natural_left]
    simp [← tensorH

中文:
定义 leftAdjointOplaxMonoidal
  签名: : F.OplaxMonoidal where
  定义体: (adj.homEquiv _ _).symm (ε G)
  δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X otimesₘ adj.unit.app Y) ≫ μ G _ _)
  δ_natural_left _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm]; rw [← Adjunction.homEquiv_naturality_left_symm]; rw [assoc]; rw [← μ_natural_left]
    simp [← tensorH

Depends on / 依赖: adj.homEquiv, homEquiv
-/
def leftAdjointOplaxMonoidal : F.OplaxMonoidal where
  η := (adj.homEquiv _ _).symm (ε G)
  δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X otimesₘ adj.unit.app Y) ≫ μ G _ _)
  δ_natural_left _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm]; rw [← Adjunction.homEquiv_naturality_left_symm]; rw [assoc]; rw [← μ_natural_left]
    simp [← tensorHom_id]
  δ_natural_right _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm]; rw [← Adjunction.homEquiv_naturality_left_symm]; rw [assoc]; rw [← μ_natural_right]
    simp [← id_tensorHom]
  oplax_associativity X Y Z := (adj.homEquiv _ _).injective (by
    rw [← Adjunction.homEquiv_naturality_right_symm]; rw [← Adjunction.homEquiv_naturality_right_symm]; rw [← Adjunction.homEquiv_naturality_left_symm]; rw [Equiv.apply_symm_apply]; rw [Equiv.apply_symm_apply]; rw [assoc]; rw [assoc]
    conv_lhs =>
      rw [homEquiv_counit]; rw [map_comp_assoc]; rw [map_comp]; rw [← μ_natural_left_assoc]; rw [map_comp]; rw [map_comp]; rw [tensorHom_def'_assoc]
      dsimp
      rw [← comp_whiskerRight_assoc]
    conv_rhs =>
      rw [← μ_natural_right]; rw [homEquiv_counit]; rw [map_comp_assoc]; rw [map_comp]; rw [tensorHom_def_assoc]; rw [← associator_naturality_left_assoc]
      dsimp
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [map_comp]; rw [unit_naturality_assoc]; rw [MonoidalCategory.whiskerLeft_comp]; rw [unit_naturality_assoc]; rw [right_triangle_components]; rw [comp_id]; rw [assoc]; rw [tensorHom_def]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← associator_naturality_middle_assoc]; rw [← associator_naturality_right_assoc]; rw [← associativity G]; rw [← comp_whiskerRight_assoc]; rw [← tensorHom_def]; rw [← whisker_exchange_assoc]; rw [← comp_whiskerRight_assoc]
    simp)
  oplax_left_unitality _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left]; rw [Adjunction.homEquiv_naturality_right]; rw [Equiv.apply_symm_apply]; rw [assoc]; rw [← μ_natural_left]; rw [← tensorHom_id]; rw [tensorHom_comp_tensorHom_assoc]
    simp [tensorHom_def', homEquiv_unit, homEquiv_counit])
  oplax_right_unitality _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left]; rw [Adjunction.homEquiv_naturality_right]; rw [Equiv.apply_symm_apply]; rw [assoc]; rw [← μ_natural_right]; rw [← id_tensorHom]; rw [tensorHom_comp_tensorHom_assoc]
    simp [tensorHom_def, homEquiv_unit, homEquiv_counit])

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: adj.leftAdjointOplaxMonoidal
    adj.IsMonoidal := by
  let := adj.leftAdjointOplaxMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · simp [homEquiv_counit, leftAdjointOplaxMonoidal_η]
  · simp [homEquiv_counit, ← μ_natural, leftAdjointOplaxMonoidal_δ]

中文:
实例 :
  定义体: adj.leftAdjointOplaxMonoidal
    adj.IsMonoidal := by
  let := adj.leftAdjointOplaxMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · simp [homEquiv_counit, leftAdjointOplaxMonoidal_η]
  · simp [homEquiv_counit, ← μ_natural, leftAdjointOplaxMonoidal_δ]

Depends on / 依赖: adj.leftAdjointOplaxMonoidal, leftAdjointOplaxMonoidal
-/
instance :
    letI := adj.leftAdjointOplaxMonoidal
    adj.IsMonoidal := by
  let := adj.leftAdjointOplaxMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · simp [homEquiv_counit, leftAdjointOplaxMonoidal_η]
  · simp [homEquiv_counit, ← μ_natural, leftAdjointOplaxMonoidal_δ]

end OplaxMonoidal

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] leftAdjointOplaxMonoidal_η leftAdjointOplaxMonoidal_δ
  rightAdjointLaxMonoidal_ε rightAdjointLaxMonoidal_μ in
/--
Definition of `laxMonoidalEquivOplaxMonoidal` / `laxMonoidalEquivOplaxMonoidal` 的定义

English:
definition laxMonoidalEquivOplaxMonoidal
  signature: : G.LaxMonoidal ≃ F.OplaxMonoidal where
  body: adj.leftAdjointOplaxMonoidal
  invFun _ := adj.rightAdjointLaxMonoidal
  left_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← μ_natural]
  right_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← δ_natural_assoc]

中文:
定义 laxMonoidalEquivOplaxMonoidal
  签名: : G.LaxMonoidal ≃ F.OplaxMonoidal where
  定义体: adj.leftAdjointOplaxMonoidal
  invFun _ := adj.rightAdjointLaxMonoidal
  left_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← μ_natural]
  right_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← δ_natural_assoc]

Depends on / 依赖: adj.leftAdjointOplaxMonoidal, leftAdjointOplaxMonoidal
-/
def laxMonoidalEquivOplaxMonoidal : G.LaxMonoidal ≃ F.OplaxMonoidal where
  toFun _ := adj.leftAdjointOplaxMonoidal
  invFun _ := adj.rightAdjointLaxMonoidal
  left_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← μ_natural]
  right_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← δ_natural_assoc]

section Monoidal
variable [F.Monoidal] [G.Monoidal] [adj.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `ε_comp_map_ε` / 引理 `ε_comp_map_ε`

English:
lemma ε_comp_map_ε
  statement: ε G ≫ G.map (ε F) = adj.unit.app (𝟙_ C)
  proof: by
  simp [← adj.unit_app_unit_comp_map_η]

@[reassoc]

中文:
引理 ε_comp_map_ε
  结论: ε G ≫ G.map (ε F) = adj.unit.app (𝟙_ C)
  证明: by
  simp [← adj.unit_app_unit_comp_map_η]

@[reassoc]

Depends on / 依赖: adj.unit_app_unit_comp_map_
-/
lemma ε_comp_map_ε : ε G ≫ G.map (ε F) = adj.unit.app (𝟙_ C) := by
  simp [← adj.unit_app_unit_comp_map_η]

@[reassoc]
/--
lemma `map_η_comp_η` / 引理 `map_η_comp_η`

English:
lemma map_η_comp_η
  statement: F.map (η G) ≫ η F = adj.counit.app (𝟙_ D)
  proof: by
  simp [← adj.map_ε_comp_counit_app_unit]

中文:
引理 map_η_comp_η
  结论: F.map (η G) ≫ η F = adj.counit.app (𝟙_ D)
  证明: by
  simp [← adj.map_ε_comp_counit_app_unit]

Depends on / 依赖: adj.map_
-/
lemma map_η_comp_η : F.map (η G) ≫ η F = adj.counit.app (𝟙_ D) := by
  simp [← adj.map_ε_comp_counit_app_unit]

end Monoidal
end Adjunction

namespace Equivalence

variable (e : C ≌ D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e.inverse.Monoidal]
  signature: : e.symm.functor.Monoidal
  body: inferInstanceAs (e.inverse.Monoidal)

中文:
实例 [e.inverse.Monoidal]
  签名: : e.symm.functor.Monoidal
  定义体: inferInstanceAs (e.inverse.Monoidal)

Depends on / 依赖: Monoidal, e.inverse.Monoidal, inverse
-/
instance [e.inverse.Monoidal] : e.symm.functor.Monoidal := inferInstanceAs (e.inverse.Monoidal)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e.functor.Monoidal]
  signature: : e.symm.inverse.Monoidal
  body: inferInstanceAs (e.functor.Monoidal)

中文:
实例 [e.functor.Monoidal]
  签名: : e.symm.inverse.Monoidal
  定义体: inferInstanceAs (e.functor.Monoidal)

Depends on / 依赖: Monoidal, e.functor.Monoidal, functor
-/
instance [e.functor.Monoidal] : e.symm.inverse.Monoidal := inferInstanceAs (e.functor.Monoidal)

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
@[instance_reducible]
/--
Definition of `inverseMonoidal` / `inverseMonoidal` 的定义

English:
definition inverseMonoidal
  signature: [e.functor.Monoidal]
  body: by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    simp only [this, Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    infer_instance
  have : forall (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y => by
    simp only [Ad

中文:
定义 inverseMonoidal
  签名: [e.functor.Monoidal]
  定义体: by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    simp only [this, Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    infer_instance
  have : forall (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y => by
    simp only [Ad

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.rightAdjointLaxMonoidal_, LaxMonoidal, Monoidal, Monoidal.ofLaxMonoidal, e.inverse, e.toAdjunction.rightAdjointLaxMonoidal, homEquiv_unit, infer_instance, inverse, ofLaxMonoidal, rightAdjointLaxMonoidal, toAdjunction
-/
noncomputable def inverseMonoidal [e.functor.Monoidal] : e.inverse.Monoidal := by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    simp only [this, Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    infer_instance
  have : forall (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y => by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
    infer_instance
  apply Monoidal.ofLaxMonoidal

/--
Definition of `IsMonoidal` / `IsMonoidal` 的定义

English:
abbreviation IsMonoidal
  signature: [e.functor.Monoidal] [e.inverse.Monoidal]
  body: e.toAdjunction.IsMonoidal

中文:
缩写 IsMonoidal
  签名: [e.functor.Monoidal] [e.inverse.Monoidal]
  定义体: e.toAdjunction.IsMonoidal

Depends on / 依赖: IsMonoidal, e.toAdjunction.IsMonoidal, toAdjunction
-/
abbrev IsMonoidal [e.functor.Monoidal] [e.inverse.Monoidal] : Prop := e.toAdjunction.IsMonoidal

set_option backward.isDefEq.respectTransparency false in
example [e.functor.Monoidal] : letI := e.inverseMonoidal; e.IsMonoidal := inferInstance

variable [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[reassoc]
/--
lemma `unitIso_hom_app_comp_inverse_map_η_functor` / 引理 `unitIso_hom_app_comp_inverse_map_η_functor`

English:
lemma unitIso_hom_app_comp_inverse_map_η_functor
  proof: e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]

中文:
引理 unitIso_hom_app_comp_inverse_map_η_functor
  证明: e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]

Depends on / 依赖: e.toAdjunction.unit_app_unit_comp_map_, toAdjunction
-/
lemma unitIso_hom_app_comp_inverse_map_η_functor :
    e.unitIso.hom.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
/--
lemma `unitIso_hom_app_tensor_comp_inverse_map_δ_functor` / 引理 `unitIso_hom_app_tensor_comp_inverse_map_δ_functor`

English:
lemma unitIso_hom_app_tensor_comp_inverse_map_δ_functor
  given: (X Y : C)
  proof: e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc]

中文:
引理 unitIso_hom_app_tensor_comp_inverse_map_δ_functor
  条件: (X Y : C)
  证明: e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc]

Depends on / 依赖: e.toAdjunction.unit_app_tensor_comp_map_, toAdjunction
-/
lemma unitIso_hom_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unitIso.hom.app (X otimes Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unitIso.hom.app X otimesₘ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc]
/--
lemma `functor_map_ε_inverse_comp_counitIso_hom_app` / 引理 `functor_map_ε_inverse_comp_counitIso_hom_app`

English:
lemma functor_map_ε_inverse_comp_counitIso_hom_app
  proof: e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]

中文:
引理 functor_map_ε_inverse_comp_counitIso_hom_app
  证明: e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]

Depends on / 依赖: e.toAdjunction.map_, toAdjunction
-/
lemma functor_map_ε_inverse_comp_counitIso_hom_app :
    e.functor.map (ε e.inverse) ≫ e.counitIso.hom.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
/--
lemma `functor_map_μ_inverse_comp_counitIso_hom_app_tensor` / 引理 `functor_map_μ_inverse_comp_counitIso_hom_app_tensor`

English:
lemma functor_map_μ_inverse_comp_counitIso_hom_app_tensor
  given: (X Y : D)
  proof: e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]

中文:
引理 functor_map_μ_inverse_comp_counitIso_hom_app_tensor
  条件: (X Y : D)
  证明: e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]

Depends on / 依赖: e.toAdjunction.map_, toAdjunction
-/
lemma functor_map_μ_inverse_comp_counitIso_hom_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counitIso.hom.app (X otimes Y) =
      δ e.functor _ _ ≫ (e.counitIso.hom.app X otimesₘ e.counitIso.hom.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]
/--
lemma `counitIso_inv_app_comp_functor_map_η_inverse` / 引理 `counitIso_inv_app_comp_functor_map_η_inverse`

English:
lemma counitIso_inv_app_comp_functor_map_η_inverse
  proof: by
  rw [← cancel_epi (η e.functor)]; rw [Monoidal.η_ε]; rw [← functor_map_ε_inverse_comp_counitIso_hom_app]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [Monoidal.map_ε_η]

中文:
引理 counitIso_inv_app_comp_functor_map_η_inverse
  证明: by
  rw [← cancel_epi (η e.functor)]; rw [Monoidal.η_ε]; rw [← functor_map_ε_inverse_comp_counitIso_hom_app]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [Monoidal.map_ε_η]

Depends on / 依赖: Category, Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal, Monoidal.map_, cancel_epi, e.functor, functor, hom_inv_id_app_assoc
-/
lemma counitIso_inv_app_comp_functor_map_η_inverse :
    e.counitIso.inv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor)]; rw [Monoidal.η_ε]; rw [← functor_map_ε_inverse_comp_counitIso_hom_app]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [Monoidal.map_ε_η]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `counitIso_inv_app_tensor_comp_functor_map_δ_inverse` / 引理 `counitIso_inv_app_tensor_comp_functor_map_δ_inverse`

English:
lemma counitIso_inv_app_tensor_comp_functor_map_δ_inverse
  given: (X Y : C)
  proof: by
  rw [← cancel_epi (δ e.functor _ _)]; rw [Monoidal.δ_μ_assoc]
  apply e.inverse.map_injective
  simp [← cancel_epi (e.unitIso.hom.app (X otimes Y)), Functor.map_comp,
    unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]

@[reassoc]

中文:
引理 counitIso_inv_app_tensor_comp_functor_map_δ_inverse
  条件: (X Y : C)
  证明: by
  rw [← cancel_epi (δ e.functor _ _)]; rw [Monoidal.δ_μ_assoc]
  apply e.inverse.map_injective
  simp [← cancel_epi (e.unitIso.hom.app (X otimes Y)), Functor.map_comp,
    unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, Monoidal, cancel_epi, e.functor, e.inverse.map_injective, e.unitIso.hom.app, functor, inverse, map_comp, map_injective, otimes, unitIso
-/
lemma counitIso_inv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitIso.inv.app (e.functor.obj X otimes e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X otimesₘ e.unitIso.hom.app Y) := by
  rw [← cancel_epi (δ e.functor _ _)]; rw [Monoidal.δ_μ_assoc]
  apply e.inverse.map_injective
  simp [← cancel_epi (e.unitIso.hom.app (X otimes Y)), Functor.map_comp,
    unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]

@[reassoc]
/--
lemma `unit_app_comp_inverse_map_η_functor` / 引理 `unit_app_comp_inverse_map_η_functor`

English:
lemma unit_app_comp_inverse_map_η_functor
  proof: e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]

中文:
引理 unit_app_comp_inverse_map_η_functor
  证明: e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]

Depends on / 依赖: e.toAdjunction.unit_app_unit_comp_map_, toAdjunction
-/
lemma unit_app_comp_inverse_map_η_functor :
    e.unit.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
/--
lemma `unit_app_tensor_comp_inverse_map_δ_functor` / 引理 `unit_app_tensor_comp_inverse_map_δ_functor`

English:
lemma unit_app_tensor_comp_inverse_map_δ_functor
  given: (X Y : C)
  proof: e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc (attr := simp)]

中文:
引理 unit_app_tensor_comp_inverse_map_δ_functor
  条件: (X Y : C)
  证明: e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc (attr := simp)]

Depends on / 依赖: e.toAdjunction.unit_app_tensor_comp_map_, toAdjunction
-/
lemma unit_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unit.app (X otimes Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unit.app X otimesₘ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc (attr := simp)]
/--
lemma `functor_map_ε_inverse_comp_counit_app` / 引理 `functor_map_ε_inverse_comp_counit_app`

English:
lemma functor_map_ε_inverse_comp_counit_app
  proof: e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]

中文:
引理 functor_map_ε_inverse_comp_counit_app
  证明: e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]

Depends on / 依赖: e.toAdjunction.map_, toAdjunction
-/
lemma functor_map_ε_inverse_comp_counit_app :
    e.functor.map (ε e.inverse) ≫ e.counit.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
/--
lemma `functor_map_μ_inverse_comp_counit_app_tensor` / 引理 `functor_map_μ_inverse_comp_counit_app_tensor`

English:
lemma functor_map_μ_inverse_comp_counit_app_tensor
  given: (X Y : D)
  proof: e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]

中文:
引理 functor_map_μ_inverse_comp_counit_app_tensor
  条件: (X Y : D)
  证明: e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]

Depends on / 依赖: e.toAdjunction.map_, toAdjunction
-/
lemma functor_map_μ_inverse_comp_counit_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counit.app (X otimes Y) =
      δ e.functor _ _ ≫ (e.counit.app X otimesₘ e.counit.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]
/--
lemma `counitInv_app_comp_functor_map_η_inverse` / 引理 `counitInv_app_comp_functor_map_η_inverse`

English:
lemma counitInv_app_comp_functor_map_η_inverse
  proof: by
  rw [← cancel_epi (η e.functor)]; rw [Monoidal.η_ε]; rw [← functor_map_ε_inverse_comp_counitIso_hom_app]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [Monoidal.map_ε_η]

@[reassoc]

中文:
引理 counitInv_app_comp_functor_map_η_inverse
  证明: by
  rw [← cancel_epi (η e.functor)]; rw [Monoidal.η_ε]; rw [← functor_map_ε_inverse_comp_counitIso_hom_app]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [Monoidal.map_ε_η]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal, Monoidal.map_, cancel_epi, e.functor, functor, hom_inv_id_app_assoc
-/
lemma counitInv_app_comp_functor_map_η_inverse :
    e.counitInv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor)]; rw [Monoidal.η_ε]; rw [← functor_map_ε_inverse_comp_counitIso_hom_app]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [Monoidal.map_ε_η]

@[reassoc]
/--
lemma `counitInv_app_tensor_comp_functor_map_δ_inverse` / 引理 `counitInv_app_tensor_comp_functor_map_δ_inverse`

English:
lemma counitInv_app_tensor_comp_functor_map_δ_inverse
  given: (X Y : C)
  proof: counitIso_inv_app_tensor_comp_functor_map_δ_inverse e X Y

@[reassoc (attr := simp)]

中文:
引理 counitInv_app_tensor_comp_functor_map_δ_inverse
  条件: (X Y : C)
  证明: counitIso_inv_app_tensor_comp_functor_map_δ_inverse e X Y

@[reassoc (attr := simp)]
-/
lemma counitInv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitInv.app (e.functor.obj X otimes e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X otimesₘ e.unitIso.hom.app Y) :=
  counitIso_inv_app_tensor_comp_functor_map_δ_inverse e X Y

@[reassoc (attr := simp)]
/--
lemma `ε_comp_map_ε` / 引理 `ε_comp_map_ε`

English:
lemma ε_comp_map_ε
  statement: ε e.inverse ≫ e.inverse.map (ε e.functor) = e.unit.app (𝟙_ C)
  proof: e.toAdjunction.ε_comp_map_ε

@[reassoc (attr := simp)]

中文:
引理 ε_comp_map_ε
  结论: ε e.inverse ≫ e.inverse.map (ε e.functor) = e.unit.app (𝟙_ C)
  证明: e.toAdjunction.ε_comp_map_ε

@[reassoc (attr := simp)]

Depends on / 依赖: e.toAdjunction, toAdjunction
-/
lemma ε_comp_map_ε : ε e.inverse ≫ e.inverse.map (ε e.functor) = e.unit.app (𝟙_ C) :=
  e.toAdjunction.ε_comp_map_ε

@[reassoc (attr := simp)]
/--
lemma `map_η_comp_η` / 引理 `map_η_comp_η`

English:
lemma map_η_comp_η
  statement: e.functor.map (η e.inverse) ≫ η e.functor = e.counit.app (𝟙_ D)
  proof: e.toAdjunction.map_η_comp_η

中文:
引理 map_η_comp_η
  结论: e.functor.map (η e.inverse) ≫ η e.functor = e.counit.app (𝟙_ D)
  证明: e.toAdjunction.map_η_comp_η

Depends on / 依赖: e.toAdjunction.map_, toAdjunction
-/
lemma map_η_comp_η : e.functor.map (η e.inverse) ≫ η e.functor = e.counit.app (𝟙_ D) :=
  e.toAdjunction.map_η_comp_η

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (refl (C := C)).functor.Monoidal
  body: inferInstanceAs (𝟭 C).Monoidal

中文:
实例 :
  签名: (refl (C := C)).functor.Monoidal
  定义体: inferInstanceAs (𝟭 C).Monoidal

Depends on / 依赖: Monoidal, functor, functor.Monoidal
-/
instance : (refl (C := C)).functor.Monoidal := inferInstanceAs (𝟭 C).Monoidal
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (refl (C := C)).inverse.Monoidal
  body: inferInstanceAs (𝟭 C).Monoidal

中文:
实例 :
  签名: (refl (C := C)).inverse.Monoidal
  定义体: inferInstanceAs (𝟭 C).Monoidal

Depends on / 依赖: Monoidal, inverse, inverse.Monoidal
-/
instance : (refl (C := C)).inverse.Monoidal := inferInstanceAs (𝟭 C).Monoidal

/--
Instance `isMonoidal_refl` / 实例 `isMonoidal_refl`

English:
instance isMonoidal_refl
  signature: : (Equivalence.refl (C := C)).IsMonoidal
  body: inferInstanceAs (Adjunction.id (C := C)).IsMonoidal

中文:
实例 isMonoidal_refl
  签名: : (Equivalence.refl (C := C)).IsMonoidal
  定义体: inferInstanceAs (Adjunction.id (C := C)).IsMonoidal

Depends on / 依赖: IsMonoidal
-/
instance isMonoidal_refl : (Equivalence.refl (C := C)).IsMonoidal :=
  inferInstanceAs (Adjunction.id (C := C)).IsMonoidal

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isMonoidal_symm` / 实例 `isMonoidal_symm`

English:
instance isMonoidal_symm
  signature: : e.symm.IsMonoidal where
  body: by
    simp only [toAdjunction]
    dsimp [symm]
    rw [counitIso_inv_app_comp_functor_map_η_inverse]
  leftAdjoint_μ X Y := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [map_comp]; rw [counitIso_inv_app_tensor_comp_functor_map_δ_inverse_assoc]
    simp [← map_comp]

中文:
实例 isMonoidal_symm
  签名: : e.symm.IsMonoidal where
  定义体: by
    simp only [toAdjunction]
    dsimp [symm]
    rw [counitIso_inv_app_comp_functor_map_η_inverse]
  leftAdjoint_μ X Y := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [map_comp]; rw [counitIso_inv_app_tensor_comp_functor_map_δ_inverse_assoc]
    simp [← map_comp]

Depends on / 依赖: map_comp, toAdjunction
-/
instance isMonoidal_symm : e.symm.IsMonoidal where
  leftAdjoint_ε := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [counitIso_inv_app_comp_functor_map_η_inverse]
  leftAdjoint_μ X Y := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [map_comp]; rw [counitIso_inv_app_tensor_comp_functor_map_δ_inverse_assoc]
    simp [← map_comp]

section

variable (e' : D ≌ E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e'.functor.Monoidal]
  signature: : (e.trans e').functor.Monoidal
  body: inferInstanceAs (e.functor ⋙ e'.functor).Monoidal

中文:
实例 [e'.functor.Monoidal]
  签名: : (e.trans e').functor.Monoidal
  定义体: inferInstanceAs (e.functor ⋙ e'.functor).Monoidal

Depends on / 依赖: Monoidal, e.functor, functor
-/
instance [e'.functor.Monoidal] : (e.trans e').functor.Monoidal :=
  inferInstanceAs (e.functor ⋙ e'.functor).Monoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e'.inverse.Monoidal]
  signature: : (e.trans e').inverse.Monoidal
  body: inferInstanceAs (e'.inverse ⋙ e.inverse).Monoidal

中文:
实例 [e'.inverse.Monoidal]
  签名: : (e.trans e').inverse.Monoidal
  定义体: inferInstanceAs (e'.inverse ⋙ e.inverse).Monoidal

Depends on / 依赖: Monoidal, e.inverse, inverse
-/
instance [e'.inverse.Monoidal] : (e.trans e').inverse.Monoidal :=
  inferInstanceAs (e'.inverse ⋙ e.inverse).Monoidal

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isMonoidal_trans` / 实例 `isMonoidal_trans`

English:
instance isMonoidal_trans
  signature: [e'.functor.Monoidal] [e'.inverse.Monoidal] [e'.IsMonoidal]
  body: by
  dsimp [Equivalence.IsMonoidal]
  rw [trans_toAdjunction]
  infer_instance

中文:
实例 isMonoidal_trans
  签名: [e'.functor.Monoidal] [e'.inverse.Monoidal] [e'.IsMonoidal]
  定义体: by
  dsimp [Equivalence.IsMonoidal]
  rw [trans_toAdjunction]
  infer_instance

Depends on / 依赖: Equivalence, Equivalence.IsMonoidal, IsMonoidal, infer_instance, trans_toAdjunction
-/
instance isMonoidal_trans [e'.functor.Monoidal] [e'.inverse.Monoidal] [e'.IsMonoidal] :
    (e.trans e').IsMonoidal := by
  dsimp [Equivalence.IsMonoidal]
  rw [trans_toAdjunction]
  infer_instance

end

end Equivalence

variable (C D)

/--
Definition of `LaxMonoidalFunctor` / `LaxMonoidalFunctor` 的定义

English:
structure LaxMonoidalFunctor
  parameters: extends C ⥤ D
  extends: C ⥤ D
  axioms and operations (1):
    - laxMonoidal : toFunctor.LaxMonoidal  [default: by infer_instance]

中文:
结构 LaxMonoidalFunctor
  参数: extends C ⥤ D
  继承: C ⥤ D
  公理与运算 (1 个):
    - laxMonoidal : toFunctor.LaxMonoidal  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure LaxMonoidalFunctor extends C ⥤ D where
  laxMonoidal : toFunctor.LaxMonoidal := by infer_instance

namespace LaxMonoidalFunctor

attribute [instance] laxMonoidal

variable {C D}

/-- Constructor for `LaxMonoidalFunctor C D`. -/
@[simps toFunctor]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (F : C ⥤ D) [F.LaxMonoidal]
  body: F

中文:
定义 of
  签名: (F : C ⥤ D) [F.LaxMonoidal]
  定义体: F
-/
def of (F : C ⥤ D) [F.LaxMonoidal] : LaxMonoidalFunctor C D where
  toFunctor := F

end LaxMonoidalFunctor

namespace Functor.Monoidal

variable {C D}

/--
Auxiliary definition for `Functor.Monoidal.transport`
-/
@[simps!]
/--
Definition of `coreMonoidalTransport` / `coreMonoidalTransport` 的定义

English:
definition coreMonoidalTransport
  signature: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  body: εIso F ≪≫ i.app _
  μIso X Y := tensorIso (i.symm.app _) (i.symm.app _) ≪≫ μIso F X Y ≪≫ i.app _
  μIso_hom_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μIso_hom_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    sim

中文:
定义 coreMonoidalTransport
  签名: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  定义体: εIso F ≪≫ i.app _
  μIso X Y := tensorIso (i.symm.app _) (i.symm.app _) ≪≫ μIso F X Y ≪≫ i.app _
  μIso_hom_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μIso_hom_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    sim

Depends on / 依赖: i.app
-/
def coreMonoidalTransport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.CoreMonoidal where
  εIso := εIso F ≪≫ i.app _
  μIso X Y := tensorIso (i.symm.app _) (i.symm.app _) ≪≫ μIso F X Y ≪≫ i.app _
  μIso_hom_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μIso_hom_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, μIso_hom, comp_whiskerRight,
      Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [← i.hom.naturality]; rw [map_associator_assoc]; rw [Functor.OplaxMonoidal.associativity_assoc]; rw [whiskerLeft_δ_μ_assoc]; rw [δ_μ_assoc]
    simp only [← Category.assoc]
    congr 1
    slice_lhs 3 4 =>
      rw [← tensorHom_id]; rw [tensorHom_comp_tensorHom]
      simp only [Iso.hom_inv_id_app, Category.id_comp, id_tensorHom]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
    simp only [tensor_whiskerLeft, Functor.LaxMonoidal.associativity, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← tensorHom_id]; rw [associator_naturality_assoc]
    simp [← id_tensorHom, -tensorHom_id]
  left_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← tensorHom_id, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.comp_id, Category.id_comp]
    rw [← i.hom.naturality]; rw [← Category.comp_id (i.inv.app X)]; rw [← Category.id_comp (Functor.LaxMonoidal.ε F)]; rw [← tensorHom_comp_tensorHom]
    simp
  right_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← id_tensorHom, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Iso.hom_inv_id_app, Category.comp_id]
    rw [← i.hom.naturality]; rw [← Category.comp_id (i.inv.app X)]; rw [← Category.id_comp (Functor.LaxMonoidal.ε F)]; rw [← tensorHom_comp_tensorHom]
    simp

/--
Transport the structure of a monoidal functor along a natural isomorphism of functors.
-/
@[instance_reducible]
/--
Definition of `transport` / `transport` 的定义

English:
definition transport
  signature: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  body: (coreMonoidalTransport i).toMonoidal

@[reassoc]

中文:
定义 transport
  签名: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  定义体: (coreMonoidalTransport i).toMonoidal

@[reassoc]

Depends on / 依赖: coreMonoidalTransport, toMonoidal
-/
def transport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.Monoidal :=
  (coreMonoidalTransport i).toMonoidal

@[reassoc]
/--
lemma `transport_ε` / 引理 `transport_ε`

English:
lemma transport_ε
  given: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  statement: letI
  proof: transport i
    LaxMonoidal.ε G = LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]

中文:
引理 transport_ε
  条件: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  结论: letI
  证明: transport i
    LaxMonoidal.ε G = LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]

Depends on / 依赖: E.mem, K.hasPullbacks_of_mem, hasPullbacks_of_mem, transport
-/
lemma transport_ε {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : letI := transport i
    LaxMonoidal.ε G = LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]
/--
lemma `transport_η` / 引理 `transport_η`

English:
lemma transport_η
  given: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  statement: letI
  proof: transport i
    OplaxMonoidal.η G = i.inv.app (𝟙_ C) ≫ OplaxMonoidal.η F :=
  rfl

@[reassoc]

中文:
引理 transport_η
  条件: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G)
  结论: letI
  证明: transport i
    OplaxMonoidal.η G = i.inv.app (𝟙_ C) ≫ OplaxMonoidal.η F :=
  rfl

@[reassoc]

Depends on / 依赖: E.presieve, hasPullback, transport
-/
lemma transport_η {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : letI := transport i
    OplaxMonoidal.η G = i.inv.app (𝟙_ C) ≫ OplaxMonoidal.η F :=
  rfl

@[reassoc]
/--
lemma `transport_μ` / 引理 `transport_μ`

English:
lemma transport_μ
  given: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C)
  statement: letI
  proof: transport i
    LaxMonoidal.μ G X Y = (i.inv.app X otimesₘ i.inv.app Y) ≫ LaxMonoidal.μ F X Y ≫ i.hom.app (X otimes Y) :=
  rfl

@[reassoc]

中文:
引理 transport_μ
  条件: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C)
  结论: letI
  证明: transport i
    LaxMonoidal.μ G X Y = (i.inv.app X otimesₘ i.inv.app Y) ≫ LaxMonoidal.μ F X Y ≫ i.hom.app (X otimes Y) :=
  rfl

@[reassoc]

Depends on / 依赖: hasPullback_symmetry, transport
-/
lemma transport_μ {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    LaxMonoidal.μ G X Y = (i.inv.app X otimesₘ i.inv.app Y) ≫ LaxMonoidal.μ F X Y ≫ i.hom.app (X otimes Y) :=
  rfl

@[reassoc]
/--
lemma `transport_δ` / 引理 `transport_δ`

English:
lemma transport_δ
  given: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C)
  statement: letI
  proof: transport i
    OplaxMonoidal.δ G X Y =
      i.inv.app (X otimes Y) ≫ OplaxMonoidal.δ F X Y ≫ (i.hom.app X otimesₘ i.hom.app Y) :=
  coreMonoidalTransport_μIso_inv _ _ _

中文:
引理 transport_δ
  条件: {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C)
  结论: letI
  证明: transport i
    OplaxMonoidal.δ G X Y =
      i.inv.app (X otimes Y) ≫ OplaxMonoidal.δ F X Y ≫ (i.hom.app X otimesₘ i.hom.app Y) :=
  coreMonoidalTransport_μIso_inv _ _ _

Depends on / 依赖: transport
-/
lemma transport_δ {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    OplaxMonoidal.δ G X Y =
      i.inv.app (X otimes Y) ≫ OplaxMonoidal.δ F X Y ≫ (i.hom.app X otimesₘ i.hom.app Y) :=
  coreMonoidalTransport_μIso_inv _ _ _

end Functor.Monoidal

namespace Equivalence

variable {C D}

/--
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` and `e.functor ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/--
Definition of `monoidalOfPrecompFunctor` / `monoidalOfPrecompFunctor` 的定义

English:
definition monoidalOfPrecompFunctor
  signature: (e : C ≌ D) (F : D ⥤ E) {F' : C ⥤ E} (i : e.functor ⋙ F ≅ F')
  body: letI : (e.functor ⋙ F).Monoidal := .transport i.symm
  .transport (e.invFunIdAssoc F)

中文:
定义 monoidalOfPrecompFunctor
  签名: (e : C ≌ D) (F : D ⥤ E) {F' : C ⥤ E} (i : e.functor ⋙ F ≅ F')
  定义体: letI : (e.functor ⋙ F).Monoidal := .transport i.symm
  .transport (e.invFunIdAssoc F)

Depends on / 依赖: Monoidal, e.functor, e.invFunIdAssoc, functor, i.symm, invFunIdAssoc, transport
-/
def monoidalOfPrecompFunctor (e : C ≌ D) (F : D ⥤ E) {F' : C ⥤ E} (i : e.functor ⋙ F ≅ F')
    [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal :=
  letI : (e.functor ⋙ F).Monoidal := .transport i.symm
  .transport (e.invFunIdAssoc F)

/--
Given a functor `F` and an equivalence of categories `e` such that `e.functor` and `e.inverse ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/--
Definition of `monoidalOfPrecompInverse` / `monoidalOfPrecompInverse` 的定义

English:
definition monoidalOfPrecompInverse
  signature: (e : C ≌ D) (F : C ⥤ E) {F' : D ⥤ E} (i : e.inverse ⋙ F ≅ F')
  body: e.symm.monoidalOfPrecompFunctor F i

中文:
定义 monoidalOfPrecompInverse
  签名: (e : C ≌ D) (F : C ⥤ E) {F' : D ⥤ E} (i : e.inverse ⋙ F ≅ F')
  定义体: e.symm.monoidalOfPrecompFunctor F i

Depends on / 依赖: e.symm.monoidalOfPrecompFunctor, monoidalOfPrecompFunctor
-/
def monoidalOfPrecompInverse (e : C ≌ D) (F : C ⥤ E) {F' : D ⥤ E} (i : e.inverse ⋙ F ≅ F')
    [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal :=
  e.symm.monoidalOfPrecompFunctor F i

/--
Given a functor `F` and an equivalence of categories `e` such that `e.functor` and `F ⋙ e.inverse`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/--
Definition of `monoidalOfPostcompInverse` / `monoidalOfPostcompInverse` 的定义

English:
definition monoidalOfPostcompInverse
  signature: (e : C ≌ D) (F : E ⥤ D) {F' : E ⥤ C} (i : F ⋙ e.inverse ≅ F')
  body: .transport (Functor.isoWhiskerRight i.symm e.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.counitIso ≪≫ F.rightUnitor)

中文:
定义 monoidalOfPostcompInverse
  签名: (e : C ≌ D) (F : E ⥤ D) {F' : E ⥤ C} (i : F ⋙ e.inverse ≅ F')
  定义体: .transport (Functor.isoWhiskerRight i.symm e.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.counitIso ≪≫ F.rightUnitor)

Depends on / 依赖: F.rightUnitor, Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, associator, counitIso, e.counitIso, e.functor, functor, i.symm, isoWhiskerLeft, isoWhiskerRight, rightUnitor, transport
-/
def monoidalOfPostcompInverse (e : C ≌ D) (F : E ⥤ D) {F' : E ⥤ C} (i : F ⋙ e.inverse ≅ F')
    [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal :=
  .transport (Functor.isoWhiskerRight i.symm e.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.counitIso ≪≫ F.rightUnitor)

/--
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` and `F ⋙ e.functor`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/--
Definition of `monoidalOfPostcompFunctor` / `monoidalOfPostcompFunctor` 的定义

English:
definition monoidalOfPostcompFunctor
  signature: (e : C ≌ D) (F : E ⥤ C) {F' : E ⥤ D} (i : F ⋙ e.functor ≅ F')
  body: e.symm.monoidalOfPostcompInverse _ i

中文:
定义 monoidalOfPostcompFunctor
  签名: (e : C ≌ D) (F : E ⥤ C) {F' : E ⥤ D} (i : F ⋙ e.functor ≅ F')
  定义体: e.symm.monoidalOfPostcompInverse _ i

Depends on / 依赖: e.symm.monoidalOfPostcompInverse, monoidalOfPostcompInverse
-/
def monoidalOfPostcompFunctor (e : C ≌ D) (F : E ⥤ C) {F' : E ⥤ D} (i : F ⋙ e.functor ≅ F')
    [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal :=
  e.symm.monoidalOfPostcompInverse _ i

end Equivalence

end CategoryTheory
