/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Model categories

We introduce a typeclass `ModelCategory C` expressing that `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" and "weak equivalences"
which satisfy the axioms of (closed) model categories as they appear for example
in *Simplicial Homotopy Theory* by Goerss and Jardine. We also provide an
alternate constructor `ModelCategory.mk'` which uses a formulation of the axioms
using weak factorization systems.

As a given category `C` may have several model category structures, it is advisable
to define only local instances of `ModelCategory`, or to set these instances on type synonyms.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]
* https://ncatlab.org/nlab/show/model+category

-/

@[expose] public section

universe w v u

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C]

/--
Definition of `ModelCategory` / `ModelCategory` 的定义

English:
class ModelCategory
  parameters: where
  axioms and operations (13):
    - categoryWithFibrations : CategoryWithFibrations C  [default: by infer_instance]
    - categoryWithCofibrations : CategoryWithCofibrations C  [default: by infer_instance]
    - categoryWithWeakEquivalences : CategoryWithWeakEquivalences C  [default: by infer_instance]
    - cm1a : HasFiniteLimits C  [default: by infer_instance]
    - cm1b : HasFiniteColimits C  [default: by infer_instance]
    - cm2 : (weakEquivalences C).HasTwoOutOfThreeProperty  [default: by infer_instance]
    - cm3a : (weakEquivalences C).IsStableUnderRetracts  [default: by infer_instance]
    - cm3b : (fibrations C).IsStableUnderRetracts  [default: by infer_instance]
    - cm3c : (cofibrations C).IsStableUnderRetracts  [default: by infer_instance]
    - cm4a({A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p]) : HasLiftingProperty i p  [default: by intros; infer_instance]
    - cm4b({A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p]) : HasLiftingProperty i p  [default: by intros; infer_instance]
    - cm5a : MorphismProperty.HasFactorization (trivialCofibrations C) (fibrations C)  [default: by infer_instance]
    - cm5b : MorphismProperty.HasFactorization (cofibrations C) (trivialFibrations C)  [default: by infer_instance]

中文:
类 ModelCategory
  参数: where
  公理与运算 (13 个):
    - categoryWithFibrations : CategoryWithFibrations C  [默认: by infer_instance]
    - categoryWithCofibrations : CategoryWithCofibrations C  [默认: by infer_instance]
    - categoryWithWeakEquivalences : CategoryWithWeakEquivalences C  [默认: by infer_instance]
    - cm1a : HasFiniteLimits C  [默认: by infer_instance]
    - cm1b : HasFiniteColimits C  [默认: by infer_instance]
    - cm2 : (weakEquivalences C).HasTwoOutOfThree命题erty  [默认: by infer_instance]
    - cm3a : (weakEquivalences C).IsStableUnderRetracts  [默认: by infer_instance]
    - cm3b : (fibrations C).IsStableUnderRetracts  [默认: by infer_instance]
    - cm3c : (cofibrations C).IsStableUnderRetracts  [默认: by infer_instance]
    - cm4a({A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p]) : HasLifting命题erty i p  [默认: by intros; infer_instance]
    - cm4b({A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p]) : HasLifting命题erty i p  [默认: by intros; infer_instance]
    - cm5a : Morphism命题erty.HasFactorization (trivialCofibrations C) (fibrations C)  [默认: by infer_instance]
    - cm5b : Morphism命题erty.HasFactorization (cofibrations C) (trivialFibrations C)  [默认: by infer_instance]

Depends on / 依赖: CategoryWithCofibrations, CategoryWithWeakEquivalences, HasFiniteColimits, HasFiniteLimits, HasTwoOutOfThreeProperty, IsStableUnderRetracts, categoryWithCofibrations, categoryWithWeakEquivalences, cofibrations, fibrations, infer_instance, weakEquivalences
-/
class ModelCategory where
  categoryWithFibrations : CategoryWithFibrations C := by infer_instance
  categoryWithCofibrations : CategoryWithCofibrations C := by infer_instance
  categoryWithWeakEquivalences : CategoryWithWeakEquivalences C := by infer_instance
  cm1a : HasFiniteLimits C := by infer_instance
  cm1b : HasFiniteColimits C := by infer_instance
  cm2 : (weakEquivalences C).HasTwoOutOfThreeProperty := by infer_instance
  cm3a : (weakEquivalences C).IsStableUnderRetracts := by infer_instance
  cm3b : (fibrations C).IsStableUnderRetracts := by infer_instance
  cm3c : (cofibrations C).IsStableUnderRetracts := by infer_instance
  cm4a {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm4b {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm5a : MorphismProperty.HasFactorization (trivialCofibrations C) (fibrations C) := by
    infer_instance
  cm5b : MorphismProperty.HasFactorization (cofibrations C) (trivialFibrations C) := by
    infer_instance

namespace ModelCategory

attribute [instance_reducible]
  categoryWithFibrations categoryWithCofibrations categoryWithWeakEquivalences
attribute [instance] categoryWithFibrations categoryWithCofibrations categoryWithWeakEquivalences
  cm1a cm1b cm2 cm3a cm3b cm3c cm4a cm4b cm5a cm5b

section

variable [ModelCategory C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)
  body: MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp => by
.mp hi obtain ⟨_, _⟩ := mem_trivialCofibrations_iff i
    rw [← fibration_iff] at hp
    infer_instance)

中文:
实例 :
  签名: Morphism命题erty.IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)
  定义体: MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp => by
.mp hi obtain ⟨_, _⟩ := mem_trivialCofibrations_iff i
    rw [← fibration_iff] at hp
    infer_instance)

Depends on / 依赖: IsWeakFactorizationSystem, MorphismProperty, MorphismProperty.IsWeakFactorizationSystem.mk, fibration_iff, infer_instance, mem_trivialCofibrations_iff
-/
instance : MorphismProperty.IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp => by
.mp hi obtain ⟨_, _⟩ := mem_trivialCofibrations_iff i
    rw [← fibration_iff] at hp
    infer_instance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)
  body: MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp => by
    rw [mem_trivialFibrations_iff] at hp
    rw [← cofibration_iff] at hi
    have := hp.1
    have := hp.2
    infer_instance)

中文:
实例 :
  签名: Morphism命题erty.IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)
  定义体: MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp => by
    rw [mem_trivialFibrations_iff] at hp
    rw [← cofibration_iff] at hi
    have := hp.1
    have := hp.2
    infer_instance)

Depends on / 依赖: IsWeakFactorizationSystem, MorphismProperty, MorphismProperty.IsWeakFactorizationSystem.mk, cofibration_iff, infer_instance, mem_trivialFibrations_iff
-/
instance : MorphismProperty.IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun {A B X Y} i p hi hp => by
    rw [mem_trivialFibrations_iff] at hp
    rw [← cofibration_iff] at hi
    have := hp.1
    have := hp.2
    infer_instance)

end

section mk'

open MorphismProperty

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/--
lemma `mk'.cm3a_aux` / 引理 `mk'.cm3a_aux`

English:
lemma mk'.cm3a_aux
  statement: [CategoryWithFibrations C] [CategoryWithCofibrations C]
  proof: by
  have hw := factorizationData (trivialCofibrations C) (fibrations C) w
  have : (trivialFibrations C).IsStableUnderRetracts := by
    rw [← cofibrations_rlp]
    infer_instance
  have sq : CommSq h.r.left hw.i f (hw.p ≫ h.r.right) := ⟨by simp⟩
  have hf : fibrations C f := by rwa [← fibration_if

中文:
引理 mk'.cm3a_aux
  结论: [CategoryWithFibrations C] [CategoryWithCofibrations C]
  证明: by
  have hw := factorizationData (trivialCofibrations C) (fibrations C) w
  have : (trivialFibrations C).IsStableUnderRetracts := by
    rw [← cofibrations_rlp]
    infer_instance
  have sq : CommSq h.r.left hw.i f (hw.p ≫ h.r.right) := ⟨by simp⟩
  have hf : fibrations C f := by rwa [← fibration_if
-/
private lemma mk'.cm3a_aux [CategoryWithFibrations C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] {A B X Y : C}
    {f : A ⟶ B} {w : X ⟶ Y} [Fibration f] [WeakEquivalence w]
    (h : RetractArrow f w) : WeakEquivalence f := by
  have hw := factorizationData (trivialCofibrations C) (fibrations C) w
  have : (trivialFibrations C).IsStableUnderRetracts := by
    rw [← cofibrations_rlp]
    infer_instance
  have sq : CommSq h.r.left hw.i f (hw.p ≫ h.r.right) := ⟨by simp⟩
  have hf : fibrations C f := by rwa [← fibration_iff]
  have : HasLiftingProperty hw.i f := hasLiftingProperty_of_wfs _ _ hw.hi hf
  have : RetractArrow f hw.p :=
    { i := Arrow.homMk (h.i.left ≫ hw.i) h.i.right
      r := Arrow.homMk sq.lift h.r.right }
  have h' : trivialFibrations C hw.p :=
    ⟨hw.hp, (weakEquivalence_iff _).1 (weakEquivalence_of_precomp_of_fac hw.fac)⟩
  simpa only [weakEquivalence_iff] using (of_retract this h').2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Constructor for `ModelCategory C` which assumes a formulation of axioms
using weak factorization systems. -/
@[instance_reducible]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [CategoryWithFibrations C] [CategoryWithCofibrations C]
  body: ⟨fun {A B X Y f w h hw} => by
    rw [← weakEquivalence_iff] at hw
    have hf := factorizationData (trivialCofibrations C) (fibrations C) f
    have : Cofibration hf.i := by
      simpa only [cofibration_iff] using hf.hi.1
    have : WeakEquivalence hf.i := by
      simpa only [weakEquivalence_iff]

中文:
定义 mk'
  签名: [CategoryWithFibrations C] [CategoryWithCofibrations C]
  定义体: ⟨fun {A B X Y f w h hw} => by
    rw [← weakEquivalence_iff] at hw
    have hf := factorizationData (trivialCofibrations C) (fibrations C) f
    have : Cofibration hf.i := by
      simpa only [cofibration_iff] using hf.hi.1
    have : WeakEquivalence hf.i := by
      simpa only [weakEquivalence_iff]

Depends on / 依赖: Cofibration, Fibration, WeakEquivalence, cofibration_iff, factorizationData, fibration_iff, fibrations, h.i.left, h.i.right, hf.hi, hf.hp, hf.i, hf.p, pushout, pushout.desc, pushout.inr, trivialCofibrations, weakEquivalence_iff
-/
def mk' [CategoryWithFibrations C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] [HasFiniteLimits C] [HasFiniteColimits C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]
    [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)] :
    ModelCategory C where
  cm3a := ⟨fun {A B X Y f w h hw} => by
    rw [← weakEquivalence_iff] at hw
    have hf := factorizationData (trivialCofibrations C) (fibrations C) f
    have : Cofibration hf.i := by
      simpa only [cofibration_iff] using hf.hi.1
    have : WeakEquivalence hf.i := by
      simpa only [weakEquivalence_iff] using hf.hi.2
    let φ : pushout hf.i h.i.left ⟶ Y :=
      pushout.desc (hf.p ≫ h.i.right) w (by simp)
    have : Fibration hf.p := by simpa only [fibration_iff] using hf.hp
    have : WeakEquivalence (pushout.inr _ _ ≫ φ) := by simpa [φ]
    have := weakEquivalence_of_precomp (pushout.inr _ _) φ
    have hp : RetractArrow hf.p φ :=
      { i := Arrow.homMk (pushout.inl _ _) h.i.right
        r := Arrow.homMk (pushout.desc (𝟙 _) (h.r.left ≫ hf.i) (by simp)) h.r.right }
    have := mk'.cm3a_aux hp
    rw [← weakEquivalence_iff]; rw [← hf.fac]
    infer_instance⟩
  cm3b := by
    rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    infer_instance
  cm3c := by
    rw [← llp_eq_of_wfs (cofibrations C) (trivialFibrations C)]
    infer_instance
  cm4a i p _ _ _ := hasLiftingProperty_of_wfs i p (mem_trivialCofibrations i) (mem_fibrations p)
  cm4b i p _ _ _ := hasLiftingProperty_of_wfs i p (mem_cofibrations i) (mem_trivialFibrations p)

end mk'

end ModelCategory

end HomotopicalAlgebra
