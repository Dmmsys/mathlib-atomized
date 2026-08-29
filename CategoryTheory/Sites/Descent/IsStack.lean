/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Stacks: effectiveness of descent

Let `C` be a category with a Grothendieck topology `J` and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
In this file, we define the typeclass `F.IsStack J` saying that `F` is a stack for `J`.
(See the terminological note in the file `Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`:
we do not require that the categories `F.obj (.mk (op S))` are groupoids.)

The typeclass `IsStack` extends `IsPrestack`. The effectiveness of descent that
is required for stacks is expressed by saying that the functors `toDescentData`
attached to covering sieves are essentially surjective. Together with the
`IsPrestack` assumption, we get that these functors are actually equivalences of
categories (see `isEquivalence_toDescentData`). Conversely, we provide a
constructor `IsStack.of_isStackFor` which assumes that these functors are
equivalences of categories.

## References
* [Jean Giraud, *Cohomologie non abélienne*][giraud1971]
* [Gérard Laumon and Laurent Moret-Bailly, *Champs algébriques*][laumon-morel-bailly-2000]

-/

public section

universe t t' v' v u' u

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
has effective descent for a Grothendieck topology, i.e. is a stack.
(See the terminological note in the introduction of the file
`Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`.) -/
@[stacks 026F]
/--
Definition of `IsStack` / `IsStack` 的定义

English:
class IsStack
  parameters: (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C)
  extends: F.IsPrestack J
  axioms and operations (1):
    - essSurj_of_sieve((F) {S : C} (R : Sieve S) (hR : R in J S)) : (F.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

中文:
类 是Stack
  参数: (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : Grothendieck拓扑 C)
  继承: F.是Prestack J
  公理与运算 (1 个):
    - essSurj_of_sieve((F) {S : C} (R : 筛 S) (hR : R in J S)) : (F.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).本质满射
-/
class IsStack (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C) : Prop
    extends F.IsPrestack J where
  essSurj_of_sieve (F) {S : C} (R : Sieve S) (hR : R in J S) :
    (F.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J : GrothendieckTopology C}

/--
lemma `isStackFor'` / 引理 `isStackFor'`

English:
lemma isStackFor'
  given: [F.IsStack J] {S : C} (R : Sieve S) (hR : R in J S)
  proof: by
  rw [isStackFor_iff]
  have hF := (F.isPrestackFor' _ hR).fullyFaithful
  have := hF.full
  have := hF.faithful
  have := IsStack.essSurj_of_sieve F _ hR
  exact { }

中文:
引理 isStackFor'
  条件: [F.是Stack J] {S : C} (R : 筛 S) (hR : R in J S)
  证明: by
  rw [isStackFor_iff]
  have hF := (F.isPrestackFor' _ hR).fullyFaithful
  have := hF.full
  have := hF.faithful
  have := IsStack.essSurj_of_sieve F _ hR
  exact { }

Depends on / 依赖: F.isPrestackFor, IsStack, IsStack.essSurj_of_sieve, essSurj_of_sieve, faithful, fullyFaithful, hF.faithful, hF.full, isPrestackFor, isStackFor_iff
-/
lemma isStackFor' [F.IsStack J] {S : C} (R : Sieve S) (hR : R in J S) :
    F.IsStackFor R.arrows := by
  rw [isStackFor_iff]
  have hF := (F.isPrestackFor' _ hR).fullyFaithful
  have := hF.full
  have := hF.faithful
  have := IsStack.essSurj_of_sieve F _ hR
  exact { }

/--
lemma `isStackFor` / 引理 `isStackFor`

English:
lemma isStackFor
  given: [F.IsStack J] {S : C} (R : Presieve S) (hR : Sieve.generate R in J S)
  proof: by
  simpa using F.isStackFor' _ hR

中文:
引理 isStackFor
  条件: [F.是Stack J] {S : C} (R : Presieve S) (hR : 筛.generate R in J S)
  证明: by
  simpa using F.isStackFor' _ hR

Depends on / 依赖: F.isStackFor, isStackFor
-/
lemma isStackFor [F.IsStack J] {S : C} (R : Presieve S) (hR : Sieve.generate R in J S) :
    F.IsStackFor R := by
  simpa using F.isStackFor' _ hR

/--
lemma `isEquivalence_toDescentData` / 引理 `isEquivalence_toDescentData`

English:
lemma isEquivalence_toDescentData
  statement: [F.IsStack J]
  proof: by
  rw [← isStackFor_ofArrows_iff]; rw [← IsStackFor_generate_iff]
  exact F.isStackFor _ (by simpa)

中文:
引理 isEquivalence_toDescentData
  结论: [F.是Stack J]
  证明: by
  rw [← isStackFor_ofArrows_iff]; rw [← IsStackFor_generate_iff]
  exact F.isStackFor _ (by simpa)

Depends on / 依赖: F.isStackFor, IsStackFor_generate_iff, isStackFor, isStackFor_ofArrows_iff
-/
lemma isEquivalence_toDescentData [F.IsStack J]
    {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S) (hf : Sieve.ofArrows _ f in J S) :
    (F.toDescentData f).IsEquivalence := by
  rw [← isStackFor_ofArrows_iff]; rw [← IsStackFor_generate_iff]
  exact F.isStackFor _ (by simpa)

variable {F} in
/--
lemma `IsStack.of_isStackFor` / 引理 `IsStack.of_isStackFor`

English:
lemma IsStack.of_isStackFor
  proof: .of_isPrestackFor (fun _ _ hR => (hF _ _ hR).isPrestackFor)
  essSurj_of_sieve R hR := by
    have := (isStackFor_iff _ _).1 (hF _ _ hR)
    infer_instance

中文:
引理 是Stack.of_isStackFor
  证明: .of_isPrestackFor (fun _ _ hR => (hF _ _ hR).isPrestackFor)
  essSurj_of_sieve R hR := by
    have := (isStackFor_iff _ _).1 (hF _ _ hR)
    infer_instance

Depends on / 依赖: isPrestackFor, of_isPrestackFor
-/
lemma IsStack.of_isStackFor
    (hF : forall (S : C) (R : Sieve S) (_ : R in J S), F.IsStackFor R.arrows) :
    F.IsStack J where
  toIsPrestack := .of_isPrestackFor (fun _ _ hR => (hF _ _ hR).isPrestackFor)
  essSurj_of_sieve R hR := by
    have := (isStackFor_iff _ _).1 (hF _ _ hR)
    infer_instance

end Pseudofunctor

end CategoryTheory
