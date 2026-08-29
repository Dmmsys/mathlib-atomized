/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# Classes of morphisms induced on quotient categories

Let `W : MorphismProperty C` and `homRel : HomRel C`. We assume that
`homRel` is stable under pre- and postcomposition. We introduce a property
`W.HasQuotient homRel` expressing that `W` induces a property of
morphisms on the quotient category, i.e. `W f ↔ W g` when `homRel f g` holds.
We denote `W.quotient homRel : MorphismProperty (Quotient homRel)` the
induced property of morphisms: a morphism in `C` satisfies `W` iff
`(Quotient.functor homRel).map f` does.

-/

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category* C]

/--
Definition of `HasQuotient` / `HasQuotient` 的定义

English:
class HasQuotient
  parameters: (W : MorphismProperty C) (homRel : HomRel C)
  axioms and operations (1):
    - iff((W)) : forall ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g -> (W f ↔ W g)

中文:
类 有商
  参数: (W : MorphismProperty C) (homRel : HomRel C)
  公理与运算 (1 个):
    - iff((W)) : 对任意 ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g -> (W f ↔ W g)
-/
class HasQuotient (W : MorphismProperty C) (homRel : HomRel C)
    [HomRel.IsStableUnderPrecomp homRel]
    [HomRel.IsStableUnderPostcomp homRel] : Prop where
  iff (W) : forall ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g -> (W f ↔ W g)

variable (W : MorphismProperty C) {homRel : HomRel C}
  [HomRel.IsStableUnderPrecomp homRel]
  [HomRel.IsStableUnderPostcomp homRel]

/--
lemma `HasQuotient.iff_of_eqvGen` / 引理 `HasQuotient.iff_of_eqvGen`

English:
lemma HasQuotient.iff_of_eqvGen
  statement: [W.HasQuotient homRel] {X Y : C} {f g : X ⟶ Y}
  proof: by
  induction h with
  | rel _ _ h => exact iff W h
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

中文:
引理 有商.iff_of_eqvGen
  结论: [W.有商 homRel] {X Y : C} {f g : X ⟶ Y}
  证明: by
  induction h with
  | rel _ _ h => exact iff W h
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

Depends on / 依赖: h.symm
-/
lemma HasQuotient.iff_of_eqvGen [W.HasQuotient homRel] {X Y : C} {f g : X ⟶ Y}
    (h : Relation.EqvGen (@homRel _ _) f g) : W f ↔ W g := by
  induction h with
  | rel _ _ h => exact iff W h
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

variable (homRel)

/-- The property of morphisms that is induced by `W : MorphismProperty C`
on the quotient category by `homRel : HomRel C` when `W.HasQuotient homRel` holds. -/
@[nolint unusedArguments]
/--
Definition of `quotient` / `quotient` 的定义

English:
definition quotient
  signature: [W.HasQuotient homRel]
  body: fun ⟨X⟩ ⟨Y⟩ f => exists (f' : X ⟶ Y) (_ : W f'), f = (Quotient.functor _).map f'

中文:
定义 quotient
  签名: [W.有商 homRel]
  定义体: fun ⟨X⟩ ⟨Y⟩ f => exists (f' : X ⟶ Y) (_ : W f'), f = (Quotient.functor _).map f'

Depends on / 依赖: Quotient, Quotient.functor, functor
-/
def quotient [W.HasQuotient homRel] : MorphismProperty (Quotient homRel) :=
  fun ⟨X⟩ ⟨Y⟩ f => exists (f' : X ⟶ Y) (_ : W f'), f = (Quotient.functor _).map f'

variable [W.HasQuotient homRel]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quotient_iff` / 引理 `quotient_iff`

English:
lemma quotient_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  refine ⟨fun ⟨f', hf', h⟩ => ?_, fun hf => ⟨f, hf, rfl⟩⟩
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self homRel] at h
  rwa [HasQuotient.iff_of_eqvGen W h]

中文:
引理 quotient_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  refine ⟨fun ⟨f', hf', h⟩ => ?_, fun hf => ⟨f, hf, rfl⟩⟩
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self homRel] at h
  rwa [HasQuotient.iff_of_eqvGen W h]

Depends on / 依赖: Functor, Functor.homRel_iff, HasQuotient, HasQuotient.iff_of_eqvGen, HomRel, HomRel.compClosure_eq_self, Quotient, Quotient.functor_homRel_eq_compClosure_eqvGen, compClosure_eq_self, functor_homRel_eq_compClosure_eqvGen, homRel, homRel_iff, iff_of_eqvGen
-/
lemma quotient_iff {X Y : C} (f : X ⟶ Y) :
    W.quotient homRel ((Quotient.functor homRel).map f) ↔ W f := by
  refine ⟨fun ⟨f', hf', h⟩ => ?_, fun hf => ⟨f, hf, rfl⟩⟩
  rw [← Functor.homRel_iff]; rw [Quotient.functor_homRel_eq_compClosure_eqvGen]; rw [HomRel.compClosure_eq_self homRel] at h
  rwa [HasQuotient.iff_of_eqvGen W h]

/--
lemma `eq_inverseImage_quotientFunctor` / 引理 `eq_inverseImage_quotientFunctor`

English:
lemma eq_inverseImage_quotientFunctor
  proof: by
  ext
  exact (quotient_iff _ _ _).symm

中文:
引理 eq_inverseImage_quotientFunctor
  证明: by
  ext
  exact (quotient_iff _ _ _).symm

Depends on / 依赖: quotient_iff
-/
lemma eq_inverseImage_quotientFunctor :
    W = (W.quotient homRel).inverseImage (Quotient.functor _) := by
  ext
  exact (quotient_iff _ _ _).symm

end MorphismProperty

end CategoryTheory
