/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import Mathlib.Order.TransfiniteIteration

/-!
# Grothendieck abelian categories have enough injectives

Let `C` be a Grothendieck abelian category. In this file, we formalize
the theorem by Grothendieck that `C` has enough injectives.

We recall that injective objects can be characterized in terms of
lifting properties (see the file `Preadditive.Injective.LiftingProperties`):
an object `I : C` is injective iff the morphism `I ⟶ 0` has the right lifting
property with respect to all monomorphisms.

The main technical lemma in this file is the lemma
`generatingMonomorphisms_rlp` which states that
if `G` is a generator of `C`, then a morphism `X ⟶ Y` has the right
lifting property with respect to the inclusions of subobjects of `G`
iff it has the right lifting property with respect to all
monomorphisms. Then, we can apply the small object argument
to the family of morphisms `generatingMonomorphisms G`
which consists of the inclusions of subobjects of `G`. When it is
applied to the morphism `X ⟶ 0`, the factorization given by the
small object is a factorization `X ⟶ I ⟶ 0` where `I` is
injective (because `I ⟶ 0` has the expected right lifting properties),
and `X ⟶ I` is a monomorphism because it is a transfinite composition
of monomorphisms (this uses the axiom AB5).

The proof of the technical lemma `generatingMonomorphisms_rlp` that
was formalized is not exactly the same as in the mathematical literature.
Assume that `p : X ⟶ Y` has the lifting property with respect to
monomorphisms in the family `generatingMonomorphisms G`.
We would like to show that `p` has the right lifting property with
respect to any monomorphism `i : A ⟶ B`. In various sources,
given a commutative square with `i` on the left and `p` on the right,
the ordered set of subobjects `A'` of `B` containing `A` equipped
with a lifting `A' ⟶ X` is introduced. The existence of a lifting `B ⟶ X`
is usually obtained by applying Zorn's lemma in this situation.
Here, we split the argument into two separate facts:
* any monomorphism `A ⟶ B` is a transfinite composition of pushouts of monomorphisms in
  `generatingMonomorphisms G` (see `generatingMonomorphisms.exists_transfiniteCompositionOfShape`);
* the class of morphisms that have the left lifting property with respect to `p` is stable under
  transfinite composition (see the file `SmallObject.TransfiniteCompositionLifting`).

## References

- [Alexander Grothendieck, *Sur quelques points d'algèbre homologique*][grothendieck-1957]

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace IsGrothendieckAbelian

/--
Definition of `generatingMonomorphisms` / `generatingMonomorphisms` 的定义

English:
definition generatingMonomorphisms
  signature: (G : C)
  body: MorphismProperty.ofHoms (fun (X : Subobject G) => X.arrow)

中文:
定义 generatingMonomorphisms
  签名: (G : C)
  定义体: MorphismProperty.ofHoms (fun (X : Subobject G) => X.arrow)

Depends on / 依赖: MorphismProperty, MorphismProperty.ofHoms, Subobject, X.arrow, ofHoms
-/
def generatingMonomorphisms (G : C) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun (X : Subobject G) => X.arrow)

instance (G : C) [Small.{w} (Subobject G)] :
    MorphismProperty.IsSmall.{w} (generatingMonomorphisms G) := by
  dsimp [generatingMonomorphisms]
  infer_instance

/--
lemma `generatingMonomorphisms_le_monomorphisms` / 引理 `generatingMonomorphisms_le_monomorphisms`

English:
lemma generatingMonomorphisms_le_monomorphisms
  given: (G : C)
  proof: by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)

中文:
引理 generatingMonomorphisms_le_monomorphisms
  条件: (G : C)
  证明: by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)
-/
lemma generatingMonomorphisms_le_monomorphisms (G : C) :
    generatingMonomorphisms G <= MorphismProperty.monomorphisms C := by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)

variable (G : C)

/--
lemma `isomorphisms_le_pushouts_generatingMonomorphisms` / 引理 `isomorphisms_le_pushouts_generatingMonomorphisms`

English:
lemma isomorphisms_le_pushouts_generatingMonomorphisms
  given: [HasZeroMorphisms C]
  proof: MorphismProperty.isomorphisms_le_pushouts _
    (fun _ => ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

中文:
引理 isomorphisms_le_pushouts_generatingMonomorphisms
  条件: [有ZeroMorphisms C]
  证明: MorphismProperty.isomorphisms_le_pushouts _
    (fun _ => ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

Depends on / 依赖: MorphismProperty, MorphismProperty.isomorphisms_le_pushouts, isomorphisms_le_pushouts
-/
lemma isomorphisms_le_pushouts_generatingMonomorphisms [HasZeroMorphisms C] :
    MorphismProperty.isomorphisms C <= (generatingMonomorphisms G).pushouts :=
  MorphismProperty.isomorphisms_le_pushouts _
    (fun _ => ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

variable [Abelian C]

namespace generatingMonomorphisms

variable {G} (hG : IsSeparator G)

include hG

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_pushouts` / 引理 `exists_pushouts`

English:
lemma exists_pushouts
  proof: by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [ObjectProperty.singleton_iff, Function.Surjective, Functor.flip_obj_map, forall_eq',
    not_forall, not_exists] at hp
  -- `f : G ⟶ Y` is a monomorphism the image of which is not contained in `X`
  obtain ⟨f, hf⟩ := hp
  -- we use the subobject `X'` of `Y` that is generated by the images of `p : X ⟶ Y`
  -- and `f : G ⟶ Y`: this is the pushout of `p` and `f` along their pullback
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _,
    pushout.desc p f pullback.condition,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa using ha =≫ pushout.desc p f pullback.condition)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) _ (by simp) (by simp)

中文:
引理 存在_pushouts
  证明: by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [ObjectProperty.singleton_iff, Function.Surjective, Functor.flip_obj_map, forall_eq',
    not_forall, not_exists] at hp
  -- `f : G ⟶ Y` is a monomorphism the image of which is not contained in `X`
  obtain ⟨f, hf⟩ := hp
  -- we use the subobject `X'` of `Y` that is generated by the images of `p : X ⟶ Y`
  -- and `f : G ⟶ Y`: this is the pushout of `p` and `f` along their pullback
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _,
    pushout.desc p f pullback.condition,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa using ha =≫ pushout.desc p f pullback.condition)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) _ (by simp) (by simp)

Depends on / 依赖: Function, Function.Surjective, Functor, Functor.flip_obj_map, ObjectProperty, ObjectProperty.singleton_iff, Surjective, flip_obj_map, forall_eq, hG.isDetector.isIso_iff_of_mono, isDetector, isIso_iff_of_mono, not_exists, not_forall, singleton_iff
-/
lemma exists_pushouts
    {X Y : C} (p : X ⟶ Y) [Mono p] (hp : ¬ IsIso p) :
    exists (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : (generatingMonomorphisms G).pushouts i)
      (_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [ObjectProperty.singleton_iff, Function.Surjective, Functor.flip_obj_map, forall_eq',
    not_forall, not_exists] at hp
  -- `f : G ⟶ Y` is a monomorphism the image of which is not contained in `X`
  obtain ⟨f, hf⟩ := hp
  -- we use the subobject `X'` of `Y` that is generated by the images of `p : X ⟶ Y`
  -- and `f : G ⟶ Y`: this is the pushout of `p` and `f` along their pullback
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _,
    pushout.desc p f pullback.condition,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa using ha =≫ pushout.desc p f pullback.condition)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) _ (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `exists_larger_subobject` / 引理 `exists_larger_subobject`

English:
lemma exists_larger_subobject
  given: {X : C} (A : Subobject X) (hA : A != ⊤)
  proof: by
  induction A using Subobject.ind with | _ f
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_pushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

中文:
引理 存在_larger_subobject
  条件: {X : C} (A : Subobject X) (hA : A != ⊤)
  证明: by
  induction A using Subobject.ind with | _ f
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_pushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

Depends on / 依赖: Arrow.isoMk, F.mono_of_mono_map, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, Subobject, Subobject.ind, Subobject.isIso_iff_mk_eq_top, Subobject.mk, Subobject.mk_lt_mk_of_comm, Subobject.ofLE_arrow, Subobject.underlyingIso, Subobject.underlyingIso_hom_comp_eq_mk, adj.homEquiv_counit, arrow_mk_iso_iff, cancel_mono, exists_pushouts, homEquiv, homEquiv_counit, isIso_iff_mk_eq_top, mk_lt_mk_of_comm
-/
lemma exists_larger_subobject {X : C} (A : Subobject X) (hA : A != ⊤) :
    exists (A' : Subobject X) (h : A < A'),
      (generatingMonomorphisms G).pushouts (Subobject.ofLE A A' h.le) := by
  induction A using Subobject.ind with | _ f
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_pushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

variable {X : C}

open scoped Classical in
/--
Definition of `largerSubobject` / `largerSubobject` 的定义

English:
definition largerSubobject
  signature: (A : Subobject X)
  body: if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

中文:
定义 largerSubobject
  签名: (A : Subobject X)
  定义体: if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

Depends on / 依赖: exists_larger_subobject
-/
noncomputable def largerSubobject (A : Subobject X) : Subobject X :=
  if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

variable (X) in
@[simp]
/--
lemma `largerSubobject_top` / 引理 `largerSubobject_top`

English:
lemma largerSubobject_top
  statement: largerSubobject hG (⊤ : Subobject X) = ⊤
  proof: dif_pos rfl

中文:
引理 largerSubobject_top
  结论: largerSubobject hG (⊤ : Subobject X) = ⊤
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
lemma largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤ := dif_pos rfl

/--
lemma `lt_largerSubobject` / 引理 `lt_largerSubobject`

English:
lemma lt_largerSubobject
  given: (A : Subobject X) (hA : A != ⊤)
  proof: by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose

中文:
引理 lt_largerSubobject
  条件: (A : Subobject X) (hA : A != ⊤)
  证明: by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, dif_neg, exists_larger_subobject, largerSubobject
-/
lemma lt_largerSubobject (A : Subobject X) (hA : A != ⊤) :
    A < largerSubobject hG A := by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose

/--
lemma `le_largerSubobject` / 引理 `le_largerSubobject`

English:
lemma le_largerSubobject
  given: (A : Subobject X)
  proof: by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

中文:
引理 le_largerSubobject
  条件: (A : Subobject X)
  证明: by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

Depends on / 依赖: largerSubobject_top, le_refl, lt_largerSubobject
-/
lemma le_largerSubobject (A : Subobject X) :
    A <= largerSubobject hG A := by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `pushouts_ofLE_le_largerSubobject` / 引理 `pushouts_ofLE_le_largerSubobject`

English:
lemma pushouts_ofLE_le_largerSubobject
  given: (A : Subobject X)
  proof: by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_pushouts_generatingMonomorphisms G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

中文:
引理 pushouts_ofLE_le_largerSubobject
  条件: (A : Subobject X)
  证明: by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_pushouts_generatingMonomorphisms G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

Depends on / 依赖: Arrow.isoMk, Iso.refl, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, MorphismProperty.isomorphisms.infer_property, Subobject, Subobject.arrow, Subobject.isIso_arrow_iff_eq_top, arrow_mk_iso_iff, choose_spec, choose_spec.choose_spec, exists_larger_subobject, infer_property, isIso_arrow_iff_eq_top, isomorphisms, isomorphisms_le_pushouts_generatingMonomorphisms, largerSubobject
-/
lemma pushouts_ofLE_le_largerSubobject (A : Subobject X) :
      (generatingMonomorphisms G).pushouts
        (Subobject.ofLE _ _ (le_largerSubobject hG A)) := by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_pushouts_generatingMonomorphisms G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

variable [IsGrothendieckAbelian.{w} C]

/--
lemma `top_mem_range` / 引理 `top_mem_range`

English:
lemma top_mem_range
  statement: (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  proof: top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h => by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

中文:
引理 top_mem_range
  结论: (A₀ : Subobject X) {J : 类型 w} [线性序 J] [有底序 J] [Succ序 J]
  证明: top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h => by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

Depends on / 依赖: hJ.of_injective, hasCardinalLT_iff_cardinal_mk_lt, largerSubobject, lt_largerSubobject, of_injective, top_mem_range_transfiniteIterate
-/
lemma top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] (hJ : HasCardinalLT (Subobject X) (Cardinal.mk J)) :
    exists (j : J), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ :=
  top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h => by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)

/--
lemma `exists_ordinal` / 引理 `exists_ordinal`

English:
lemma exists_ordinal
  given: (A₀ : Subobject X)
  proof: by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

中文:
引理 存在_ordinal
  条件: (A₀ : Subobject X)
  证明: by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

Depends on / 依赖: Cardinal, Cardinal.mk, Nonempty, Order.lt_succ, Order.succ, Shrink, Subobject, ToType, WellFoundedLT, WellFoundedLT.toOrderBot, lt_of_lt_of_le, lt_succ, ord.ToType, toOrderBot, top_mem_range
-/
lemma exists_ordinal (A₀ : Subobject X) :
    exists (o : Ordinal.{w}) (j : o.ToType), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

section

variable (A₀ : Subobject X) (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Let `C` be a Grothendieck abelian category with a generator (`hG`),
`X : C`, `A₀ : Subobject X`. Let `J` be a well-ordered type. This is
the functor `J ⥤ MonoOver X` which corresponds to the evaluation
at `A₀` of the transfinite iteration of the map
`largerSubobject hG : Subobject X → Subobject X`. -/
@[simps]
/--
Definition of `functorToMonoOver` / `functorToMonoOver` 的定义

English:
definition functorToMonoOver
  signature: : J ⥤ MonoOver X where
  body: MonoOver.mk (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

中文:
定义 functorToMonoOver
  签名: : J ⥤ MonoOver X where
  定义体: MonoOver.mk (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

Depends on / 依赖: MonoOver, MonoOver.mk, largerSubobject, transfiniteIterate
-/
noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

/--
Definition of `functor` / `functor` 的定义

English:
abbreviation functor
  signature: : J ⥤ C
  body: functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

中文:
缩写 functor
  签名: : J ⥤ C
  定义体: functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

Depends on / 依赖: MonoOver, MonoOver.forget, Over.forget, forget, functorToMonoOver
-/
noncomputable abbrev functor : J ⥤ C :=
  functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor hG A₀ J).IsWellOrderContinuous
  body: ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hG A₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

中文:
实例 :
  签名: (functor hG A₀ J).是WellOrderContinuous
  定义体: ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hG A₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

Depends on / 依赖: IsGrothendieckAbelian, IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup, MonoOver, MonoOver.forget, Set.principalSegIio, Subobject, Subobject.mk_arrow, c.pt.hom, cocone, forget, functor, functorToMonoOver, hm.nonempty_Iio.to_subtype, infer_instance, isColimitMapCoconeOfSubobjectMkEqISup, largerSubobject, mk_arrow, monotone, monotone.functor, nonempty_Iio
-/
instance : (functor hG A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hG A₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {J} in
/--
Definition of `transfiniteCompositionOfShapeMapFromBot` / `transfiniteCompositionOfShapeMapFromBot` 的定义

English:
definition transfiniteCompositionOfShapeMapFromBot
  signature: (j : J)
  body: (Set.initialSegIic j).monotone.functor ⋙ functor hG A₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor hG A₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    dsimp [MonoOver.forget]
    convert!
      pushouts_ofLE_le_largerSubobject hG (transfiniteIterate (largerSubobject hG) k.1 A₀) using 2
    all_goals
      rw [Set.Iic.succ_eq_of_not_isMax hk]; rw [transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

中文:
定义 transfiniteCompositionOfShapeMapFromBot
  签名: (j : J)
  定义体: (Set.initialSegIic j).monotone.functor ⋙ functor hG A₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor hG A₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    dsimp [MonoOver.forget]
    convert!
      pushouts_ofLE_le_largerSubobject hG (transfiniteIterate (largerSubobject hG) k.1 A₀) using 2
    all_goals
      rw [Set.Iic.succ_eq_of_not_isMax hk]; rw [transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

Depends on / 依赖: Set.initialSegIic, functor, initialSegIic, monotone, monotone.functor
-/
noncomputable def transfiniteCompositionOfShapeMapFromBot (j : J) :
    (generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape (Set.Iic j)
    ((functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ functor hG A₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor hG A₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    dsimp [MonoOver.forget]
    convert!
      pushouts_ofLE_le_largerSubobject hG (transfiniteIterate (largerSubobject hG) k.1 A₀) using 2
    all_goals
      rw [Set.Iic.succ_eq_of_not_isMax hk]; rw [transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

end

variable {A : C} {f : A ⟶ X} [Mono f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `transfiniteCompositionOfShapeOfEqTop` / `transfiniteCompositionOfShapeOfEqTop` 的定义

English:
definition transfiniteCompositionOfShapeOfEqTop
  body: by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).2 hj
  apply (transfiniteCompositionOfShapeMapFromBot hG (Subobject.mk f) j).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc]; rw [Subobject.underlyingIso_hom_comp_eq_mk]; rw [Subobject.ofLE_arrow]; rw [Subobject.ofLE_arrow]

中文:
定义 transfiniteCompositionOfShapeOfEqTop
  定义体: by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).2 hj
  apply (transfiniteCompositionOfShapeMapFromBot hG (Subobject.mk f) j).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc]; rw [Subobject.underlyingIso_hom_comp_eq_mk]; rw [Subobject.ofLE_arrow]; rw [Subobject.ofLE_arrow]

Depends on / 依赖: Arrow.isoMk, MonoOver, MonoOver.forget, Subobject, Subobject.isIso_arrow_iff_eq_top, Subobject.isoOfEq, Subobject.mk, Subobject.ofLE_arrow, Subobject.underlyingIso, Subobject.underlyingIso_hom_comp_eq_mk, forget, isIso_arrow_iff_eq_top, isoOfEq, largerSubobject, ofArrowIso, ofLE_arrow, t.arrow, transfiniteCompositionOfShapeMapFromBot, transfiniteIterate, transfiniteIterate_bot
-/
noncomputable def transfiniteCompositionOfShapeOfEqTop
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] {j : J}
    (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤) :
    (generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape (Set.Iic j) f := by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).2 hj
  apply (transfiniteCompositionOfShapeMapFromBot hG (Subobject.mk f) j).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc]; rw [Subobject.underlyingIso_hom_comp_eq_mk]; rw [Subobject.ofLE_arrow]; rw [Subobject.ofLE_arrow]

variable (f)

/--
lemma `exists_transfiniteCompositionOfShape` / 引理 `exists_transfiniteCompositionOfShape`

English:
lemma exists_transfiniteCompositionOfShape
  proof: by
  obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk f)
  have : Nonempty o.ToType := ⟨j⟩
  have : OrderBot o.ToType := WellFoundedLT.toOrderBot _
  exact ⟨_, _, _, _, _, ⟨transfiniteCompositionOfShapeOfEqTop hG hj⟩⟩

中文:
引理 存在_transfiniteCompositionOfShape
  证明: by
  obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk f)
  have : Nonempty o.ToType := ⟨j⟩
  have : OrderBot o.ToType := WellFoundedLT.toOrderBot _
  exact ⟨_, _, _, _, _, ⟨transfiniteCompositionOfShapeOfEqTop hG hj⟩⟩

Depends on / 依赖: Nonempty, OrderBot, Subobject, Subobject.mk, ToType, WellFoundedLT, WellFoundedLT.toOrderBot, exists_ordinal, o.ToType, toOrderBot, transfiniteCompositionOfShapeOfEqTop
-/
lemma exists_transfiniteCompositionOfShape :
    exists (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J)
        (_ : WellFoundedLT J),
    Nonempty ((generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape J f) := by
  obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk f)
  have : Nonempty o.ToType := ⟨j⟩
  have : OrderBot o.ToType := WellFoundedLT.toOrderBot _
  exact ⟨_, _, _, _, _, ⟨transfiniteCompositionOfShapeOfEqTop hG hj⟩⟩

end generatingMonomorphisms

open MorphismProperty

variable {G}

/--
lemma `generatingMonomorphisms_rlp` / 引理 `generatingMonomorphisms_rlp`

English:
lemma generatingMonomorphisms_rlp
  given: [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G)
  proof: by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨J, _, _, _, _, ⟨h⟩⟩ :=
      generatingMonomorphisms.exists_transfiniteCompositionOfShape hG i
    exact transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ (by simpa)
  · exact antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

中文:
引理 generatingMonomorphisms_rlp
  条件: [是GrothendieckAbelian.{w} C] (hG : IsSeparator G)
  证明: by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨J, _, _, _, _, ⟨h⟩⟩ :=
      generatingMonomorphisms.exists_transfiniteCompositionOfShape hG i
    exact transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ (by simpa)
  · exact antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

Depends on / 依赖: antitone_rlp, exists_transfiniteCompositionOfShape, generatingMonomorphisms, generatingMonomorphisms.exists_transfiniteCompositionOfShape, generatingMonomorphisms_le_monomorphisms, h.mem, le_antisymm, transfiniteCompositionsOfShape_le_llp_rlp
-/
lemma generatingMonomorphisms_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    (generatingMonomorphisms G).rlp = (monomorphisms C).rlp := by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨J, _, _, _, _, ⟨h⟩⟩ :=
      generatingMonomorphisms.exists_transfiniteCompositionOfShape hG i
    exact transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ (by simpa)
  · exact antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

open MorphismProperty

variable [IsGrothendieckAbelian.{w} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSmallObjectArgument.{w} (generatingMonomorphisms G)
  body: by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)
  have : Fact κ.IsRegular := ⟨hκ'⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ'.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ <= monomorphisms C) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generatingMonomorphisms_le_monomorphisms G }
        have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ)
        obtain ⟨S⟩ := hi
        exact Subobject.hasCardinalLT_of_mono hκ S.arrow }⟩

中文:
实例 :
  签名: 有SmallObjectArgument.{w} (generatingMonomorphisms G)
  定义体: by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)
  have : Fact κ.IsRegular := ⟨hκ'⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ'.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ <= monomorphisms C) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generatingMonomorphisms_le_monomorphisms G }
        have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ)
        obtain ⟨S⟩ := hi
        exact Subobject.hasCardinalLT_of_mono hκ S.arrow }⟩

Depends on / 依赖: HasCardinalLT, HasCardinalLT.exists_regular_cardinal, IsRegular, Nonempty, Subobject, ToType, TransfiniteCompositionOfShape, WellFoundedLT, WellFoundedLT.toOrderBot, attachCells, exists_regular_cardinal, hf.attachCells, hf.toTransfiniteCompositionOfShape, map_mem, monomorphisms, ne_zero, ord.ToType, preservesColimit, toOrderBot, toTransfiniteCompositionOfShape
-/
instance : HasSmallObjectArgument.{w} (generatingMonomorphisms G) := by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)
  have : Fact κ.IsRegular := ⟨hκ'⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ'.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ <= monomorphisms C) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generatingMonomorphisms_le_monomorphisms G }
        have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ)
        obtain ⟨S⟩ := hi
        exact Subobject.hasCardinalLT_of_mono hκ S.arrow }⟩

/--
lemma `llp_rlp_monomorphisms` / 引理 `llp_rlp_monomorphisms`

English:
lemma llp_rlp_monomorphisms
  given: (hG : IsSeparator G)
  proof: by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← generatingMonomorphisms_rlp hG]; rw [llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monomorphisms C)).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    apply generatingMonomorphisms_le_monomorphisms
  · simp

中文:
引理 llp_rlp_monomorphisms
  条件: (hG : IsSeparator G)
  证明: by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← generatingMonomorphisms_rlp hG]; rw [llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monomorphisms C)).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    apply generatingMonomorphisms_le_monomorphisms
  · simp

Depends on / 依赖: coproducts, coproducts_monotone, generatingMonomorphisms_le_monomorphisms, generatingMonomorphisms_rlp, le_antisymm, le_llp_rlp, llp_rlp_of_hasSmallObjectArgument, monomorphisms, pushouts, pushouts_monotone, retracts, retracts_monotone, transfiniteCompositions, transfiniteCompositions_monotone
-/
lemma llp_rlp_monomorphisms (hG : IsSeparator G) :
    (monomorphisms C).rlp.llp = monomorphisms C := by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← generatingMonomorphisms_rlp hG]; rw [llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monomorphisms C)).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    apply generatingMonomorphisms_le_monomorphisms
  · simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp
  body: by
  have hG := isSeparator_separator C
  rw [← generatingMonomorphisms_rlp hG]; rw [← llp_rlp_monomorphisms hG]; rw [← generatingMonomorphisms_rlp hG]
  infer_instance

中文:
实例 :
  签名: 有FunctorialFactorization (monomorphisms C) (monomorphisms C).rlp
  定义体: by
  have hG := isSeparator_separator C
  rw [← generatingMonomorphisms_rlp hG]; rw [← llp_rlp_monomorphisms hG]; rw [← generatingMonomorphisms_rlp hG]
  infer_instance

Depends on / 依赖: generatingMonomorphisms_rlp, infer_instance, isSeparator_separator, llp_rlp_monomorphisms
-/
instance : HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp := by
  have hG := isSeparator_separator C
  rw [← generatingMonomorphisms_rlp hG]; rw [← llp_rlp_monomorphisms hG]; rw [← generatingMonomorphisms_rlp hG]
  infer_instance

/--
Definition of `monoMapFactorizationDataRlp` / `monoMapFactorizationDataRlp` 的定义

English:
abbreviation monoMapFactorizationDataRlp
  signature: {X Y : C} (f : X ⟶ Y)
  body: (functorialFactorizationData _ _).factorizationData f

中文:
缩写 monoMapFactorizationDataRlp
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: (functorialFactorizationData _ _).factorizationData f

Depends on / 依赖: factorizationData, functorialFactorizationData
-/
noncomputable abbrev monoMapFactorizationDataRlp {X Y : C} (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms C) (monomorphisms C).rlp f :=
  (functorialFactorizationData _ _).factorizationData f

instance {X Y : C} (f : X ⟶ Y) :
    Mono (monoMapFactorizationDataRlp f).i :=
  (monoMapFactorizationDataRlp f).hi

instance {X : C} : Injective (monoMapFactorizationDataRlp (0 : X ⟶ 0)).Z := by
  let fac := (monoMapFactorizationDataRlp (0 : X ⟶ 0))
  simpa only [injective_iff_rlp_monomorphisms_zero,
    (isZero_zero C).eq_of_tgt fac.p 0] using fac.hp

/-- A Grothendieck abelian category has enough injectives. -/
@[stacks 079H]
/--
Instance `enoughInjectives` / 实例 `enoughInjectives`

English:
instance enoughInjectives
  signature: : EnoughInjectives C where
  body: ⟨{ J := _, f := (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i }⟩

中文:
实例 enoughInjectives
  签名: : 有足够单射 C where
  定义体: ⟨{ J := _, f := (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i }⟩

Depends on / 依赖: monoMapFactorizationDataRlp
-/
instance enoughInjectives : EnoughInjectives C where
  presentation X := ⟨{ J := _, f := (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i }⟩

end IsGrothendieckAbelian

end CategoryTheory
