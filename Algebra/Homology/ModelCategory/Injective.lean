/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ModelCategory.Lifting
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The model category structure on bounded below complexes

Let `C` be an abelian category with enough injectives. In this file,
we define a model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in `C`.
The cofibrations are monomorphisms, the weak equivalences are
quasi-isomorphisms and the fibrations are those morphisms
that are degreewise epimorphisms with an injective kernel.
The `ModelCategory` instance is scoped in the namespace
`CochainComplex.Plus.modelCategoryQuillen`.

## References
* [Daniel G. Quillen, Homotopical algebra, §I.1, Example B][Quillen1967]

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits

namespace CochainComplex.Plus.modelCategoryQuillen

variable {C : Type*} [Category C] [Abelian C]

/-- The weak equivalences in the category `CochainComplex.Plus C` of bounded
below cochain complexes are quasi-isomorphisms. -/
scoped instance : CategoryWithWeakEquivalences (CochainComplex.Plus C) where
  weakEquivalences := quasiIso C

/-- The cofibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are monomorphisms. -/
scoped instance : CategoryWithCofibrations (CochainComplex.Plus C) where
  cofibrations := .monomorphisms _

/-- The fibrations in the category `CochainComplex.Plus C` of bounded
below cochain complexes are the morphisms that are degreewise epi with
an injective kernel. -/
scoped instance : CategoryWithFibrations (CochainComplex.Plus C) where
  fibrations := degreewiseEpiWithInjectiveKernel.inverseImage (ι C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (weakEquivalences (Plus C)).HasTwoOutOfThreeProperty
  body: inferInstanceAs (quasiIso C).HasTwoOutOfThreeProperty

中文:
实例 :
  签名: (weakEquivalences (Plus C)).有TwoOutOfThreeProperty
  定义体: inferInstanceAs (quasiIso C).HasTwoOutOfThreeProperty

Depends on / 依赖: HasTwoOutOfThreeProperty, quasiIso
-/
instance : (weakEquivalences (Plus C)).HasTwoOutOfThreeProperty :=
  inferInstanceAs (quasiIso C).HasTwoOutOfThreeProperty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (weakEquivalences (Plus C)).IsStableUnderRetracts
  body: inferInstanceAs (quasiIso C).IsStableUnderRetracts

中文:
实例 :
  签名: (weakEquivalences (Plus C)).是StableUnderRetracts
  定义体: inferInstanceAs (quasiIso C).IsStableUnderRetracts

Depends on / 依赖: IsStableUnderRetracts, quasiIso
-/
instance : (weakEquivalences (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (quasiIso C).IsStableUnderRetracts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cofibrations (Plus C)).IsStableUnderRetracts
  body: inferInstanceAs (MorphismProperty.monomorphisms _).IsStableUnderRetracts

中文:
实例 :
  签名: (cofibrations (Plus C)).是StableUnderRetracts
  定义体: inferInstanceAs (MorphismProperty.monomorphisms _).IsStableUnderRetracts

Depends on / 依赖: IsStableUnderRetracts, MorphismProperty, MorphismProperty.monomorphisms, monomorphisms
-/
instance : (cofibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (MorphismProperty.monomorphisms _).IsStableUnderRetracts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fibrations (Plus C)).IsStableUnderRetracts
  body: inferInstanceAs (degreewiseEpiWithInjectiveKernel.inverseImage (ι C)).IsStableUnderRetracts

中文:
实例 :
  签名: (fibrations (Plus C)).是StableUnderRetracts
  定义体: inferInstanceAs (degreewiseEpiWithInjectiveKernel.inverseImage (ι C)).IsStableUnderRetracts

Depends on / 依赖: IsStableUnderRetracts, degreewiseEpiWithInjectiveKernel, degreewiseEpiWithInjectiveKernel.inverseImage, inverseImage
-/
instance : (fibrations (Plus C)).IsStableUnderRetracts :=
  inferInstanceAs (degreewiseEpiWithInjectiveKernel.inverseImage (ι C)).IsStableUnderRetracts

/--
lemma `cofibration_iff` / 引理 `cofibration_iff`

English:
lemma cofibration_iff
  given: {X Y : Plus C} (f : X ⟶ Y)
  proof: HomotopicalAlgebra.cofibration_iff _

中文:
引理 cofibration_iff
  条件: {X Y : Plus C} (f : X ⟶ Y)
  证明: HomotopicalAlgebra.cofibration_iff _

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.cofibration_iff, cofibration_iff
-/
lemma cofibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Cofibration f ↔ Mono f :=
  HomotopicalAlgebra.cofibration_iff _

/--
lemma `fibration_iff` / 引理 `fibration_iff`

English:
lemma fibration_iff
  given: {X Y : Plus C} (f : X ⟶ Y)
  proof: HomotopicalAlgebra.fibration_iff _

中文:
引理 fibration_iff
  条件: {X Y : Plus C} (f : X ⟶ Y)
  证明: HomotopicalAlgebra.fibration_iff _

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.fibration_iff, fibration_iff
-/
lemma fibration_iff {X Y : Plus C} (f : X ⟶ Y) :
    Fibration f ↔ degreewiseEpiWithInjectiveKernel f.hom :=
  HomotopicalAlgebra.fibration_iff _

/--
lemma `isFibrant_iff` / 引理 `isFibrant_iff`

English:
lemma isFibrant_iff
  given: (X : Plus C)
  proof: by
  rw [HomotopicalAlgebra.isFibrant_iff]; rw [fibration_iff]; rw [degreewiseEpiWithInjectiveKernel_iff_of_isZero]
  exact Functor.map_isZero (Plus.ι C) (IsZero.of_mono_zero _ X)

中文:
引理 isFibrant_iff
  条件: (X : Plus C)
  证明: by
  rw [HomotopicalAlgebra.isFibrant_iff]; rw [fibration_iff]; rw [degreewiseEpiWithInjectiveKernel_iff_of_isZero]
  exact Functor.map_isZero (Plus.ι C) (IsZero.of_mono_zero _ X)

Depends on / 依赖: Functor, Functor.map_isZero, HomotopicalAlgebra, HomotopicalAlgebra.isFibrant_iff, IsZero, IsZero.of_mono_zero, degreewiseEpiWithInjectiveKernel_iff_of_isZero, fibration_iff, isFibrant_iff, map_isZero, of_mono_zero
-/
lemma isFibrant_iff (X : Plus C) :
    IsFibrant X ↔ forall (n : Int), Injective (X.obj.X n) := by
  rw [HomotopicalAlgebra.isFibrant_iff]; rw [fibration_iff]; rw [degreewiseEpiWithInjectiveKernel_iff_of_isZero]
  exact Functor.map_isZero (Plus.ι C) (IsZero.of_mono_zero _ X)

/--
lemma `weakEquivalence_iff` / 引理 `weakEquivalence_iff`

English:
lemma weakEquivalence_iff
  given: {X Y : Plus C} (f : X ⟶ Y)
  proof: HomotopicalAlgebra.weakEquivalence_iff _

中文:
引理 weakEquivalence_iff
  条件: {X Y : Plus C} (f : X ⟶ Y)
  证明: HomotopicalAlgebra.weakEquivalence_iff _

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.weakEquivalence_iff, weakEquivalence_iff
-/
lemma weakEquivalence_iff {X Y : Plus C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ QuasiIso f.hom :=
  HomotopicalAlgebra.weakEquivalence_iff _

instance {A B : CochainComplex.Plus C} (i : A ⟶ B) [Cofibration i] :
    Mono i := by
  rwa [← cofibration_iff]

set_option backward.defeqAttrib.useBackward true in
open HomComplex in
/--
lemma `lifting` / 引理 `lifting`

English:
lemma lifting
  statement: {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
  proof: by
    /- The proof is similar in both cases (whether `i` or `p` is a quasi-isomorphism).
    We first transform the variables so as to get a commutative square in `CochainComplex C ℤ`
    instead of the full subcategory `CochainComplex.Plus C`. -/
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    have hi : Mono i.hom := inferInstance
    have hp : degreewiseEpiWithInjectiveKernel p.hom :=
      (fibration_iff p).1 inferInstance
    obtain ⟨i, rfl⟩ := ObjectProperty.homMk_surjective i
    obtain ⟨p, rfl⟩ := ObjectProperty.homMk_surjective p
    obtain ⟨t, rfl⟩ := ObjectProperty.homMk_surjective t
    obtain ⟨b, rfl⟩ := ObjectProperty.homMk_surjective b
    dsimp at i p t b hp hi
    have hip : QuasiIso i ∨ QuasiIso p := by
      simpa only [weakEquivalence_iff] using! hip
    replace sq : CommSq t i p b := sq.map (ObjectProperty.ι _)
    suffices sq.HasLift from ⟨⟨{ l := ObjectProperty.homMk sq.lift }⟩⟩
    have sq' (n : Int) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      (sq.map (HomologicalComplex.eval _ _ n))
    /- The commutative square in `C` obtained by evaluating in a degree `n`
    admits a lifting because `i.f n` is a monomorphism and `p.f n` is
    an epimorphism with injective kernel. -/
    have (n : Int) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    /- In order to obtain a lifting in the original square, the obstruction
    lies in a cocycle `β : Cocycle (cokernel i) (kernel p) 1`. Thanks to the
    lemma `CochainComplex.Lifting.hasLift`, it suffices to show that `β`
    is a coboundary. -/
    let β : Cocycle (cokernel i) (kernel p) 1 :=
      Lifting.cocycle₁ sq (fun n => { l := (sq' n).lift })
        (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    have (n : Int) : Injective ((kernel p).X n) :=
      Injective.of_iso
        (asIso (kernelComparison p (HomologicalComplex.eval _ _ n))).symm (hp n).2
    have : (kernel p).IsKInjective := by
      obtain ⟨d, hd⟩ := hX
      have : (kernel p).IsStrictlyGE d := by
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono ((kernel.ι p).f i)]
        apply (X.isZero_of_isStrictlyGE d i).eq_of_tgt
      exact isKInjective_of_injective _ d
    /- The cocycle `β` is a coboundary when `i` or `p` is a quasi-isomorphism. -/
    obtain ⟨α, hα⟩ : exists (α : Cochain (cokernel i) (kernel p) 0), δ 0 1 α = β.1 := by
      cases hip
      · refine IsKInjective.eq_δ_of_cocycle β ?_ 0 (by simp)
        have : (ShortComplex.mk _ _ (cokernel.condition i)).ShortExact :=
          { exact := ShortComplex.exact_cokernel i }
        exact this.acyclic_X₃ (by dsimp; infer_instance)
      · refine IsKInjective.eq_δ_of_cocycle' β ?_ 0 (by simp)
        have := hp.epi
        have : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
          { exact := ShortComplex.exact_kernel p }
        exact this.acyclic_X₁ (by dsimp; infer_instance)
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _) α hα

中文:
引理 lifting
  结论: {A B X Y : 上链复形.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
  证明: by
    /- The proof is similar in both cases (whether `i` or `p` is a quasi-isomorphism).
    We first transform the variables so as to get a commutative square in `CochainComplex C ℤ`
    instead of the full subcategory `CochainComplex.Plus C`. -/
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    have hi : Mono i.hom := inferInstance
    have hp : degreewiseEpiWithInjectiveKernel p.hom :=
      (fibration_iff p).1 inferInstance
    obtain ⟨i, rfl⟩ := ObjectProperty.homMk_surjective i
    obtain ⟨p, rfl⟩ := ObjectProperty.homMk_surjective p
    obtain ⟨t, rfl⟩ := ObjectProperty.homMk_surjective t
    obtain ⟨b, rfl⟩ := ObjectProperty.homMk_surjective b
    dsimp at i p t b hp hi
    have hip : QuasiIso i ∨ QuasiIso p := by
      simpa only [weakEquivalence_iff] using! hip
    replace sq : CommSq t i p b := sq.map (ObjectProperty.ι _)
    suffices sq.HasLift from ⟨⟨{ l := ObjectProperty.homMk sq.lift }⟩⟩
    have sq' (n : Int) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      (sq.map (HomologicalComplex.eval _ _ n))
    /- The commutative square in `C` obtained by evaluating in a degree `n`
    admits a lifting because `i.f n` is a monomorphism and `p.f n` is
    an epimorphism with injective kernel. -/
    have (n : Int) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    /- In order to obtain a lifting in the original square, the obstruction
    lies in a cocycle `β : Cocycle (cokernel i) (kernel p) 1`. Thanks to the
    lemma `CochainComplex.Lifting.hasLift`, it suffices to show that `β`
    is a coboundary. -/
    let β : Cocycle (cokernel i) (kernel p) 1 :=
      Lifting.cocycle₁ sq (fun n => { l := (sq' n).lift })
        (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    have (n : Int) : Injective ((kernel p).X n) :=
      Injective.of_iso
        (asIso (kernelComparison p (HomologicalComplex.eval _ _ n))).symm (hp n).2
    have : (kernel p).IsKInjective := by
      obtain ⟨d, hd⟩ := hX
      have : (kernel p).IsStrictlyGE d := by
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono ((kernel.ι p).f i)]
        apply (X.isZero_of_isStrictlyGE d i).eq_of_tgt
      exact isKInjective_of_injective _ d
    /- The cocycle `β` is a coboundary when `i` or `p` is a quasi-isomorphism. -/
    obtain ⟨α, hα⟩ : exists (α : Cochain (cokernel i) (kernel p) 0), δ 0 1 α = β.1 := by
      cases hip
      · refine IsKInjective.eq_δ_of_cocycle β ?_ 0 (by simp)
        have : (ShortComplex.mk _ _ (cokernel.condition i)).ShortExact :=
          { exact := ShortComplex.exact_cokernel i }
        exact this.acyclic_X₃ (by dsimp; infer_instance)
      · refine IsKInjective.eq_δ_of_cocycle' β ?_ 0 (by simp)
        have := hp.epi
        have : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
          { exact := ShortComplex.exact_kernel p }
        exact this.acyclic_X₁ (by dsimp; infer_instance)
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _) α hα
-/
private lemma lifting {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] (hip : WeakEquivalence i ∨ WeakEquivalence p) :
    HasLiftingProperty i p where
  sq_hasLift {t b} sq := by
    /- The proof is similar in both cases (whether `i` or `p` is a quasi-isomorphism).
    We first transform the variables so as to get a commutative square in `CochainComplex C ℤ`
    instead of the full subcategory `CochainComplex.Plus C`. -/
    obtain ⟨A, hA⟩ := A
    obtain ⟨B, hB⟩ := B
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    have hi : Mono i.hom := inferInstance
    have hp : degreewiseEpiWithInjectiveKernel p.hom :=
      (fibration_iff p).1 inferInstance
    obtain ⟨i, rfl⟩ := ObjectProperty.homMk_surjective i
    obtain ⟨p, rfl⟩ := ObjectProperty.homMk_surjective p
    obtain ⟨t, rfl⟩ := ObjectProperty.homMk_surjective t
    obtain ⟨b, rfl⟩ := ObjectProperty.homMk_surjective b
    dsimp at i p t b hp hi
    have hip : QuasiIso i ∨ QuasiIso p := by
      simpa only [weakEquivalence_iff] using! hip
    replace sq : CommSq t i p b := sq.map (ObjectProperty.ι _)
    suffices sq.HasLift from ⟨⟨{ l := ObjectProperty.homMk sq.lift }⟩⟩
    have sq' (n : Int) : CommSq (t.f n) (i.f n) (p.f n) (b.f n) :=
      (sq.map (HomologicalComplex.eval _ _ n))
    /- The commutative square in `C` obtained by evaluating in a degree `n`
    admits a lifting because `i.f n` is a monomorphism and `p.f n` is
    an epimorphism with injective kernel. -/
    have (n : Int) : (sq' n).HasLift := by
      have := (hp n).hasLiftingProperty (i.f n)
      infer_instance
    /- In order to obtain a lifting in the original square, the obstruction
    lies in a cocycle `β : Cocycle (cokernel i) (kernel p) 1`. Thanks to the
    lemma `CochainComplex.Lifting.hasLift`, it suffices to show that `β`
    is a coboundary. -/
    let β : Cocycle (cokernel i) (kernel p) 1 :=
      Lifting.cocycle₁ sq (fun n => { l := (sq' n).lift })
        (cokernelIsCokernel i) (kernelIsKernel p) (hπ := by simp) (hι := by simp)
    have (n : Int) : Injective ((kernel p).X n) :=
      Injective.of_iso
        (asIso (kernelComparison p (HomologicalComplex.eval _ _ n))).symm (hp n).2
    have : (kernel p).IsKInjective := by
      obtain ⟨d, hd⟩ := hX
      have : (kernel p).IsStrictlyGE d := by
        rw [isStrictlyGE_iff]
        intro i hi
        rw [IsZero.iff_id_eq_zero]; rw [← cancel_mono ((kernel.ι p).f i)]
        apply (X.isZero_of_isStrictlyGE d i).eq_of_tgt
      exact isKInjective_of_injective _ d
    /- The cocycle `β` is a coboundary when `i` or `p` is a quasi-isomorphism. -/
    obtain ⟨α, hα⟩ : exists (α : Cochain (cokernel i) (kernel p) 0), δ 0 1 α = β.1 := by
      cases hip
      · refine IsKInjective.eq_δ_of_cocycle β ?_ 0 (by simp)
        have : (ShortComplex.mk _ _ (cokernel.condition i)).ShortExact :=
          { exact := ShortComplex.exact_cokernel i }
        exact this.acyclic_X₃ (by dsimp; infer_instance)
      · refine IsKInjective.eq_δ_of_cocycle' β ?_ 0 (by simp)
        have := hp.epi
        have : (ShortComplex.mk _ _ (kernel.condition p)).ShortExact :=
          { exact := ShortComplex.exact_kernel p }
        exact this.acyclic_X₁ (by dsimp; infer_instance)
    exact Lifting.hasLift sq _ (cokernelIsCokernel _) (kernelIsKernel _) α hα

instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [WeakEquivalence i] [Fibration p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inl inferInstance)

instance {A B X Y : CochainComplex.Plus C} (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p :=
  lifting _ _ (Or.inr inferInstance)

variable [EnoughInjectives C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (trivialCofibrations (Plus C)).HasFactorization (fibrations (Plus C))
  body: by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : exists (d : Int), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, _, hp, fac⟩ := cm5a f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi :=
        ⟨by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff],
          by assumption⟩
      hp := hp }⟩

中文:
实例 :
  签名: (trivialCofibrations (Plus C)).有分解 (fibrations (Plus C))
  定义体: by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : exists (d : Int), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, _, hp, fac⟩ := cm5a f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi :=
        ⟨by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff],
          by assumption⟩
      hp := hp }⟩

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.cofibration_iff, IsStrictlyGE, K.IsStrictlyGE, K.isStrictlyGE_of_ge, L.IsStrictlyGE, L.isStrictlyGE_of_ge, ObjectProperty, ObjectProperty.homMk, Plus.mono_iff, cofibration_iff, isStrictlyGE_of_ge, mono_iff
-/
instance : (trivialCofibrations (Plus C)).HasFactorization (fibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : exists (d : Int), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, _, hp, fac⟩ := cm5a f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi :=
        ⟨by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff],
          by assumption⟩
      hp := hp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cofibrations (Plus C)).HasFactorization (trivialFibrations (Plus C))
  body: by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : exists (d : Int), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, hp, _, fac⟩ := cm5b f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi := by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff]
      hp := ⟨hp, by assumption⟩ }⟩

中文:
实例 :
  签名: (cofibrations (Plus C)).有分解 (trivialFibrations (Plus C))
  定义体: by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : exists (d : Int), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, hp, _, fac⟩ := cm5b f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi := by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff]
      hp := ⟨hp, by assumption⟩ }⟩

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.cofibration_iff, IsStrictlyGE, K.IsStrictlyGE, K.isStrictlyGE_of_ge, L.IsStrictlyGE, L.isStrictlyGE_of_ge, ObjectProperty, ObjectProperty.homMk, Plus.mono_iff, cofibration_iff, isStrictlyGE_of_ge, mono_iff
-/
instance : (cofibrations (Plus C)).HasFactorization (trivialFibrations (Plus C)) where
  nonempty_mapFactorizationData := by
    intro ⟨K, n, hn⟩ ⟨L, m, hm⟩ ⟨f⟩
    obtain ⟨d, _, _⟩ : exists (d : Int), K.IsStrictlyGE (d + 1) ∧ L.IsStrictlyGE d :=
      ⟨min (n - 1) m, K.isStrictlyGE_of_ge _ n (by grind),
        L.isStrictlyGE_of_ge _ m (by simp)⟩
    obtain ⟨K', _, i, p, _, hp, _, fac⟩ := cm5b f d
    exact ⟨{
      Z := ⟨K', d, inferInstance⟩
      i := ObjectProperty.homMk i
      p := ObjectProperty.homMk p
      hi := by rwa [← HomotopicalAlgebra.cofibration_iff, cofibration_iff, Plus.mono_iff]
      hp := ⟨hp, by assumption⟩ }⟩

/-- The Quillen model category structure on the category `CochainComplex.Plus C`
of bounded below cochain complexes in an abelian category `C` with enough injectives. -/
scoped instance : ModelCategory (CochainComplex.Plus C) where

end CochainComplex.Plus.modelCategoryQuillen
