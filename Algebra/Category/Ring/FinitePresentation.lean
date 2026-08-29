/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation

/-!

# Finitely presentable objects in `Under R` with `R : CommRingCat`

In this file, we show that finitely presented algebras are finitely presentable in `Under R`,
i.e. `Hom_R(S, -)` preserves filtered colimits.

-/

public section

open CategoryTheory Limits

universe vJ uJ u

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)
variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)
variable [PreservesColimit F (forget CommRingCat)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/--
lemma `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit` / 引理 `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`

English:
lemma RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
  statement: (hf : f.hom.EssFiniteType)
  proof: by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose k f₁ f₂ h using fun x : S =>
    (Types.FilteredColimit.isColimit_eq_iff _ hc').mp congr(($hab).hom x)
  let J' : MulticospanShape := ⟨Unit oplus Unit, hf.finset, fun _ => .inl .unit, fun _ => .inr .unit⟩
  let D : MulticospanI

中文:
引理 RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
  结论: (hf : f.hom.EssFiniteType)
  证明: by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose k f₁ f₂ h using fun x : S =>
    (Types.FilteredColimit.isColimit_eq_iff _ hc').mp congr(($hab).hom x)
  let J' : MulticospanShape := ⟨Unit oplus Unit, hf.finset, fun _ => .inl .unit, fun _ => .inr .unit⟩
  let D : MulticospanI

Depends on / 依赖: D.multicospan, FilteredColimit, IsFiltered, IsFiltered.cocone_nonempty, MulticospanIndex, MulticospanShape, Sum.elim, Types.FilteredColimit.isColimit_eq_iff, classical, cocone_nonempty, finset, forget, hf.finset, isColimitOfPreserves, isColimit_eq_iff, multicospan
-/
lemma RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit (hf : f.hom.EssFiniteType)
    {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i)
    {j : J} (b : S ⟶ F.obj j) (hb : f ≫ b = α.app j)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    exists (k : J) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ F.map hik = b ≫ F.map hjk := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  choose k f₁ f₂ h using fun x : S =>
    (Types.FilteredColimit.isColimit_eq_iff _ hc').mp congr(($hab).hom x)
  let J' : MulticospanShape := ⟨Unit oplus Unit, hf.finset, fun _ => .inl .unit, fun _ => .inr .unit⟩
  let D : MulticospanIndex J' J :=
  { left := Sum.elim (fun _ => i) (fun _ => j)
    right x := k x.1
    fst x := f₁ x
    snd x := f₂ x }
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty D.multicospan
  refine ⟨c'.pt, c'.ι.app (.left (.inl .unit)), c'.ι.app (.left (.inr .unit)), ?_⟩
  ext1
  apply hf.ext
  · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, reassoc_of% ha, reassoc_of% hb]
    simp [← α.naturality]
  · intro x hx
    rw [← c'.w (.fst (by exact ⟨x]; rw [hx⟩))]; rw [← c'.w (.snd (by exact ⟨x]; rw [hx⟩))]
    have (x : _) : F.map (f₁ x) (a x) = F.map (f₂ x) (b x) := h x
    simp [D, this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/--
lemma `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` / 引理 `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`

English:
lemma RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
  statement: (hf : f.hom.FinitePresentation)
  proof: by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  let P := CommRingCat.of (MvPolynomial (Fin n) R)
  let iP : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      exists π : P ⟶ S, iP ≫ π = f ∧ Function.Surject

中文:
引理 RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
  结论: (hf : f.hom.FinitePresentation)
  证明: by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  let P := CommRingCat.of (MvPolynomial (Fin n) R)
  let iP : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      exists π : P ⟶ S, iP ≫ π = f ∧ Function.Surject

Depends on / 依赖: CommRingCat, CommRingCat.of, CommRingCat.ofHom, F.obj, Function, Function.Surjective, MvPolynomial, MvPolynomial.C, RingHom, RingHom.ker, Surjective, classical, comp_algebraMap, f.hom.toAlgebra, forget, isColimitOfPreserves, toAlgebra
-/
lemma RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (hf : f.hom.FinitePresentation)
    (g : S ⟶ c.pt) (hg : forall i, f ≫ g = α.app i ≫ c.ι.app i) :
    exists (i : J) (g' : S ⟶ F.obj i), f ≫ g' = α.app i ∧ g = g' ≫ c.ι.app i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  let P := CommRingCat.of (MvPolynomial (Fin n) R)
  let iP : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      exists π : P ⟶ S, iP ≫ π = f ∧ Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, h₁, h₂⟩ := hn
    exact ⟨CommRingCat.ofHom π, by ext1; exact π.comp_algebraMap, h₁, h₂⟩
  obtain ⟨i, g', hg', hg''⟩ : exists (i : J) (g' : P ⟶ F.obj i),
      π ≫ g = g' ≫ c.ι.app i ∧ iP ≫ g' = α.app i := by
    choose j x h using fun i => Types.jointly_surjective_of_isColimit hc' ((π ≫ g) (.X i))
    obtain ⟨i, ⟨hi⟩⟩ : exists i, Nonempty (forall a, (j a ⟶ i)) := by
      have : exists i, forall a, Nonempty (j a ⟶ i) := by
        simpa using! IsFiltered.sup_objs_exists (Finset.univ.image j)
      simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using! this
    refine ⟨i, CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (α.app i).hom (F.map (hi _) <| x ·)), ?_, ?_⟩
    · ext1
      apply MvPolynomial.ringHom_ext
      · simpa using! fun x => congr($(hg i).hom x)
      · intro i
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          Functor.const_obj_obj, CommRingCat.hom_ofHom, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_X]
        exact (congr($(c.w (hi i)).hom (x i)).trans (h i)).symm
    · ext x
      simp [P, iP]
  have : forall r : s, exists (i' : J) (hi' : i ⟶ i'), F.map hi' (g' r) = 0 := by
    intro r
    have := Types.FilteredColimit.isColimit_eq_iff _ hc' (xi := g' r) (j := i) (xj := (0 : F.obj i))
    suffices H : (g' ≫ c.ι.app i) r = 0 by
      obtain ⟨k, f, g, e⟩ := this.mp (by simpa using! H)
      exact ⟨k, f, by simpa using! e⟩
    rw [← hg']
    simp [show π r = 0 from hs.le (Ideal.subset_span r.2)]
  choose i' hi' hi'' using this
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan i i' hi')
  refine ⟨c'.pt, CommRingCat.ofHom (RingHom.liftOfSurjective π.hom hπ
    ⟨(g' ≫ F.map (c'.ι.app none)).hom, ?_⟩), ?_, ?_⟩
  · rw [← hs, Ideal.span_le]
    intro r hr
    rw [← c'.w (.init ⟨r]; rw [hr⟩)]
    simp [hi'']
  · ext x
    suffices (iP ≫ g' ≫ F.map (c'.ι.app none)) x = α.app c'.pt x by
      simpa [RingHom.liftOfRightInverse_comp_apply] using! this
    rw [← Category.assoc]; rw [hg'']; rw [← NatTrans.naturality]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  · ext x
    obtain ⟨x, rfl⟩ := hπ x
    suffices (π ≫ g) x = (g' ≫ F.map (c'.ι.app none) ≫ c.ι.app _) x by
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.liftOfRightInverse_comp_apply, coe_comp, Function.comp_apply] using! this
    rw [c.w]; rw [hg']
    rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `CommRingCat.preservesColimit_coyoneda_of_finitePresentation` / 引理 `CommRingCat.preservesColimit_coyoneda_of_finitePresentation`

English:
lemma CommRingCat.preservesColimit_coyoneda_of_finitePresentation
  proof: by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨i, g, h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
       R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.

中文:
引理 CommRingCat.preservesColimit_coyoneda_of_finitePresentation
  证明: by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨i, g, h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
       R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.

Depends on / 依赖: EssFiniteType, F.obj, FilteredColimit, PreservesColimit, PreservesColimit.preserves, RingHom, RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit, RingHom.EssFiniteType.exists_eq_comp_, S.hom, Types.FilteredColimit.isColimitOf, Under.UnderMorphism.ext, Under.forget, Under.homMk, UnderMorphism, exists_comp_map_eq_of_isColimit, f.right, forget, isColimitOf, mapCocone, preserves
-/
lemma CommRingCat.preservesColimit_coyoneda_of_finitePresentation
    (S : Under R) (hS : S.hom.hom.FinitePresentation) (F : J ⥤ Under R)
    [PreservesColimit (F ⋙ Under.forget R) (forget CommRingCat)] :
    PreservesColimit F (coyoneda.obj (.op S)) := by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨i, g, h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
       R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some hS f.right (by simp)
    exact ⟨i, Under.homMk g h₁, Under.UnderMorphism.ext h₂⟩
  · intro i j f₁ f₂ e
    obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
      R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some
      (RingHom.FiniteType.of_finitePresentation hS).essFiniteType
      f₁.right (Under.w f₁) f₂.right (Under.w f₂) congr($(e).right)
    exact ⟨k, hik, hjk, Under.UnderMorphism.ext e⟩

/--
lemma `CommRingCat.preservesFilteredColimits_coyoneda` / 引理 `CommRingCat.preservesFilteredColimits_coyoneda`

English:
lemma CommRingCat.preservesFilteredColimits_coyoneda
  statement: (S : Under R)
  proof: ⟨fun _ _ _ => ⟨preservesColimit_coyoneda_of_finitePresentation R S hS _⟩⟩

中文:
引理 CommRingCat.preservesFilteredColimits_coyoneda
  结论: (S : Under R)
  证明: ⟨fun _ _ _ => ⟨preservesColimit_coyoneda_of_finitePresentation R S hS _⟩⟩

Depends on / 依赖: preservesColimit_coyoneda_of_finitePresentation
-/
lemma CommRingCat.preservesFilteredColimits_coyoneda (S : Under R)
    (hS : S.hom.hom.FinitePresentation) :
    PreservesFilteredColimits (coyoneda.obj (.op S)) :=
  ⟨fun _ _ _ => ⟨preservesColimit_coyoneda_of_finitePresentation R S hS _⟩⟩

/--
lemma `CommRingCat.isFinitelyPresentable_under` / 引理 `CommRingCat.isFinitelyPresentable_under`

English:
lemma CommRingCat.isFinitelyPresentable_under
  given: (S : Under R) (hS : S.hom.hom.FinitePresentation)
  proof: by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact preservesFilteredColimits_coyoneda R S hS

中文:
引理 CommRingCat.isFinitelyPresentable_under
  条件: (S : Under R) (hS : S.hom.hom.FinitePresentation)
  证明: by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact preservesFilteredColimits_coyoneda R S hS

Depends on / 依赖: isFinitelyPresentable_iff_preservesFilteredColimits, preservesFilteredColimits_coyoneda
-/
lemma CommRingCat.isFinitelyPresentable_under (S : Under R) (hS : S.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{u} S := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  exact preservesFilteredColimits_coyoneda R S hS

variable {R} in
/--
lemma `CommRingCat.isFinitelyPresentable_hom` / 引理 `CommRingCat.isFinitelyPresentable_hom`

English:
lemma CommRingCat.isFinitelyPresentable_hom
  statement: {S : CommRingCat.{u}} (f : R ⟶ S)
  proof: isFinitelyPresentable_under R (Under.mk f) hf

中文:
引理 CommRingCat.isFinitelyPresentable_hom
  结论: {S : CommRingCat.{u}} (f : R ⟶ S)
  证明: isFinitelyPresentable_under R (Under.mk f) hf

Depends on / 依赖: Under.mk, isFinitelyPresentable_under
-/
lemma CommRingCat.isFinitelyPresentable_hom {S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.FinitePresentation) :
    MorphismProperty.isFinitelyPresentable.{u} _ f :=
  isFinitelyPresentable_under R (Under.mk f) hf
