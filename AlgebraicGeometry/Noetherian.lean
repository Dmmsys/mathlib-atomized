/-
Copyright (c) 2024 Geno Racklin Asher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geno Racklin Asher
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Noetherian and Locally Noetherian Schemes

We introduce the concept of (locally) Noetherian schemes,
giving definitions, equivalent conditions, and basic properties.

## Main definitions

* `AlgebraicGeometry.IsLocallyNoetherian`: A scheme is locally Noetherian
  if the components of the structure sheaf at each affine open are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian`: A scheme is Noetherian if it is locally Noetherian
  and quasi-compact as a topological space.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`: A scheme is locally Noetherian
  if and only if it is covered by affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`: A locally Noetherian scheme is
  quasi-separated.

* `AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover`: A scheme is Noetherian
  if and only if it is covered by finitely many affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian.noetherianSpace`: A Noetherian scheme is
  topologically a Noetherian space.

## References

* [Stacks: Noetherian Schemes](https://stacks.math.columbia.edu/tag/01OU)
* [Robin Hartshorne, *Algebraic Geometry*][Har77]

-/

public section

universe u v

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

namespace AlgebraicGeometry

/--
Definition of `IsLocallyNoetherian` / `IsLocallyNoetherian` 的定义

English:
class IsLocallyNoetherian
  parameters: (X : Scheme)
  axioms and operations (1):
    - component_noetherian : forall (U : X.affineOpens), IsNoetherianRing Γ(X, U)  [default: by infer_instance]

中文:
类 是LocallyNoetherian
  参数: (X : 概形)
  公理与运算 (1 个):
    - component_noetherian : 对任意 (U : X.affineOpens), 是Noether环 Γ(X, U)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : forall (U : X.affineOpens),
    IsNoetherianRing Γ(X, U) := by infer_instance

section localizationProps

variable {R : Type u} [CommRing R] (S : Finset R) (hS : Ideal.span (α := R) S = ⊤)
  (hN : forall s : S, IsNoetherianRing (Away (M := R) s))

include hS hN in
/--
theorem `isNoetherianRing_of_away` / 定理 `isNoetherianRing_of_away`

English:
theorem isNoetherianRing_of_away
  statement: IsNoetherianRing R
  proof: by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : Nat | forall m : Nat, n <= m -> (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : forall s : S, minN s in suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : Nat ->o Ideal (Away (M := R) s) :=
      ⟨fun n => Ideal.map (floc s) (I n), fun _ _ h => Ideal.map_mono (I.monotone h)⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : forall s : S, minN s <= N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I N)]; rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I n)]; rw [iInf_subtype']; rw [iInf_subtype']
  apply iInf_congr
  intro s
  congr 1
  rw [← hSuit s N (hN s)]
exact hSuit s n Nat.le_trans (hN s) hn

中文:
定理 isNoetherianRing_of_away
  结论: 是Noether环 R
  证明: by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : Nat | forall m : Nat, n <= m -> (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : forall s : S, minN s in suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : Nat ->o Ideal (Away (M := R) s) :=
      ⟨fun n => Ideal.map (floc s) (I n), fun _ _ h => Ideal.map_mono (I.monotone h)⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : forall s : S, minN s <= N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I N)]; rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I n)]; rw [iInf_subtype']; rw [iInf_subtype']
  apply iInf_congr
  intro s
  congr 1
  rw [← hSuit s N (hN s)]
exact hSuit s n Nat.le_trans (hN s) hn

Depends on / 依赖: I.monotone, Ideal.map, Ideal.map_mono, Nat.sInf_mem, algebraMap, map_mono, monotone, monotone_stabilizes_iff_noetherian, monotone_stabilizes_iff_noetherian.mp, monotone_stabilizes_iff_noetherian.mpr, sInf_mem, suitableN
-/
theorem isNoetherianRing_of_away : IsNoetherianRing R := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : Nat | forall m : Nat, n <= m -> (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : forall s : S, minN s in suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : Nat ->o Ideal (Away (M := R) s) :=
      ⟨fun n => Ideal.map (floc s) (I n), fun _ _ h => Ideal.map_mono (I.monotone h)⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : forall s : S, minN s <= N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I N)]; rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I n)]; rw [iInf_subtype']; rw [iInf_subtype']
  apply iInf_congr
  intro s
  congr 1
  rw [← hSuit s N (hN s)]
exact hSuit s n Nat.le_trans (hN s) hn

end localizationProps

variable {X : Scheme}

/--
theorem `isLocallyNoetherian_of_affine_cover` / 定理 `isLocallyNoetherian_of_affine_cover`

English:
theorem isLocallyNoetherian_of_affine_cover
  statement: {ι} {S : ι -> X.affineOpens}
  proof: by
  refine ⟨fun U => ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hN =>
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  | openCover U s _ hN =>
    apply isNoetherianRing_of_away s ‹_›
    intro ⟨f, hf⟩
    have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
    have := U.prop.isLocalization_basicOpen f
    have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
    exact isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f) hEq.symm.toRingEquiv
  | hU => exact hS' _

中文:
定理 isLocallyNoetherian_of_affine_cover
  结论: {ι} {S : ι -> X.affineOpens}
  证明: by
  refine ⟨fun U => ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hN =>
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  | openCover U s _ hN =>
    apply isNoetherianRing_of_away s ‹_›
    intro ⟨f, hf⟩
    have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
    have := U.prop.isLocalization_basicOpen f
    have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
    exact isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f) hEq.symm.toRingEquiv
  | hU => exact hS' _

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, IsLocalization.isNoetherianRing, IsNoetherianRing, Localization, Localization.Away, U.prop.isLocalization_basicOpen, X.basicOpen, algEquiv, basicOpen, isLocalization_basicOpen, isNoetherianRing, isNoetherianRing_of, isNoetherianRing_of_away, of_affine_open_cover, openCover, powers
-/
theorem isLocallyNoetherian_of_affine_cover {ι} {S : ι -> X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤)
    (hS' : forall i, IsNoetherianRing Γ(X, S i)) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hN =>
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  | openCover U s _ hN =>
    apply isNoetherianRing_of_away s ‹_›
    intro ⟨f, hf⟩
    have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
    have := U.prop.isLocalization_basicOpen f
    have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
    exact isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f) hEq.symm.toRingEquiv
  | hU => exact hS' _

/--
theorem `isLocallyNoetherian_iff_of_iSup_eq_top` / 定理 `isLocallyNoetherian_iff_of_iSup_eq_top`

English:
theorem isLocallyNoetherian_iff_of_iSup_eq_top
  statement: {ι} {S : ι -> X.affineOpens}
  proof: ⟨fun _ i => IsLocallyNoetherian.component_noetherian (S i),
   isLocallyNoetherian_of_affine_cover hS⟩

中文:
定理 isLocallyNoetherian_iff_of_iSup_eq_top
  结论: {ι} {S : ι -> X.affineOpens}
  证明: ⟨fun _ i => IsLocallyNoetherian.component_noetherian (S i),
   isLocallyNoetherian_of_affine_cover hS⟩

Depends on / 依赖: IsLocallyNoetherian, IsLocallyNoetherian.component_noetherian, component_noetherian, decidable_of_iff, isLocallyNoetherian_of_affine_cover, objEquiv, stdSimplex, stdSimplex.objEquiv
-/
theorem isLocallyNoetherian_iff_of_iSup_eq_top {ι} {S : ι -> X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsLocallyNoetherian X ↔ forall i, IsNoetherianRing Γ(X, S i) :=
  ⟨fun _ i => IsLocallyNoetherian.component_noetherian (S i),
   isLocallyNoetherian_of_affine_cover hS⟩

/--
theorem `isLocallyNoetherian_iff_of_affine_openCover` / 定理 `isLocallyNoetherian_iff_of_affine_openCover`

English:
theorem isLocallyNoetherian_iff_of_affine_openCover
  statement: (𝒰 : Scheme.OpenCover.{v, u} X)
  proof: by
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (𝒰.f i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (IsOpenImmersion.ΓIsoTop (𝒰.f i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
    apply isLocallyNoetherian_of_affine_cover (S := fS)
    · rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
    intro i
    apply isNoetherianRing_of_ringEquiv (R := Γ(𝒰.X i, ⊤))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact IsOpenImmersion.ΓIsoTop (𝒰.f i)

中文:
定理 isLocallyNoetherian_iff_of_affine_openCover
  结论: (𝒰 : 概形.OpenCover.{v, u} X)
  证明: by
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (𝒰.f i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (IsOpenImmersion.ΓIsoTop (𝒰.f i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
    apply isLocallyNoetherian_of_affine_cover (S := fS)
    · rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
    intro i
    apply isNoetherianRing_of_ringEquiv (R := Γ(𝒰.X i, ⊤))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact IsOpenImmersion.ΓIsoTop (𝒰.f i)

Depends on / 依赖: CategoryTheory, CategoryTheory.Iso.commRingCatIsoToRingEquiv, IsOpenImmersion, OpenCover, Scheme, Scheme.Hom.opensRange, Scheme.OpenCover.iSup_opensRange, X.affineOpens, affineOpens, commRingCatIsoToRingEquiv, component_noetherian, h.component_noetherian, hCNoeth, iSup_opensRange, isAffineOpen_opensRange, isLocallyNoetherian_of_affine_cover, isNoetherian, isNoetherianRing_of_ringEquiv, objEquiv, opensRange
-/
theorem isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X)
    [forall i, IsAffine (𝒰.X i)] :
    IsLocallyNoetherian X ↔ forall (i : 𝒰.I₀), IsNoetherianRing Γ(𝒰.X i, ⊤) := by
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (𝒰.f i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (IsOpenImmersion.ΓIsoTop (𝒰.f i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
    apply isLocallyNoetherian_of_affine_cover (S := fS)
    · rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
    intro i
    apply isNoetherianRing_of_ringEquiv (R := Γ(𝒰.X i, ⊤))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact IsOpenImmersion.ΓIsoTop (𝒰.f i)

-- Also see `LocallyOfFiniteType.isLocallyNoetherian`.
/--
lemma `isLocallyNoetherian_of_isOpenImmersion` / 引理 `isLocallyNoetherian_of_isOpenImmersion`

English:
lemma isLocallyNoetherian_of_isOpenImmersion
  statement: {Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: have : IsNoetherianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyNoetherian.component_noetherian ⟨_, U.2.image_of_isOpenImmersion f⟩
    isNoetherianRing_of_surjective _ _ _ (f.appIso U).commRingCatIsoToRingEquiv.surjective

中文:
引理 isLocallyNoetherian_of_isOpenImmersion
  结论: {Y : 概形} (f : X ⟶ Y) [是开浸入 f]
  证明: have : IsNoetherianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyNoetherian.component_noetherian ⟨_, U.2.image_of_isOpenImmersion f⟩
    isNoetherianRing_of_surjective _ _ _ (f.appIso U).commRingCatIsoToRingEquiv.surjective

Depends on / 依赖: IsLocallyNoetherian, IsLocallyNoetherian.component_noetherian, IsNoetherianRing, appIso, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.surjective, component_noetherian, f.appIso, image_of_isOpenImmersion, isNoetherianRing_of_surjective, surjective
-/
lemma isLocallyNoetherian_of_isOpenImmersion {Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X where
  component_noetherian U :=
    have : IsNoetherianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyNoetherian.component_noetherian ⟨_, U.2.image_of_isOpenImmersion f⟩
    isNoetherianRing_of_surjective _ _ _ (f.appIso U).commRingCatIsoToRingEquiv.surjective

instance {U : X.Opens} [IsLocallyNoetherian X] : IsLocallyNoetherian U :=
  isLocallyNoetherian_of_isOpenImmersion U.ι

instance {U : X.OpenCover} (i) [IsLocallyNoetherian X] : IsLocallyNoetherian (U.X i) :=
  isLocallyNoetherian_of_isOpenImmersion (U.f i)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isLocallyNoetherian_iff_openCover` / 定理 `isLocallyNoetherian_iff_openCover`

English:
theorem isLocallyNoetherian_iff_openCover
  given: (𝒰 : Scheme.OpenCover X)
  proof: by
  refine ⟨fun _ => inferInstance, ?_⟩
  · rw [isLocallyNoetherian_iff_of_affine_openCover (𝒰 := 𝒰.affineRefinement.openCover)]
    intro h i
    exact @isNoetherianRing_of_ringEquiv _ _ _ _
      (IsOpenImmersion.ΓIsoTop (PreZeroHypercover.f _ i.2)).symm.commRingCatIsoToRingEquiv
      (IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange _⟩)

中文:
定理 isLocallyNoetherian_iff_openCover
  条件: (𝒰 : 概形.OpenCover X)
  证明: by
  refine ⟨fun _ => inferInstance, ?_⟩
  · rw [isLocallyNoetherian_iff_of_affine_openCover (𝒰 := 𝒰.affineRefinement.openCover)]
    intro h i
    exact @isNoetherianRing_of_ringEquiv _ _ _ _
      (IsOpenImmersion.ΓIsoTop (PreZeroHypercover.f _ i.2)).symm.commRingCatIsoToRingEquiv
      (IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange _⟩)

Depends on / 依赖: IsLocallyNoetherian, IsLocallyNoetherian.component_noetherian, IsOpenImmersion, PreZeroHypercover, PreZeroHypercover.f, affineRefinement, affineRefinement.openCover, commRingCatIsoToRingEquiv, component_noetherian, isAffineOpen_opensRange, isLocallyNoetherian_iff_of_affine_openCover, isNoetherianRing_of_ringEquiv, openCover, symm.commRingCatIsoToRingEquiv
-/
theorem isLocallyNoetherian_iff_openCover (𝒰 : Scheme.OpenCover X) :
    IsLocallyNoetherian X ↔ forall (i : 𝒰.I₀), IsLocallyNoetherian (𝒰.X i) := by
  refine ⟨fun _ => inferInstance, ?_⟩
  · rw [isLocallyNoetherian_iff_of_affine_openCover (𝒰 := 𝒰.affineRefinement.openCover)]
    intro h i
    exact @isNoetherianRing_of_ringEquiv _ _ _ _
      (IsOpenImmersion.ΓIsoTop (PreZeroHypercover.f _ i.2)).symm.commRingCatIsoToRingEquiv
      (IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange _⟩)

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian topological space. -/
instance {R : CommRingCat} [IsNoetherianRing R] :
    NoetherianSpace (Spec R) := by
  convert! PrimeSpectrum.instNoetherianSpace (R := R)

/--
lemma `noetherianSpace_of_isAffine` / 引理 `noetherianSpace_of_isAffine`

English:
lemma noetherianSpace_of_isAffine
  given: [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
  proof: (noetherianSpace_iff_of_homeomorph X.isoSpec.inv.homeomorph).mp inferInstance

中文:
引理 noetherianSpace_of_isAffine
  条件: [是仿射 X] [是Noether环 Γ(X, ⊤)]
  证明: (noetherianSpace_iff_of_homeomorph X.isoSpec.inv.homeomorph).mp inferInstance

Depends on / 依赖: X.isoSpec.inv.homeomorph, homeomorph, isoSpec, noetherianSpace_iff_of_homeomorph
-/
lemma noetherianSpace_of_isAffine [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] :
    NoetherianSpace X :=
  (noetherianSpace_iff_of_homeomorph X.isoSpec.inv.homeomorph).mp inferInstance

/--
lemma `noetherianSpace_of_isAffineOpen` / 引理 `noetherianSpace_of_isAffineOpen`

English:
lemma noetherianSpace_of_isAffineOpen
  statement: (U : X.Opens) (hU : IsAffineOpen U)
  proof: by
  have : IsNoetherianRing Γ(U, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U)).symm.commRingCatIsoToRingEquiv
  exact @noetherianSpace_of_isAffine _ hU _

中文:
引理 noetherianSpace_of_isAffineOpen
  结论: (U : X.Opens) (hU : 是仿射开集 U)
  证明: by
  have : IsNoetherianRing Γ(U, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U)).symm.commRingCatIsoToRingEquiv
  exact @noetherianSpace_of_isAffine _ hU _

Depends on / 依赖: IsNoetherianRing, Scheme, Scheme.restrictFunctor, commRingCatIsoToRingEquiv, isNoetherianRing_of_ringEquiv, noetherianSpace_of_isAffine, symm.commRingCatIsoToRingEquiv
-/
lemma noetherianSpace_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] :
    NoetherianSpace U := by
  have : IsNoetherianRing Γ(U, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U)).symm.commRingCatIsoToRingEquiv
  exact @noetherianSpace_of_isAffine _ hU _

instance {R : CommRingCat} [IsNoetherianRing R] : IsLocallyNoetherian (Spec R) :=
  isLocallyNoetherian_of_affine_cover (S := fun _ : Unit => ⟨⊤, isAffineOpen_top (Spec R)⟩) (by simp)
    fun _ => isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv

@[simp]
/--
theorem `isLocallyNoetherian_Spec` / 定理 `isLocallyNoetherian_Spec`

English:
theorem isLocallyNoetherian_Spec
  given: {R : CommRingCat}
  proof: have := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  mpr _ := inferInstance

中文:
定理 isLocallyNoetherian_Spec
  条件: {R : 交换环范畴}
  证明: have := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  mpr _ := inferInstance

Depends on / 依赖: IsLocallyNoetherian, IsLocallyNoetherian.component_noetherian, Scheme, commRingCatIsoToRingEquiv, component_noetherian, isAffineOpen_top, isNoetherianRing_of_ringEquiv
-/
theorem isLocallyNoetherian_Spec {R : CommRingCat} :
    IsLocallyNoetherian (Spec R) ↔ IsNoetherianRing R where
  mp _ :=
    have := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  mpr _ := inferInstance

/-- Any open immersion `Z ⟶ X` with `X` locally Noetherian is quasi-compact. -/
@[stacks 01OX]
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [IsOpenImmersion f] : QuasiCompact f := by
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  rw [Opens.map_coe]; rw [← Set.preimage_inter_range]
  apply f.isOpenEmbedding.isInducing.isCompact_preimage'
  · apply (noetherianSpace_set_iff _).mp
    · convert! noetherianSpace_of_isAffineOpen U hU
      apply IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    · exact Set.inter_subset_left
  · exact Set.inter_subset_right

set_option backward.isDefEq.respectTransparency.types false in
/-- A locally Noetherian scheme is quasi-separated. -/
@[stacks 01OY]
instance (priority := 100) IsLocallyNoetherian.quasiSeparatedSpace [IsLocallyNoetherian X] :
    QuasiSeparatedSpace X := by
  apply quasiSeparatedSpace_iff_forall_affineOpens.mpr
  intro U V
  have hInd := U.2.fromSpec.isOpenEmbedding.isInducing
  apply (hInd.isCompact_preimage_iff ?_).mp
  · rw [← Set.preimage_inter_range, IsAffineOpen.range_fromSpec, Set.inter_comm]
    apply hInd.isCompact_preimage'
    · apply (noetherianSpace_set_iff _).mp
      · convert! noetherianSpace_of_isAffineOpen U.1 U.2
        apply IsLocallyNoetherian.component_noetherian
      · exact Set.inter_subset_left
    · rw [IsAffineOpen.range_fromSpec]
      exact Set.inter_subset_left
  · rw [IsAffineOpen.range_fromSpec]
    exact Set.inter_subset_left

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LocallyOfFiniteType.isLocallyNoetherian` / 定理 `LocallyOfFiniteType.isLocallyNoetherian`

English:
theorem LocallyOfFiniteType.isLocallyNoetherian
  proof: by
  change id (IsLocallyNoetherian X) -- avoid wlog hypotheses confusing the instance synthesizer
  wlog hY : exists R, Y = Spec R
  · exact (isLocallyNoetherian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i =>
      this (Limits.pullback.snd f (Y.affineCover.f i)) ⟨_, rfl⟩
  wlog hX : exists S, X = Spec S
  · exact (isLocallyNoetherian_iff_openCover X.affineCover).mpr
      fun i => this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  simp_all [Algebra.FiniteType.isNoetherianRing R]

中文:
定理 局部有限型.isLocallyNoetherian
  证明: by
  change id (IsLocallyNoetherian X) -- avoid wlog hypotheses confusing the instance synthesizer
  wlog hY : exists R, Y = Spec R
  · exact (isLocallyNoetherian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i =>
      this (Limits.pullback.snd f (Y.affineCover.f i)) ⟨_, rfl⟩
  wlog hX : exists S, X = Spec S
  · exact (isLocallyNoetherian_iff_openCover X.affineCover).mpr
      fun i => this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  simp_all [Algebra.FiniteType.isNoetherianRing R]

Depends on / 依赖: IsLocallyNoetherian, Limits, Limits.pullback.snd, Spec.map_surjective, X.affineCover, X.affineCover.f, Y.affineCover.f, Y.affineCover.pullback, affineCover, confusing, hypotheses, instance, isLocallyNoetherian_iff_openCover, map_surjective, pullback, synthesizer
-/
theorem LocallyOfFiniteType.isLocallyNoetherian
    {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X := by
  change id (IsLocallyNoetherian X) -- avoid wlog hypotheses confusing the instance synthesizer
  wlog hY : exists R, Y = Spec R
  · exact (isLocallyNoetherian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i =>
      this (Limits.pullback.snd f (Y.affineCover.f i)) ⟨_, rfl⟩
  wlog hX : exists S, X = Spec S
  · exact (isLocallyNoetherian_iff_openCover X.affineCover).mpr
      fun i => this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  simp_all [Algebra.FiniteType.isNoetherianRing R]

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsLocallyNoetherian (Limits.pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.snd _ _)

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [LocallyOfFiniteType g] :
    IsLocallyNoetherian (Limits.pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst _ _)

instance (priority := low) {X Y : Scheme} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f := by
  refine ⟨fun {U hU V hV} hUV => ?_⟩
  let := (f.appLE U V hUV).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact Algebra.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hUV)

/--
lemma `LocallyOfFinitePresentation.iff_locallyOfFiniteType` / 引理 `LocallyOfFinitePresentation.iff_locallyOfFiniteType`

English:
lemma LocallyOfFinitePresentation.iff_locallyOfFiniteType
  statement: {X Y : Scheme} {f : X ⟶ Y}
  proof: ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
引理 局部有限呈现.iff_locallyOfFiniteType
  结论: {X Y : 概形} {f : X ⟶ Y}
  证明: ⟨fun _ => inferInstance, fun _ => inferInstance⟩
-/
lemma LocallyOfFinitePresentation.iff_locallyOfFiniteType {X Y : Scheme} {f : X ⟶ Y}
    [IsLocallyNoetherian Y] : LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-- A scheme `X` is Noetherian if it is locally Noetherian and compact. -/
@[mk_iff]
/--
Definition of `IsNoetherian` / `IsNoetherian` 的定义

English:
class IsNoetherian
  parameters: (X : Scheme)
  extends: IsLocallyNoetherian X, CompactSpace X
  (no additional axioms)

中文:
类 是Noether
  参数: (X : 概形)
  继承: 是LocallyNoetherian X, 紧空间 X
  (无附加公理)
-/
class IsNoetherian (X : Scheme) : Prop extends IsLocallyNoetherian X, CompactSpace X

/--
theorem `isNoetherian_iff_of_finite_iSup_eq_top` / 定理 `isNoetherian_iff_of_finite_iSup_eq_top`

English:
theorem isNoetherian_iff_of_finite_iSup_eq_top
  statement: {ι} [Finite ι] {S : ι -> X.affineOpens}
  proof: by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
  · intro h
    convert! IsNoetherian.mk
    · exact isLocallyNoetherian_of_affine_cover hS h
    · constructor
      rw [← Opens.coe_top]; rw [← hS]; rw [Opens.iSup_mk]
      apply isCompact_iUnion
      intro i
      apply isCompact_iff_isCompact_univ.mpr
      convert! CompactSpace.isCompact_univ
      have : NoetherianSpace (S i) := by
        apply noetherianSpace_of_isAffineOpen (S i).1 (S i).2
      apply NoetherianSpace.compactSpace (S i)

中文:
定理 isNoetherian_iff_of_finite_iSup_eq_top
  结论: {ι} [有限 ι] {S : ι -> X.affineOpens}
  证明: by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
  · intro h
    convert! IsNoetherian.mk
    · exact isLocallyNoetherian_of_affine_cover hS h
    · constructor
      rw [← Opens.coe_top]; rw [← hS]; rw [Opens.iSup_mk]
      apply isCompact_iUnion
      intro i
      apply isCompact_iff_isCompact_univ.mpr
      convert! CompactSpace.isCompact_univ
      have : NoetherianSpace (S i) := by
        apply noetherianSpace_of_isAffineOpen (S i).1 (S i).2
      apply NoetherianSpace.compactSpace (S i)

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, IsNoetherian, IsNoetherian.mk, NoetherianSpace, NoetherianSpace.compactSpace, Opens.coe_top, Opens.iSup_mk, coe_top, compactSpace, convert, h.toIsLocallyNoetherian, iSup_mk, isCompact_iUnion, isCompact_iff_isCompact_univ, isCompact_iff_isCompact_univ.mpr, isCompact_univ, isLocallyNoetherian_iff_of_iSup_eq_top, isLocallyNoetherian_of_affine_cover, noetherianSpace_of_isAffineOpen
-/
theorem isNoetherian_iff_of_finite_iSup_eq_top {ι} [Finite ι] {S : ι -> X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsNoetherian X ↔ forall i, IsNoetherianRing Γ(X, S i) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
  · intro h
    convert! IsNoetherian.mk
    · exact isLocallyNoetherian_of_affine_cover hS h
    · constructor
      rw [← Opens.coe_top]; rw [← hS]; rw [Opens.iSup_mk]
      apply isCompact_iUnion
      intro i
      apply isCompact_iff_isCompact_univ.mpr
      convert! CompactSpace.isCompact_univ
      have : NoetherianSpace (S i) := by
        apply noetherianSpace_of_isAffineOpen (S i).1 (S i).2
      apply NoetherianSpace.compactSpace (S i)

/--
theorem `isNoetherian_iff_of_finite_affine_openCover` / 定理 `isNoetherian_iff_of_finite_affine_openCover`

English:
theorem isNoetherian_iff_of_finite_affine_openCover
  statement: {𝒰 : Scheme.OpenCover.{v, u} X}
  proof: by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover _).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert! IsNoetherian.mk
    · exact (isLocallyNoetherian_iff_of_affine_openCover _).mpr hNoeth
    · exact Scheme.OpenCover.compactSpace 𝒰

中文:
定理 isNoetherian_iff_of_finite_affine_openCover
  结论: {𝒰 : 概形.OpenCover.{v, u} X}
  证明: by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover _).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert! IsNoetherian.mk
    · exact (isLocallyNoetherian_iff_of_affine_openCover _).mpr hNoeth
    · exact Scheme.OpenCover.compactSpace 𝒰

Depends on / 依赖: IsNoetherian, IsNoetherian.mk, OpenCover, Scheme, Scheme.OpenCover.compactSpace, compactSpace, convert, h.toIsLocallyNoetherian, hNoeth, isLocallyNoetherian_iff_of_affine_openCover, toIsLocallyNoetherian
-/
theorem isNoetherian_iff_of_finite_affine_openCover {𝒰 : Scheme.OpenCover.{v, u} X}
    [Finite 𝒰.I₀] [forall i, IsAffine (𝒰.X i)] :
    IsNoetherian X ↔ forall (i : 𝒰.I₀), IsNoetherianRing Γ(𝒰.X i, ⊤) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover _).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert! IsNoetherian.mk
    · exact (isLocallyNoetherian_iff_of_affine_openCover _).mpr hNoeth
    · exact Scheme.OpenCover.compactSpace 𝒰

set_option backward.isDefEq.respectTransparency.types false in
/-- A Noetherian scheme has a Noetherian underlying topological space. -/
@[stacks 01OZ]
instance (priority := 100) IsNoetherian.noetherianSpace [IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  let 𝒰 := X.affineCover.finiteSubcover
  rw [← 𝒰.iUnion_range]
  suffices forall i : 𝒰.I₀, NoetherianSpace (Set.range <| (𝒰.f i)) by
    apply NoetherianSpace.iUnion
  intro i
  have : IsAffine (𝒰.X i) := by
    rw [X.affineCover.finiteSubcover_X]
    apply Scheme.isAffine_affineCover
  let U : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
  convert! noetherianSpace_of_isAffineOpen U.1 U.2
  apply IsLocallyNoetherian.component_noetherian

/-- Any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact. -/
@[stacks 01P0]
instance (priority := 100) quasiCompact_of_noetherianSpace_source {X Y : Scheme}
    [NoetherianSpace X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian scheme. -/
instance {R : CommRingCat} [IsNoetherianRing R] : IsNoetherian (Spec R) where

instance {R} [CommRing R] [IsNoetherianRing R] :
IsNoetherian Spec .of R := by
  suffices IsNoetherianRing (CommRingCat.of R) by infer_instance
  assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocallyNoetherian
  signature: X] {x
  body: by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)

中文:
实例 [是LocallyNoetherian
  签名: X] {x
  定义体: by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.IsAffineOpen.isLocalization_stalk, IsAffineOpen, IsLocalization, IsLocalization.isNoetherianRing, IsLocallyNoetherian, IsLocallyNoetherian.component_noetherian, X.presheaf.algebra_section_stalk, X.presheaf.stalk, algebra_section_stalk, asIdeal, asIdeal.primeCompl, component_noetherian, exists_isAffineOpen_mem_and_subset, hU.primeIdealOf, isLocalization_stalk, isNoetherianRing, presheaf, primeCompl, primeIdealOf
-/
instance [IsLocallyNoetherian X] {x : X} : IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)

/-- `R` is a Noetherian ring if and only if `Spec R` is a Noetherian scheme. -/
@[simp]
/--
theorem `isNoetherian_Spec` / 定理 `isNoetherian_Spec`

English:
theorem isNoetherian_Spec
  given: {R : CommRingCat}
  proof: by
  simp [AlgebraicGeometry.isNoetherian_iff, (inferInstance : CompactSpace (Spec R))]

中文:
定理 isNoetherian_Spec
  条件: {R : 交换环范畴}
  证明: by
  simp [AlgebraicGeometry.isNoetherian_iff, (inferInstance : CompactSpace (Spec R))]

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.isNoetherian_iff, CompactSpace, isNoetherian_iff
-/
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Spec R) ↔ IsNoetherianRing R := by
  simp [AlgebraicGeometry.isNoetherian_iff, (inferInstance : CompactSpace (Spec R))]

/-- A Noetherian scheme has a finite number of irreducible components. -/
@[stacks 0BA8]
/--
theorem `finite_irreducibleComponents_of_isNoetherian` / 定理 `finite_irreducibleComponents_of_isNoetherian`

English:
theorem finite_irreducibleComponents_of_isNoetherian
  given: [IsNoetherian X]
  proof: NoetherianSpace.finite_irreducibleComponents

中文:
定理 finite_irreducibleComponents_of_isNoetherian
  条件: [是Noether X]
  证明: NoetherianSpace.finite_irreducibleComponents

Depends on / 依赖: NoetherianSpace, NoetherianSpace.finite_irreducibleComponents, finite_irreducibleComponents
-/
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents

end AlgebraicGeometry
