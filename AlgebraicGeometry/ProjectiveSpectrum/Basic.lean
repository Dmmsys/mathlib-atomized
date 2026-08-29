/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing

/-!

# Basic properties of the scheme `Proj A`

The scheme `Proj 𝒜` for a graded ring `𝒜` is constructed in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`.
In this file we provide basic properties of the scheme.

## Main results
- `AlgebraicGeometry.Proj.toSpecZero`: The structure map `Proj A ⟶ Spec (A 0)`.
- `AlgebraicGeometry.Proj.basicOpenIsoSpec`:
  The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
  when `f` is homogeneous of positive degree.
- `AlgebraicGeometry.Proj.awayι`: The open immersion `Spec (A_f)₀ ⟶ Proj A`.
- `AlgebraicGeometry.Proj.affineOpenCover`: The open cover of `Proj A` by `Spec (A_f)₀` for all
  homogeneous `f` of positive degree.
- `AlgebraicGeometry.Proj.stalkIso`:
  The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`.
- `AlgebraicGeometry.Proj.fromOfGlobalSections`:
  Given a map `f : A →+* Γ(X, ⊤)` such that the image of the irrelevant ideal under `f`
  generates the whole ring, we can construct a map `X ⟶ Proj 𝒜`.

-/

@[expose] public section

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization CategoryTheory

universe u

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : Nat -> σ)
variable [GradedRing 𝒜]

section basicOpen

variable (f g : A)

/--
Definition of `basicOpen` / `basicOpen` 的定义

English:
definition basicOpen
  signature: : (Proj 𝒜).Opens
  body: ProjectiveSpectrum.basicOpen 𝒜 f

@[simp]

中文:
定义 basicOpen
  签名: : (Proj 𝒜).Opens
  定义体: ProjectiveSpectrum.basicOpen 𝒜 f

@[simp]

Depends on / 依赖: ProjectiveSpectrum, ProjectiveSpectrum.basicOpen, basicOpen
-/
def basicOpen : (Proj 𝒜).Opens :=
  ProjectiveSpectrum.basicOpen 𝒜 f

@[simp]
/--
theorem `mem_basicOpen` / 定理 `mem_basicOpen`

English:
theorem mem_basicOpen
  given: (x : Proj 𝒜)
  proof: Iff.rfl

中文:
定理 mem_basicOpen
  条件: (x : Proj 𝒜)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_basicOpen (x : Proj 𝒜) :
    x in basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

/--
theorem `basicOpen_one` / 定理 `basicOpen_one`

English:
theorem basicOpen_one
  statement: basicOpen 𝒜 1 = ⊤
  proof: ProjectiveSpectrum.basicOpen_one ..

中文:
定理 basicOpen_one
  结论: basicOpen 𝒜 1 = ⊤
  证明: ProjectiveSpectrum.basicOpen_one ..
-/
@[simp] theorem basicOpen_one : basicOpen 𝒜 1 = ⊤ := ProjectiveSpectrum.basicOpen_one ..

/--
theorem `basicOpen_zero` / 定理 `basicOpen_zero`

English:
theorem basicOpen_zero
  statement: basicOpen 𝒜 0 = ⊥
  proof: ProjectiveSpectrum.basicOpen_zero ..

中文:
定理 basicOpen_zero
  结论: basicOpen 𝒜 0 = ⊥
  证明: ProjectiveSpectrum.basicOpen_zero ..
-/
@[simp] theorem basicOpen_zero : basicOpen 𝒜 0 = ⊥ := ProjectiveSpectrum.basicOpen_zero ..

/--
theorem `basicOpen_pow` / 定理 `basicOpen_pow`

English:
theorem basicOpen_pow
  given: (n) (hn : 0 < n)
  statement: basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f
  proof: ProjectiveSpectrum.basicOpen_pow 𝒜 f n hn

中文:
定理 basicOpen_pow
  条件: (n) (hn : 0 < n)
  结论: basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f
  证明: ProjectiveSpectrum.basicOpen_pow 𝒜 f n hn
-/
@[simp] theorem basicOpen_pow (n) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  ProjectiveSpectrum.basicOpen_pow 𝒜 f n hn

/--
theorem `basicOpen_mul` / 定理 `basicOpen_mul`

English:
theorem basicOpen_mul
  statement: basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
  proof: ProjectiveSpectrum.basicOpen_mul ..

中文:
定理 basicOpen_mul
  结论: basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
  证明: ProjectiveSpectrum.basicOpen_mul ..

Depends on / 依赖: ProjectiveSpectrum, ProjectiveSpectrum.basicOpen_mul, basicOpen_mul
-/
theorem basicOpen_mul : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
  ProjectiveSpectrum.basicOpen_mul ..

/--
theorem `basicOpen_mono` / 定理 `basicOpen_mono`

English:
theorem basicOpen_mono
  given: (hfg : f ∣ g)
  statement: basicOpen 𝒜 g <= basicOpen 𝒜 f
  proof: (hfg.choose_spec ▸ basicOpen_mul 𝒜 f _).trans_le inf_le_left

中文:
定理 basicOpen_mono
  条件: (hfg : f ∣ g)
  结论: basicOpen 𝒜 g <= basicOpen 𝒜 f
  证明: (hfg.choose_spec ▸ basicOpen_mul 𝒜 f _).trans_le inf_le_left

Depends on / 依赖: basicOpen_mul, choose_spec, hfg.choose_spec, inf_le_left, trans_le
-/
theorem basicOpen_mono (hfg : f ∣ g) : basicOpen 𝒜 g <= basicOpen 𝒜 f :=
  (hfg.choose_spec ▸ basicOpen_mul 𝒜 f _).trans_le inf_le_left

/--
theorem `basicOpen_eq_iSup_proj` / 定理 `basicOpen_eq_iSup_proj`

English:
theorem basicOpen_eq_iSup_proj
  given: (f : A)
  proof: ProjectiveSpectrum.basicOpen_eq_union_of_projection ..

中文:
定理 basicOpen_eq_iSup_proj
  条件: (f : A)
  证明: ProjectiveSpectrum.basicOpen_eq_union_of_projection ..

Depends on / 依赖: ProjectiveSpectrum, ProjectiveSpectrum.basicOpen_eq_union_of_projection, basicOpen_eq_union_of_projection
-/
theorem basicOpen_eq_iSup_proj (f : A) :
    basicOpen 𝒜 f = ⨆ i : Nat, basicOpen 𝒜 (GradedRing.proj 𝒜 i f) :=
  ProjectiveSpectrum.basicOpen_eq_union_of_projection ..

/--
theorem `isBasis_basicOpen` / 定理 `isBasis_basicOpen`

English:
theorem isBasis_basicOpen
  proof: by
  delta TopologicalSpace.Opens.IsBasis
  convert! ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜
  exact (Set.range_comp _ _).symm

中文:
定理 isBasis_basicOpen
  证明: by
  delta TopologicalSpace.Opens.IsBasis
  convert! ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜
  exact (Set.range_comp _ _).symm

Depends on / 依赖: IsBasis, ProjectiveSpectrum, ProjectiveSpectrum.isTopologicalBasis_basic_opens, Set.range_comp, TopologicalSpace, TopologicalSpace.Opens.IsBasis, convert, isTopologicalBasis_basic_opens, range_comp
-/
theorem isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (basicOpen 𝒜)) := by
  delta TopologicalSpace.Opens.IsBasis
  convert! ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜
  exact (Set.range_comp _ _).symm

/--
lemma `iSup_basicOpen_eq_top` / 引理 `iSup_basicOpen_eq_top`

English:
lemma iSup_basicOpen_eq_top
  statement: {ι : Type*} (f : ι -> A)
  proof: by
  classical
  refine top_le_iff.mp fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  rwa [Ideal.span_le, Set.range_subset_iff]

中文:
引理 iSup_basicOpen_eq_top
  结论: {ι : 类型} (f : ι -> A)
  证明: by
  classical
  refine top_le_iff.mp fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  rwa [Ideal.span_le, Set.range_subset_iff]

Depends on / 依赖: Decidable, Decidable.not_not, Ideal.span_le, Set.range_subset_iff, TopologicalSpace, TopologicalSpace.Opens.mem_iSup.mpr, classical, hf.trans, mem_basicOpen, mem_iSup, not_irrelevant_le, not_not, range_subset_iff, span_le, top_le_iff, top_le_iff.mp, x.not_irrelevant_le
-/
lemma iSup_basicOpen_eq_top {ι : Type*} (f : ι -> A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal <= Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  refine top_le_iff.mp fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_contra! H
  simp only [mem_basicOpen, Decidable.not_not] at H
  refine x.not_irrelevant_le (hf.trans ?_)
  rwa [Ideal.span_le, Set.range_subset_iff]

/--
lemma `iSup_basicOpen_eq_top'` / 引理 `iSup_basicOpen_eq_top'`

English:
lemma iSup_basicOpen_eq_top'
  statement: {ι : Type*} (f : ι -> A)
  proof: by
  apply Proj.iSup_basicOpen_eq_top
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x in _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x in $hf)).mpr trivial

中文:
引理 iSup_basicOpen_eq_top'
  结论: {ι : 类型} (f : ι -> A)
  证明: by
  apply Proj.iSup_basicOpen_eq_top
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x in _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x in $hf)).mpr trivial

Depends on / 依赖: Algebra, Algebra.adjoin_induction, DirectSum, DirectSum.decompose_of_mem_same, GradedRing, GradedRing.projZeroRingHom, GradedRing.projZeroRingHom_apply, GradedRing.proj_apply, HomogeneousIdeal, HomogeneousIdeal.mem_irrelevant_iff, Proj.iSup_basicOpen_eq_top, adjoin_induction, convert_to, decompose_of_mem_same, eq_iff_iff, eq_iff_iff.mp, iSup_basicOpen_eq_top, mem_irrelevant_iff, projZeroRingHom, projZeroRingHom_apply
-/
lemma iSup_basicOpen_eq_top' {ι : Type*} (f : ι -> A)
    (hfn : forall i, exists n, f i in 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x in _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x in $hf)).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hfn i
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    convert! zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add]; rw [add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert!
      add_mem (Ideal.mul_mem_left _ x hy')
        (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
    rw [map_mul]
    ring

/--
Definition of `awayToSection` / `awayToSection` 的定义

English:
definition awayToSection
  signature: : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f)
  body: ProjectiveSpectrum.Proj.awayToSection ..

中文:
定义 awayToSection
  签名: : 交换环范畴.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f)
  定义体: ProjectiveSpectrum.Proj.awayToSection ..

Depends on / 依赖: ProjectiveSpectrum, ProjectiveSpectrum.Proj.awayToSection, awayToSection
-/
def awayToSection : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  ProjectiveSpectrum.Proj.awayToSection ..

/-- The canonical map `Proj A |_ D₊(f) ⟶ Spec (A_f)₀`.
This is an isomorphism when `f` is homogeneous of positive degree. See `basicOpenIsoSpec` below. -/
noncomputable
/--
Definition of `basicOpenToSpec` / `basicOpenToSpec` 的定义

English:
definition basicOpenToSpec
  signature: : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f)
  body: (basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)

中文:
定义 basicOpenToSpec
  签名: : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f)
  定义体: (basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)

Depends on / 依赖: Spec.map, awayToSection, basicOpen
-/
def basicOpenToSpec : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f) :=
  (basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `basicOpenToSpec_app_top` / 引理 `basicOpenToSpec_app_top`

English:
lemma basicOpenToSpec_app_top
  proof: by
  simp [basicOpenToSpec, Scheme.Opens.toSpecΓ_appTop]

中文:
引理 basicOpenToSpec_app_top
  证明: by
  simp [basicOpenToSpec, Scheme.Opens.toSpecΓ_appTop]

Depends on / 依赖: Scheme, Scheme.Opens.toSpec, basicOpenToSpec
-/
lemma basicOpenToSpec_app_top :
    (basicOpenToSpec 𝒜 f).app ⊤ = (Scheme.ΓSpecIso _).hom ≫ awayToSection 𝒜 f ≫
      (basicOpen 𝒜 f).topIso.inv := by
  simp [basicOpenToSpec, Scheme.Opens.toSpecΓ_appTop]

/-- The structure map `Proj A ⟶ Spec A₀`. -/
noncomputable
/--
Definition of `toSpecZero` / `toSpecZero` 的定义

English:
definition toSpecZero
  signature: : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0)
  body: (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))

中文:
定义 toSpecZero
  签名: : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0)
  定义体: (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Scheme, Scheme.isoOfEq, Scheme.topIso, Spec.map, basicOpenToSpec, basicOpen_one, fromZeroRingHom, isoOfEq, topIso
-/
def toSpecZero : Proj 𝒜 ⟶ Spec (.of <| 𝒜 0) :=
  (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (basicOpen_one _)).inv ≫
    basicOpenToSpec 𝒜 1 ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))

variable {m} (f_deg : f in 𝒜 m) (hm : 0 < m)

/-- The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
when `f` is homogeneous of positive degree. -/
@[simps! -isSimp hom]
noncomputable
/--
Definition of `basicOpenIsoSpec` / `basicOpenIsoSpec` 的定义

English:
definition basicOpenIsoSpec
  signature: : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f)
  body: have : IsIso (basicOpenToSpec 𝒜 f) := by
    apply (isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_
    convert! ProjectiveSpectrum.Proj.isIso_toSpec 𝒜 f f_deg hm using 1
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [basicOpenTo

中文:
定义 basicOpenIsoSpec
  签名: : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f)
  定义体: have : IsIso (basicOpenToSpec 𝒜 f) := by
    apply (isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_
    convert! ProjectiveSpectrum.Proj.isIso_toSpec 𝒜 f f_deg hm using 1
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [basicOpenTo

Depends on / 依赖: Category, Category.assoc, Eq.trans, ProjectiveSpectrum, ProjectiveSpectrum.Proj.isIso_toSpec, Scheme, Scheme.Opens.toSpec, Scheme.forgetToLocallyRingedSpace, Spec.locallyRingedSpaceAdjunction.homEquiv_apply, Spec.map_comp, basicOpenToSpec, convert, f_deg, forgetToLocallyRingedSpace, homEquiv_apply, isIso_iff_of_reflects_iso, isIso_toSpec, locallyRingedSpaceAdjunction, map_comp
-/
def basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f) :=
  have : IsIso (basicOpenToSpec 𝒜 f) := by
    apply (isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_
    convert! ProjectiveSpectrum.Proj.isIso_toSpec 𝒜 f f_deg hm using 1
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  asIso (basicOpenToSpec 𝒜 f)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `(A_f)₀ ≅ Γ(Proj A, D₊(f))`
when `f` is homogeneous of positive degree. -/
@[simps! -isSimp hom]
noncomputable
/--
Definition of `basicOpenIsoAway` / `basicOpenIsoAway` 的定义

English:
definition basicOpenIsoAway
  signature: : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)
  body: have : IsIso (awayToSection 𝒜 f) := by
    have := basicOpenToSpec_app_top 𝒜 f
    rw [← Iso.inv_comp_eq]; rw [Iso.eq_comp_inv] at this
    rw [← this]; rw [← basicOpenIsoSpec_hom 𝒜 f f_deg hm]
    infer_instance
  asIso (awayToSection 𝒜 f)

中文:
定义 basicOpenIsoAway
  签名: : 交换环范畴.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)
  定义体: have : IsIso (awayToSection 𝒜 f) := by
    have := basicOpenToSpec_app_top 𝒜 f
    rw [← Iso.inv_comp_eq]; rw [Iso.eq_comp_inv] at this
    rw [← this]; rw [← basicOpenIsoSpec_hom 𝒜 f f_deg hm]
    infer_instance
  asIso (awayToSection 𝒜 f)

Depends on / 依赖: Iso.eq_comp_inv, Iso.inv_comp_eq, awayToSection, basicOpenIsoSpec_hom, basicOpenToSpec_app_top, eq_comp_inv, f_deg, infer_instance, inv_comp_eq
-/
def basicOpenIsoAway : CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f) :=
  have : IsIso (awayToSection 𝒜 f) := by
    have := basicOpenToSpec_app_top 𝒜 f
    rw [← Iso.inv_comp_eq]; rw [Iso.eq_comp_inv] at this
    rw [← this]; rw [← basicOpenIsoSpec_hom 𝒜 f f_deg hm]
    infer_instance
  asIso (awayToSection 𝒜 f)

/-- The open immersion `Spec (A_f)₀ ⟶ Proj A`. -/
noncomputable
/--
Definition of `awayι` / `awayι` 的定义

English:
definition awayι
  signature: : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜
  body: (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι

@[reassoc]

中文:
定义 awayι
  签名: : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜
  定义体: (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι

@[reassoc]

Depends on / 依赖: Proj.basicOpen, basicOpen, basicOpenIsoSpec, f_deg
-/
def awayι : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜 :=
  (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι

@[reassoc]
/--
lemma `basicOpenIsoSpec_inv_ι` / 引理 `basicOpenIsoSpec_inv_ι`

English:
lemma basicOpenIsoSpec_inv_ι
  proof: rfl

中文:
引理 basicOpenIsoSpec_inv_ι
  证明: rfl
-/
lemma basicOpenIsoSpec_inv_ι :
    (basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι = awayι 𝒜 f f_deg hm := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm)
  body: IsOpenImmersion.comp _ _

中文:
实例 :
  签名: 是开浸入 (Proj.awayι 𝒜 f f_deg hm)
  定义体: IsOpenImmersion.comp _ _

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.comp
-/
instance : IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) :=
  IsOpenImmersion.comp _ _

/--
lemma `opensRange_awayι` / 引理 `opensRange_awayι`

English:
lemma opensRange_awayι
  proof: (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (basicOpen 𝒜 f).opensRange_ι

include f_deg hm in

中文:
引理 opensRange_awayι
  证明: (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (basicOpen 𝒜 f).opensRange_ι

include f_deg hm in

Depends on / 依赖: Scheme, Scheme.Hom.opensRange_comp_of_isIso, basicOpen, opensRange_comp_of_isIso
-/
lemma opensRange_awayι :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (basicOpen 𝒜 f).opensRange_ι

include f_deg hm in
/--
lemma `isAffineOpen_basicOpen` / 引理 `isAffineOpen_basicOpen`

English:
lemma isAffineOpen_basicOpen
  statement: IsAffineOpen (basicOpen 𝒜 f)
  proof: by
  rw [← opensRange_awayι 𝒜 f f_deg hm]
  exact isAffineOpen_opensRange (awayι _ _ _ _)

@[reassoc]

中文:
引理 isAffineOpen_basicOpen
  结论: 是仿射开集 (basicOpen 𝒜 f)
  证明: by
  rw [← opensRange_awayι 𝒜 f f_deg hm]
  exact isAffineOpen_opensRange (awayι _ _ _ _)

@[reassoc]

Depends on / 依赖: f_deg, isAffineOpen_opensRange
-/
lemma isAffineOpen_basicOpen : IsAffineOpen (basicOpen 𝒜 f) := by
  rw [← opensRange_awayι 𝒜 f f_deg hm]
  exact isAffineOpen_opensRange (awayι _ _ _ _)

@[reassoc]
/--
lemma `awayι_toSpecZero` / 引理 `awayι_toSpecZero`

English:
lemma awayι_toSpecZero
  statement: awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
  proof: by
  rw [toSpecZero]; rw [basicOpenToSpec]; rw [awayι]
  simp only [Category.assoc, Iso.inv_comp_eq, basicOpenIsoSpec_hom]
  have (U) (e : U = ⊤) : (basicOpen 𝒜 f).ι ≫ (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e).inv =
      Scheme.homOfLE _ (le_top.trans_eq e.symm) := by
    simp only [← Category.a

中文:
引理 awayι_toSpecZero
  结论: awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
  证明: by
  rw [toSpecZero]; rw [basicOpenToSpec]; rw [awayι]
  simp only [Category.assoc, Iso.inv_comp_eq, basicOpenIsoSpec_hom]
  have (U) (e : U = ⊤) : (basicOpen 𝒜 f).ι ≫ (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e).inv =
      Scheme.homOfLE _ (le_top.trans_eq e.symm) := by
    simp only [← Category.a

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.inv_comp_eq, Scheme, Scheme.Opens.toSpec, Scheme.homOfLE, Scheme.homOfLE_, Scheme.isoOfEq, Scheme.isoOfEq_hom_, Scheme.topIso, Scheme.topIso_hom, basicOpen, basicOpenIsoSpec_hom, basicOpenToSpec, comp_inv_eq, e.symm, homOfLE, inv_comp_eq, isoOfEq
-/
lemma awayι_toSpecZero : awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
    Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
  rw [toSpecZero]; rw [basicOpenToSpec]; rw [awayι]
  simp only [Category.assoc, Iso.inv_comp_eq, basicOpenIsoSpec_hom]
  have (U) (e : U = ⊤) : (basicOpen 𝒜 f).ι ≫ (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e).inv =
      Scheme.homOfLE _ (le_top.trans_eq e.symm) := by
    simp only [← Category.assoc, Iso.comp_inv_eq]
    simp only [Scheme.topIso_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
  rw [reassoc_of% this]; rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]; rw [basicOpenToSpec]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [← Spec.map_comp]; rw [← Spec.map_comp]
  rfl

variable {f}
variable {m' : Nat} {g : A} (g_deg : g in 𝒜 m') (hm' : 0 < m') {x : A} (hx : x = f * g)

@[reassoc]
/--
lemma `awayMap_awayToSection` / 引理 `awayMap_awayToSection`

English:
lemma awayMap_awayToSection
  proof: by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [CommRingCat.hom_ofHom]; rw [val_awayMa

中文:
引理 awayMap_awayToSection
  证明: by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [CommRingCat.hom_ofHom]; rw [val_awayMa

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, CommRingCat.hom_ofHom, Function, Function.comp_apply, IsLocalization, IsLocalization.map_mk, Localization, Localization.mk_eq_mk, Localization.mk_eq_mk_iff.mpr, Localization.r_iff_exists, ProjectiveSpectrum, ProjectiveSpectrum.Proj.awayToSection_apply, RingHom, RingHom.coe_comp, Subtype, Subtype.ext, awayToSection_apply, coe_comp, comp_apply
-/
lemma awayMap_awayToSection :
    CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ awayToSection 𝒜 x =
      awayToSection 𝒜 f ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩)).op := by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [CommRingCat.hom_ofHom]; rw [val_awayMap_mk]; rw [Localization.mk_eq_mk']; rw [IsLocalization.map_mk']; rw [← Localization.mk_eq_mk']
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp [hx]
  ring

@[reassoc]
/--
lemma `basicOpenToSpec_SpecMap_awayMap` / 引理 `basicOpenToSpec_SpecMap_awayMap`

English:
lemma basicOpenToSpec_SpecMap_awayMap
  proof: by
  rw [basicOpenToSpec]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [awayMap_awayToSection]; rw [Spec.map_comp]; rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

@[reassoc]

中文:
引理 basicOpenToSpec_SpecMap_awayMap
  证明: by
  rw [basicOpenToSpec]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [awayMap_awayToSection]; rw [Spec.map_comp]; rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Scheme, Scheme.Opens.toSpec, Spec.map_comp, awayMap_awayToSection, basicOpenToSpec, map_comp
-/
lemma basicOpenToSpec_SpecMap_awayMap :
    basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) =
      (Proj 𝒜).homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩) ≫ basicOpenToSpec 𝒜 f := by
  rw [basicOpenToSpec]; rw [Category.assoc]; rw [← Spec.map_comp]; rw [awayMap_awayToSection]; rw [Spec.map_comp]; rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  rfl

@[reassoc]
/--
lemma `SpecMap_awayMap_awayι` / 引理 `SpecMap_awayMap_awayι`

English:
lemma SpecMap_awayMap_awayι
  proof: by
  rw [awayι]; rw [awayι]; rw [Iso.eq_inv_comp]; rw [basicOpenIsoSpec_hom]; rw [basicOpenToSpec_SpecMap_awayMap_assoc]; rw [← basicOpenIsoSpec_hom _ _ f_deg hm]; rw [Iso.hom_inv_id_assoc]; rw [Scheme.homOfLE_ι]

中文:
引理 SpecMap_awayMap_awayι
  证明: by
  rw [awayι]; rw [awayι]; rw [Iso.eq_inv_comp]; rw [basicOpenIsoSpec_hom]; rw [basicOpenToSpec_SpecMap_awayMap_assoc]; rw [← basicOpenIsoSpec_hom _ _ f_deg hm]; rw [Iso.hom_inv_id_assoc]; rw [Scheme.homOfLE_ι]

Depends on / 依赖: Iso.eq_inv_comp, Iso.hom_inv_id_assoc, Scheme, Scheme.homOfLE_, basicOpenIsoSpec_hom, basicOpenToSpec_SpecMap_awayMap_assoc, eq_inv_comp, f_deg, hom_inv_id_assoc
-/
lemma SpecMap_awayMap_awayι :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫ awayι 𝒜 f f_deg hm =
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) := by
  rw [awayι]; rw [awayι]; rw [Iso.eq_inv_comp]; rw [basicOpenIsoSpec_hom]; rw [basicOpenToSpec_SpecMap_awayMap_assoc]; rw [← basicOpenIsoSpec_hom _ _ f_deg hm]; rw [Iso.hom_inv_id_assoc]; rw [Scheme.homOfLE_ι]

/-- The isomorphism `D₊(f) ×[Proj 𝒜] D₊(g) ≅ D₊(fg)`. -/
noncomputable
/--
Definition of `pullbackAwayιIso` / `pullbackAwayιIso` 的定义

English:
definition pullbackAwayιIso
  signature: :
  body: IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
(awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  change ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜

中文:
定义 pullbackAwayιIso
  签名: :
  定义体: IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
(awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  change ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsOpenImmersion.range_pullback_to_base_of_left, Limits, Limits.pullback.fst, SetLike, SetLike.mul_mem_graded, basicOpen_mul, f_deg, g_deg, hm.trans_le, isoOfRangeEq, le_add_right, m.le_add_right, mul_mem_graded, opensRange, pullback, range_pullback_to_base_of_left, trans_le
-/
def pullbackAwayιIso :
    Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅ Spec (.of <| Away 𝒜 x) :=
    IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
(awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  change ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜 _ _ _).opensRange.1
  rw [opensRange_awayι]; rw [opensRange_awayι]; rw [opensRange_awayι]; rw [← basicOpen_mul]; rw [hx]

@[reassoc (attr := simp)]
/--
lemma `pullbackAwayιIso_hom_awayι` / 引理 `pullbackAwayιIso_hom_awayι`

English:
lemma pullbackAwayιIso_hom_awayι
  proof: IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]

中文:
引理 pullbackAwayιIso_hom_awayι
  证明: IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_hom_fac, isoOfRangeEq_hom_fac
-/
lemma pullbackAwayιIso_hom_awayι :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) =
      Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]
/--
lemma `pullbackAwayιIso_hom_SpecMap_awayMap_left` / 引理 `pullbackAwayιIso_hom_SpecMap_awayMap_left`

English:
lemma pullbackAwayιIso_hom_SpecMap_awayMap_left
  proof: by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm)]; rw [← pullbackAwayιIso_hom_awayι]; rw [Category.assoc]; rw [SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]

中文:
引理 pullbackAwayιIso_hom_SpecMap_awayMap_left
  证明: by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm)]; rw [← pullbackAwayιIso_hom_awayι]; rw [Category.assoc]; rw [SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, cancel_mono, f_deg
-/
lemma pullbackAwayιIso_hom_SpecMap_awayMap_left :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) = Limits.pullback.fst _ _ := by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm)]; rw [← pullbackAwayιIso_hom_awayι]; rw [Category.assoc]; rw [SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]
/--
lemma `pullbackAwayιIso_hom_SpecMap_awayMap_right` / 引理 `pullbackAwayιIso_hom_SpecMap_awayMap_right`

English:
lemma pullbackAwayιIso_hom_SpecMap_awayMap_right
  proof: by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm')]; rw [← Limits.pullback.condition]; rw [← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx]; rw [Category.assoc]; rw [SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]

中文:
引理 pullbackAwayιIso_hom_SpecMap_awayMap_right
  证明: by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm')]; rw [← Limits.pullback.condition]; rw [← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx]; rw [Category.assoc]; rw [SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Limits, Limits.pullback.condition, cancel_mono, condition, f_deg, g_deg, pullback
-/
lemma pullbackAwayιIso_hom_SpecMap_awayMap_right :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) =
      Limits.pullback.snd _ _ := by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm')]; rw [← Limits.pullback.condition]; rw [← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx]; rw [Category.assoc]; rw [SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]
/--
lemma `pullbackAwayιIso_inv_fst` / 引理 `pullbackAwayιIso_inv_fst`

English:
lemma pullbackAwayιIso_inv_fst
  proof: by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left]; rw [Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]

中文:
引理 pullbackAwayιIso_inv_fst
  证明: by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left]; rw [Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id_assoc, inv_hom_id_assoc
-/
lemma pullbackAwayιIso_inv_fst :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left]; rw [Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `pullbackAwayιIso_inv_snd` / 引理 `pullbackAwayιIso_inv_snd`

English:
lemma pullbackAwayιIso_inv_snd
  proof: by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right (hx := hx) ..]; rw [Iso.inv_hom_id_assoc]

include hm' in

中文:
引理 pullbackAwayιIso_inv_snd
  证明: by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right (hx := hx) ..]; rw [Iso.inv_hom_id_assoc]

include hm' in

Depends on / 依赖: Iso.inv_hom_id_assoc, inv_hom_id_assoc
-/
lemma pullbackAwayιIso_inv_snd :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right (hx := hx) ..]; rw [Iso.inv_hom_id_assoc]

include hm' in
/--
lemma `awayι_preimage_basicOpen` / 引理 `awayι_preimage_basicOpen`

English:
lemma awayι_preimage_basicOpen
  proof: by
  ext1
  trans Set.range (Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg rfl)))
  · rw [← pullbackAwayιIso_inv_fst 𝒜 f_deg hm g_deg hm' rfl]
    simp only [TopologicalSpace.Opens.map_coe, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [Set.range_eq_univ.

中文:
引理 awayι_preimage_basicOpen
  证明: by
  ext1
  trans Set.range (Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg rfl)))
  · rw [← pullbackAwayιIso_inv_fst 𝒜 f_deg hm g_deg hm' rfl]
    simp only [TopologicalSpace.Opens.map_coe, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [Set.range_eq_univ.

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, ContinuousMap, ContinuousMap.coe_comp, IsOpenImmersion, IsOpenImmersion.range_pullbackFst, Scheme, Scheme.Hom.comp_base, Set.range, Set.range_comp, Set.range_eq_univ.mpr, Spec.map, TopCat, TopCat.hom_comp, TopologicalSpace, TopologicalSpace.Opens.map_coe, awayMap, coe_comp, comp_base, f_deg
-/
lemma awayι_preimage_basicOpen :
    awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 g =
      PrimeSpectrum.basicOpen (Away.isLocalizationElem f_deg g_deg) := by
  ext1
  trans Set.range (Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg rfl)))
  · rw [← pullbackAwayιIso_inv_fst 𝒜 f_deg hm g_deg hm' rfl]
    simp only [TopologicalSpace.Opens.map_coe, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [Set.range_eq_univ.mpr (by exact
      (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' rfl).inv.homeomorph.surjective)]; rw [← opensRange_awayι _ _ g_deg hm']
    simp [IsOpenImmersion.range_pullbackFst]
  · let := (awayMap (f := f) 𝒜 g_deg rfl).toAlgebra
    let := HomogeneousLocalization.Away.isLocalization_mul f_deg g_deg rfl hm.ne'
    exact PrimeSpectrum.localization_away_comap_range _ _

open TopologicalSpace.Opens in
/-- Given a family of homogeneous elements `f` of positive degree that spans the irrelevant ideal,
`Spec (A_f)₀ ⟶ Proj A` forms an affine open cover of `Proj A`. -/
noncomputable
/--
Definition of `affineOpenCoverOfIrrelevantLESpan` / `affineOpenCoverOfIrrelevantLESpan` 的定义

English:
definition affineOpenCoverOfIrrelevantLESpan
  signature: {ι : Type*} (f : ι -> A) {m : ι -> Nat}
  body: ι
  X i := .of (Away 𝒜 (f i))
  f i := awayι 𝒜 (f i) (f_deg i) (hm i)
  idx x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
  covers x := by
    change x in (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (

中文:
定义 affineOpenCoverOfIrrelevantLESpan
  签名: {ι : 类型} (f : ι -> A) {m : ι -> 自然数}
  定义体: ι
  X i := .of (Away 𝒜 (f i))
  f i := awayι 𝒜 (f i) (f_deg i) (hm i)
  idx x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
  covers x := by
    change x in (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (
-/
def affineOpenCoverOfIrrelevantLESpan {ι : Type*} (f : ι -> A) {m : ι -> Nat}
    (f_deg : forall i, f i in 𝒜 (m i)) (hm : forall i, 0 < m i)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal <= Ideal.span (Set.range f)) :
    (Proj 𝒜).AffineOpenCover where
  I₀ := ι
  X i := .of (Away 𝒜 (f i))
  f i := awayι 𝒜 (f i) (f_deg i) (hm i)
  idx x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
  covers x := by
    change x in (awayι 𝒜 _ _ _).opensRange
    rw [opensRange_awayι]
    exact (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose_spec

/-- `Proj A` is covered by `Spec (A_f)₀` for all homogeneous elements of positive degree. -/
@[simps! f] noncomputable
/--
Definition of `affineOpenCover` / `affineOpenCover` 的定义

English:
definition affineOpenCover
  signature: : (Proj 𝒜).AffineOpenCover
  body: affineOpenCoverOfIrrelevantLESpan 𝒜
(ι := Σ i : PNat, 𝒜 i) (m := fun i => i.1) (fun i => i.2) (fun i => i.2.2) (fun i => i.1.2) by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc => if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.po

中文:
定义 affineOpenCover
  签名: : (Proj 𝒜).AffineOpenCover
  定义体: affineOpenCoverOfIrrelevantLESpan 𝒜
(ι := Σ i : PNat, 𝒜 i) (m := fun i => i.1) (fun i => i.2) (fun i => i.2.2) (fun i => i.1.2) by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc => if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.po

Depends on / 依赖: DirectSum, DirectSum.sum_support_decompose, Ideal.subset_span, Ideal.sum_mem, Ideal.zero_mem, Nat.pos_iff_ne_zero.mpr, affineOpenCoverOfIrrelevantLESpan, classical, convert, pos_iff_ne_zero, subset_span, sum_mem, sum_support_decompose, zero_mem
-/
def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan 𝒜
(ι := Σ i : PNat, 𝒜 i) (m := fun i => i.1) (fun i => i.2) (fun i => i.2.2) (fun i => i.1.2) by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc => if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
  convert! Ideal.zero_mem _
  subst hc0
  exact hz

end basicOpen

section stalk

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`. -/
noncomputable
/--
Definition of `stalkIso` / `stalkIso` 的定义

English:
definition stalkIso
  signature: (x : Proj 𝒜)
  body: (stalkIso' 𝒜 x).toCommRingCatIso

中文:
定义 stalkIso
  签名: (x : Proj 𝒜)
  定义体: (stalkIso' 𝒜 x).toCommRingCatIso

Depends on / 依赖: stalkIso, toCommRingCatIso
-/
def stalkIso (x : Proj 𝒜) :
    (Proj 𝒜).presheaf.stalk x ≅ .of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
  (stalkIso' 𝒜 x).toCommRingCatIso

end stalk

noncomputable section ofGlobalSection

open Limits

variable {X : Scheme.{u}} (f : A ->+* Γ(X, ⊤)) {x x' : Γ(X, ⊤)} {t t' : A} {d d' : Nat}

/--
Definition of `toBasicOpenOfGlobalSections` / `toBasicOpenOfGlobalSections` 的定义

English:
definition toBasicOpenOfGlobalSections
  signature: (H : f t = x) (h0d : 0 < d) (hd : t in 𝒜 d)
  body: by
  refine ?_ ≫ (basicOpenIsoSpec _ _ hd h0d).inv
  refine (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ _ ≫ ?_
  refine (basicOpenIsoSpecAway _).hom ≫
    Spec.map (CommRingCat.ofHom (RingHom.comp ?_ (algebraMap _ (Localization.Away t))))
  refine IsLocalization.map (M := .powers

中文:
定义 toBasicOpenOfGlobalSections
  签名: (H : f t = x) (h0d : 0 < d) (hd : t in 𝒜 d)
  定义体: by
  refine ?_ ≫ (basicOpenIsoSpec _ _ hd h0d).inv
  refine (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ _ ≫ ?_
  refine (basicOpenIsoSpecAway _).hom ≫
    Spec.map (CommRingCat.ofHom (RingHom.comp ?_ (algebraMap _ (Localization.Away t))))
  refine IsLocalization.map (M := .powers

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalization, IsLocalization.map, Localization, Localization.Away, RingHom, RingHom.comp, Spec.map, Submonoid, Submonoid.map_le_iff_le_comap, Submonoid.map_powers, X.isoOfEq, X.toSpec, algebraMap, basicOpenIsoSpec, basicOpenIsoSpecAway, isoOfEq, map_le_iff_le_comap, map_powers
-/
def toBasicOpenOfGlobalSections (H : f t = x) (h0d : 0 < d) (hd : t in 𝒜 d) :
    (X.basicOpen x).toScheme ⟶ basicOpen 𝒜 t := by
  refine ?_ ≫ (basicOpenIsoSpec _ _ hd h0d).inv
  refine (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ _ ≫ ?_
  refine (basicOpenIsoSpecAway _).hom ≫
    Spec.map (CommRingCat.ofHom (RingHom.comp ?_ (algebraMap _ (Localization.Away t))))
  refine IsLocalization.map (M := .powers t) (T := .powers x) _ f ?_
  · rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
    simp [H]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `homOfLE_toBasicOpenOfGlobalSections_ι` / 引理 `homOfLE_toBasicOpenOfGlobalSections_ι`

English:
lemma homOfLE_toBasicOpenOfGlobalSections_ι
  proof: by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, basicOpenIsoSpec_inv_ι]
  have hx'x : PrimeSpectrum.basicOpen x' <= PrimeSpectrum.basicOpen x := by
    

中文:
引理 homOfLE_toBasicOpenOfGlobalSections_ι
  证明: by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, basicOpenIsoSpec_inv_ι]
  have hx'x : PrimeSpectrum.basicOpen x' <= PrimeSpectrum.basicOpen x := by
    

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.ofHom_comp, Iso.inv_comp_eq, PrimeSpectrum, PrimeSpectrum.basicOpen, PrimeSpectrum.basicOpen_mul, Scheme, Scheme.Hom.map_resLE_assoc, Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_map_assoc, Scheme.isoOfEq_inv, Spec.map_comp, X.toSpec, basicOpen, basicOpen_mul, inv_comp_eq, isoOfEq_inv, map_comp
-/
lemma homOfLE_toBasicOpenOfGlobalSections_ι
    {H : f t = x} {h0d : 0 < d} {hd : t in 𝒜 d} {H' : f t' = x'} {h0d' : 0 < d'} {hd' : t' in 𝒜 d'}
    {s : A} (hts : t * s = t') {n : Nat} (hn : d + n = d') (hs : s in 𝒜 n) :
    X.homOfLE (by aesop) ≫ toBasicOpenOfGlobalSections 𝒜 f H h0d hd ≫ (basicOpen 𝒜 t).ι =
      toBasicOpenOfGlobalSections 𝒜 f H' h0d' hd' ≫ (basicOpen 𝒜 t').ι := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, CommRingCat.ofHom_comp, Spec.map_comp,
    Scheme.Hom.map_resLE_assoc, Category.assoc, basicOpenIsoSpec_inv_ι]
  have hx'x : PrimeSpectrum.basicOpen x' <= PrimeSpectrum.basicOpen x := by
    aesop (add simp PrimeSpectrum.basicOpen_mul)
  rw [← Scheme.Hom.resLE_map_assoc _ (by simp [X.toSpecΓ_preimage_basicOpen]) hx'x]
  congr 1
  simp only [← Iso.inv_comp_eq]
  subst hts hn
  rw [← SpecMap_awayMap_awayι (𝒜 := 𝒜) hd h0d
    hs rfl]; rw [basicOpenIsoSpecAway_inv_homOfLE_assoc (R := Γ(X]; rw [⊤)) x (f s) x' (by simp [← H']; rw [H]),
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_awayMap]
  simp only [← RingHom.comp_apply]
  congr 1
  apply IsLocalization.ringHom_ext (M := .powers t)
  ext i
  simp [IsLocalization.Away.awayToAwayRight_eq]

variable (f : A ->+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `openCoverOfMapIrrelevantEqTop` / `openCoverOfMapIrrelevantEqTop` 的定义

English:
definition openCoverOfMapIrrelevantEqTop
  signature: : X.OpenCover
  body: X.openCoverOfIsOpenCover (fun ir : Σ' i r, 0 < i ∧ r in 𝒜 i =>
    X.basicOpen (f ir.2.1)) (by
    classical
    have H : Ideal.span (Set.range fun x : Σ' i r, 0 < i ∧ r in 𝒜 i => x.2.1) =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.ra

中文:
定义 openCoverOfMapIrrelevantEqTop
  签名: : X.OpenCover
  定义体: X.openCoverOfIsOpenCover (fun ir : Σ' i r, 0 < i ∧ r in 𝒜 i =>
    X.basicOpen (f ir.2.1)) (by
    classical
    have H : Ideal.span (Set.range fun x : Σ' i r, 0 < i ∧ r in 𝒜 i => x.2.1) =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.ra

Depends on / 依赖: DirectSum, DirectSum.decompose_of_mem_ne, DirectSum.sum_support_decompose, HomogeneousIdeal, HomogeneousIdeal.irrelevant, Ideal.span, Ideal.span_le, Ideal.sum_mem, Set.range, Set.range_subset_iff, X.basicOpen, X.openCoverOfIsOpenCover, ZeroMemClass, ZeroMemClass.coe_eq_zero, basicOpen, classical, coe_eq_zero, decompose_of_mem_ne, hi0.ne, irrelevant
-/
def openCoverOfMapIrrelevantEqTop : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun ir : Σ' i r, 0 < i ∧ r in 𝒜 i =>
    X.basicOpen (f ir.2.1)) (by
    classical
    have H : Ideal.span (Set.range fun x : Σ' i r, 0 < i ∧ r in 𝒜 i => x.2.1) =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.range_subset_iff]
        rintro ⟨i, r, hi0, hri⟩
        simp [-ZeroMemClass.coe_eq_zero,
          DirectSum.decompose_of_mem_ne 𝒜 hri hi0.ne']
      · intro x hx
        rw [← DirectSum.sum_support_decompose 𝒜 x]
        refine Ideal.sum_mem _ fun c hc => ?_
        have : c != 0 := by contrapose hc; simpa [hc] using hx
        exact Ideal.subset_span ⟨⟨c, _, this.bot_lt, by simp⟩, rfl⟩
    ext1
    apply compl_injective
    simp only [TopologicalSpace.Opens.coe_iSup, Set.compl_iUnion, ← Scheme.zeroLocus_singleton,
      ← Scheme.zeroLocus_iUnion, Set.iUnion_singleton_eq_range, TopologicalSpace.Opens.coe_top,
      Set.compl_univ]
    rw [← Scheme.zeroLocus_span]; rw [Set.range_comp']; rw [← Ideal.map_span]; rw [H]; rw [hf]
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fromOfGlobalSections` / `fromOfGlobalSections` 的定义

English:
definition fromOfGlobalSections
  signature: : X ⟶ Proj 𝒜
  body: by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).glueMorphisms
    (fun ri => toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f x)
      ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f y) ≅ (X.basicOpen 

中文:
定义 fromOfGlobalSections
  签名: : X ⟶ Proj 𝒜
  定义体: by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).glueMorphisms
    (fun ri => toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f x)
      ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f y) ≅ (X.basicOpen 

Depends on / 依赖: Nat.add_pos_left, Scheme, Scheme.Opens, SetLike, SetLike.mul_mem_gra, X.basicOpen, X.isoOfEq, add_pos_left, basicOpen, cancel_epi, e.inv, glueMorphisms, isPullback_opens_inf, isoOfEq, isoPullback, isoPullback.symm, mul_mem_gra, openCoverOfMapIrrelevantEqTop, pullback, toBasicOpenOfGlobalSections
-/
def fromOfGlobalSections : X ⟶ Proj 𝒜 := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).glueMorphisms
    (fun ri => toBasicOpenOfGlobalSections 𝒜 f rfl ri.2.2.1 ri.2.2.2 ≫ Scheme.Opens.ι _) ?_
  rintro x y
  let e : pullback ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f x)
      ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f y) ≅ (X.basicOpen (f (x.snd.fst * y.snd.fst))) :=
    (isPullback_opens_inf _ _).isoPullback.symm ≪≫ X.isoOfEq (by simp)
  rw [← cancel_epi e.inv]
  trans toBasicOpenOfGlobalSections 𝒜 f rfl (Nat.add_pos_left x.2.2.1 y.1)
    (SetLike.mul_mem_graded x.2.2.2 y.2.2.2) ≫ (Scheme.Opens.ι _)
  · simpa [e, openCoverOfMapIrrelevantEqTop, Scheme.isoOfEq_inv] using
      homOfLE_toBasicOpenOfGlobalSections_ι _ _ rfl rfl y.2.2.2
  · simpa [e, openCoverOfMapIrrelevantEqTop, Scheme.isoOfEq_inv] using
      (homOfLE_toBasicOpenOfGlobalSections_ι _ _ (mul_comm _ _) (add_comm _ _) x.2.2.2).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromOfGlobalSections_preimage_basicOpen` / 引理 `fromOfGlobalSections_preimage_basicOpen`

English:
lemma fromOfGlobalSections_preimage_basicOpen
  given: {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n)
  proof: by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, x, rfl⟩ := (openCoverOfMapIrrelevantEqTop 𝒜 f hf).exists_eq x
    rw [← SetLike.mem_coe] at hx -- TODO : mem version of TopologicalSpace.Opens.map_coe
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme

中文:
引理 fromOfGlobalSections_preimage_basicOpen
  条件: {r : A} {n : 自然数} (hn : 0 < n) (hr : r in 𝒜 n)
  证明: by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, x, rfl⟩ := (openCoverOfMapIrrelevantEqTop 𝒜 f hf).exists_eq x
    rw [← SetLike.mem_coe] at hx -- TODO : mem version of TopologicalSpace.Opens.map_coe
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme

Depends on / 依赖: Category, Category.assoc, Scheme, Scheme.Cover, Scheme.Hom.comp_apply, Scheme.isoOfEq_inv, Set.mem_preimage, SetLike, SetLike.mem_coe, TopologicalSpace, TopologicalSpace.Opens.map_coe, comp_apply, exists_eq, fromOfGlobalSections, isoOfEq_inv, le_antisymm, map_coe, mem_coe, mem_preimage, openCoverOfMapIrrelevantEqTop
-/
lemma fromOfGlobalSections_preimage_basicOpen {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) :
    fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ basicOpen 𝒜 r = X.basicOpen (f r) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, x, rfl⟩ := (openCoverOfMapIrrelevantEqTop 𝒜 f hf).exists_eq x
    rw [← SetLike.mem_coe] at hx -- TODO : mem version of TopologicalSpace.Opens.map_coe
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      ← Scheme.Hom.comp_apply, fromOfGlobalSections, Scheme.Cover.ι_glueMorphisms] at hx
    simp only [openCoverOfMapIrrelevantEqTop,
      toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc, basicOpenIsoSpec_inv_ι] at hx
    simp only [Scheme.Hom.comp_base, Scheme.homOfLE_base, homOfLE_leOfHom, TopCat.hom_comp,
      ContinuousMap.comp_assoc, ContinuousMap.comp_apply, morphismRestrict_base,
      TopologicalSpace.Opens.carrier_eq_coe] at hx
    rw [← SetLike.mem_coe]; rw [← Set.mem_preimage]; rw [← TopologicalSpace.Opens.map_coe]; rw [Proj.awayι_preimage_basicOpen (𝒜 := 𝒜) i.2.2.2 i.2.2.1 hr hn]; rw [← Set.mem_preimage]; rw [← TopologicalSpace.Opens.map_coe]; rw [← Function.Injective.mem_set_image
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X]; rw [⊤) _))).isOpenEmbedding.injective]; rw [← Scheme.Hom.comp_apply]; rw [basicOpenIsoSpecAway]; rw [IsOpenImmersion.isoOfRangeEq_hom_fac] at hx
    rw [← SetLike.mem_coe]; rw [← Scheme.toSpecΓ_preimage_basicOpen]; rw [TopologicalSpace.Opens.map_coe]; rw [Set.mem_preimage]
    refine Set.mem_of_subset_of_mem (Set.image_subset_iff.mpr ?_) hx
    change PrimeSpectrum.basicOpen _ <= PrimeSpectrum.basicOpen _
    simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow,
      PrimeSpectrum.basicOpen_le_basicOpen_iff, IsLocalization.mk'_mem_iff]
    exact Ideal.pow_mem_of_mem _ (Ideal.le_radical (Ideal.mem_span_singleton_self _)) _ i.2.2.1
  · intro x hx
    let I : (openCoverOfMapIrrelevantEqTop 𝒜 f hf).I₀ := ⟨n, r, hn, hr⟩
    obtain ⟨x, rfl⟩ : x in ((openCoverOfMapIrrelevantEqTop 𝒜 f hf).f I).opensRange := by
      simpa [openCoverOfMapIrrelevantEqTop] using hx
    rw [← SetLike.mem_coe] -- TODO : mem version of TopologicalSpace.Opens.map_coe
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, fromOfGlobalSections]
    simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `fromOfGlobalSections_morphismRestrict` / 引理 `fromOfGlobalSections_morphismRestrict`

English:
lemma fromOfGlobalSections_morphismRestrict
  given: {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n)
  proof: by
  rw [← Iso.inv_comp_eq]; rw [← cancel_mono (basicOpen 𝒜 r).ι]
  simp only [Scheme.isoOfEq_inv, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
    fromOfGlobalSections]
  exact (openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩

中文:
引理 fromOfGlobalSections_morphismRestrict
  条件: {r : A} {n : 自然数} (hn : 0 < n) (hr : r in 𝒜 n)
  证明: by
  rw [← Iso.inv_comp_eq]; rw [← cancel_mono (basicOpen 𝒜 r).ι]
  simp only [Scheme.isoOfEq_inv, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
    fromOfGlobalSections]
  exact (openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩

Depends on / 依赖: Category, Category.assoc, Iso.inv_comp_eq, Scheme, Scheme.homOfLE_, Scheme.isoOfEq_inv, basicOpen, cancel_mono, fromOfGlobalSections, inv_comp_eq, isoOfEq_inv, openCoverOfMapIrrelevantEqTop
-/
lemma fromOfGlobalSections_morphismRestrict {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) :
    (fromOfGlobalSections 𝒜 f hf) ∣_ (basicOpen 𝒜 r) =
      (Scheme.isoOfEq _ (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr)).hom ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← Iso.inv_comp_eq]; rw [← cancel_mono (basicOpen 𝒜 r).ι]
  simp only [Scheme.isoOfEq_inv, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
    fromOfGlobalSections]
  exact (openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩

/--
lemma `fromOfGlobalSections_resLE` / 引理 `fromOfGlobalSections_resLE`

English:
lemma fromOfGlobalSections_resLE
  given: {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n)
  proof: by
  rw [← (Iso.inv_comp_eq _).mpr (fromOfGlobalSections_morphismRestrict 𝒜 f hf hn hr)]; rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  simp [Scheme.isoOfEq_inv]

中文:
引理 fromOfGlobalSections_resLE
  条件: {r : A} {n : 自然数} (hn : 0 < n) (hr : r in 𝒜 n)
  证明: by
  rw [← (Iso.inv_comp_eq _).mpr (fromOfGlobalSections_morphismRestrict 𝒜 f hf hn hr)]; rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  simp [Scheme.isoOfEq_inv]

Depends on / 依赖: Iso.inv_comp_eq, Scheme, Scheme.Hom.resLE_eq_morphismRestrict, Scheme.isoOfEq_inv, fromOfGlobalSections_morphismRestrict, inv_comp_eq, isoOfEq_inv, resLE_eq_morphismRestrict
-/
lemma fromOfGlobalSections_resLE {r : A} {n : Nat} (hn : 0 < n) (hr : r in 𝒜 n) :
    (fromOfGlobalSections 𝒜 f hf).resLE _ _
      (fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr).ge =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr := by
  rw [← (Iso.inv_comp_eq _).mpr (fromOfGlobalSections_morphismRestrict 𝒜 f hf hn hr)]; rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  simp [Scheme.isoOfEq_inv]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `fromOfGlobalSections_toSpecZero` / 引理 `fromOfGlobalSections_toSpecZero`

English:
lemma fromOfGlobalSections_toSpecZero
  proof: by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun x => ?_
  simp only [fromOfGlobalSections, toBasicOpenOfGlobalSections, CommRingCat.ofHom_comp,
    Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc, basicOpenIsoSpec_inv_ι_assoc,
    awayι_toSpecZero, Iso.inv_comp_eq]
  simp only 

中文:
引理 fromOfGlobalSections_toSpecZero
  证明: by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun x => ?_
  simp only [fromOfGlobalSections, toBasicOpenOfGlobalSections, CommRingCat.ofHom_comp,
    Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc, basicOpenIsoSpec_inv_ι_assoc,
    awayι_toSpecZero, Iso.inv_comp_eq]
  simp only 

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.ofHom_comp, Iso.eq_, Iso.inv_comp_eq, Scheme, Scheme.Cover, Scheme.isoOfEq_hom_, Scheme.openCoverOfIsOpenCover_f, Spec.map_comp, basicOpenIsoSpecAway, fromOfGlobalSections, hom_ext, inv_comp_eq, map_comp, ofHom_comp, openCoverOfIsOpenCover_f, openCoverOfMapIrrelevantEqTop, toBasicOpenOfGlobalSections
-/
lemma fromOfGlobalSections_toSpecZero
    (f : A ->+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    fromOfGlobalSections 𝒜 f hf ≫ toSpecZero 𝒜 =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp (algebraMap _ _))) := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun x => ?_
  simp only [fromOfGlobalSections, toBasicOpenOfGlobalSections, CommRingCat.ofHom_comp,
    Category.assoc, Scheme.Cover.ι_glueMorphisms_assoc, basicOpenIsoSpec_inv_ι_assoc,
    awayι_toSpecZero, Iso.inv_comp_eq]
  simp only [openCoverOfMapIrrelevantEqTop,
    Scheme.openCoverOfIsOpenCover_f, Scheme.isoOfEq_hom_ι_assoc, ← morphismRestrict_ι_assoc]
  congr 1
  simp only [basicOpenIsoSpecAway, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← Iso.eq_inv_comp,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, ← HomogeneousLocalization.algebraMap_eq]
  congr 2
  rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq _ A]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_assoc]

end ofGlobalSection

end AlgebraicGeometry.Proj
