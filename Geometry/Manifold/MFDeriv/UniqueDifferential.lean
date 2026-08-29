/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Unique derivative sets in manifolds

In this file, we prove various properties of unique derivative sets in manifolds.
* `image_denseRange`: suppose `f` is differentiable on `s` and its derivative at every point of `s`
  has dense range. If `s` has the unique differential property, then so does `f '' s`.
* `uniqueMDiffOn_preimage`: the unique differential property is preserved by local diffeomorphisms
* `uniqueDiffOn_target_inter`: the unique differential property is preserved by
  pullbacks of extended charts
* `tangentBundle_proj_preimage`: if `s` has the unique differential property,
  its preimage under the tangent bundle projection also has
-/

public section

noncomputable section

open scoped Manifold
open Set

/-! ### Unique derivative sets in manifolds -/

section UniqueMDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H' M'']
  {s : Set M} {x : M}

section

/--
theorem `UniqueMDiffWithinAt.image_denseRange` / 定理 `UniqueMDiffWithinAt.image_denseRange`

English:
theorem UniqueMDiffWithinAt.image_denseRange
  statement: (hs : UniqueMDiffAt[s] x)
  proof: by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
have := hs.inter' hf.1 (extChartAt_source_mem_nhds (I := I') (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩

中文:
定理 UniqueMDiffWithinAt.image_denseRange
  结论: (hs : UniqueMDiffAt[s] x)
  证明: by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
have := hs.inter' hf.1 (extChartAt_source_mem_nhds (I := I') (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩
-/
theorem UniqueMDiffWithinAt.image_denseRange (hs : UniqueMDiffAt[s] x)
    {f : M -> M'} {f' : E ->L[𝕜] E'} (hf : HasMFDerivAt[s] f x f')
    (hd : DenseRange f') : UniqueMDiffAt[f '' s] (f x) := by
  /- Rewrite in coordinates, apply `HasFDerivWithinAt.uniqueDiffWithinAt`. -/
have := hs.inter' hf.1 (extChartAt_source_mem_nhds (I := I') (f x))
  refine (((hf.2.mono ?sub1).uniqueDiffWithinAt this hd).mono ?sub2).congr_pt ?pt
  case pt => simp only [mfld_simps]
  case sub1 => mfld_set_tac
  case sub2 =>
    rintro _ ⟨y, ⟨⟨hys, hfy⟩, -⟩, rfl⟩
    exact ⟨⟨_, hys, ((extChartAt I' (f x)).left_inv hfy).symm⟩, mem_range_self _⟩

/--
theorem `UniqueMDiffOn.image_denseRange'` / 定理 `UniqueMDiffOn.image_denseRange'`

English:
theorem UniqueMDiffOn.image_denseRange'
  statement: (hs : UniqueMDiff[s]) {f : M -> M'}
  proof: forall_mem_image.2 fun x hx => (hs x hx).image_denseRange (hf x hx) (hd x hx)

中文:
定理 UniqueMDiffOn.image_denseRange'
  结论: (hs : UniqueMDiff[s]) {f : M -> M'}
  证明: forall_mem_image.2 fun x hx => (hs x hx).image_denseRange (hf x hx) (hd x hx)

Depends on / 依赖: forall_mem_image, image_denseRange
-/
theorem UniqueMDiffOn.image_denseRange' (hs : UniqueMDiff[s]) {f : M -> M'}
    {f' : M -> E ->L[𝕜] E'} (hf : forall x in s, HasMFDerivAt[s] f x (f' x))
    (hd : forall x in s, DenseRange (f' x)) :
    UniqueMDiff[f '' s] :=
  forall_mem_image.2 fun x hx => (hs x hx).image_denseRange (hf x hx) (hd x hx)

/--
theorem `UniqueMDiffOn.image_denseRange` / 定理 `UniqueMDiffOn.image_denseRange`

English:
theorem UniqueMDiffOn.image_denseRange
  statement: (hs : UniqueMDiff[s]) {f : M -> M'}
  proof: hs.image_denseRange' (fun x hx => (hf x hx).hasMFDerivWithinAt) hd

中文:
定理 UniqueMDiffOn.image_denseRange
  结论: (hs : UniqueMDiff[s]) {f : M -> M'}
  证明: hs.image_denseRange' (fun x hx => (hf x hx).hasMFDerivWithinAt) hd

Depends on / 依赖: hasMFDerivWithinAt, hs.image_denseRange, image_denseRange
-/
theorem UniqueMDiffOn.image_denseRange (hs : UniqueMDiff[s]) {f : M -> M'}
    (hf : MDiff[s] f) (hd : forall x in s, DenseRange (mfderiv[s] f x)) :
    UniqueMDiff[f '' s] :=
  hs.image_denseRange' (fun x hx => (hf x hx).hasMFDerivWithinAt) hd

/--
theorem `UniqueMDiffWithinAt.preimage_openPartialHomeomorph` / 定理 `UniqueMDiffWithinAt.preimage_openPartialHomeomorph`

English:
theorem UniqueMDiffWithinAt.preimage_openPartialHomeomorph
  proof: by
  rw [← e.image_source_inter_eq']; rw [inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange

中文:
定理 UniqueMDiffWithinAt.preimage_openPartialHomeomorph
  证明: by
  rw [← e.image_source_inter_eq']; rw [inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange
-/
protected theorem UniqueMDiffWithinAt.preimage_openPartialHomeomorph
    (hs : UniqueMDiffAt[s] x) {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I')
    (hx : x in e.source) : UniqueMDiffAt[e.target inter e.symm ⁻¹' s] (e x) := by
  rw [← e.image_source_inter_eq']; rw [inter_comm]
  exact (hs.inter (e.open_source.mem_nhds hx)).image_denseRange
    (he.mdifferentiableAt hx).hasMFDerivAt.hasMFDerivWithinAt
    (he.mfderiv_surjective hx).denseRange

/--
theorem `UniqueMDiffOn.uniqueMDiffOn_preimage` / 定理 `UniqueMDiffOn.uniqueMDiffOn_preimage`

English:
theorem UniqueMDiffOn.uniqueMDiffOn_preimage
  statement: (hs : UniqueMDiff[s])
  proof: fun _x hx =>
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_openPartialHomeomorph he (e.map_target hx.1)

中文:
定理 UniqueMDiffOn.uniqueMDiffOn_preimage
  结论: (hs : UniqueMDiff[s])
  证明: fun _x hx =>
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_openPartialHomeomorph he (e.map_target hx.1)
-/
theorem UniqueMDiffOn.uniqueMDiffOn_preimage (hs : UniqueMDiff[s])
    {e : OpenPartialHomeomorph M M'} (he : e.MDifferentiable I I') :
    UniqueMDiff[e.target inter e.symm ⁻¹' s] := fun _x hx =>
  e.right_inv hx.1 ▸ (hs _ hx.2).preimage_openPartialHomeomorph he (e.map_target hx.1)

variable [IsManifold I 1 M] in
/--
theorem `UniqueMDiffOn.uniqueMDiffOn_target_inter` / 定理 `UniqueMDiffOn.uniqueMDiffOn_target_inter`

English:
theorem UniqueMDiffOn.uniqueMDiffOn_target_inter
  given: (hs : UniqueMDiff[s]) (x : M)
  proof: by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  rw [← PartialEquiv.image_source_inter_eq']; rw [inter_comm]; rw [extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy => hasMFDerivWithinAt_extChartAt hy.2)
    fun y hy => ((mdifferentiable_chart _).mfderiv_surjective hy.2).denseRange

中文:
定理 UniqueMDiffOn.uniqueMDiffOn_target_inter
  条件: (hs : UniqueMDiff[s]) (x : M)
  证明: by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  rw [← PartialEquiv.image_source_inter_eq']; rw [inter_comm]; rw [extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy => hasMFDerivWithinAt_extChartAt hy.2)
    fun y hy => ((mdifferentiable_chart _).mfderiv_surjective hy.2).denseRange
-/
theorem UniqueMDiffOn.uniqueMDiffOn_target_inter (hs : UniqueMDiff[s]) (x : M) :
    UniqueMDiff[(extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s] := by
  -- this is just a reformulation of `UniqueMDiffOn.uniqueMDiffOn_preimage`, using as `e`
  -- the local chart at `x`.
  rw [← PartialEquiv.image_source_inter_eq']; rw [inter_comm]; rw [extChartAt_source]
  exact (hs.inter (chartAt H x).open_source).image_denseRange'
    (fun y hy => hasMFDerivWithinAt_extChartAt hy.2)
    fun y hy => ((mdifferentiable_chart _).mfderiv_surjective hy.2).denseRange

variable [IsManifold I 1 M] in
/--
theorem `UniqueMDiffOn.uniqueDiffOn_target_inter` / 定理 `UniqueMDiffOn.uniqueDiffOn_target_inter`

English:
theorem UniqueMDiffOn.uniqueDiffOn_target_inter
  given: (hs : UniqueMDiff[s]) (x : M)
  proof: (hs.uniqueMDiffOn_target_inter x).uniqueDiffOn

中文:
定理 UniqueMDiffOn.uniqueDiffOn_target_inter
  条件: (hs : UniqueMDiff[s]) (x : M)
  证明: (hs.uniqueMDiffOn_target_inter x).uniqueDiffOn

Depends on / 依赖: hs.uniqueMDiffOn_target_inter, uniqueDiffOn, uniqueMDiffOn_target_inter
-/
theorem UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiff[s]) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s) :=
  (hs.uniqueMDiffOn_target_inter x).uniqueDiffOn

variable [IsManifold I 1 M] in
/--
theorem `UniqueMDiffOn.uniqueDiffWithinAt_range_inter` / 定理 `UniqueMDiffOn.uniqueDiffWithinAt_range_inter`

English:
theorem UniqueMDiffOn.uniqueDiffWithinAt_range_inter
  statement: (hs : UniqueMDiff[s]) (x : M) (y : E)
  proof: by
  apply (hs.uniqueDiffOn_target_inter x y hy).mono
  apply inter_subset_inter_left _ (extChartAt_target_subset_range x)

中文:
定理 UniqueMDiffOn.uniqueDiffWithinAt_range_inter
  结论: (hs : UniqueMDiff[s]) (x : M) (y : E)
  证明: by
  apply (hs.uniqueDiffOn_target_inter x y hy).mono
  apply inter_subset_inter_left _ (extChartAt_target_subset_range x)

Depends on / 依赖: extChartAt_target_subset_range, hs.uniqueDiffOn_target_inter, inter_subset_inter_left, uniqueDiffOn_target_inter
-/
theorem UniqueMDiffOn.uniqueDiffWithinAt_range_inter (hs : UniqueMDiff[s]) (x : M) (y : E)
    (hy : y in (extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s) :
    UniqueDiffWithinAt 𝕜 (range I inter (extChartAt I x).symm ⁻¹' s) y := by
  apply (hs.uniqueDiffOn_target_inter x y hy).mono
  apply inter_subset_inter_left _ (extChartAt_target_subset_range x)

variable [IsManifold I 1 M] in
/--
theorem `UniqueMDiffOn.uniqueDiffOn_inter_preimage` / 定理 `UniqueMDiffOn.uniqueDiffOn_inter_preimage`

English:
theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage
  statement: (hs : UniqueMDiff[s]) (x : M) (y : M'')
  proof: haveI : UniqueMDiff[s inter f ⁻¹' (extChartAt I' y).source] := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

中文:
定理 UniqueMDiffOn.uniqueDiffOn_inter_preimage
  结论: (hs : UniqueMDiff[s]) (x : M) (y : M'')
  证明: haveI : UniqueMDiff[s inter f ⁻¹' (extChartAt I' y).source] := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

Depends on / 依赖: UniqueMDiff, extChartAt, isOpen_extChartAt_source, mem_nhds, preimage_mem_nhdsWithin, source, this.uniqueDiffOn_target_inter, uniqueDiffOn_target_inter
-/
theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiff[s]) (x : M) (y : M'')
    {f : M -> M''} (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜
      ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMDiff[s inter f ⁻¹' (extChartAt I' y).source] := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source y).mem_nhds hz.2
  this.uniqueDiffOn_target_inter _

end

open Bundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {Z : M -> Type*}
  [TopologicalSpace (TotalSpace F Z)] [forall b, TopologicalSpace (Z b)] [FiberBundle F Z]

/--
lemma `UniqueMDiffWithinAt.bundle_preimage_aux` / 引理 `UniqueMDiffWithinAt.bundle_preimage_aux`

English:
lemma UniqueMDiffWithinAt.bundle_preimage_aux
  statement: {p : TotalSpace F Z}
  proof: by
  suffices ((extChartAt I p.proj).symm ⁻¹' s inter range I) ×ˢ univ subseteq
      (extChartAt (I.prod 𝓘(𝕜, F)) p).symm ⁻¹' (TotalSpace.proj ⁻¹' s) inter range (I.prod 𝓘(𝕜, F)) by
    let w := (extChartAt (I.prod 𝓘(𝕜, F)) p p).2
    have A : extChartAt (I.prod 𝓘(𝕜, F)) p p = (extChartAt I p.1 p.1, w) := by
      ext
      · simp [FiberBundle.chartedSpace_chartAt]
      · rfl
    simp only [UniqueMDiffWithinAt, A] at hs ⊢
    exact (hs.prod (uniqueDiffWithinAt_univ (x := w))).mono this
  rcases p with ⟨x, v⟩
  dsimp
  rintro ⟨z, w⟩ ⟨hz, -⟩
  simp only [mem_inter_iff, mem_preimage, Function.comp_apply,
    mem_range] at hz
  simp only [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.coe_trans_symm, mem_inter_iff,
    mem_preimage, Function.comp_apply, mem_range]
  constructor
  · rw [PartialEquiv.prod_symm, PartialEquiv.refl_symm, PartialEquiv.prod_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.refl_coe,
      OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    convert! hz.1
    apply Trivialization.proj_symm_apply'
    exact h's hz.1
  · rcases hz.2 with ⟨u, rfl⟩
    exact ⟨(u, w), rfl⟩

中文:
引理 UniqueMDiffWithinAt.bundle_preimage_aux
  结论: {p : 全空间 F Z}
  证明: by
  suffices ((extChartAt I p.proj).symm ⁻¹' s inter range I) ×ˢ univ subseteq
      (extChartAt (I.prod 𝓘(𝕜, F)) p).symm ⁻¹' (TotalSpace.proj ⁻¹' s) inter range (I.prod 𝓘(𝕜, F)) by
    let w := (extChartAt (I.prod 𝓘(𝕜, F)) p p).2
    have A : extChartAt (I.prod 𝓘(𝕜, F)) p p = (extChartAt I p.1 p.1, w) := by
      ext
      · simp [FiberBundle.chartedSpace_chartAt]
      · rfl
    simp only [UniqueMDiffWithinAt, A] at hs ⊢
    exact (hs.prod (uniqueDiffWithinAt_univ (x := w))).mono this
  rcases p with ⟨x, v⟩
  dsimp
  rintro ⟨z, w⟩ ⟨hz, -⟩
  simp only [mem_inter_iff, mem_preimage, Function.comp_apply,
    mem_range] at hz
  simp only [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.coe_trans_symm, mem_inter_iff,
    mem_preimage, Function.comp_apply, mem_range]
  constructor
  · rw [PartialEquiv.prod_symm, PartialEquiv.refl_symm, PartialEquiv.prod_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.refl_coe,
      OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    convert! hz.1
    apply Trivialization.proj_symm_apply'
    exact h's hz.1
  · rcases hz.2 with ⟨u, rfl⟩
    exact ⟨(u, w), rfl⟩
-/
private lemma UniqueMDiffWithinAt.bundle_preimage_aux {p : TotalSpace F Z}
    (hs : UniqueMDiffAt[s] p.proj) (h's : s subseteq (trivializationAt F Z p.proj).baseSet) :
    UniqueMDiffAt[π F Z ⁻¹' s] p := by
  suffices ((extChartAt I p.proj).symm ⁻¹' s inter range I) ×ˢ univ subseteq
      (extChartAt (I.prod 𝓘(𝕜, F)) p).symm ⁻¹' (TotalSpace.proj ⁻¹' s) inter range (I.prod 𝓘(𝕜, F)) by
    let w := (extChartAt (I.prod 𝓘(𝕜, F)) p p).2
    have A : extChartAt (I.prod 𝓘(𝕜, F)) p p = (extChartAt I p.1 p.1, w) := by
      ext
      · simp [FiberBundle.chartedSpace_chartAt]
      · rfl
    simp only [UniqueMDiffWithinAt, A] at hs ⊢
    exact (hs.prod (uniqueDiffWithinAt_univ (x := w))).mono this
  rcases p with ⟨x, v⟩
  dsimp
  rintro ⟨z, w⟩ ⟨hz, -⟩
  simp only [mem_inter_iff, mem_preimage, Function.comp_apply,
    mem_range] at hz
  simp only [FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.coe_trans_symm, mem_inter_iff,
    mem_preimage, Function.comp_apply, mem_range]
  constructor
  · rw [PartialEquiv.prod_symm, PartialEquiv.refl_symm, PartialEquiv.prod_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.refl_coe,
      OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply]
    convert! hz.1
    apply Trivialization.proj_symm_apply'
    exact h's hz.1
  · rcases hz.2 with ⟨u, rfl⟩
    exact ⟨(u, w), rfl⟩

/--
theorem `UniqueMDiffWithinAt.bundle_preimage` / 定理 `UniqueMDiffWithinAt.bundle_preimage`

English:
theorem UniqueMDiffWithinAt.bundle_preimage
  given: {p : TotalSpace F Z} (hs : UniqueMDiffAt[s] p.proj)
  proof: by
  suffices UniqueMDiffAt[π F Z ⁻¹' (s inter (trivializationAt F Z p.proj).baseSet)] p from
    this.mono (by simp)
  apply UniqueMDiffWithinAt.bundle_preimage_aux (hs.inter _) inter_subset_right
  exact (trivializationAt F Z p.proj).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' p.proj)

中文:
定理 UniqueMDiffWithinAt.bundle_preimage
  条件: {p : 全空间 F Z} (hs : UniqueMDiffAt[s] p.proj)
  证明: by
  suffices UniqueMDiffAt[π F Z ⁻¹' (s inter (trivializationAt F Z p.proj).baseSet)] p from
    this.mono (by simp)
  apply UniqueMDiffWithinAt.bundle_preimage_aux (hs.inter _) inter_subset_right
  exact (trivializationAt F Z p.proj).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' p.proj)

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, UniqueMDiffAt, UniqueMDiffWithinAt, UniqueMDiffWithinAt.bundle_preimage_aux, baseSet, bundle_preimage_aux, hs.inter, inter_subset_right, mem_baseSet_trivializationAt, mem_nhds, open_baseSet, open_baseSet.mem_nhds, p.proj, this.mono, trivializationAt
-/
theorem UniqueMDiffWithinAt.bundle_preimage {p : TotalSpace F Z} (hs : UniqueMDiffAt[s] p.proj) :
    UniqueMDiffAt[π F Z ⁻¹' s] p := by
  suffices UniqueMDiffAt[π F Z ⁻¹' (s inter (trivializationAt F Z p.proj).baseSet)] p from
    this.mono (by simp)
  apply UniqueMDiffWithinAt.bundle_preimage_aux (hs.inter _) inter_subset_right
  exact (trivializationAt F Z p.proj).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' p.proj)

variable (Z)

/--
theorem `UniqueMDiffWithinAt.bundle_preimage'` / 定理 `UniqueMDiffWithinAt.bundle_preimage'`

English:
theorem UniqueMDiffWithinAt.bundle_preimage'
  given: {b : M} (hs : UniqueMDiffAt[s] b) (x : Z b)
  proof: hs.bundle_preimage (p := ⟨b, x⟩)

中文:
定理 UniqueMDiffWithinAt.bundle_preimage'
  条件: {b : M} (hs : UniqueMDiffAt[s] b) (x : Z b)
  证明: hs.bundle_preimage (p := ⟨b, x⟩)

Depends on / 依赖: bundle_preimage, hs.bundle_preimage
-/
theorem UniqueMDiffWithinAt.bundle_preimage' {b : M} (hs : UniqueMDiffAt[s] b) (x : Z b) :
    UniqueMDiffAt[π F Z ⁻¹' s] ⟨b, x⟩ :=
  hs.bundle_preimage (p := ⟨b, x⟩)

/--
theorem `UniqueMDiffOn.bundle_preimage` / 定理 `UniqueMDiffOn.bundle_preimage`

English:
theorem UniqueMDiffOn.bundle_preimage
  given: (hs : UniqueMDiff[s])
  statement: UniqueMDiff[π F Z ⁻¹' s]
  proof: fun _p hp => (hs _ hp).bundle_preimage

中文:
定理 UniqueMDiffOn.bundle_preimage
  条件: (hs : UniqueMDiff[s])
  结论: UniqueMDiff[π F Z ⁻¹' s]
  证明: fun _p hp => (hs _ hp).bundle_preimage

Depends on / 依赖: bundle_preimage
-/
theorem UniqueMDiffOn.bundle_preimage (hs : UniqueMDiff[s]) : UniqueMDiff[π F Z ⁻¹' s] :=
  fun _p hp => (hs _ hp).bundle_preimage

end UniqueMDiff
