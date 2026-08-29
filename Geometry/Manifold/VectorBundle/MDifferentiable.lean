/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of functions in vector bundles

-/

public section

open Bundle Set ContinuousLinearMap Pretrivialization Filter
open scoped Manifold Topology

section


variable {𝕜 B B' F M : Type*} {E : B -> Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [forall x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB) (E' : B -> Type*) [forall x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : Nat∞}

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]


/--
theorem `mdifferentiableWithinAt_totalSpace` / 定理 `mdifferentiableWithinAt_totalSpace`

English:
theorem mdifferentiableWithinAt_totalSpace
  given: (f : M -> TotalSpace F E) {s : Set M} {x₀ : M}
  proof: by
  simp +singlePass only [mdifferentiableWithinAt_iff_target]
  rw [and_and_and_comm]; rw [← FiberBundle.continuousWithinAt_totalSpace]; rw [and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, Par

中文:
定理 mdifferentiableWithinAt_totalSpace
  条件: (f : M -> 全空间 F E) {s : 集合 M} {x₀ : M}
  证明: by
  simp +singlePass only [mdifferentiableWithinAt_iff_target]
  rw [and_and_and_comm]; rw [← FiberBundle.continuousWithinAt_totalSpace]; rw [and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, Par

Depends on / 依赖: FiberBundle, FiberBundle.continuousWithinAt_totalSpace, FiberBundle.extChartAt, Function, Function.comp_def, Function.id_def, Iff.rfl, PartialEquiv, PartialEquiv.prod_coe, PartialEquiv.refl_coe, PartialEquiv.trans_apply, and_and_and_comm, and_congr, and_congr_right_iff, chartedSpaceSelf_prod, comp_def, continuousWithinAt_totalSpace, extChartAt, extChartAt_self_apply, id_def
-/
theorem mdifferentiableWithinAt_totalSpace (f : M -> TotalSpace F E) {s : Set M} {x₀ : M} :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x => (f x).proj) x₀ ∧
      MDiffAt[s] (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp +singlePass only [mdifferentiableWithinAt_iff_target]
  rw [and_and_and_comm]; rw [← FiberBundle.continuousWithinAt_totalSpace]; rw [and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (mdifferentiableWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet in 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.mdifferentiableWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

/--
theorem `mdifferentiableAt_totalSpace` / 定理 `mdifferentiableAt_totalSpace`

English:
theorem mdifferentiableAt_totalSpace
  given: (f : M -> TotalSpace F E) {x₀ : M}
  proof: by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

中文:
定理 mdifferentiableAt_totalSpace
  条件: (f : M -> 全空间 F E) {x₀ : M}
  证明: by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

Depends on / 依赖: mdifferentiableWithinAt_totalSpace, mdifferentiableWithinAt_univ
-/
theorem mdifferentiableAt_totalSpace (f : M -> TotalSpace F E) {x₀ : M} :
    MDiffAt f x₀ ↔
      MDiffAt (fun x => (f x).proj) x₀ ∧
      MDiffAt (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_totalSpace _ f

/--
theorem `mdifferentiableWithinAt_section` / 定理 `mdifferentiableWithinAt_section`

English:
theorem mdifferentiableWithinAt_section
  given: (s : Π b, E b) {u : Set B} {b₀ : B}
  proof: by
  rw [mdifferentiableWithinAt_totalSpace]
  change MDifferentiableWithinAt _ _ id _ _ ∧ _ ↔ _
  simp [mdifferentiableWithinAt_id]

中文:
定理 mdifferentiableWithinAt_section
  条件: (s : Π b, E b) {u : 集合 B} {b₀ : B}
  证明: by
  rw [mdifferentiableWithinAt_totalSpace]
  change MDifferentiableWithinAt _ _ id _ _ ∧ _ ↔ _
  simp [mdifferentiableWithinAt_id]

Depends on / 依赖: MDifferentiableWithinAt, mdifferentiableWithinAt_id, mdifferentiableWithinAt_totalSpace
-/
theorem mdifferentiableWithinAt_section (s : Π b, E b) {u : Set B} {b₀ : B} :
    MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun b => (trivializationAt F E b₀ (s b)).2) b₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  change MDifferentiableWithinAt _ _ id _ _ ∧ _ ↔ _
  simp [mdifferentiableWithinAt_id]

/--
theorem `mdifferentiableAt_section` / 定理 `mdifferentiableAt_section`

English:
theorem mdifferentiableAt_section
  given: (s : Π b, E b) {b₀ : B}
  proof: by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_section _ _

中文:
定理 mdifferentiableAt_section
  条件: (s : Π b, E b) {b₀ : B}
  证明: by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_section _ _

Depends on / 依赖: mdifferentiableWithinAt_section, mdifferentiableWithinAt_univ
-/
theorem mdifferentiableAt_section (s : Π b, E b) {b₀ : B} :
    MDiffAt (T% s) b₀ ↔ MDiffAt (fun b => (trivializationAt F E b₀ (s b)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using mdifferentiableWithinAt_section _ _

namespace Bundle

variable (E) {IB}

/--
theorem `mdifferentiable_proj` / 定理 `mdifferentiable_proj`

English:
theorem mdifferentiable_proj
  statement: MDiff (π F E)
  proof: fun x => by
  have : MDiffAt (@id <| TotalSpace F E) x := mdifferentiableAt_id
  rw [mdifferentiableAt_totalSpace] at this
  exact this.1

中文:
定理 mdifferentiable_proj
  结论: MDiff (π F E)
  证明: fun x => by
  have : MDiffAt (@id <| TotalSpace F E) x := mdifferentiableAt_id
  rw [mdifferentiableAt_totalSpace] at this
  exact this.1

Depends on / 依赖: MDiffAt, TotalSpace, mdifferentiableAt_id, mdifferentiableAt_totalSpace
-/
theorem mdifferentiable_proj : MDiff (π F E) := fun x => by
  have : MDiffAt (@id <| TotalSpace F E) x := mdifferentiableAt_id
  rw [mdifferentiableAt_totalSpace] at this
  exact this.1

/--
theorem `mdifferentiableOn_proj` / 定理 `mdifferentiableOn_proj`

English:
theorem mdifferentiableOn_proj
  given: {s : Set (TotalSpace F E)}
  statement: MDiff[s] (π F E)
  proof: (mdifferentiable_proj E).mdifferentiableOn

中文:
定理 mdifferentiableOn_proj
  条件: {s : 集合 (全空间 F E)}
  结论: MDiff[s] (π F E)
  证明: (mdifferentiable_proj E).mdifferentiableOn

Depends on / 依赖: mdifferentiableOn, mdifferentiable_proj
-/
theorem mdifferentiableOn_proj {s : Set (TotalSpace F E)} : MDiff[s] (π F E) :=
  (mdifferentiable_proj E).mdifferentiableOn

/--
theorem `mdifferentiableAt_proj` / 定理 `mdifferentiableAt_proj`

English:
theorem mdifferentiableAt_proj
  given: {p : TotalSpace F E}
  statement: MDiffAt (π F E) p
  proof: (mdifferentiable_proj E).mdifferentiableAt

中文:
定理 mdifferentiableAt_proj
  条件: {p : 全空间 F E}
  结论: MDiffAt (π F E) p
  证明: (mdifferentiable_proj E).mdifferentiableAt

Depends on / 依赖: mdifferentiableAt, mdifferentiable_proj
-/
theorem mdifferentiableAt_proj {p : TotalSpace F E} : MDiffAt (π F E) p :=
  (mdifferentiable_proj E).mdifferentiableAt

/--
theorem `mdifferentiableWithinAt_proj` / 定理 `mdifferentiableWithinAt_proj`

English:
theorem mdifferentiableWithinAt_proj
  given: {s : Set (TotalSpace F E)} {p : TotalSpace F E}
  proof: (mdifferentiableAt_proj E).mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_proj
  条件: {s : 集合 (全空间 F E)} {p : 全空间 F E}
  证明: (mdifferentiableAt_proj E).mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_proj, mdifferentiableWithinAt
-/
theorem mdifferentiableWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    MDiffAt[s] (π F E) p :=
  (mdifferentiableAt_proj E).mdifferentiableWithinAt

section

variable (𝕜) [forall x, AddCommMonoid (E x)]
variable [forall x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

/--
theorem `mdifferentiable_zeroSection` / 定理 `mdifferentiable_zeroSection`

English:
theorem mdifferentiable_zeroSection
  statement: MDiff (zeroSection F E)
  proof: by
  intro x
  unfold zeroSection
  rw [mdifferentiableAt_section]
  apply (mdifferentiableAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).z

中文:
定理 mdifferentiable_zeroSection
  结论: MDiff (zeroSection F E)
  证明: by
  intro x
  unfold zeroSection
  rw [mdifferentiableAt_section]
  apply (mdifferentiableAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).z

Depends on / 依赖: Prod.snd, congr_arg, congr_of_eventuallyEq, filter_upwards, mdifferentiableAt_const, mdifferentiableAt_section, mem_baseSet_trivializationAt, mem_nhds, open_baseSet, open_baseSet.mem_nhds, trivializationAt, zeroSection
-/
theorem mdifferentiable_zeroSection : MDiff (zeroSection F E) := by
  intro x
  unfold zeroSection
  rw [mdifferentiableAt_section]
  apply (mdifferentiableAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).zeroSection 𝕜 hy

/--
theorem `mdifferentiableOn_zeroSection` / 定理 `mdifferentiableOn_zeroSection`

English:
theorem mdifferentiableOn_zeroSection
  given: {t : Set B}
  statement: MDiff[t] (zeroSection F E)
  proof: (mdifferentiable_zeroSection _ _).mdifferentiableOn

中文:
定理 mdifferentiableOn_zeroSection
  条件: {t : 集合 B}
  结论: MDiff[t] (zeroSection F E)
  证明: (mdifferentiable_zeroSection _ _).mdifferentiableOn

Depends on / 依赖: mdifferentiableOn, mdifferentiable_zeroSection
-/
theorem mdifferentiableOn_zeroSection {t : Set B} : MDiff[t] (zeroSection F E) :=
  (mdifferentiable_zeroSection _ _).mdifferentiableOn

/--
theorem `mdifferentiableAt_zeroSection` / 定理 `mdifferentiableAt_zeroSection`

English:
theorem mdifferentiableAt_zeroSection
  given: {x : B}
  statement: MDiffAt (zeroSection F E) x
  proof: (mdifferentiable_zeroSection _ _).mdifferentiableAt

中文:
定理 mdifferentiableAt_zeroSection
  条件: {x : B}
  结论: MDiffAt (zeroSection F E) x
  证明: (mdifferentiable_zeroSection _ _).mdifferentiableAt

Depends on / 依赖: mdifferentiableAt, mdifferentiable_zeroSection
-/
theorem mdifferentiableAt_zeroSection {x : B} : MDiffAt (zeroSection F E) x :=
  (mdifferentiable_zeroSection _ _).mdifferentiableAt

/--
theorem `mdifferentiableWithinAt_zeroSection` / 定理 `mdifferentiableWithinAt_zeroSection`

English:
theorem mdifferentiableWithinAt_zeroSection
  given: {t : Set B} {x : B}
  proof: (mdifferentiable_zeroSection _ _ x).mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_zeroSection
  条件: {t : 集合 B} {x : B}
  证明: (mdifferentiable_zeroSection _ _ x).mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableWithinAt, mdifferentiable_zeroSection
-/
theorem mdifferentiableWithinAt_zeroSection {t : Set B} {x : B} :
    MDiffAt[t] (zeroSection F E) x :=
  (mdifferentiable_zeroSection _ _ x).mdifferentiableWithinAt

end

variable {s : forall x, E x} {u : Set B} {x : B}

@[nontriviality]
/--
lemma `mdifferentiableWithinAt_section_of_subsingleton` / 引理 `mdifferentiableWithinAt_section_of_subsingleton`

English:
lemma mdifferentiableWithinAt_section_of_subsingleton
  given: [Subsingleton F]
  proof: (contMDiffWithinAt_section_of_subsingleton _).mdifferentiableWithinAt one_ne_zero

@[nontriviality]

中文:
引理 mdifferentiableWithinAt_section_of_subsingleton
  条件: [子单例 F]
  证明: (contMDiffWithinAt_section_of_subsingleton _).mdifferentiableWithinAt one_ne_zero

@[nontriviality]

Depends on / 依赖: contMDiffWithinAt_section_of_subsingleton, mdifferentiableWithinAt, one_ne_zero
-/
lemma mdifferentiableWithinAt_section_of_subsingleton [Subsingleton F] :
    MDiffAt[u] (T% s) x :=
  (contMDiffWithinAt_section_of_subsingleton _).mdifferentiableWithinAt one_ne_zero

@[nontriviality]
/--
lemma `mdifferentiableAt_section_of_subsingleton` / 引理 `mdifferentiableAt_section_of_subsingleton`

English:
lemma mdifferentiableAt_section_of_subsingleton
  given: [Subsingleton F]
  statement: MDiffAt (T% s) x
  proof: by
  rw [← mdifferentiableWithinAt_univ]
  apply mdifferentiableWithinAt_section_of_subsingleton

@[nontriviality]

中文:
引理 mdifferentiableAt_section_of_subsingleton
  条件: [子单例 F]
  结论: MDiffAt (T% s) x
  证明: by
  rw [← mdifferentiableWithinAt_univ]
  apply mdifferentiableWithinAt_section_of_subsingleton

@[nontriviality]

Depends on / 依赖: mdifferentiableWithinAt_section_of_subsingleton, mdifferentiableWithinAt_univ
-/
lemma mdifferentiableAt_section_of_subsingleton [Subsingleton F] : MDiffAt (T% s) x := by
  rw [← mdifferentiableWithinAt_univ]
  apply mdifferentiableWithinAt_section_of_subsingleton

@[nontriviality]
/--
lemma `mdifferentiableOn_section_of_subsingleton` / 引理 `mdifferentiableOn_section_of_subsingleton`

English:
lemma mdifferentiableOn_section_of_subsingleton
  given: [Subsingleton F]
  statement: MDiff[u] (T% s)
  proof: fun _x _hx => mdifferentiableWithinAt_section_of_subsingleton ..

@[nontriviality]

中文:
引理 mdifferentiableOn_section_of_subsingleton
  条件: [子单例 F]
  结论: MDiff[u] (T% s)
  证明: fun _x _hx => mdifferentiableWithinAt_section_of_subsingleton ..

@[nontriviality]

Depends on / 依赖: mdifferentiableWithinAt_section_of_subsingleton
-/
lemma mdifferentiableOn_section_of_subsingleton [Subsingleton F] : MDiff[u] (T% s) :=
  fun _x _hx => mdifferentiableWithinAt_section_of_subsingleton ..

@[nontriviality]
/--
lemma `mdifferentiable_section_of_subsingleton` / 引理 `mdifferentiable_section_of_subsingleton`

English:
lemma mdifferentiable_section_of_subsingleton
  given: [Subsingleton F]
  statement: MDiff (T% s)
  proof: fun _x => mdifferentiableAt_section_of_subsingleton ..

中文:
引理 mdifferentiable_section_of_subsingleton
  条件: [子单例 F]
  结论: MDiff (T% s)
  证明: fun _x => mdifferentiableAt_section_of_subsingleton ..

Depends on / 依赖: mdifferentiableAt_section_of_subsingleton
-/
lemma mdifferentiable_section_of_subsingleton [Subsingleton F] : MDiff (T% s) :=
  fun _x => mdifferentiableAt_section_of_subsingleton ..

end Bundle

section coordChange

variable [(x : B) -> AddCommMonoid (E x)] [(x : B) -> Module 𝕜 (E x)]
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]
variable {IB}

/--
theorem `mdifferentiableOn_coordChangeL` / 定理 `mdifferentiableOn_coordChangeL`

English:
theorem mdifferentiableOn_coordChangeL
  proof: (contMDiffOn_coordChangeL e e').mdifferentiableOn one_ne_zero

中文:
定理 mdifferentiableOn_coordChangeL
  证明: (contMDiffOn_coordChangeL e e').mdifferentiableOn one_ne_zero

Depends on / 依赖: contMDiffOn_coordChangeL, mdifferentiableOn, one_ne_zero
-/
theorem mdifferentiableOn_coordChangeL :
    MDiff[e.baseSet inter e'.baseSet] (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) :=
  (contMDiffOn_coordChangeL e e').mdifferentiableOn one_ne_zero

/--
theorem `mdifferentiableOn_symm_coordChangeL` / 定理 `mdifferentiableOn_symm_coordChangeL`

English:
theorem mdifferentiableOn_symm_coordChangeL
  proof: (contMDiffOn_symm_coordChangeL e e').mdifferentiableOn one_ne_zero

中文:
定理 mdifferentiableOn_symm_coordChangeL
  证明: (contMDiffOn_symm_coordChangeL e e').mdifferentiableOn one_ne_zero

Depends on / 依赖: contMDiffOn_symm_coordChangeL, mdifferentiableOn, one_ne_zero
-/
theorem mdifferentiableOn_symm_coordChangeL :
    MDiff[e.baseSet inter e'.baseSet] (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F ->L[𝕜] F)) :=
  (contMDiffOn_symm_coordChangeL e e').mdifferentiableOn one_ne_zero

variable {e e'}

/--
theorem `mdifferentiableAt_coordChangeL` / 定理 `mdifferentiableAt_coordChangeL`

English:
theorem mdifferentiableAt_coordChangeL
  statement: {x : B}
  proof: (contMDiffAt_coordChangeL h h').mdifferentiableAt one_ne_zero

中文:
定理 mdifferentiableAt_coordChangeL
  结论: {x : B}
  证明: (contMDiffAt_coordChangeL h h').mdifferentiableAt one_ne_zero

Depends on / 依赖: contMDiffAt_coordChangeL, mdifferentiableAt, one_ne_zero
-/
theorem mdifferentiableAt_coordChangeL {x : B}
    (h : x in e.baseSet) (h' : x in e'.baseSet) :
    MDiffAt (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) x :=
  (contMDiffAt_coordChangeL h h').mdifferentiableAt one_ne_zero

variable {s : Set M} {f : M -> B} {g : M -> F} {x : M}

/--
theorem `MDifferentiableWithinAt.coordChangeL` / 定理 `MDifferentiableWithinAt.coordChangeL`

English:
theorem MDifferentiableWithinAt.coordChangeL
  statement: (hf : MDiffAt[s] f x)
  proof: (mdifferentiableAt_coordChangeL he he').comp_mdifferentiableWithinAt _ hf

中文:
定理 MDifferentiableWithinAt.coordChangeL
  结论: (hf : MDiffAt[s] f x)
  证明: (mdifferentiableAt_coordChangeL he he').comp_mdifferentiableWithinAt _ hf
-/
protected theorem MDifferentiableWithinAt.coordChangeL (hf : MDiffAt[s] f x)
    (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    MDiffAt[s] (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) x :=
  (mdifferentiableAt_coordChangeL he he').comp_mdifferentiableWithinAt _ hf

/--
theorem `MDifferentiableAt.coordChangeL` / 定理 `MDifferentiableAt.coordChangeL`

English:
theorem MDifferentiableAt.coordChangeL
  proof: MDifferentiableWithinAt.coordChangeL hf he he'

中文:
定理 MDifferentiableAt.coordChangeL
  证明: MDifferentiableWithinAt.coordChangeL hf he he'
-/
protected theorem MDifferentiableAt.coordChangeL
    (hf : MDiffAt f x) (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    MDiffAt (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) x :=
  MDifferentiableWithinAt.coordChangeL hf he he'

/--
theorem `MDifferentiableOn.coordChangeL` / 定理 `MDifferentiableOn.coordChangeL`

English:
theorem MDifferentiableOn.coordChangeL
  proof: fun x hx => (hf x hx).coordChangeL (he hx) (he' hx)

中文:
定理 MDifferentiableOn.coordChangeL
  证明: fun x hx => (hf x hx).coordChangeL (he hx) (he' hx)
-/
protected theorem MDifferentiableOn.coordChangeL
    (hf : MDiff[s] f) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    MDiff[s] (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) :=
  fun x hx => (hf x hx).coordChangeL (he hx) (he' hx)

/--
theorem `MDifferentiable.coordChangeL` / 定理 `MDifferentiable.coordChangeL`

English:
theorem MDifferentiable.coordChangeL
  proof: fun x => (hf x).coordChangeL (he x) (he' x)

中文:
定理 MDifferentiable.coordChangeL
  证明: fun x => (hf x).coordChangeL (he x) (he' x)
-/
protected theorem MDifferentiable.coordChangeL
    (hf : MDiff f) (he : forall x, f x in e.baseSet) (he' : forall x, f x in e'.baseSet) :
    MDiff (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) :=
  fun x => (hf x).coordChangeL (he x) (he' x)

/--
theorem `MDifferentiableWithinAt.coordChange` / 定理 `MDifferentiableWithinAt.coordChange`

English:
theorem MDifferentiableWithinAt.coordChange
  proof: by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet inter e'.baseSet in 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e

中文:
定理 MDifferentiableWithinAt.coordChange
  证明: by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet inter e'.baseSet in 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e
-/
protected theorem MDifferentiableWithinAt.coordChange
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    MDiffAt[s] (fun y => e.coordChange e' (f y) (g y)) x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet inter e'.baseSet in 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm

/--
theorem `MDifferentiableAt.coordChange` / 定理 `MDifferentiableAt.coordChange`

English:
theorem MDifferentiableAt.coordChange
  proof: MDifferentiableWithinAt.coordChange hf hg he he'

中文:
定理 MDifferentiableAt.coordChange
  证明: MDifferentiableWithinAt.coordChange hf hg he he'
-/
protected theorem MDifferentiableAt.coordChange
    (hf : MDiffAt f x) (hg : MDiffAt g x)
    (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    MDiffAt (fun y => e.coordChange e' (f y) (g y)) x :=
  MDifferentiableWithinAt.coordChange hf hg he he'

/--
theorem `MDifferentiableOn.coordChange` / 定理 `MDifferentiableOn.coordChange`

English:
theorem MDifferentiableOn.coordChange
  proof: fun x hx =>
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

中文:
定理 MDifferentiableOn.coordChange
  证明: fun x hx =>
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)
-/
protected theorem MDifferentiableOn.coordChange
    (hf : MDiff[s] f) (hg : MDiff[s] g)
    (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    MDiff[s] (fun y => e.coordChange e' (f y) (g y)) := fun x hx =>
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

/--
theorem `MDifferentiable.coordChange` / 定理 `MDifferentiable.coordChange`

English:
theorem MDifferentiable.coordChange
  proof: fun x =>
  (hf x).coordChange (hg x) (he x) (he' x)

中文:
定理 MDifferentiable.coordChange
  证明: fun x =>
  (hf x).coordChange (hg x) (he x) (he' x)
-/
protected theorem MDifferentiable.coordChange
    (hf : MDiff f) (hg : MDiff g) (he : forall x, f x in e.baseSet) (he' : forall x, f x in e'.baseSet) :
    MDiff (fun y => e.coordChange e' (f y) (g y)) := fun x =>
  (hf x).coordChange (hg x) (he x) (he' x)

end coordChange

variable [(x : B) -> AddCommMonoid (E x)] [(x : B) -> Module 𝕜 (E x)]
  [VectorBundle 𝕜 F E] [ContMDiffVectorBundle 1 F E IB]

/--
lemma `MDifferentiableWithinAt.change_section_trivialization` / 引理 `MDifferentiableWithinAt.change_section_trivialization`

English:
lemma MDifferentiableWithinAt.change_section_trivialization
  proof: by
  rw [Trivialization.mem_source] at he he'
  refine (hf.coordChange he'f he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hf.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

中文:
引理 MDifferentiableWithinAt.change_section_trivialization
  证明: by
  rw [Trivialization.mem_source] at he he'
  refine (hf.coordChange he'f he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hf.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

Depends on / 依赖: Trivialization, Trivialization.mem_source, congr_of_eventuallyEq, continuousWithinAt, coordChange, e.open_baseSet.mem_nhds, filter_upwards, hf.continuousWithinAt, hf.coordChange, mem_nhds, mem_source, open_baseSet
-/
lemma MDifferentiableWithinAt.change_section_trivialization
    {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
    {e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e']
    {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
    (hf : MDiffAt[s] (π F E ∘ f) x₀) (he'f : MDiffAt[s] (fun x => (e (f x)).2) x₀)
    (he : f x₀ in e.source) (he' : f x₀ in e'.source) :
    MDiffAt[s] (fun x => (e' (f x)).2) x₀ := by
  rw [Trivialization.mem_source] at he he'
  refine (hf.coordChange he'f he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hf.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

namespace Bundle.Trivialization

/--
theorem `mdifferentiableWithinAt_snd_comp_iff₂` / 定理 `mdifferentiableWithinAt_snd_comp_iff₂`

English:
theorem mdifferentiableWithinAt_snd_comp_iff₂
  proof: ⟨(hf.change_section_trivialization IB · hex₀ he'x₀),
   (hf.change_section_trivialization IB · he'x₀ hex₀)⟩

中文:
定理 mdifferentiableWithinAt_snd_comp_iff₂
  证明: ⟨(hf.change_section_trivialization IB · hex₀ he'x₀),
   (hf.change_section_trivialization IB · he'x₀ hex₀)⟩

Depends on / 依赖: change_section_trivialization, hf.change_section_trivialization
-/
theorem mdifferentiableWithinAt_snd_comp_iff₂
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
    (hex₀ : f x₀ in e.source) (he'x₀ : f x₀ in e'.source)
    (hf : MDiffAt[s] (π F E ∘ f) x₀) :
    MDiffAt[s] (fun x => (e (f x)).2) x₀ ↔ MDiffAt[s] (fun x => (e' (f x)).2) x₀ :=
  ⟨(hf.change_section_trivialization IB · hex₀ he'x₀),
   (hf.change_section_trivialization IB · he'x₀ hex₀)⟩

variable (e e')

/--
theorem `mdifferentiableAt_snd_comp_iff₂` / 定理 `mdifferentiableAt_snd_comp_iff₂`

English:
theorem mdifferentiableAt_snd_comp_iff₂
  proof: by
  simpa [← mdifferentiableWithinAt_univ] using
    e.mdifferentiableWithinAt_snd_comp_iff₂ IB he he' hf

中文:
定理 mdifferentiableAt_snd_comp_iff₂
  证明: by
  simpa [← mdifferentiableWithinAt_univ] using
    e.mdifferentiableWithinAt_snd_comp_iff₂ IB he he' hf

Depends on / 依赖: e.mdifferentiableWithinAt_snd_comp_iff, mdifferentiableWithinAt_univ
-/
theorem mdifferentiableAt_snd_comp_iff₂
    {e e' : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {f : M -> TotalSpace F E} {x₀ : M}
    (he : f x₀ in e.source) (he' : f x₀ in e'.source)
    (hf : MDiffAt (fun x => (f x).proj) x₀) :
    MDiffAt (fun x => (e (f x)).2) x₀ ↔ MDiffAt (fun x => (e' (f x)).2) x₀ := by
  simpa [← mdifferentiableWithinAt_univ] using
    e.mdifferentiableWithinAt_snd_comp_iff₂ IB he he' hf

/--
theorem `mdifferentiableWithinAt_totalSpace_iff` / 定理 `mdifferentiableWithinAt_totalSpace_iff`

English:
theorem mdifferentiableWithinAt_totalSpace_iff
  proof: by
  rw [mdifferentiableWithinAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableWithinAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

中文:
定理 mdifferentiableWithinAt_totalSpace_iff
  证明: by
  rw [mdifferentiableWithinAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableWithinAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

Depends on / 依赖: FiberBundle, FiberBundle.mem_trivializationAt_proj_source, Trivialization, Trivialization.mdifferentiableWithinAt_snd_comp_iff, and_congr_right, mdifferentiableWithinAt_totalSpace, mem_trivializationAt_proj_source
-/
theorem mdifferentiableWithinAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)) [MemTrivializationAtlas e]
    (f : M -> TotalSpace F E) {s : Set M} {x₀ : M}
    (he : f x₀ in e.source) :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x => (f x).proj) x₀ ∧ MDiffAt[s] (fun x => (e (f x)).2) x₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableWithinAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

/--
theorem `mdifferentiableAt_totalSpace_iff` / 定理 `mdifferentiableAt_totalSpace_iff`

English:
theorem mdifferentiableAt_totalSpace_iff
  proof: by
  rw [mdifferentiableAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

中文:
定理 mdifferentiableAt_totalSpace_iff
  证明: by
  rw [mdifferentiableAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

Depends on / 依赖: FiberBundle, FiberBundle.mem_trivializationAt_proj_source, Trivialization, Trivialization.mdifferentiableAt_snd_comp_iff, and_congr_right, mdifferentiableAt_totalSpace, mem_trivializationAt_proj_source
-/
theorem mdifferentiableAt_totalSpace_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)) [MemTrivializationAtlas e]
    (f : M -> TotalSpace F E) {x₀ : M}
    (he : f x₀ in e.source) :
    MDiffAt f x₀ ↔ MDiffAt (fun x => (f x).proj) x₀ ∧ MDiffAt (fun x => (e (f x)).2) x₀ := by
  rw [mdifferentiableAt_totalSpace]
  apply and_congr_right
  intro hf
  rw [Trivialization.mdifferentiableAt_snd_comp_iff₂ IB
    (FiberBundle.mem_trivializationAt_proj_source) he hf]

/--
theorem `mdifferentiableWithinAt_section_iff` / 定理 `mdifferentiableWithinAt_section_iff`

English:
theorem mdifferentiableWithinAt_section_iff
  proof: by
  rw [e.mdifferentiableWithinAt_totalSpace_iff IB]
  · change MDiffAt[u] (@id B) b₀ ∧ _ ↔ _
    simp [mdifferentiableWithinAt_id]
  exact (coe_mem_source e).mpr hex₀

中文:
定理 mdifferentiableWithinAt_section_iff
  证明: by
  rw [e.mdifferentiableWithinAt_totalSpace_iff IB]
  · change MDiffAt[u] (@id B) b₀ ∧ _ ↔ _
    simp [mdifferentiableWithinAt_id]
  exact (coe_mem_source e).mpr hex₀

Depends on / 依赖: MDiffAt, coe_mem_source, e.mdifferentiableWithinAt_totalSpace_iff, mdifferentiableWithinAt_id, mdifferentiableWithinAt_totalSpace_iff
-/
theorem mdifferentiableWithinAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {u : Set B} {b₀ : B}
    (hex₀ : b₀ in e.baseSet) :
    MDiffAt[u] (T% s) b₀ ↔ MDiffAt[u] (fun x => (e (s x)).2) b₀ := by
  rw [e.mdifferentiableWithinAt_totalSpace_iff IB]
  · change MDiffAt[u] (@id B) b₀ ∧ _ ↔ _
    simp [mdifferentiableWithinAt_id]
  exact (coe_mem_source e).mpr hex₀

/--
theorem `mdifferentiableAt_section_iff` / 定理 `mdifferentiableAt_section_iff`

English:
theorem mdifferentiableAt_section_iff
  proof: by
  simpa [← mdifferentiableWithinAt_univ] using e.mdifferentiableWithinAt_section_iff IB s hex₀

中文:
定理 mdifferentiableAt_section_iff
  证明: by
  simpa [← mdifferentiableWithinAt_univ] using e.mdifferentiableWithinAt_section_iff IB s hex₀

Depends on / 依赖: e.mdifferentiableWithinAt_section_iff, mdifferentiableWithinAt_section_iff, mdifferentiableWithinAt_univ
-/
theorem mdifferentiableAt_section_iff
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E -> B)) [MemTrivializationAtlas e]
    (s : Π b : B, E b) {b₀ : B}
    (hex₀ : b₀ in e.baseSet) :
    MDiffAt (T% s) b₀ ↔ MDiffAt (fun x => (e (s x)).2) b₀ := by
  simpa [← mdifferentiableWithinAt_univ] using e.mdifferentiableWithinAt_section_iff IB s hex₀

variable {IB} in
/--
theorem `mdifferentiableOn_section_iff` / 定理 `mdifferentiableOn_section_iff`

English:
theorem mdifferentiableOn_section_iff
  statement: {s : forall x, E x} {a : Set B}
  proof: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩ <;>
have := (h x hx).mdifferentiableAt ha.mem_nhds hx
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mp this).mdifferentiableWithinAt
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mpr this).mdifferentiableWithinAt

中文:
定理 mdifferentiableOn_section_iff
  结论: {s : 对任意 x, E x} {a : 集合 B}
  证明: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩ <;>
have := (h x hx).mdifferentiableAt ha.mem_nhds hx
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mp this).mdifferentiableWithinAt
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mpr this).mdifferentiableWithinAt

Depends on / 依赖: e.mdifferentiableAt_section_iff, ha.mem_nhds, mdifferentiableAt, mdifferentiableAt_section_iff, mdifferentiableWithinAt, mem_nhds
-/
theorem mdifferentiableOn_section_iff {s : forall x, E x} {a : Set B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B))
    [MemTrivializationAtlas e] (ha : IsOpen a) (ha' : a subseteq e.baseSet) :
    MDiff[a] (T% s) ↔ MDiff[a] (fun x => (e ⟨x, s x⟩).2) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩ <;>
have := (h x hx).mdifferentiableAt ha.mem_nhds hx
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mp this).mdifferentiableWithinAt
  · exact ((e.mdifferentiableAt_section_iff _ _ (ha' hx)).mpr this).mdifferentiableWithinAt

variable {IB} in
/--
theorem `mdifferentiableOn_section_baseSet_iff` / 定理 `mdifferentiableOn_section_baseSet_iff`

English:
theorem mdifferentiableOn_section_baseSet_iff
  statement: {s : forall x, E x}
  proof: e.mdifferentiableOn_section_iff e.open_baseSet subset_rfl

中文:
定理 mdifferentiableOn_section_baseSet_iff
  结论: {s : 对任意 x, E x}
  证明: e.mdifferentiableOn_section_iff e.open_baseSet subset_rfl

Depends on / 依赖: e.mdifferentiableOn_section_iff, e.open_baseSet, mdifferentiableOn_section_iff, open_baseSet, subset_rfl
-/
theorem mdifferentiableOn_section_baseSet_iff {s : forall x, E x}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B))
    [MemTrivializationAtlas e] :
    MDiff[e.baseSet] (T% s) ↔ MDiff[e.baseSet] (fun x => (e ⟨x, s x⟩).2) :=
  e.mdifferentiableOn_section_iff e.open_baseSet subset_rfl

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (Z : M -> Type*) [TopologicalSpace (TotalSpace F Z)] [forall b, TopologicalSpace (Z b)]
  [FiberBundle F Z] [forall b, AddCommMonoid (Z b)] [forall b, Module 𝕜 (Z b)] [VectorBundle 𝕜 F Z]

/--
theorem `mdifferentiable` / 定理 `mdifferentiable`

English:
theorem mdifferentiable
  statement: [ContMDiffVectorBundle 1 F Z I]
  proof: ⟨e.contMDiffOn.mdifferentiableOn one_ne_zero, e.contMDiffOn_symm.mdifferentiableOn one_ne_zero⟩

中文:
定理 mdifferentiable
  结论: [余ntMDiffVectorBundle 1 F Z I]
  证明: ⟨e.contMDiffOn.mdifferentiableOn one_ne_zero, e.contMDiffOn_symm.mdifferentiableOn one_ne_zero⟩

Depends on / 依赖: contMDiffOn, contMDiffOn_symm, e.contMDiffOn.mdifferentiableOn, e.contMDiffOn_symm.mdifferentiableOn, mdifferentiableOn, one_ne_zero
-/
theorem mdifferentiable [ContMDiffVectorBundle 1 F Z I]
    (e : Trivialization F (π F Z)) [MemTrivializationAtlas e] :
    e.MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) :=
  ⟨e.contMDiffOn.mdifferentiableOn one_ne_zero, e.contMDiffOn_symm.mdifferentiableOn one_ne_zero⟩

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Bundle.Trivialization.mdifferentiable := mdifferentiable

end

end Bundle.Trivialization

end

section operations

variable {𝕜 B B' F M : Type*} {E : B -> Type*}

variable
  -- Let `E` be a fiber bundle with base `B` and fiber `F` (a vector space over `𝕜`)
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [forall x, TopologicalSpace (E x)]
  [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [FiberBundle F E]
  -- Moreover let `E` be a vector bundle
  [(x : B) -> AddCommGroup (E x)] [(x : B) -> Module 𝕜 (E x)] [VectorBundle 𝕜 F E]
  -- Let the base `B` be charted over a fixed model space `HB`
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  -- Moreover let `HB` be modelled on a normed space `EB` so that `B` (and hence `E`) have
  -- differentiable structures
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {I : ModelWithCorners 𝕜 EB HB}

variable {f : B -> 𝕜} {a : 𝕜} {s t : Π x : B, E x} {u : Set B} {x₀ : B}

/--
lemma `mdifferentiableWithinAt_add_section` / 引理 `mdifferentiableWithinAt_add_section`

English:
lemma mdifferentiableWithinAt_add_section
  proof: by
  rw [mdifferentiableWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exac

中文:
引理 mdifferentiableWithinAt_add_section
  证明: by
  rw [mdifferentiableWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exac

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, e.baseSet, e.linear, e.open_baseSet.mem_nhds, eventually_of_mem, hs.add, linear, mdifferentiableWithinAt_section, mem_baseSet_trivializationAt, mem_nhds, mem_nhdsWithin_of_mem_nhds, open_baseSet, trivializationAt
-/
lemma mdifferentiableWithinAt_add_section
    (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) :
    MDiffAt[u] (T% (s + t)) x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ht ⊢
  set e := trivializationAt F E x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx => (e.linear 𝕜 hx).1 ..
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1 ..

/--
lemma `mdifferentiableAt_add_section` / 引理 `mdifferentiableAt_add_section`

English:
lemma mdifferentiableAt_add_section
  proof: by
  rw [← mdifferentiableWithinAt_univ] at hs ht ⊢
  apply mdifferentiableWithinAt_add_section hs ht

中文:
引理 mdifferentiableAt_add_section
  证明: by
  rw [← mdifferentiableWithinAt_univ] at hs ht ⊢
  apply mdifferentiableWithinAt_add_section hs ht

Depends on / 依赖: mdifferentiableWithinAt_add_section, mdifferentiableWithinAt_univ
-/
lemma mdifferentiableAt_add_section
    (hs : MDiffAt (T% s) x₀) (ht : MDiffAt (T% t) x₀) :
    MDiffAt (T% (s + t)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ht ⊢
  apply mdifferentiableWithinAt_add_section hs ht

/--
lemma `mdifferentiableOn_add_section` / 引理 `mdifferentiableOn_add_section`

English:
lemma mdifferentiableOn_add_section
  proof: fun x₀ hx₀ => mdifferentiableWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)

中文:
引理 mdifferentiableOn_add_section
  证明: fun x₀ hx₀ => mdifferentiableWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)

Depends on / 依赖: mdifferentiableWithinAt_add_section
-/
lemma mdifferentiableOn_add_section
    (hs : MDiff[u] (T% s)) (ht : MDiff[u] (T% t)) : MDiff[u] (T% (s + t)) :=
  fun x₀ hx₀ => mdifferentiableWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)

/--
lemma `mdifferentiable_add_section` / 引理 `mdifferentiable_add_section`

English:
lemma mdifferentiable_add_section
  proof: fun x₀ => mdifferentiableAt_add_section (hs x₀) (ht x₀)

中文:
引理 mdifferentiable_add_section
  证明: fun x₀ => mdifferentiableAt_add_section (hs x₀) (ht x₀)

Depends on / 依赖: mdifferentiableAt_add_section
-/
lemma mdifferentiable_add_section
    (hs : MDiff (T% s)) (ht : MDiff (T% t)) : MDiff (T% (s + t)) :=
  fun x₀ => mdifferentiableAt_add_section (hs x₀) (ht x₀)

/--
lemma `mdifferentiableWithinAt_neg_section` / 引理 `mdifferentiableWithinAt_neg_section`

English:
lemma mdifferentiableWithinAt_neg_section
  proof: by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x 

中文:
引理 mdifferentiableWithinAt_neg_section
  证明: by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x 

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, e.baseSet, e.linear, e.open_baseSet.mem_nhds, eventually_of_mem, hs.neg.congr_of_eventuallyEq, linear, map_neg, mdifferentiableWithinAt_section, mem_baseSet_trivializationAt, mem_nhds, mem_nhdsWithin_of_mem_nhds, open_baseSet, trivializationAt
-/
lemma mdifferentiableWithinAt_neg_section
    (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (-s)) x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx => (e.linear 𝕜 hx).map_neg ..
  · exact (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg ..

/--
lemma `mdifferentiableAt_neg_section` / 引理 `mdifferentiableAt_neg_section`

English:
lemma mdifferentiableAt_neg_section
  proof: by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact mdifferentiableWithinAt_neg_section hs

中文:
引理 mdifferentiableAt_neg_section
  证明: by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact mdifferentiableWithinAt_neg_section hs

Depends on / 依赖: mdifferentiableWithinAt_neg_section, mdifferentiableWithinAt_univ
-/
lemma mdifferentiableAt_neg_section
    (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (-s)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact mdifferentiableWithinAt_neg_section hs

/--
lemma `mdifferentiableOn_neg_section` / 引理 `mdifferentiableOn_neg_section`

English:
lemma mdifferentiableOn_neg_section
  proof: fun x₀ hx₀ => mdifferentiableWithinAt_neg_section (hs x₀ hx₀)

中文:
引理 mdifferentiableOn_neg_section
  证明: fun x₀ hx₀ => mdifferentiableWithinAt_neg_section (hs x₀ hx₀)

Depends on / 依赖: mdifferentiableWithinAt_neg_section
-/
lemma mdifferentiableOn_neg_section
    (hs : MDiff[u] (T% s)) : MDiff[u] (T% (-s)) :=
  fun x₀ hx₀ => mdifferentiableWithinAt_neg_section (hs x₀ hx₀)

/--
lemma `mdifferentiable_neg_section` / 引理 `mdifferentiable_neg_section`

English:
lemma mdifferentiable_neg_section
  given: (hs : MDiff (T% s))
  statement: MDiff (T% (-s))
  proof: fun x₀ => mdifferentiableAt_neg_section (hs x₀)

中文:
引理 mdifferentiable_neg_section
  条件: (hs : MDiff (T% s))
  结论: MDiff (T% (-s))
  证明: fun x₀ => mdifferentiableAt_neg_section (hs x₀)

Depends on / 依赖: mdifferentiableAt_neg_section
-/
lemma mdifferentiable_neg_section (hs : MDiff (T% s)) : MDiff (T% (-s)) :=
  fun x₀ => mdifferentiableAt_neg_section (hs x₀)

/--
lemma `mdifferentiableWithinAt_sub_section` / 引理 `mdifferentiableWithinAt_sub_section`

English:
lemma mdifferentiableWithinAt_sub_section
  proof: by
  rw [sub_eq_add_neg]
apply mdifferentiableWithinAt_add_section hs mdifferentiableWithinAt_neg_section ht

中文:
引理 mdifferentiableWithinAt_sub_section
  证明: by
  rw [sub_eq_add_neg]
apply mdifferentiableWithinAt_add_section hs mdifferentiableWithinAt_neg_section ht

Depends on / 依赖: mdifferentiableWithinAt_add_section, mdifferentiableWithinAt_neg_section, sub_eq_add_neg
-/
lemma mdifferentiableWithinAt_sub_section
    (hs : MDiffAt[u] (T% s) x₀) (ht : MDiffAt[u] (T% t) x₀) :
    MDiffAt[u] (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
apply mdifferentiableWithinAt_add_section hs mdifferentiableWithinAt_neg_section ht

/--
lemma `mdifferentiableAt_sub_section` / 引理 `mdifferentiableAt_sub_section`

English:
lemma mdifferentiableAt_sub_section
  proof: by
  rw [sub_eq_add_neg]
apply mdifferentiableAt_add_section hs mdifferentiableAt_neg_section ht

中文:
引理 mdifferentiableAt_sub_section
  证明: by
  rw [sub_eq_add_neg]
apply mdifferentiableAt_add_section hs mdifferentiableAt_neg_section ht

Depends on / 依赖: mdifferentiableAt_add_section, mdifferentiableAt_neg_section, sub_eq_add_neg
-/
lemma mdifferentiableAt_sub_section
    (hs : MDiffAt (T% s) x₀) (ht : MDiffAt (T% t) x₀) :
    MDiffAt (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
apply mdifferentiableAt_add_section hs mdifferentiableAt_neg_section ht

/--
lemma `mDifferentiableOn_sub_section` / 引理 `mDifferentiableOn_sub_section`

English:
lemma mDifferentiableOn_sub_section
  proof: fun x₀ hx₀ => mdifferentiableWithinAt_sub_section (hs x₀ hx₀) (ht x₀ hx₀)

中文:
引理 mDifferentiableOn_sub_section
  证明: fun x₀ hx₀ => mdifferentiableWithinAt_sub_section (hs x₀ hx₀) (ht x₀ hx₀)

Depends on / 依赖: mdifferentiableWithinAt_sub_section
-/
lemma mDifferentiableOn_sub_section
    (hs : MDiff[u] (T% s)) (ht : MDiff[u] (T% t)) : MDiff[u] (T% (s - t)) :=
  fun x₀ hx₀ => mdifferentiableWithinAt_sub_section (hs x₀ hx₀) (ht x₀ hx₀)

/--
lemma `mdifferentiable_sub_section` / 引理 `mdifferentiable_sub_section`

English:
lemma mdifferentiable_sub_section
  proof: fun x₀ => mdifferentiableAt_sub_section (hs x₀) (ht x₀)

中文:
引理 mdifferentiable_sub_section
  证明: fun x₀ => mdifferentiableAt_sub_section (hs x₀) (ht x₀)

Depends on / 依赖: mdifferentiableAt_sub_section
-/
lemma mdifferentiable_sub_section
    (hs : MDiff (T% s)) (ht : MDiff (T% t)) : MDiff (T% (s - t)) :=
  fun x₀ => mdifferentiableAt_sub_section (hs x₀) (ht x₀)

/--
lemma `MDifferentiableWithinAt.smul_section` / 引理 `MDifferentiableWithinAt.smul_section`

English:
lemma MDifferentiableWithinAt.smul_section
  proof: by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact 

中文:
引理 MDifferentiableWithinAt.smul_section
  证明: by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact 

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, e.baseSet, e.linear, e.open_baseSet.mem_nhds, eventually_of_mem, hf.smul, linear, mdifferentiableWithinAt_section, mem_baseSet_trivializationAt, mem_nhds, mem_nhdsWithin_of_mem_nhds, open_baseSet, trivializationAt
-/
lemma MDifferentiableWithinAt.smul_section
    (hf : MDiffAt[u] f x₀) (hs : MDiffAt[u] (T% s) x₀) : MDiffAt[u] (T% (f • s)) x₀ := by
  rw [mdifferentiableWithinAt_section] at hs ⊢
  set e := trivializationAt F E x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
· exact mem_nhdsWithin_of_mem_nhds
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E x₀)
    · exact fun x hx => (e.linear 𝕜 hx).2 ..
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

/--
lemma `MDifferentiableAt.smul_section` / 引理 `MDifferentiableAt.smul_section`

English:
lemma MDifferentiableAt.smul_section
  proof: by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

中文:
引理 MDifferentiableAt.smul_section
  证明: by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

Depends on / 依赖: mdifferentiableWithinAt_univ, smul_section
-/
lemma MDifferentiableAt.smul_section
    (hf : MDiffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀ := by
  rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

/--
lemma `MDifferentiableOn.smul_section` / 引理 `MDifferentiableOn.smul_section`

English:
lemma MDifferentiableOn.smul_section
  proof: fun x₀ hx₀ => .smul_section (hf x₀ hx₀) (hs x₀ hx₀)

中文:
引理 MDifferentiableOn.smul_section
  证明: fun x₀ hx₀ => .smul_section (hf x₀ hx₀) (hs x₀ hx₀)

Depends on / 依赖: smul_section
-/
lemma MDifferentiableOn.smul_section
    (hf : MDiff[u] f) (hs : MDiff[u] (T% s)) : MDiff[u] (T% (f • s)) :=
  fun x₀ hx₀ => .smul_section (hf x₀ hx₀) (hs x₀ hx₀)

/--
lemma `mdifferentiable_smul_section` / 引理 `mdifferentiable_smul_section`

English:
lemma mdifferentiable_smul_section
  proof: fun x₀ => (hf x₀).smul_section (hs x₀)

中文:
引理 mdifferentiable_smul_section
  证明: fun x₀ => (hf x₀).smul_section (hs x₀)

Depends on / 依赖: smul_section
-/
lemma mdifferentiable_smul_section
    (hf : MDiff f) (hs : MDiff (T% s)) : MDiff (T% (f • s)) :=
  fun x₀ => (hf x₀).smul_section (hs x₀)

/--
lemma `mdifferentiableWithinAt_smul_const_section` / 引理 `mdifferentiableWithinAt_smul_const_section`

English:
lemma mdifferentiableWithinAt_smul_const_section
  proof: .smul_section mdifferentiableWithinAt_const hs

中文:
引理 mdifferentiableWithinAt_smul_const_section
  证明: .smul_section mdifferentiableWithinAt_const hs

Depends on / 依赖: mdifferentiableWithinAt_const, smul_section
-/
lemma mdifferentiableWithinAt_smul_const_section
    (hs : MDiffAt[u] (T% s) x₀) :
    MDiffAt[u] (T% (a • s)) x₀ :=
  .smul_section mdifferentiableWithinAt_const hs

/--
lemma `MDifferentiableAt.smul_const_section` / 引理 `MDifferentiableAt.smul_const_section`

English:
lemma MDifferentiableAt.smul_const_section
  proof: .smul_section mdifferentiableAt_const hs

中文:
引理 MDifferentiableAt.smul_const_section
  证明: .smul_section mdifferentiableAt_const hs

Depends on / 依赖: mdifferentiableAt_const, smul_section
-/
lemma MDifferentiableAt.smul_const_section
    (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (a • s)) x₀ :=
  .smul_section mdifferentiableAt_const hs

/--
lemma `MDifferentiableOn.smul_const_section` / 引理 `MDifferentiableOn.smul_const_section`

English:
lemma MDifferentiableOn.smul_const_section
  proof: .smul_section mdifferentiableOn_const hs

中文:
引理 MDifferentiableOn.smul_const_section
  证明: .smul_section mdifferentiableOn_const hs

Depends on / 依赖: mdifferentiableOn_const, smul_section
-/
lemma MDifferentiableOn.smul_const_section
    (hs : MDiff[u] (T% s)) : MDiff[u] (T% (a • s)) :=
  .smul_section mdifferentiableOn_const hs

/--
lemma `mdifferentiable_smul_const_section` / 引理 `mdifferentiable_smul_const_section`

English:
lemma mdifferentiable_smul_const_section
  proof: fun x₀ => (hs x₀).smul_const_section

中文:
引理 mdifferentiable_smul_const_section
  证明: fun x₀ => (hs x₀).smul_const_section

Depends on / 依赖: smul_const_section
-/
lemma mdifferentiable_smul_const_section
    (hs : MDiff (T% s)) : MDiff (T% (a • s)) :=
  fun x₀ => (hs x₀).smul_const_section

/--
lemma `MDifferentiableWithinAt.sum_section` / 引理 `MDifferentiableWithinAt.sum_section`

English:
lemma MDifferentiableWithinAt.sum_section
  statement: {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (contMDiffWithinAt_zeroSection 𝕜 E).mdifferentiableWithinAt one_ne_zero
  | insert i s hi h =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simpa [Finset.sum_insert hi] using mdifferentiableWithinA

中文:
引理 MDifferentiableWithinAt.sum_section
  结论: {ι : 类型} {s : 有限集 ι} {t : ι -> (x : B) -> E x}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (contMDiffWithinAt_zeroSection 𝕜 E).mdifferentiableWithinAt one_ne_zero
  | insert i s hi h =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simpa [Finset.sum_insert hi] using mdifferentiableWithinA

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sum_insert, classical, contMDiffWithinAt_zeroSection, forall_eq_or_imp, induction_on, insert, mdifferentiableWithinAt, mdifferentiableWithinAt_add_section, mem_insert, one_ne_zero, sum_insert
-/
lemma MDifferentiableWithinAt.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x}
    (hs : forall i in s, MDiffAt[u] (T% (t i ·)) x₀) :
    MDiffAt[u] (T% (fun x => ∑ i in s, (t i x))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (contMDiffWithinAt_zeroSection 𝕜 E).mdifferentiableWithinAt one_ne_zero
  | insert i s hi h =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    simpa [Finset.sum_insert hi] using mdifferentiableWithinAt_add_section (hs.1) (h hs.2)

/--
lemma `MDifferentiableAt.sum_section` / 引理 `MDifferentiableAt.sum_section`

English:
lemma MDifferentiableAt.sum_section
  statement: {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B}
  proof: by
  simp_rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact MDifferentiableWithinAt.sum_section hs

中文:
引理 MDifferentiableAt.sum_section
  结论: {ι : 类型} {s : 有限集 ι} {t : ι -> (x : B) -> E x} {x₀ : B}
  证明: by
  simp_rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact MDifferentiableWithinAt.sum_section hs

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.sum_section, mdifferentiableWithinAt_univ, simp_rw, sum_section
-/
lemma MDifferentiableAt.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B}
    (hs : forall i in s, MDiffAt (T% (t i ·)) x₀) :
    MDiffAt (T% (fun x => ∑ i in s, (t i x))) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at hs ⊢
  exact MDifferentiableWithinAt.sum_section hs

/--
lemma `MDifferentiableOn.sum_section` / 引理 `MDifferentiableOn.sum_section`

English:
lemma MDifferentiableOn.sum_section
  statement: {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x}
  proof: fun x₀ hx₀ => .sum_section fun i hi => hs i hi x₀ hx₀

中文:
引理 MDifferentiableOn.sum_section
  结论: {ι : 类型} {s : 有限集 ι} {t : ι -> (x : B) -> E x}
  证明: fun x₀ hx₀ => .sum_section fun i hi => hs i hi x₀ hx₀

Depends on / 依赖: sum_section
-/
lemma MDifferentiableOn.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x}
    (hs : forall i in s, MDiff[u] (T% (t i ·))) :
    MDiff[u] (T% (fun x => ∑ i in s, (t i x))) :=
  fun x₀ hx₀ => .sum_section fun i hi => hs i hi x₀ hx₀

/--
lemma `MDifferentiable.sum_section` / 引理 `MDifferentiable.sum_section`

English:
lemma MDifferentiable.sum_section
  statement: {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x}
  proof: fun x₀ => .sum_section fun i hi => (hs i) hi x₀

中文:
引理 MDifferentiable.sum_section
  结论: {ι : 类型} {s : 有限集 ι} {t : ι -> (x : B) -> E x}
  证明: fun x₀ => .sum_section fun i hi => (hs i) hi x₀

Depends on / 依赖: sum_section
-/
lemma MDifferentiable.sum_section {ι : Type*} {s : Finset ι} {t : ι -> (x : B) -> E x}
    (hs : forall i in s, MDiff (T% (t i ·))) :
    MDiff (T% (fun x => ∑ i in s, (t i x))) :=
  fun x₀ => .sum_section fun i hi => (hs i) hi x₀

/--
lemma `MDifferentiableOn.smul_section_of_tsupport` / 引理 `MDifferentiableOn.smul_section_of_tsupport`

English:
lemma MDifferentiableOn.smul_section_of_tsupport
  statement: {s : Π (x : B), E x} {ψ : B -> 𝕜}
  proof: by
  apply mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((mdifferentiable_zeroSection _ _).mdifferentiableOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, z

中文:
引理 MDifferentiableOn.smul_section_of_tsupport
  结论: {s : Π (x : B), E x} {ψ : B -> 𝕜}
  证明: by
  apply mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((mdifferentiable_zeroSection _ _).mdifferentiableOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, z

Depends on / 依赖: Set.compl_subset_compl.mpr, Set.compl_subset_iff_union.mp, compl_subset_compl, compl_subset_iff_union, image_eq_zero_of_notMem_tsupport, isClosed_tsupport, isOpen_compl_iff, isOpen_compl_iff.mpr, mdifferentiableOn, mdifferentiable_of_mdifferentiableOn_union_of_isOpen, mdifferentiable_zeroSection, smul_section, tsupport, zeroSection
-/
lemma MDifferentiableOn.smul_section_of_tsupport {s : Π (x : B), E x} {ψ : B -> 𝕜}
    (hψ : MDiff[u] ψ) (ht : IsOpen u) (ht' : tsupport ψ subseteq u) (hs : MDiff[u] (T% s)) :
    MDiff (T% (ψ • s)) := by
  apply mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((mdifferentiable_zeroSection _ _).mdifferentiableOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
· exact Set.compl_subset_iff_union.mp Set.compl_subset_compl.mpr ht'

variable {ι : Type*} {t : ι -> (x : B) -> E x}

open Function

/--
lemma `MDifferentiableWithinAt.sum_section_of_locallyFinite` / 引理 `MDifferentiableWithinAt.sum_section_of_locallyFinite`

English:
lemma MDifferentiableWithinAt.sum_section_of_locallyFinite
  proof: by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i => {x | t i x != 0}) i inter u').Nonempty}
  have := hfin.fintype
  have : MDiffAt[

中文:
引理 MDifferentiableWithinAt.sum_section_of_locallyFinite
  证明: by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i => {x | t i x != 0}) i inter u').Nonempty}
  have := hfin.fintype
  have : MDiffAt[
-/
lemma MDifferentiableWithinAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0})
    (ht' : forall i, MDiffAt[u] (T% (t i ·)) x₀) :
    MDiffAt[u] (T% (fun x => ∑' i, (t i x))) x₀ := by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i => {x | t i x != 0}) i inter u').Nonempty}
  have := hfin.fintype
  have : MDiffAt[u inter u'] (T% (fun x => ∑ i in s, (t i x))) x₀ :=
     .sum_section fun i _ => ((ht' i).mono inter_subset_left)
  apply (mdifferentiableWithinAt_inter hu').mp
  apply this.congr' (fun y hy => ?_) inter_subset_right (mem_of_mem_nhds hu')
  rw [TotalSpace.mk_inj]; rw [tsum_eq_sum']
  refine support_subset_iff'.mpr fun i hi => ?_
  by_contra! h
  have : i in s.toFinset := by
    refine Set.mem_toFinset.mpr ?_
    simp only [s, ne_eq, Set.mem_ofPred_eq]
    use y
    simp [h, hy]
  exact hi this

/--
lemma `MDifferentiableAt.sum_section_of_locallyFinite` / 引理 `MDifferentiableAt.sum_section_of_locallyFinite`

English:
lemma MDifferentiableAt.sum_section_of_locallyFinite
  proof: by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

中文:
引理 MDifferentiableAt.sum_section_of_locallyFinite
  证明: by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

Depends on / 依赖: mdifferentiableWithinAt_univ, simp_rw, sum_section_of_locallyFinite
-/
lemma MDifferentiableAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0})
    (ht' : forall i, MDiffAt (T% (t i ·)) x₀) :
    MDiffAt (T% (fun x => ∑' i, (t i x))) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

/--
lemma `MDifferentiableOn.sum_section_of_locallyFinite` / 引理 `MDifferentiableOn.sum_section_of_locallyFinite`

English:
lemma MDifferentiableOn.sum_section_of_locallyFinite
  proof: fun x hx => .sum_section_of_locallyFinite ht (ht' · x hx)

中文:
引理 MDifferentiableOn.sum_section_of_locallyFinite
  证明: fun x hx => .sum_section_of_locallyFinite ht (ht' · x hx)

Depends on / 依赖: sum_section_of_locallyFinite
-/
lemma MDifferentiableOn.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0})
    (ht' : forall i, MDiff[u] (T% (t i ·))) :
    MDiff[u] (T% (fun x => ∑' i, (t i x))) :=
  fun x hx => .sum_section_of_locallyFinite ht (ht' · x hx)

/--
lemma `MDifferentiable.sum_section_of_locallyFinite` / 引理 `MDifferentiable.sum_section_of_locallyFinite`

English:
lemma MDifferentiable.sum_section_of_locallyFinite
  statement: (ht : LocallyFinite fun i => {x : B | t i x != 0})
  proof: fun x => .sum_section_of_locallyFinite ht fun i => ht' i x

中文:
引理 MDifferentiable.sum_section_of_locallyFinite
  结论: (ht : 局部有限 fun i => {x : B | t i x != 0})
  证明: fun x => .sum_section_of_locallyFinite ht fun i => ht' i x

Depends on / 依赖: sum_section_of_locallyFinite
-/
lemma MDifferentiable.sum_section_of_locallyFinite (ht : LocallyFinite fun i => {x : B | t i x != 0})
    (ht' : forall i, MDiff (T% (t i ·))) :
    MDiff (T% (fun x => ∑' i, (t i x))) :=
  fun x => .sum_section_of_locallyFinite ht fun i => ht' i x

/--
lemma `MDifferentiableWithinAt.finsum_section_of_locallyFinite` / 引理 `MDifferentiableWithinAt.finsum_section_of_locallyFinite`

English:
lemma MDifferentiableWithinAt.finsum_section_of_locallyFinite
  proof: by
  apply (MDifferentiableWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy => ?_) (by grind) trivial
  choose U hu hfin using ht y
  have : {x | t x y != 0} subseteq {i | ((fun i => {x | t i x != 0}) i inter U).Nonempty} := by
    intro x hx
    rw [Set.mem_ofPre

中文:
引理 MDifferentiableWithinAt.finsum_section_of_locallyFinite
  证明: by
  apply (MDifferentiableWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy => ?_) (by grind) trivial
  choose U hu hfin using ht y
  have : {x | t x y != 0} subseteq {i | ((fun i => {x | t i x != 0}) i inter U).Nonempty} := by
    intro x hx
    rw [Set.mem_ofPre

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.sum_section_of_locallyFinite, Nonempty, Set.mem_ofPred, Set.univ, hfin.subset, mem_ofPred, mem_of_mem_nhds, subset, subseteq, sum_section_of_locallyFinite, tsum_eq_finsum
-/
lemma MDifferentiableWithinAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0})
    (ht' : forall i, MDiffAt[u] (T% (t i ·)) x₀) :
    MDiffAt[u] (T% (fun x => ∑ᶠ i, t i x)) x₀ := by
  apply (MDifferentiableWithinAt.sum_section_of_locallyFinite ht ht').congr' (t := Set.univ)
      (fun y hy => ?_) (by grind) trivial
  choose U hu hfin using ht y
  have : {x | t x y != 0} subseteq {i | ((fun i => {x | t i x != 0}) i inter U).Nonempty} := by
    intro x hx
    rw [Set.mem_ofPred] at hx ⊢
    use y
    simpa using ⟨hx, mem_of_mem_nhds hu⟩
  rw [tsum_eq_finsum (hfin.subset this)]

/--
lemma `MDifferentiableAt.finsum_section_of_locallyFinite` / 引理 `MDifferentiableAt.finsum_section_of_locallyFinite`

English:
lemma MDifferentiableAt.finsum_section_of_locallyFinite
  proof: by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

中文:
引理 MDifferentiableAt.finsum_section_of_locallyFinite
  证明: by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

Depends on / 依赖: finsum_section_of_locallyFinite, mdifferentiableWithinAt_univ, simp_rw
-/
lemma MDifferentiableAt.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0})
    (ht' : forall i, MDiffAt (T% (t i ·)) x₀) :
    MDiffAt (T% (fun x => ∑ᶠ i, t i x)) x₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at ht' ⊢
  exact .finsum_section_of_locallyFinite ht ht'

/--
lemma `MDifferentiableOn.finsum_section_of_locallyFinite` / 引理 `MDifferentiableOn.finsum_section_of_locallyFinite`

English:
lemma MDifferentiableOn.finsum_section_of_locallyFinite
  proof: fun x hx => .finsum_section_of_locallyFinite ht fun i => ht' i x hx

中文:
引理 MDifferentiableOn.finsum_section_of_locallyFinite
  证明: fun x hx => .finsum_section_of_locallyFinite ht fun i => ht' i x hx

Depends on / 依赖: finsum_section_of_locallyFinite
-/
lemma MDifferentiableOn.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0}) (ht' : forall i, MDiff[u] (T% (t i ·))) :
    MDiff[u] (T% (fun x => ∑ᶠ i, t i x)) :=
  fun x hx => .finsum_section_of_locallyFinite ht fun i => ht' i x hx

/--
lemma `MDifferentiable.finsum_section_of_locallyFinite` / 引理 `MDifferentiable.finsum_section_of_locallyFinite`

English:
lemma MDifferentiable.finsum_section_of_locallyFinite
  proof: fun x => .finsum_section_of_locallyFinite ht fun i => ht' i x

中文:
引理 MDifferentiable.finsum_section_of_locallyFinite
  证明: fun x => .finsum_section_of_locallyFinite ht fun i => ht' i x

Depends on / 依赖: finsum_section_of_locallyFinite
-/
lemma MDifferentiable.finsum_section_of_locallyFinite
    (ht : LocallyFinite fun i => {x : B | t i x != 0}) (ht' : forall i, MDiff (T% (t i ·))) :
    MDiff (T% (fun x => ∑ᶠ i, t i x)) :=
  fun x => .finsum_section_of_locallyFinite ht fun i => ht' i x

end operations

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ -> Type*} {E₂ : B₂ -> Type*} [NontriviallyNormedField 𝕜]
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, TopologicalSpace (E₁ x)] [forall x, AddCommGroup (E₂ x)]
  [forall x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [forall x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : Nat∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M -> B₁} {b₂ : M -> B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) ->L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/--
lemma `MDifferentiableWithinAt.clm_apply_of_inCoordinates` / 引理 `MDifferentiableWithinAt.clm_apply_of_inCoordinates`

English:
lemma MDifferentiableWithinAt.clm_apply_of_inCoordinates
  proof: by
  rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_insert
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.insert.continuousWithinAt
    appl

中文:
引理 MDifferentiableWithinAt.clm_apply_of_inCoordinates
  证明: by
  rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_insert
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.insert.continuousWithinAt
    appl

Depends on / 依赖: FiberBundle, FiberBundle.mem_baseSet_trivializationAt, MDifferentiableWithinAt, MDifferentiableWithinAt.clm_apply, baseSet, clm_apply, congr_of_eventuallyEq_insert, continuousWithinAt, insert, insert.continuousWithinAt, mdifferentiableWithinAt_totalSpace, mem_baseSet_trivializationAt, mem_nhds, open_baseSet, open_baseSet.mem_nhds, trivializationAt
-/
lemma MDifferentiableWithinAt.clm_apply_of_inCoordinates
    (hϕ : MDiffAt[s] (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : MDiffAt[s] (fun m => (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : MDiffAt[s] b₂ m₀) :
    MDiffAt[s] (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_insert
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.insert.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.insert.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp [hm]

/--
lemma `MDifferentiableAt.clm_apply_of_inCoordinates` / 引理 `MDifferentiableAt.clm_apply_of_inCoordinates`

English:
lemma MDifferentiableAt.clm_apply_of_inCoordinates
  proof: by
  rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

中文:
引理 MDifferentiableAt.clm_apply_of_inCoordinates
  证明: by
  rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.clm_apply_of_inCoordinates, clm_apply_of_inCoordinates, mdifferentiableWithinAt_univ
-/
lemma MDifferentiableAt.clm_apply_of_inCoordinates
    (hϕ : MDiffAt (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : MDiffAt (fun m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : MDiffAt b₂ m₀) :
    MDiffAt (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end

section extend

namespace FiberBundle
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F]
  {V : M -> Type*} [TopologicalSpace (TotalSpace F V)] [(x : M) -> AddCommGroup (V x)]
  [(x : M) -> TopologicalSpace (V x)]
  [FiberBundle F V] [NormedSpace 𝕜 F] {k : WithTop Nat∞}

/--
lemma `exists_contMDiffOn_extend` / 引理 `exists_contMDiffOn_extend`

English:
lemma exists_contMDiffOn_extend
  statement: [(x : M) -> Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  proof: by
  set t := trivializationAt F V x₀
  refine ⟨t.baseSet, ?_, ?_⟩
  · refine t.open_baseSet.mem_nhds ?_
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  suffices CMDiff[t.baseSet] k (fun x => (t ⟨x, extend F σ₀ x⟩).2) by
    intro x hx
    rw [t.contMDiffWithinAt_section _ hx]
    exact thi

中文:
引理 存在_contMDiffOn_extend
  结论: [(x : M) -> 模 𝕜 (V x)] [向量丛 𝕜 F V]
  证明: by
  set t := trivializationAt F V x₀
  refine ⟨t.baseSet, ?_, ?_⟩
  · refine t.open_baseSet.mem_nhds ?_
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  suffices CMDiff[t.baseSet] k (fun x => (t ⟨x, extend F σ₀ x⟩).2) by
    intro x hx
    rw [t.contMDiffWithinAt_section _ hx]
    exact thi

Depends on / 依赖: CMDiff, FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, contMDiffOn_const, contMDiffWithinAt_section, extend, mem_baseSet_trivializationAt, mem_nhds, open_baseSet, t.baseSet, t.contMDiffWithinAt_section, t.open_baseSet.mem_nhds, this.congr, trivializationAt
-/
lemma exists_contMDiffOn_extend [(x : M) -> Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
    [ContMDiffVectorBundle k F V I] {x₀ : M} (σ₀ : V x₀) :
    exists s in 𝓝 x₀, CMDiff[s] k (T% (extend F σ₀)) := by
  set t := trivializationAt F V x₀
  refine ⟨t.baseSet, ?_, ?_⟩
  · refine t.open_baseSet.mem_nhds ?_
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  suffices CMDiff[t.baseSet] k (fun x => (t ⟨x, extend F σ₀ x⟩).2) by
    intro x hx
    rw [t.contMDiffWithinAt_section _ hx]
    exact this x hx
  let w : F := (t ⟨x₀, σ₀⟩).2
  have : CMDiff[t.baseSet] k (fun (_x : M) => w) := contMDiffOn_const
  exact this.congr (fun x hx => by simp [extend, t, w, hx])

/--
lemma `contMDiffAt_extend` / 引理 `contMDiffAt_extend`

English:
lemma contMDiffAt_extend
  given: {x : M} (σ₀ : V x)
  statement: CMDiffAt k (T% (extend F σ₀)) x
  proof: by
  rw [contMDiffAt_section]
  set t := trivializationAt F V x
  let w : F := (t ⟨x, σ₀⟩).2
  have : CMDiffAt k (fun (_x : M) => w) x := contMDiffAt_const
  refine this.congr_of_eventuallyEq ?_
  apply eventually_nhds_iff.mpr
  refine ⟨t.baseSet, ?_, t.open_baseSet, ?_⟩
  · intro x hx
    simp [ext

中文:
引理 contMDiffAt_extend
  条件: {x : M} (σ₀ : V x)
  结论: CMDiffAt k (T% (extend F σ₀)) x
  证明: by
  rw [contMDiffAt_section]
  set t := trivializationAt F V x
  let w : F := (t ⟨x, σ₀⟩).2
  have : CMDiffAt k (fun (_x : M) => w) x := contMDiffAt_const
  refine this.congr_of_eventuallyEq ?_
  apply eventually_nhds_iff.mpr
  refine ⟨t.baseSet, ?_, t.open_baseSet, ?_⟩
  · intro x hx
    simp [ext

Depends on / 依赖: CMDiffAt, FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, congr_of_eventuallyEq, contMDiffAt_const, contMDiffAt_section, eventually_nhds_iff, eventually_nhds_iff.mpr, extend, mem_baseSet_trivializationAt, open_baseSet, t.baseSet, t.open_baseSet, this.congr_of_eventuallyEq, trivializationAt
-/
lemma contMDiffAt_extend {x : M} (σ₀ : V x) : CMDiffAt k (T% (extend F σ₀)) x := by
  rw [contMDiffAt_section]
  set t := trivializationAt F V x
  let w : F := (t ⟨x, σ₀⟩).2
  have : CMDiffAt k (fun (_x : M) => w) x := contMDiffAt_const
  refine this.congr_of_eventuallyEq ?_
  apply eventually_nhds_iff.mpr
  refine ⟨t.baseSet, ?_, t.open_baseSet, ?_⟩
  · intro x hx
    simp [extend, t, hx, w]
  · exact FiberBundle.mem_baseSet_trivializationAt' x

@[deprecated (since := "2026-06-30")] alias contMDiffAt_extend' := contMDiffAt_extend

/--
lemma `exists_mdifferentiableOn_extend` / 引理 `exists_mdifferentiableOn_extend`

English:
lemma exists_mdifferentiableOn_extend
  statement: [forall x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  proof: by
  obtain ⟨s, hs, hsσ⟩ := exists_contMDiffOn_extend (k := 1) I F σ₀
  exact ⟨s, hs, hsσ.mdifferentiableOn one_ne_zero⟩

中文:
引理 存在_mdifferentiableOn_extend
  结论: [对任意 x, 模 𝕜 (V x)] [向量丛 𝕜 F V]
  证明: by
  obtain ⟨s, hs, hsσ⟩ := exists_contMDiffOn_extend (k := 1) I F σ₀
  exact ⟨s, hs, hsσ.mdifferentiableOn one_ne_zero⟩

Depends on / 依赖: exists_contMDiffOn_extend, mdifferentiableOn, one_ne_zero
-/
lemma exists_mdifferentiableOn_extend [forall x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
    [ContMDiffVectorBundle 1 F V I] {x₀ : M} (σ₀ : V x₀) :
    exists s in 𝓝 x₀, MDiff[s] (T% (extend F σ₀)) := by
  obtain ⟨s, hs, hsσ⟩ := exists_contMDiffOn_extend (k := 1) I F σ₀
  exact ⟨s, hs, hsσ.mdifferentiableOn one_ne_zero⟩

/--
lemma `mdifferentiableAt_extend` / 引理 `mdifferentiableAt_extend`

English:
lemma mdifferentiableAt_extend
  given: {x : M} (σ₀ : V x)
  proof: (contMDiffAt_extend (k := 1) I F σ₀).mdifferentiableAt one_ne_zero

中文:
引理 mdifferentiableAt_extend
  条件: {x : M} (σ₀ : V x)
  证明: (contMDiffAt_extend (k := 1) I F σ₀).mdifferentiableAt one_ne_zero

Depends on / 依赖: contMDiffAt_extend, mdifferentiableAt, one_ne_zero
-/
lemma mdifferentiableAt_extend {x : M} (σ₀ : V x) :
    MDiffAt (T% (extend F σ₀)) x :=
  (contMDiffAt_extend (k := 1) I F σ₀).mdifferentiableAt one_ne_zero

variable (V) in
/--
lemma `_root_.VectorBundle.injective_eval_mdifferentiableAt_sec` / 引理 `_root_.VectorBundle.injective_eval_mdifferentiableAt_sec`

English:
lemma _root_.VectorBundle.injective_eval_mdifferentiableAt_sec
  statement: [forall x, Module 𝕜 (V x)]
  proof: by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (mdifferentiableAt_extend ..))

中文:
引理 _root_.向量丛.injective_eval_mdifferentiableAt_sec
  结论: [对任意 x, 模 𝕜 (V x)]
  证明: by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (mdifferentiableAt_extend ..))

Depends on / 依赖: extend, mdifferentiableAt_extend
-/
lemma _root_.VectorBundle.injective_eval_mdifferentiableAt_sec [forall x, Module 𝕜 (V x)]
    (W : Type*) [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] (x : M) :
    Function.Injective
      (fun A : V x ->L[𝕜] W =>
        fun (Z : Π x, V x) (_ : MDiffAt (T% Z) x) => A (Z x)) := by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (mdifferentiableAt_extend ..))

variable (V) in
/--
lemma `_root_.VectorBundle.injective_eval_contMDiffAt_sec` / 引理 `_root_.VectorBundle.injective_eval_contMDiffAt_sec`

English:
lemma _root_.VectorBundle.injective_eval_contMDiffAt_sec
  statement: {n : WithTop Nat∞} [forall x, Module 𝕜 (V x)]
  proof: by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (contMDiffAt_extend ..))

中文:
引理 _root_.向量丛.injective_eval_contMDiffAt_sec
  结论: {n : WithTop 自然数∞} [对任意 x, 模 𝕜 (V x)]
  证明: by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (contMDiffAt_extend ..))

Depends on / 依赖: contMDiffAt_extend, extend
-/
lemma _root_.VectorBundle.injective_eval_contMDiffAt_sec {n : WithTop Nat∞} [forall x, Module 𝕜 (V x)]
    (W : Type*) [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] (x : M) :
    Function.Injective
      (fun A : V x ->L[𝕜] W =>
        fun (Z : Π x, V x) (_ : CMDiffAt n (T% Z) x) => A (Z x)) := by
  intro X X' h
  ext σ₀
  simpa using congr($h (extend F σ₀) (contMDiffAt_extend ..))

end FiberBundle
end extend
