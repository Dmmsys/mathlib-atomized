/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear
public import Mathlib.Topology.VectorBundle.Constructions

/-! # `C^n` vector bundles

This file defines `C^n` vector bundles over a manifold.

Let `E` be a topological vector bundle, with model fiber `F` and base space `B`. We consider `E` as
carrying a charted space structure given by its trivializations -- these are charts to `B × F`.
Then, by "composition", if `B` is itself a charted space over `H` (e.g. a smooth manifold), then `E`
is also a charted space over `H × F`.

Now, we define `ContMDiffVectorBundle` as the `Prop` of having `C^n` transition functions.
Recall the structure groupoid `contMDiffFiberwiseLinear` on `B × F` consisting of `C^n`, fiberwise
linear open partial homeomorphisms. We show that our definition of "`C^n` vector bundle" implies
`HasGroupoid` for this groupoid, and show (by a "composition" of `HasGroupoid` instances) that
this means that a `C^n` vector bundle is a `C^n` manifold.

Since `ContMDiffVectorBundle` is a mixin, it should be easy to make variants and for many such
variants to coexist -- vector bundles can be `C^n` vector bundles over several different base
fields, etc.

## Main definitions and constructions

* `FiberBundle.chartedSpace`: A fiber bundle `E` over a base `B` with model fiber `F` is naturally
  a charted space modelled on `B × F`.

* `FiberBundle.chartedSpace'`: Let `B` be a charted space modelled on `HB`. Then a fiber bundle
  `E` over a base `B` with model fiber `F` is naturally a charted space modelled on `HB.prod F`.

* `ContMDiffVectorBundle`: Mixin class stating that a (topological) `VectorBundle` is `C^n`, in the
  sense of having `C^n` transition functions, where the smoothness index `n`
  belongs to `ℕ∞ω` (notation for `WithTop ℕ∞` in the `ContDiff` scope).

* `ContMDiffFiberwiseLinear.hasGroupoid`: For a `C^n` vector bundle `E` over `B` with fiber
  modelled on `F`, the change-of-co-ordinates between two trivializations `e`, `e'` for `E`,
  considered as charts to `B × F`, is `C^n` and fiberwise linear, in the sense of belonging to the
  structure groupoid `contMDiffFiberwiseLinear`.

* `Bundle.TotalSpace.isManifold`: A `C^n` vector bundle is naturally a `C^n` manifold.

* `VectorBundleCore.instContMDiffVectorBundle`: If a (topological) `VectorBundleCore` is `C^n`,
  in the sense of having `C^n` transition functions (cf. `VectorBundleCore.IsContMDiff`),
  then the vector bundle constructed from it is a `C^n` vector bundle.

* `VectorPrebundle.contMDiffVectorBundle`: If a `VectorPrebundle` is `C^n`,
  in the sense of having `C^n` transition functions (cf. `VectorPrebundle.IsContMDiff`),
  then the vector bundle constructed from it is a `C^n` vector bundle.

* `Bundle.Prod.contMDiffVectorBundle`: The direct sum of two `C^n` vector bundles is a `C^n`
  vector bundle.
-/

@[expose] public section

assert_not_exists mfderiv

open Bundle Set OpenPartialHomeomorph

open Function (id_def)

open Filter

open scoped Manifold Bundle Topology ContDiff

variable {n : Nat∞ω} {𝕜 B B' F M : Type*} {E : B -> Type*}

/-! ### Charted space structure on a fiber bundle -/


section

variable [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)] [forall x, TopologicalSpace (E x)]
  {HB : Type*} [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

/--
Instance `FiberBundle.chartedSpace'` / 实例 `FiberBundle.chartedSpace'`

English:
instance FiberBundle.chartedSpace'
  signature: : ChartedSpace (B × F) (TotalSpace F E) where
  body: (fun e : Trivialization F (π F E) => e.toOpenPartialHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toOpenPartialHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas _ := me

中文:
实例 FiberBundle.chartedSpace'
  签名: : ChartedSpace (B × F) (TotalSpace F E) where
  定义体: (fun e : Trivialization F (π F E) => e.toOpenPartialHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toOpenPartialHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas _ := me

Depends on / 依赖: Trivialization, chartAt, chart_mem_atlas, e.toOpenPartialHomeomorph, mem_baseSet_trivializationAt, mem_chart_source, mem_image_of_mem, mem_source, mem_source.mpr, toOpenPartialHomeomorph, trivializationAt, trivializationAtlas, trivialization_mem_atlas, x.proj
-/
instance FiberBundle.chartedSpace' : ChartedSpace (B × F) (TotalSpace F E) where
  atlas :=
    (fun e : Trivialization F (π F E) => e.toOpenPartialHomeomorph) '' trivializationAtlas F E
  chartAt x := (trivializationAt F E x.proj).toOpenPartialHomeomorph
  mem_chart_source x :=
    (trivializationAt F E x.proj).mem_source.mpr (mem_baseSet_trivializationAt F E x.proj)
  chart_mem_atlas _ := mem_image_of_mem _ (trivialization_mem_atlas F E _)

/--
theorem `FiberBundle.chartedSpace'_chartAt` / 定理 `FiberBundle.chartedSpace'_chartAt`

English:
theorem FiberBundle.chartedSpace'_chartAt
  given: (x : TotalSpace F E)
  proof: rfl

中文:
定理 FiberBundle.chartedSpace'_chartAt
  条件: (x : TotalSpace F E)
  证明: rfl
-/
theorem FiberBundle.chartedSpace'_chartAt (x : TotalSpace F E) :
    chartAt (B × F) x = (trivializationAt F E x.proj).toOpenPartialHomeomorph :=
  rfl

/- Porting note: In Lean 3, the next instance was inside a section with locally reducible
`ModelProd` and it used `ModelProd B F` as the intermediate space. Using `B × F` in the middle
gives the same instance.
-/
--attribute [local reducible] ModelProd

/--
Instance `FiberBundle.chartedSpace` / 实例 `FiberBundle.chartedSpace`

English:
instance FiberBundle.chartedSpace
  signature: : ChartedSpace (ModelProd HB F) (TotalSpace F E)
  body: ChartedSpace.comp _ (B × F) _

中文:
实例 FiberBundle.chartedSpace
  签名: : ChartedSpace (ModelProd HB F) (TotalSpace F E)
  定义体: ChartedSpace.comp _ (B × F) _

Depends on / 依赖: ChartedSpace, ChartedSpace.comp
-/
instance FiberBundle.chartedSpace : ChartedSpace (ModelProd HB F) (TotalSpace F E) :=
  ChartedSpace.comp _ (B × F) _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FiberBundle.chartedSpace_chartAt` / 定理 `FiberBundle.chartedSpace_chartAt`

English:
theorem FiberBundle.chartedSpace_chartAt
  given: (x : TotalSpace F E)
  proof: by
  dsimp only [chartAt_comp, prodChartedSpace_chartAt, FiberBundle.chartedSpace'_chartAt,
    chartAt_self_eq]
  rw [Trivialization.coe_coe]; rw [Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E x.proj)]

中文:
定理 FiberBundle.chartedSpace_chartAt
  条件: (x : TotalSpace F E)
  证明: by
  dsimp only [chartAt_comp, prodChartedSpace_chartAt, FiberBundle.chartedSpace'_chartAt,
    chartAt_self_eq]
  rw [Trivialization.coe_coe]; rw [Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E x.proj)]

Depends on / 依赖: FiberBundle, FiberBundle.chartedSpace, Trivialization, Trivialization.coe_coe, Trivialization.coe_fst, _chartAt, chartAt_comp, chartAt_self_eq, chartedSpace, coe_coe, coe_fst, mem_baseSet_trivializationAt, prodChartedSpace_chartAt, x.proj
-/
theorem FiberBundle.chartedSpace_chartAt (x : TotalSpace F E) :
    chartAt (ModelProd HB F) x =
      (trivializationAt F E x.proj).toOpenPartialHomeomorph ≫ₕ
        (chartAt HB x.proj).prod (OpenPartialHomeomorph.refl F) := by
  dsimp only [chartAt_comp, prodChartedSpace_chartAt, FiberBundle.chartedSpace'_chartAt,
    chartAt_self_eq]
  rw [Trivialization.coe_coe]; rw [Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E x.proj)]

/--
theorem `FiberBundle.chartedSpace_chartAt_symm_fst` / 定理 `FiberBundle.chartedSpace_chartAt_symm_fst`

English:
theorem FiberBundle.chartedSpace_chartAt_symm_fst
  statement: (x : TotalSpace F E) (y : ModelProd HB F)
  proof: by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  exact (trivializationAt F E x.proj).proj_symm_apply hy.2

中文:
定理 FiberBundle.chartedSpace_chartAt_symm_fst
  结论: (x : TotalSpace F E) (y : ModelProd HB F)
  证明: by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  exact (trivializationAt F E x.proj).proj_symm_apply hy.2

Depends on / 依赖: FiberBundle, FiberBundle.chartedSpace_chartAt, chartedSpace_chartAt, mfld_simps, proj_symm_apply, trivializationAt, x.proj
-/
theorem FiberBundle.chartedSpace_chartAt_symm_fst (x : TotalSpace F E) (y : ModelProd HB F)
    (hy : y in (chartAt (ModelProd HB F) x).target) :
    ((chartAt (ModelProd HB F) x).symm y).proj = (chartAt HB x.proj).symm y.1 := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps] at hy ⊢
  exact (trivializationAt F E x.proj).proj_symm_apply hy.2

end

section

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [forall x, TopologicalSpace (E x)] {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} (E' : B -> Type*) [forall x, Zero (E' x)] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]

variable [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FiberBundle.extChartAt` / 定理 `FiberBundle.extChartAt`

English:
theorem FiberBundle.extChartAt
  given: (x : TotalSpace F E)
  proof: by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.extend]
  simp only [PartialEquiv.trans_assoc, mfld_simps]
  -- Porting note: should not be needed
  rw [PartialEquiv.prod_trans]; rw [PartialEquiv.refl_trans]

中文:
定理 FiberBundle.extChartAt
  条件: (x : TotalSpace F E)
  证明: by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.extend]
  simp only [PartialEquiv.trans_assoc, mfld_simps]
  -- Porting note: should not be needed
  rw [PartialEquiv.prod_trans]; rw [PartialEquiv.refl_trans]
-/
protected theorem FiberBundle.extChartAt (x : TotalSpace F E) :
    extChartAt (IB.prod 𝓘(𝕜, F)) x =
      (trivializationAt F E x.proj).toPartialEquiv ≫
        (extChartAt IB x.proj).prod (PartialEquiv.refl F) := by
  simp_rw [extChartAt, FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.extend]
  simp only [PartialEquiv.trans_assoc, mfld_simps]
  -- Porting note: should not be needed
  rw [PartialEquiv.prod_trans]; rw [PartialEquiv.refl_trans]

/--
theorem `FiberBundle.extChartAt_target` / 定理 `FiberBundle.extChartAt_target`

English:
theorem FiberBundle.extChartAt_target
  given: (x : TotalSpace F E)
  proof: by
  rw [FiberBundle.extChartAt]; rw [PartialEquiv.trans_target]; rw [Trivialization.target_eq]; rw [inter_prod]
  rfl

中文:
定理 FiberBundle.extChartAt_target
  条件: (x : TotalSpace F E)
  证明: by
  rw [FiberBundle.extChartAt]; rw [PartialEquiv.trans_target]; rw [Trivialization.target_eq]; rw [inter_prod]
  rfl
-/
protected theorem FiberBundle.extChartAt_target (x : TotalSpace F E) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) x).target =
      ((extChartAt IB x.proj).target inter
        (extChartAt IB x.proj).symm ⁻¹' (trivializationAt F E x.proj).baseSet) ×ˢ univ := by
  rw [FiberBundle.extChartAt]; rw [PartialEquiv.trans_target]; rw [Trivialization.target_eq]; rw [inter_prod]
  rfl

/--
theorem `FiberBundle.writtenInExtChartAt_trivializationAt` / 定理 `FiberBundle.writtenInExtChartAt_trivializationAt`

English:
theorem FiberBundle.writtenInExtChartAt_trivializationAt
  statement: {x : TotalSpace F E} {y}
  proof: writtenInExtChartAt_chartAt_comp _ hy

中文:
定理 FiberBundle.writtenInExtChartAt_trivializationAt
  结论: {x : TotalSpace F E} {y}
  证明: writtenInExtChartAt_chartAt_comp _ hy

Depends on / 依赖: writtenInExtChartAt_chartAt_comp
-/
theorem FiberBundle.writtenInExtChartAt_trivializationAt {x : TotalSpace F E} {y}
    (hy : y in (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) x
      (trivializationAt F E x.proj) y = y :=
  writtenInExtChartAt_chartAt_comp _ hy

/--
theorem `FiberBundle.writtenInExtChartAt_trivializationAt_symm` / 定理 `FiberBundle.writtenInExtChartAt_trivializationAt_symm`

English:
theorem FiberBundle.writtenInExtChartAt_trivializationAt_symm
  statement: {x : TotalSpace F E} {y}
  proof: writtenInExtChartAt_chartAt_symm_comp _ hy

中文:
定理 FiberBundle.writtenInExtChartAt_trivializationAt_symm
  结论: {x : TotalSpace F E} {y}
  证明: writtenInExtChartAt_chartAt_symm_comp _ hy

Depends on / 依赖: writtenInExtChartAt_chartAt_symm_comp
-/
theorem FiberBundle.writtenInExtChartAt_trivializationAt_symm {x : TotalSpace F E} {y}
    (hy : y in (extChartAt (IB.prod 𝓘(𝕜, F)) x).target) :
    writtenInExtChartAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivializationAt F E x.proj x)
      (trivializationAt F E x.proj).toOpenPartialHomeomorph.symm y = y :=
  writtenInExtChartAt_chartAt_symm_comp _ hy

/-! ### Regularity of maps in/out fiber bundles

Note: For these results we don't need that the bundle is a `C^n` vector bundle, or even a vector
bundle at all, just that it is a fiber bundle over a charted base space.
-/

namespace Bundle

/--
theorem `contMDiffWithinAt_totalSpace` / 定理 `contMDiffWithinAt_totalSpace`

English:
theorem contMDiffWithinAt_totalSpace
  given: {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
  proof: by
  simp +singlePass only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm]; rw [← FiberBundle.continuousWithinAt_totalSpace]; rw [and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEq

中文:
定理 contMDiffWithinAt_totalSpace
  条件: {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
  证明: by
  simp +singlePass only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm]; rw [← FiberBundle.continuousWithinAt_totalSpace]; rw [and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEq

Depends on / 依赖: FiberBundle, FiberBundle.continuousWithinAt_totalSpace, FiberBundle.extChartAt, Function, Function.comp_def, Function.id_def, Iff.rfl, PartialEquiv, PartialEquiv.prod_coe, PartialEquiv.refl_coe, PartialEquiv.trans_apply, and_and_and_comm, and_congr, and_congr_right_iff, chartedSpaceSelf_prod, comp_def, contMDiffWithinAt_iff_target, contMDiffWithinAt_prod_iff, continuousWithinAt_totalSpace, extChartAt
-/
theorem contMDiffWithinAt_totalSpace {f : M -> TotalSpace F E} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  simp +singlePass only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm]; rw [← FiberBundle.continuousWithinAt_totalSpace]; rw [and_congr_right_iff]
  intro hf
  simp_rw +instances [modelWithCornersSelf_prod, FiberBundle.extChartAt, Function.comp_def,
    PartialEquiv.trans_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    extChartAt_self_apply, modelWithCornersSelf_coe, Function.id_def, ← chartedSpaceSelf_prod]
  refine (contMDiffWithinAt_prod_iff _).trans (and_congr ?_ Iff.rfl)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet in 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine EventuallyEq.contMDiffWithinAt_iff (eventually_of_mem h1 fun x hx => ?_) ?_
  · simp_rw [Function.comp, OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe]
    rw [Trivialization.coe_fst']
    exact hx
  · simp only [mfld_simps]

/--
theorem `contMDiffAt_totalSpace` / 定理 `contMDiffAt_totalSpace`

English:
theorem contMDiffAt_totalSpace
  given: {f : M -> TotalSpace F E} {x₀ : M}
  proof: by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_totalSpace

中文:
定理 contMDiffAt_totalSpace
  条件: {f : M -> TotalSpace F E} {x₀ : M}
  证明: by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_totalSpace

Depends on / 依赖: contMDiffWithinAt_totalSpace, contMDiffWithinAt_univ, simp_rw
-/
theorem contMDiffAt_totalSpace {f : M -> TotalSpace F E} {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F) n (fun x => (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_totalSpace

/--
theorem `contMDiffWithinAt_section` / 定理 `contMDiffWithinAt_section`

English:
theorem contMDiffWithinAt_section
  given: {s : forall x, E x} {a : Set B} {x₀ : B}
  proof: by
  simp_rw [contMDiffWithinAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffWithinAt_id

中文:
定理 contMDiffWithinAt_section
  条件: {s : 对任意 x, E x} {a : Set B} {x₀ : B}
  证明: by
  simp_rw [contMDiffWithinAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffWithinAt_id

Depends on / 依赖: and_iff_right_iff_imp, contMDiffWithinAt_id, contMDiffWithinAt_totalSpace, simp_rw
-/
theorem contMDiffWithinAt_section {s : forall x, E x} {a : Set B} {x₀ : B} :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔
      ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x => (trivializationAt F E x₀ ⟨x, s x⟩).2) a x₀ := by
  simp_rw [contMDiffWithinAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffWithinAt_id

/--
theorem `contMDiffAt_section` / 定理 `contMDiffAt_section`

English:
theorem contMDiffAt_section
  given: {s : forall x, E x} (x₀ : B)
  proof: by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id

中文:
定理 contMDiffAt_section
  条件: {s : 对任意 x, E x} (x₀ : B)
  证明: by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id

Depends on / 依赖: and_iff_right_iff_imp, contMDiffAt_id, contMDiffAt_totalSpace, simp_rw
-/
theorem contMDiffAt_section {s : forall x, E x} (x₀ : B) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x => (trivializationAt F E x₀ ⟨x, s x⟩).2) x₀ := by
  simp_rw [contMDiffAt_totalSpace, and_iff_right_iff_imp]; intro; exact contMDiffAt_id

variable (E)

/--
theorem `contMDiff_proj` / 定理 `contMDiff_proj`

English:
theorem contMDiff_proj
  statement: ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E)
  proof: fun x => by
  have : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id x := contMDiffAt_id
  rw [contMDiffAt_totalSpace] at this
  exact this.1

中文:
定理 contMDiff_proj
  结论: ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E)
  证明: fun x => by
  have : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id x := contMDiffAt_id
  rw [contMDiffAt_totalSpace] at this
  exact this.1

Depends on / 依赖: ContMDiffAt, IB.prod, contMDiffAt_id, contMDiffAt_totalSpace
-/
theorem contMDiff_proj : ContMDiff (IB.prod 𝓘(𝕜, F)) IB n (π F E) := fun x => by
  have : ContMDiffAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id x := contMDiffAt_id
  rw [contMDiffAt_totalSpace] at this
  exact this.1

/--
theorem `contMDiffOn_proj` / 定理 `contMDiffOn_proj`

English:
theorem contMDiffOn_proj
  given: {s : Set (TotalSpace F E)}
  proof: (contMDiff_proj E).contMDiffOn

中文:
定理 contMDiffOn_proj
  条件: {s : Set (TotalSpace F E)}
  证明: (contMDiff_proj E).contMDiffOn

Depends on / 依赖: contMDiffOn, contMDiff_proj
-/
theorem contMDiffOn_proj {s : Set (TotalSpace F E)} :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) IB n (π F E) s :=
  (contMDiff_proj E).contMDiffOn

/--
theorem `contMDiffAt_proj` / 定理 `contMDiffAt_proj`

English:
theorem contMDiffAt_proj
  given: {p : TotalSpace F E}
  statement: ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p
  proof: (contMDiff_proj E).contMDiffAt

中文:
定理 contMDiffAt_proj
  条件: {p : TotalSpace F E}
  结论: ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p
  证明: (contMDiff_proj E).contMDiffAt

Depends on / 依赖: contMDiffAt, contMDiff_proj
-/
theorem contMDiffAt_proj {p : TotalSpace F E} : ContMDiffAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) p :=
  (contMDiff_proj E).contMDiffAt

/--
theorem `contMDiffWithinAt_proj` / 定理 `contMDiffWithinAt_proj`

English:
theorem contMDiffWithinAt_proj
  given: {s : Set (TotalSpace F E)} {p : TotalSpace F E}
  proof: (contMDiffAt_proj E).contMDiffWithinAt

中文:
定理 contMDiffWithinAt_proj
  条件: {s : Set (TotalSpace F E)} {p : TotalSpace F E}
  证明: (contMDiffAt_proj E).contMDiffWithinAt

Depends on / 依赖: contMDiffAt_proj, contMDiffWithinAt
-/
theorem contMDiffWithinAt_proj {s : Set (TotalSpace F E)} {p : TotalSpace F E} :
    ContMDiffWithinAt (IB.prod 𝓘(𝕜, F)) IB n (π F E) s p :=
  (contMDiffAt_proj E).contMDiffWithinAt

section

variable (𝕜) [forall x, AddCommMonoid (E x)]
variable [forall x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

/--
theorem `contMDiff_zeroSection` / 定理 `contMDiff_zeroSection`

English:
theorem contMDiff_zeroSection
  statement: ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E)
  proof: by
  intro x
  unfold zeroSection
  rw [contMDiffAt_section]
  apply (contMDiffAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).zeroSection 𝕜

中文:
定理 contMDiff_zeroSection
  结论: ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E)
  证明: by
  intro x
  unfold zeroSection
  rw [contMDiffAt_section]
  apply (contMDiffAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).zeroSection 𝕜

Depends on / 依赖: Prod.snd, congr_arg, congr_of_eventuallyEq, contMDiffAt_const, contMDiffAt_section, filter_upwards, mem_baseSet_trivializationAt, mem_nhds, open_baseSet, open_baseSet.mem_nhds, trivializationAt, zeroSection
-/
theorem contMDiff_zeroSection : ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) := by
  intro x
  unfold zeroSection
  rw [contMDiffAt_section]
  apply (contMDiffAt_const (c := 0)).congr_of_eventuallyEq
  filter_upwards [(trivializationAt F E x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x)] with y hy
using congr_arg Prod.snd (trivializationAt F E x).zeroSection 𝕜 hy

/--
theorem `contMDiffOn_zeroSection` / 定理 `contMDiffOn_zeroSection`

English:
theorem contMDiffOn_zeroSection
  given: {t : Set B}
  proof: (contMDiff_zeroSection _ _).contMDiffOn

中文:
定理 contMDiffOn_zeroSection
  条件: {t : Set B}
  证明: (contMDiff_zeroSection _ _).contMDiffOn

Depends on / 依赖: contMDiffOn, contMDiff_zeroSection
-/
theorem contMDiffOn_zeroSection {t : Set B} :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t :=
  (contMDiff_zeroSection _ _).contMDiffOn

/--
theorem `contMDiffAt_zeroSection` / 定理 `contMDiffAt_zeroSection`

English:
theorem contMDiffAt_zeroSection
  given: {x : B}
  statement: ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) x
  proof: (contMDiff_zeroSection _ _).contMDiffAt

中文:
定理 contMDiffAt_zeroSection
  条件: {x : B}
  结论: ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) x
  证明: (contMDiff_zeroSection _ _).contMDiffAt

Depends on / 依赖: contMDiffAt, contMDiff_zeroSection
-/
theorem contMDiffAt_zeroSection {x : B} : ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) x :=
  (contMDiff_zeroSection _ _).contMDiffAt

/--
theorem `contMDiffWithinAt_zeroSection` / 定理 `contMDiffWithinAt_zeroSection`

English:
theorem contMDiffWithinAt_zeroSection
  given: {t : Set B} {x : B}
  proof: (contMDiff_zeroSection _ _ x).contMDiffWithinAt

中文:
定理 contMDiffWithinAt_zeroSection
  条件: {t : Set B} {x : B}
  证明: (contMDiff_zeroSection _ _ x).contMDiffWithinAt

Depends on / 依赖: contMDiffWithinAt, contMDiff_zeroSection
-/
theorem contMDiffWithinAt_zeroSection {t : Set B} {x : B} :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (zeroSection F E) t x :=
  (contMDiff_zeroSection _ _ x).contMDiffWithinAt

end

variable {s : forall x, E x} {u : Set B} {x : B}

@[nontriviality]
/--
lemma `contMDiffWithinAt_section_of_subsingleton` / 引理 `contMDiffWithinAt_section_of_subsingleton`

English:
lemma contMDiffWithinAt_section_of_subsingleton
  given: [Subsingleton F]
  proof: by
  rw [contMDiffWithinAt_section]
.congr apply contMDiffWithinAt_const
  · intro y _
    apply Subsingleton.elim
  rfl

@[nontriviality]

中文:
引理 contMDiffWithinAt_section_of_subsingleton
  条件: [Subsingleton F]
  证明: by
  rw [contMDiffWithinAt_section]
.congr apply contMDiffWithinAt_const
  · intro y _
    apply Subsingleton.elim
  rfl

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, contMDiffWithinAt_const, contMDiffWithinAt_section
-/
lemma contMDiffWithinAt_section_of_subsingleton [Subsingleton F] :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) u x := by
  rw [contMDiffWithinAt_section]
.congr apply contMDiffWithinAt_const
  · intro y _
    apply Subsingleton.elim
  rfl

@[nontriviality]
/--
lemma `contMDiffAt_section_of_subsingleton` / 引理 `contMDiffAt_section_of_subsingleton`

English:
lemma contMDiffAt_section_of_subsingleton
  given: [Subsingleton F]
  proof: by
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_section_of_subsingleton

@[nontriviality]

中文:
引理 contMDiffAt_section_of_subsingleton
  条件: [Subsingleton F]
  证明: by
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_section_of_subsingleton

@[nontriviality]

Depends on / 依赖: contMDiffWithinAt_section_of_subsingleton, contMDiffWithinAt_univ
-/
lemma contMDiffAt_section_of_subsingleton [Subsingleton F] :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x := by
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_section_of_subsingleton

@[nontriviality]
/--
lemma `contMDiffOn_section_of_subsingleton` / 引理 `contMDiffOn_section_of_subsingleton`

English:
lemma contMDiffOn_section_of_subsingleton
  given: [Subsingleton F]
  proof: fun _x _hx => contMDiffWithinAt_section_of_subsingleton ..

@[nontriviality]

中文:
引理 contMDiffOn_section_of_subsingleton
  条件: [Subsingleton F]
  证明: fun _x _hx => contMDiffWithinAt_section_of_subsingleton ..

@[nontriviality]

Depends on / 依赖: contMDiffWithinAt_section_of_subsingleton
-/
lemma contMDiffOn_section_of_subsingleton [Subsingleton F] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) u :=
  fun _x _hx => contMDiffWithinAt_section_of_subsingleton ..

@[nontriviality]
/--
lemma `contMDiff_section_of_subsingleton` / 引理 `contMDiff_section_of_subsingleton`

English:
lemma contMDiff_section_of_subsingleton
  given: [Subsingleton F]
  proof: fun _x => contMDiffAt_section_of_subsingleton ..

中文:
引理 contMDiff_section_of_subsingleton
  条件: [Subsingleton F]
  证明: fun _x => contMDiffAt_section_of_subsingleton ..

Depends on / 依赖: contMDiffAt_section_of_subsingleton
-/
lemma contMDiff_section_of_subsingleton [Subsingleton F] :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) :=
  fun _x => contMDiffAt_section_of_subsingleton ..

end Bundle

end

/-! ### `C^n` vector bundles -/


variable [NontriviallyNormedField 𝕜] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  [forall x, AddCommMonoid (E x)] [forall x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section WithTopology

variable [TopologicalSpace (TotalSpace F E)] [forall x, TopologicalSpace (E x)] (F E)
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (n IB) in
/--
Definition of `ContMDiffVectorBundle` / `ContMDiffVectorBundle` 的定义

English:
class ContMDiffVectorBundle
  parameters: : Prop where
  axioms and operations (1):
    - contMDiffOn_coordChangeL : forall (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'], ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet inter e'.baseSet)

中文:
类 ContMDiffVectorBundle
  参数: : 命题 where
  公理与运算 (1 个):
    - contMDiffOn_coordChangeL : 对任意 (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'], ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet inter e'.baseSet)

Depends on / 依赖: contMDiffOn_coordChangeL, h.contMDiffOn_coordChangeL, of_le
-/
class ContMDiffVectorBundle : Prop where
  protected contMDiffOn_coordChangeL :
    forall (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F))
        (e.baseSet inter e'.baseSet)

variable {F E} in
/--
theorem `ContMDiffVectorBundle.of_le` / 定理 `ContMDiffVectorBundle.of_le`

English:
theorem ContMDiffVectorBundle.of_le
  statement: {m n : Nat∞ω} (hmn : m <= n)
  proof: ⟨fun e e' _ _ => (h.contMDiffOn_coordChangeL e e').of_le hmn⟩

中文:
定理 ContMDiffVectorBundle.of_le
  结论: {m n : 自然数∞ω} (hmn : m <= n)
  证明: ⟨fun e e' _ _ => (h.contMDiffOn_coordChangeL e e').of_le hmn⟩
-/
protected theorem ContMDiffVectorBundle.of_le {m n : Nat∞ω} (hmn : m <= n)
    [h : ContMDiffVectorBundle n F E IB] : ContMDiffVectorBundle m F E IB :=
  ⟨fun e e' _ _ => (h.contMDiffOn_coordChangeL e e').of_le hmn⟩

instance {a : Nat∞ω} [ContMDiffVectorBundle ∞ F E IB] [h : ENat.LEInfty a] :
    ContMDiffVectorBundle a F E IB :=
  ContMDiffVectorBundle.of_le h.out

instance {a : Nat∞ω} [ContMDiffVectorBundle ω F E IB] : ContMDiffVectorBundle a F E IB :=
  ContMDiffVectorBundle.of_le le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContMDiffVectorBundle
  signature: 2 F E IB] : ContMDiffVectorBundle 1 F E IB
  body: ContMDiffVectorBundle.of_le one_le_two

中文:
实例 [ContMDiffVectorBundle
  签名: 2 F E IB] : ContMDiffVectorBundle 1 F E IB
  定义体: ContMDiffVectorBundle.of_le one_le_two

Depends on / 依赖: ContMDiffVectorBundle, ContMDiffVectorBundle.of_le, of_le, one_le_two
-/
instance [ContMDiffVectorBundle 2 F E IB] : ContMDiffVectorBundle 1 F E IB :=
  ContMDiffVectorBundle.of_le one_le_two

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContMDiffVectorBundle 0 F E IB
  body: by
  constructor
  intro e e' he he'
  rw [contMDiffOn_zero_iff]
  exact VectorBundle.continuousOn_coordChange' e e'

中文:
实例 :
  签名: ContMDiffVectorBundle 0 F E IB
  定义体: by
  constructor
  intro e e' he he'
  rw [contMDiffOn_zero_iff]
  exact VectorBundle.continuousOn_coordChange' e e'

Depends on / 依赖: VectorBundle, VectorBundle.continuousOn_coordChange, contMDiffOn_zero_iff, continuousOn_coordChange
-/
instance : ContMDiffVectorBundle 0 F E IB := by
  constructor
  intro e e' he he'
  rw [contMDiffOn_zero_iff]
  exact VectorBundle.continuousOn_coordChange' e e'

variable [ContMDiffVectorBundle n F E IB]

section ContMDiffCoordChange

variable {F E}
variable (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']

/--
theorem `contMDiffOn_coordChangeL` / 定理 `contMDiffOn_coordChangeL`

English:
theorem contMDiffOn_coordChangeL
  proof: ContMDiffVectorBundle.contMDiffOn_coordChangeL e e'

中文:
定理 contMDiffOn_coordChangeL
  证明: ContMDiffVectorBundle.contMDiffOn_coordChangeL e e'

Depends on / 依赖: ContMDiffVectorBundle, ContMDiffVectorBundle.contMDiffOn_coordChangeL, contMDiffOn_coordChangeL
-/
theorem contMDiffOn_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F))
      (e.baseSet inter e'.baseSet) :=
  ContMDiffVectorBundle.contMDiffOn_coordChangeL e e'

/--
theorem `contMDiffOn_symm_coordChangeL` / 定理 `contMDiffOn_symm_coordChangeL`

English:
theorem contMDiffOn_symm_coordChangeL
  proof: by
  rw [inter_comm]
  refine (ContMDiffVectorBundle.contMDiffOn_coordChangeL e' e).congr fun b hb => ?_
  rw [e.symm_coordChangeL e' hb]

中文:
定理 contMDiffOn_symm_coordChangeL
  证明: by
  rw [inter_comm]
  refine (ContMDiffVectorBundle.contMDiffOn_coordChangeL e' e).congr fun b hb => ?_
  rw [e.symm_coordChangeL e' hb]

Depends on / 依赖: ContMDiffVectorBundle, ContMDiffVectorBundle.contMDiffOn_coordChangeL, contMDiffOn_coordChangeL, e.symm_coordChangeL, inter_comm, symm_coordChangeL
-/
theorem contMDiffOn_symm_coordChangeL :
    ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => ((e.coordChangeL 𝕜 e' b).symm : F ->L[𝕜] F))
      (e.baseSet inter e'.baseSet) := by
  rw [inter_comm]
  refine (ContMDiffVectorBundle.contMDiffOn_coordChangeL e' e).congr fun b hb => ?_
  rw [e.symm_coordChangeL e' hb]

variable {e e'}

/--
theorem `contMDiffAt_coordChangeL` / 定理 `contMDiffAt_coordChangeL`

English:
theorem contMDiffAt_coordChangeL
  given: {x : B} (h : x in e.baseSet) (h' : x in e'.baseSet)
  proof: (contMDiffOn_coordChangeL e e').contMDiffAt
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

中文:
定理 contMDiffAt_coordChangeL
  条件: {x : B} (h : x in e.baseSet) (h' : x in e'.baseSet)
  证明: (contMDiffOn_coordChangeL e e').contMDiffAt
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

Depends on / 依赖: contMDiffAt, contMDiffOn_coordChangeL, e.open_baseSet.inter, mem_nhds, open_baseSet
-/
theorem contMDiffAt_coordChangeL {x : B} (h : x in e.baseSet) (h' : x in e'.baseSet) :
    ContMDiffAt IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) x :=
(contMDiffOn_coordChangeL e e').contMDiffAt
    (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨h, h'⟩

variable {s : Set M} {f : M -> B} {g : M -> F} {x : M}

/--
theorem `ContMDiffWithinAt.coordChangeL` / 定理 `ContMDiffWithinAt.coordChangeL`

English:
theorem ContMDiffWithinAt.coordChangeL
  proof: (contMDiffAt_coordChangeL he he').comp_contMDiffWithinAt _ hf

protected nonrec theorem ContMDiffAt.coordChangeL
    (hf : ContMDiffAt IM IB n f x) (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) x :=
  hf.

中文:
定理 ContMDiffWithinAt.coordChangeL
  证明: (contMDiffAt_coordChangeL he he').comp_contMDiffWithinAt _ hf

protected nonrec theorem ContMDiffAt.coordChangeL
    (hf : ContMDiffAt IM IB n f x) (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) x :=
  hf.
-/
protected theorem ContMDiffWithinAt.coordChangeL
    (hf : ContMDiffWithinAt IM IB n f s x) (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) s x :=
  (contMDiffAt_coordChangeL he he').comp_contMDiffWithinAt _ hf

protected nonrec theorem ContMDiffAt.coordChangeL
    (hf : ContMDiffAt IM IB n f x) (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) x :=
  hf.coordChangeL he he'

/--
theorem `ContMDiffOn.coordChangeL` / 定理 `ContMDiffOn.coordChangeL`

English:
theorem ContMDiffOn.coordChangeL
  proof: fun x hx => (hf x hx).coordChangeL (he hx) (he' hx)

中文:
定理 ContMDiffOn.coordChangeL
  证明: fun x hx => (hf x hx).coordChangeL (he hx) (he' hx)
-/
protected theorem ContMDiffOn.coordChangeL
    (hf : ContMDiffOn IM IB n f s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) s :=
  fun x hx => (hf x hx).coordChangeL (he hx) (he' hx)

/--
theorem `ContMDiff.coordChangeL` / 定理 `ContMDiff.coordChangeL`

English:
theorem ContMDiff.coordChangeL
  proof: fun x =>
  (hf x).coordChangeL (he x) (he' x)

中文:
定理 ContMDiff.coordChangeL
  证明: fun x =>
  (hf x).coordChangeL (he x) (he' x)
-/
protected theorem ContMDiff.coordChangeL
    (hf : ContMDiff IM IB n f) (he : forall x, f x in e.baseSet) (he' : forall x, f x in e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F ->L[𝕜] F) n (fun y => (e.coordChangeL 𝕜 e' (f y) : F ->L[𝕜] F)) := fun x =>
  (hf x).coordChangeL (he x) (he' x)

/--
theorem `ContMDiffWithinAt.coordChange` / 定理 `ContMDiffWithinAt.coordChange`

English:
theorem ContMDiffWithinAt.coordChange
  proof: by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet inter e'.baseSet in 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e

中文:
定理 ContMDiffWithinAt.coordChange
  证明: by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet inter e'.baseSet in 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e
-/
protected theorem ContMDiffWithinAt.coordChange
    (hf : ContMDiffWithinAt IM IB n f s x) (hg : ContMDiffWithinAt IM 𝓘(𝕜, F) n g s x)
    (he : f x in e.baseSet) (he' : f x in e'.baseSet) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => e.coordChange e' (f y) (g y)) s x := by
  refine ((hf.coordChangeL he he').clm_apply hg).congr_of_eventuallyEq ?_ ?_
  · have : e.baseSet inter e'.baseSet in 𝓝 (f x) :=
     (e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨he, he'⟩
    filter_upwards [hf.continuousWithinAt this] with y hy
    exact (Trivialization.coordChangeL_apply' e e' hy (g y)).symm
  · exact (Trivialization.coordChangeL_apply' e e' ⟨he, he'⟩ (g x)).symm

protected nonrec theorem ContMDiffAt.coordChange
    (hf : ContMDiffAt IM IB n f x) (hg : ContMDiffAt IM 𝓘(𝕜, F) n g x) (he : f x in e.baseSet)
    (he' : f x in e'.baseSet) :
    ContMDiffAt IM 𝓘(𝕜, F) n (fun y => e.coordChange e' (f y) (g y)) x :=
  hf.coordChange hg he he'

/--
theorem `ContMDiffOn.coordChange` / 定理 `ContMDiffOn.coordChange`

English:
theorem ContMDiffOn.coordChange
  statement: (hf : ContMDiffOn IM IB n f s)
  proof: fun x hx =>
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

中文:
定理 ContMDiffOn.coordChange
  结论: (hf : ContMDiffOn IM IB n f s)
  证明: fun x hx =>
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)
-/
protected theorem ContMDiffOn.coordChange (hf : ContMDiffOn IM IB n f s)
    (hg : ContMDiffOn IM 𝓘(𝕜, F) n g s) (he : MapsTo f s e.baseSet) (he' : MapsTo f s e'.baseSet) :
    ContMDiffOn IM 𝓘(𝕜, F) n (fun y => e.coordChange e' (f y) (g y)) s := fun x hx =>
  (hf x hx).coordChange (hg x hx) (he hx) (he' hx)

/--
theorem `ContMDiff.coordChange` / 定理 `ContMDiff.coordChange`

English:
theorem ContMDiff.coordChange
  statement: (hf : ContMDiff IM IB n f)
  proof: fun x =>
  (hf x).coordChange (hg x) (he x) (he' x)

中文:
定理 ContMDiff.coordChange
  结论: (hf : ContMDiff IM IB n f)
  证明: fun x =>
  (hf x).coordChange (hg x) (he x) (he' x)
-/
protected theorem ContMDiff.coordChange (hf : ContMDiff IM IB n f)
    (hg : ContMDiff IM 𝓘(𝕜, F) n g) (he : forall x, f x in e.baseSet) (he' : forall x, f x in e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F) n (fun y => e.coordChange e' (f y) (g y)) := fun x =>
  (hf x).coordChange (hg x) (he x) (he' x)

variable (e e')

variable (IB) in
/--
theorem `Bundle.Trivialization.contMDiffOn_symm_trans` / 定理 `Bundle.Trivialization.contMDiffOn_symm_trans`

English:
theorem Bundle.Trivialization.contMDiffOn_symm_trans
  proof: by
  have Hmaps : MapsTo Prod.fst (e.target inter e'.target) (e.baseSet inter e'.baseSet) := fun x hx =>
    ⟨e.mem_target.1 hx.1, e'.mem_target.1 hx.2⟩
  rw [mapsTo_inter] at Hmaps
  -- TODO: drop `congr` https://github.com/leanprover-community/mathlib4/issues/5473
  refine (contMDiffOn_fst.prodMk


中文:
定理 Bundle.Trivialization.contMDiffOn_symm_trans
  证明: by
  have Hmaps : MapsTo Prod.fst (e.target inter e'.target) (e.baseSet inter e'.baseSet) := fun x hx =>
    ⟨e.mem_target.1 hx.1, e'.mem_target.1 hx.2⟩
  rw [mapsTo_inter] at Hmaps
  -- TODO: drop `congr` https://github.com/leanprover-community/mathlib4/issues/5473
  refine (contMDiffOn_fst.prodMk


Depends on / 依赖: MapsTo, Prod.fst, baseSet, e.baseSet, e.mem_target, e.target, mapsTo_inter, mem_target, target
-/
theorem Bundle.Trivialization.contMDiffOn_symm_trans :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph) (e.target inter e'.target) := by
  have Hmaps : MapsTo Prod.fst (e.target inter e'.target) (e.baseSet inter e'.baseSet) := fun x hx =>
    ⟨e.mem_target.1 hx.1, e'.mem_target.1 hx.2⟩
  rw [mapsTo_inter] at Hmaps
  -- TODO: drop `congr` https://github.com/leanprover-community/mathlib4/issues/5473
  refine (contMDiffOn_fst.prodMk
    (contMDiffOn_fst.coordChange contMDiffOn_snd Hmaps.1 Hmaps.2)).congr ?_
  rintro ⟨b, x⟩ hb
  refine Prod.ext ?_ rfl
  have : (e.toOpenPartialHomeomorph.symm (b, x)).1 in e'.baseSet := by
    simp_all only [Trivialization.mem_target, mfld_simps]
  exact (e'.coe_fst' this).trans (e.proj_symm_apply hb.1)

variable {e e'}

/--
theorem `ContMDiffWithinAt.change_section_trivialization` / 定理 `ContMDiffWithinAt.change_section_trivialization`

English:
theorem ContMDiffWithinAt.change_section_trivialization
  statement: {f : M -> TotalSpace F E}
  proof: by
  rw [Trivialization.mem_source] at he he'
  refine (hp.coordChange hf he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hp.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

中文:
定理 ContMDiffWithinAt.change_section_trivialization
  结论: {f : M -> TotalSpace F E}
  证明: by
  rw [Trivialization.mem_source] at he he'
  refine (hp.coordChange hf he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hp.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

Depends on / 依赖: Trivialization, Trivialization.mem_source, congr_of_eventuallyEq, continuousWithinAt, coordChange, e.open_baseSet.mem_nhds, filter_upwards, hp.continuousWithinAt, hp.coordChange, mem_nhds, mem_source, open_baseSet
-/
theorem ContMDiffWithinAt.change_section_trivialization {f : M -> TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (hf : ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => (e (f y)).2) s x)
    (he : f x in e.source) (he' : f x in e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => (e' (f y)).2) s x := by
  rw [Trivialization.mem_source] at he he'
  refine (hp.coordChange hf he he').congr_of_eventuallyEq ?_ (by simp [he])
  filter_upwards [hp.continuousWithinAt (e.open_baseSet.mem_nhds he)] with y hy
  simp_all

/--
theorem `Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂` / 定理 `Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂`

English:
theorem Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂
  statement: {f : M -> TotalSpace F E}
  proof: ⟨(hp.change_section_trivialization · he he'), (hp.change_section_trivialization · he' he)⟩

中文:
定理 Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂
  结论: {f : M -> TotalSpace F E}
  证明: ⟨(hp.change_section_trivialization · he he'), (hp.change_section_trivialization · he' he)⟩

Depends on / 依赖: change_section_trivialization, hp.change_section_trivialization
-/
theorem Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂ {f : M -> TotalSpace F E}
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x)
    (he : f x in e.source) (he' : f x in e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => (e (f y)).2) s x ↔
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y => (e' (f y)).2) s x :=
  ⟨(hp.change_section_trivialization · he he'), (hp.change_section_trivialization · he' he)⟩

end ContMDiffCoordChange

variable [IsManifold IB n B] in
/--
Instance `ContMDiffFiberwiseLinear.hasGroupoid` / 实例 `ContMDiffFiberwiseLinear.hasGroupoid`

English:
instance ContMDiffFiberwiseLinear.hasGroupoid
  signature: :
  body: by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    rw [mem_contMDiffFiberwiseLinear_iff]
    refine ⟨_, _, e.open_baseSet.inter e'.open_baseSet, contMDiffOn_coordChangeL e e',
      contMDiffOn_symm_coordChangeL

中文:
实例 ContMDiffFiberwiseLinear.hasGroupoid
  签名: :
  定义体: by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    rw [mem_contMDiffFiberwiseLinear_iff]
    refine ⟨_, _, e.open_baseSet.inter e'.open_baseSet, contMDiffOn_coordChangeL e e',
      contMDiffOn_symm_coordChangeL

Depends on / 依赖: FiberwiseLinear, FiberwiseLinear.openPartialHomeomorph, MemTrivializationAtlas, OpenPartialHomeomorph, OpenPartialHomeomorph.eqOnSourceSetoid.symm, contMDiffOn_coordChangeL, contMDiffOn_symm_coordChangeL, e.apply, e.open_baseSet.inter, e.symm_trans_source_eq, eqOnSourceSetoid, mem_contMDiffFiberwiseLinear_iff, openPartialHomeomorph, open_baseSet, symm_toPartialEquiv, symm_trans_source_eq, trans_toPartialEquiv
-/
instance ContMDiffFiberwiseLinear.hasGroupoid :
    HasGroupoid (TotalSpace F E) (contMDiffFiberwiseLinear B F IB n) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    rw [mem_contMDiffFiberwiseLinear_iff]
    refine ⟨_, _, e.open_baseSet.inter e'.open_baseSet, contMDiffOn_coordChangeL e e',
      contMDiffOn_symm_coordChangeL e e', ?_⟩
    refine OpenPartialHomeomorph.eqOnSourceSetoid.symm ⟨?_, ?_⟩
    · simp only [FiberwiseLinear.openPartialHomeomorph, trans_toPartialEquiv, symm_toPartialEquiv,
        e.symm_trans_source_eq e']
    · rintro ⟨b, v⟩ hb
      exact (e.apply_symm_apply_eq_coordChangeL e' hb.1 v).symm

variable [IsManifold IB n B] in
/--
Instance `Bundle.TotalSpace.isManifold` / 实例 `Bundle.TotalSpace.isManifold`

English:
instance Bundle.TotalSpace.isManifold
  signature: :
  body: by
  refine { StructureGroupoid.HasGroupoid.comp (contMDiffFiberwiseLinear B F IB n) ?_ with }
  intro e he
  rw [mem_contMDiffFiberwiseLinear_iff] at he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine ⟨ContMDiffOn.congr ?_ (EqOnSource.eqOn heφ),
  

中文:
实例 Bundle.TotalSpace.isManifold
  签名: :
  定义体: by
  refine { StructureGroupoid.HasGroupoid.comp (contMDiffFiberwiseLinear B F IB n) ?_ with }
  intro e he
  rw [mem_contMDiffFiberwiseLinear_iff] at he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine ⟨ContMDiffOn.congr ?_ (EqOnSource.eqOn heφ),
  

Depends on / 依赖: ContMDiffOn, ContMDiffOn.congr, EqOnSource, EqOnSource.eqOn, EqOnSource.source_eq, EqOnSource.symm, HasGroupoid, StructureGroupoid, StructureGroupoid.HasGroupoid.comp, clm_apply, contMDiffFiberwiseLinear, contMDiffOn_fst, contMDiffOn_fst.prodMk, contMDiffOn_snd, isLocalStructomorphOn_contDiffGroupoid_iff, mem_contMDiffFiberwiseLinear_iff, prodMk, prod_subset_preimage_fst, source_eq
-/
instance Bundle.TotalSpace.isManifold :
    IsManifold (IB.prod 𝓘(𝕜, F)) n (TotalSpace F E) := by
  refine { StructureGroupoid.HasGroupoid.comp (contMDiffFiberwiseLinear B F IB n) ?_ with }
  intro e he
  rw [mem_contMDiffFiberwiseLinear_iff] at he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine ⟨ContMDiffOn.congr ?_ (EqOnSource.eqOn heφ),
      ContMDiffOn.congr ?_ (EqOnSource.eqOn (EqOnSource.symm' heφ))⟩
  · rw [EqOnSource.source_eq heφ]
    apply contMDiffOn_fst.prodMk
    exact (hφ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd
  · rw [EqOnSource.target_eq heφ]
    apply contMDiffOn_fst.prodMk
    exact (h2φ.comp contMDiffOn_fst <| prod_subset_preimage_fst _ _).clm_apply contMDiffOn_snd

section

variable {F E}
variable {e e' : Trivialization F (π F E)} [MemTrivializationAtlas e] [MemTrivializationAtlas e']

namespace Bundle.Trivialization

/--
theorem `contMDiffWithinAt_iff` / 定理 `contMDiffWithinAt_iff`

English:
theorem contMDiffWithinAt_iff
  statement: {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
  proof: contMDiffWithinAt_totalSpace.trans and_congr_right fun h =>
    Trivialization.contMDiffWithinAt_snd_comp_iff₂ h FiberBundle.mem_trivializationAt_proj_source he

中文:
定理 contMDiffWithinAt_iff
  结论: {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
  证明: contMDiffWithinAt_totalSpace.trans and_congr_right fun h =>
    Trivialization.contMDiffWithinAt_snd_comp_iff₂ h FiberBundle.mem_trivializationAt_proj_source he

Depends on / 依赖: FiberBundle, FiberBundle.mem_trivializationAt_proj_source, Trivialization, Trivialization.contMDiffWithinAt_snd_comp_iff, and_congr_right, contMDiffWithinAt_totalSpace, contMDiffWithinAt_totalSpace.trans, mem_trivializationAt_proj_source
-/
theorem contMDiffWithinAt_iff {f : M -> TotalSpace F E} {s : Set M} {x₀ : M}
    (he : f x₀ in e.source) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x => (f x).proj) s x₀ ∧
      ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x => (e (f x)).2) s x₀ :=
contMDiffWithinAt_totalSpace.trans and_congr_right fun h =>
    Trivialization.contMDiffWithinAt_snd_comp_iff₂ h FiberBundle.mem_trivializationAt_proj_source he

/--
theorem `contMDiffAt_iff` / 定理 `contMDiffAt_iff`

English:
theorem contMDiffAt_iff
  given: {f : M -> TotalSpace F E} {x₀ : M} (he : f x₀ in e.source)
  proof: e.contMDiffWithinAt_iff he

中文:
定理 contMDiffAt_iff
  条件: {f : M -> TotalSpace F E} {x₀ : M} (he : f x₀ in e.source)
  证明: e.contMDiffWithinAt_iff he

Depends on / 依赖: contMDiffWithinAt_iff, e.contMDiffWithinAt_iff
-/
theorem contMDiffAt_iff {f : M -> TotalSpace F E} {x₀ : M} (he : f x₀ in e.source) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x => (f x).proj) x₀ ∧
      ContMDiffAt IM 𝓘(𝕜, F) n (fun x => (e (f x)).2) x₀ :=
  e.contMDiffWithinAt_iff he

/--
theorem `contMDiffOn_iff` / 定理 `contMDiffOn_iff`

English:
theorem contMDiffOn_iff
  statement: {f : M -> TotalSpace F E} {s : Set M}
  proof: by
  simp only [ContMDiffOn, ← forall_and]
  exact forall₂_congr fun x hx => e.contMDiffWithinAt_iff (he hx)

中文:
定理 contMDiffOn_iff
  结论: {f : M -> TotalSpace F E} {s : Set M}
  证明: by
  simp only [ContMDiffOn, ← forall_and]
  exact forall₂_congr fun x hx => e.contMDiffWithinAt_iff (he hx)

Depends on / 依赖: ContMDiffOn, contMDiffWithinAt_iff, e.contMDiffWithinAt_iff, forall_and
-/
theorem contMDiffOn_iff {f : M -> TotalSpace F E} {s : Set M}
    (he : MapsTo f s e.source) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n f s ↔
      ContMDiffOn IM IB n (fun x => (f x).proj) s ∧
      ContMDiffOn IM 𝓘(𝕜, F) n (fun x => (e (f x)).2) s := by
  simp only [ContMDiffOn, ← forall_and]
  exact forall₂_congr fun x hx => e.contMDiffWithinAt_iff (he hx)

/--
theorem `contMDiff_iff` / 定理 `contMDiff_iff`

English:
theorem contMDiff_iff
  given: {f : M -> TotalSpace F E} (he : forall x, f x in e.source)
  proof: (forall_congr' fun x => e.contMDiffAt_iff (he x)).trans forall_and

中文:
定理 contMDiff_iff
  条件: {f : M -> TotalSpace F E} (he : 对任意 x, f x in e.source)
  证明: (forall_congr' fun x => e.contMDiffAt_iff (he x)).trans forall_and

Depends on / 依赖: contMDiffAt_iff, e.contMDiffAt_iff, forall_and, forall_congr
-/
theorem contMDiff_iff {f : M -> TotalSpace F E} (he : forall x, f x in e.source) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n f ↔
      ContMDiff IM IB n (fun x => (f x).proj) ∧
      ContMDiff IM 𝓘(𝕜, F) n (fun x => (e (f x)).2) :=
  (forall_congr' fun x => e.contMDiffAt_iff (he x)).trans forall_and

/--
theorem `contMDiffOn` / 定理 `contMDiffOn`

English:
theorem contMDiffOn
  given: (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
  proof: by
  have : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id e.source := contMDiffOn_id
  rw [e.contMDiffOn_iff (mapsTo_id _)] at this
  exact (this.1.prodMk this.2).congr fun x hx => (e.mk_proj_snd hx).symm

中文:
定理 contMDiffOn
  条件: (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
  证明: by
  have : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id e.source := contMDiffOn_id
  rw [e.contMDiffOn_iff (mapsTo_id _)] at this
  exact (this.1.prodMk this.2).congr fun x hx => (e.mk_proj_snd hx).symm

Depends on / 依赖: ContMDiffOn, IB.prod, contMDiffOn_id, contMDiffOn_iff, e.contMDiffOn_iff, e.mk_proj_snd, e.source, mapsTo_id, mk_proj_snd, prodMk, source
-/
theorem contMDiffOn (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e e.source := by
  have : ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n id e.source := contMDiffOn_id
  rw [e.contMDiffOn_iff (mapsTo_id _)] at this
  exact (this.1.prodMk this.2).congr fun x hx => (e.mk_proj_snd hx).symm

/--
theorem `contMDiffOn_symm` / 定理 `contMDiffOn_symm`

English:
theorem contMDiffOn_symm
  given: (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
  proof: by
  rw [e.contMDiffOn_iff e.toOpenPartialHomeomorph.mapsTo_symm]
  refine ⟨contMDiffOn_fst.congr fun x hx => e.proj_symm_apply hx,
    contMDiffOn_snd.congr fun x hx => ?_⟩
  rw [e.apply_symm_apply hx]

中文:
定理 contMDiffOn_symm
  条件: (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
  证明: by
  rw [e.contMDiffOn_iff e.toOpenPartialHomeomorph.mapsTo_symm]
  refine ⟨contMDiffOn_fst.congr fun x hx => e.proj_symm_apply hx,
    contMDiffOn_snd.congr fun x hx => ?_⟩
  rw [e.apply_symm_apply hx]

Depends on / 依赖: apply_symm_apply, contMDiffOn_fst, contMDiffOn_fst.congr, contMDiffOn_iff, contMDiffOn_snd, contMDiffOn_snd.congr, e.apply_symm_apply, e.contMDiffOn_iff, e.proj_symm_apply, e.toOpenPartialHomeomorph.mapsTo_symm, mapsTo_symm, proj_symm_apply, toOpenPartialHomeomorph
-/
theorem contMDiffOn_symm (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e.toOpenPartialHomeomorph.symm e.target := by
  rw [e.contMDiffOn_iff e.toOpenPartialHomeomorph.mapsTo_symm]
  refine ⟨contMDiffOn_fst.congr fun x hx => e.proj_symm_apply hx,
    contMDiffOn_snd.congr fun x hx => ?_⟩
  rw [e.apply_symm_apply hx]

/--
theorem `contMDiffWithinAt_section` / 定理 `contMDiffWithinAt_section`

English:
theorem contMDiffWithinAt_section
  statement: {s : forall x, E x} (a : Set B) {x₀ : B}
  proof: by
  rw [e.contMDiffWithinAt_iff]
  · change ContMDiffWithinAt IB IB n id a x₀ ∧ _ ↔ _
    simp [contMDiffWithinAt_id]
  · rwa [mem_source]

中文:
定理 contMDiffWithinAt_section
  结论: {s : 对任意 x, E x} (a : Set B) {x₀ : B}
  证明: by
  rw [e.contMDiffWithinAt_iff]
  · change ContMDiffWithinAt IB IB n id a x₀ ∧ _ ↔ _
    simp [contMDiffWithinAt_id]
  · rwa [mem_source]

Depends on / 依赖: ContMDiffWithinAt, contMDiffWithinAt_id, contMDiffWithinAt_iff, e.contMDiffWithinAt_iff, mem_source
-/
theorem contMDiffWithinAt_section {s : forall x, E x} (a : Set B) {x₀ : B}
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B)}
    [MemTrivializationAtlas e] (hx₀ : x₀ in e.baseSet) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) a x₀ ↔
      ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x => (e ⟨x, s x⟩).2) a x₀ := by
  rw [e.contMDiffWithinAt_iff]
  · change ContMDiffWithinAt IB IB n id a x₀ ∧ _ ↔ _
    simp [contMDiffWithinAt_id]
  · rwa [mem_source]

/--
theorem `contMDiffAt_section_iff` / 定理 `contMDiffAt_section_iff`

English:
theorem contMDiffAt_section_iff
  statement: {s : forall x, E x} {x₀ : B}
  proof: by
  simp_rw [← contMDiffWithinAt_univ]
  exact e.contMDiffWithinAt_section univ hx₀

中文:
定理 contMDiffAt_section_iff
  结论: {s : 对任意 x, E x} {x₀ : B}
  证明: by
  simp_rw [← contMDiffWithinAt_univ]
  exact e.contMDiffWithinAt_section univ hx₀

Depends on / 依赖: contMDiffWithinAt_section, contMDiffWithinAt_univ, e.contMDiffWithinAt_section, simp_rw
-/
theorem contMDiffAt_section_iff {s : forall x, E x} {x₀ : B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B))
    [MemTrivializationAtlas e] (hx₀ : x₀ in e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x => (e ⟨x, s x⟩).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact e.contMDiffWithinAt_section univ hx₀

/--
theorem `contMDiffOn_section_iff` / 定理 `contMDiffOn_section_iff`

English:
theorem contMDiffOn_section_iff
  statement: {s : forall x, E x} {a : Set B}
  proof: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩ <;>
have := (h x hx).contMDiffAt ha.mem_nhds hx
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mp this).contMDiffWithinAt
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mpr this).contMDiffWithinAt

中文:
定理 contMDiffOn_section_iff
  结论: {s : 对任意 x, E x} {a : Set B}
  证明: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩ <;>
have := (h x hx).contMDiffAt ha.mem_nhds hx
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mp this).contMDiffWithinAt
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mpr this).contMDiffWithinAt

Depends on / 依赖: contMDiffAt, contMDiffAt_section_iff, contMDiffWithinAt, e.contMDiffAt_section_iff, ha.mem_nhds, mem_nhds
-/
theorem contMDiffOn_section_iff {s : forall x, E x} {a : Set B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B))
    [MemTrivializationAtlas e] (ha : IsOpen a) (ha' : a subseteq e.baseSet) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) a ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x => (e ⟨x, s x⟩).2) a := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩ <;>
have := (h x hx).contMDiffAt ha.mem_nhds hx
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mp this).contMDiffWithinAt
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mpr this).contMDiffWithinAt

/--
theorem `contMDiffOn_section_baseSet_iff` / 定理 `contMDiffOn_section_baseSet_iff`

English:
theorem contMDiffOn_section_baseSet_iff
  statement: {s : forall x, E x}
  proof: e.contMDiffOn_section_iff e.open_baseSet subset_rfl

中文:
定理 contMDiffOn_section_baseSet_iff
  结论: {s : 对任意 x, E x}
  证明: e.contMDiffOn_section_iff e.open_baseSet subset_rfl

Depends on / 依赖: contMDiffOn_section_iff, e.contMDiffOn_section_iff, e.open_baseSet, open_baseSet, subset_rfl
-/
theorem contMDiffOn_section_baseSet_iff {s : forall x, E x}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E -> B))
    [MemTrivializationAtlas e] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (s x)) e.baseSet ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x => (e ⟨x, s x⟩).2) e.baseSet :=
  e.contMDiffOn_section_iff e.open_baseSet subset_rfl

end Bundle.Trivialization

end

/-! ### Core construction for `C^n` vector bundles -/

namespace VectorBundleCore

variable {F}
variable {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι)

/--
Definition of `IsContMDiff` / `IsContMDiff` 的定义

English:
class IsContMDiff
  parameters: (IB : ModelWithCorners 𝕜 EB HB) (n : Nat∞ω)
  axioms and operations (1):
    - contMDiffOn_coordChange : forall i j, ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (Z.coordChange i j) (Z.baseSet i inter Z.baseSet j)

中文:
类 IsContMDiff
  参数: (IB : ModelWithCorners 𝕜 EB HB) (n : 自然数∞ω)
  公理与运算 (1 个):
    - contMDiffOn_coordChange : 对任意 i j, ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (Z.coordChange i j) (Z.baseSet i inter Z.baseSet j)
-/
class IsContMDiff (IB : ModelWithCorners 𝕜 EB HB) (n : Nat∞ω) : Prop where
  contMDiffOn_coordChange :
    forall i j, ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (Z.coordChange i j) (Z.baseSet i inter Z.baseSet j)

/--
theorem `contMDiffOn_coordChange` / 定理 `contMDiffOn_coordChange`

English:
theorem contMDiffOn_coordChange
  given: (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsContMDiff IB n] (i j : ι)
  proof: h.1 i j

中文:
定理 contMDiffOn_coordChange
  条件: (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsContMDiff IB n] (i j : ι)
  证明: h.1 i j
-/
theorem contMDiffOn_coordChange (IB : ModelWithCorners 𝕜 EB HB) [h : Z.IsContMDiff IB n] (i j : ι) :
    ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (Z.coordChange i j) (Z.baseSet i inter Z.baseSet j) :=
  h.1 i j

variable [Z.IsContMDiff IB n]

/--
Instance `instContMDiffVectorBundle` / 实例 `instContMDiffVectorBundle`

English:
instance instContMDiffVectorBundle
  signature: : ContMDiffVectorBundle n F Z.Fiber IB where
  body: by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.contMDiffOn_coordChange IB i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

中文:
实例 instContMDiffVectorBundle
  签名: : ContMDiffVectorBundle n F Z.Fiber IB where
  定义体: by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.contMDiffOn_coordChange IB i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

Depends on / 依赖: Z.contMDiffOn_coordChange, Z.localTriv_coordChange_eq, contMDiffOn_coordChange, localTriv_coordChange_eq
-/
instance instContMDiffVectorBundle : ContMDiffVectorBundle n F Z.Fiber IB where
  contMDiffOn_coordChangeL := by
    rintro - - ⟨i, rfl⟩ ⟨i', rfl⟩
    refine (Z.contMDiffOn_coordChange IB i i').congr fun b hb => ?_
    ext v
    exact Z.localTriv_coordChange_eq i i' hb v

end VectorBundleCore

/-! ### The trivial `C^n` vector bundle -/

/--
Instance `Bundle.Trivial.contMDiffVectorBundle` / 实例 `Bundle.Trivial.contMDiffVectorBundle`

English:
instance Bundle.Trivial.contMDiffVectorBundle
  signature: :
  body: by
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiff_const.contMDiffOn

中文:
实例 Bundle.Trivial.contMDiffVectorBundle
  签名: :
  定义体: by
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiff_const.contMDiffOn

Depends on / 依赖: Bundle, Bundle.Trivial.eq_trivialization, Bundle.Trivial.trivialization.coordChangeL, Trivial, contMDiffOn, contMDiff_const, contMDiff_const.contMDiffOn, coordChangeL, eq_trivialization, simp_rw, trivialization
-/
instance Bundle.Trivial.contMDiffVectorBundle :
    ContMDiffVectorBundle n F (Bundle.Trivial B F) IB where
  contMDiffOn_coordChangeL := by
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiff_const.contMDiffOn

/-! ### Direct sums of `C^n` vector bundles -/


section Prod

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B -> Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, AddCommMonoid (E₁ x)] [forall x, Module 𝕜 (E₁ x)]

variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B -> Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)] [forall x, AddCommMonoid (E₂ x)] [forall x, Module 𝕜 (E₂ x)]

variable [forall x : B, TopologicalSpace (E₁ x)] [forall x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

variable [IsManifold IB n B]

/--
Instance `Bundle.Prod.contMDiffVectorBundle` / 实例 `Bundle.Prod.contMDiffVectorBundle`

English:
instance Bundle.Prod.contMDiffVectorBundle
  signature: : ContMDiffVectorBundle n (F₁ × F₂) (E₁ ×ᵇ E₂) IB where
  body: by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    refine ContMDiffOn.congr ?_ (e₁.coordChangeL_prod 𝕜 e₁' e₂ e₂')
    refine ContMDiffOn.clm_prodMap ?_ ?_
    · refine (contMDiffOn_coordChangeL e₁ e₁').mono ?_
      simp only [Trivialization.prod_baseSet, mfld_simps]
      mfld_s

中文:
实例 Bundle.Prod.contMDiffVectorBundle
  签名: : ContMDiffVectorBundle n (F₁ × F₂) (E₁ ×ᵇ E₂) IB where
  定义体: by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    refine ContMDiffOn.congr ?_ (e₁.coordChangeL_prod 𝕜 e₁' e₂ e₂')
    refine ContMDiffOn.clm_prodMap ?_ ?_
    · refine (contMDiffOn_coordChangeL e₁ e₁').mono ?_
      simp only [Trivialization.prod_baseSet, mfld_simps]
      mfld_s

Depends on / 依赖: ContMDiffOn, ContMDiffOn.clm_prodMap, ContMDiffOn.congr, Trivialization, Trivialization.prod_baseSet, clm_prodMap, contMDiffOn_coordChangeL, coordChangeL_prod, mfld_set_tac, mfld_simps, prod_baseSet
-/
instance Bundle.Prod.contMDiffVectorBundle : ContMDiffVectorBundle n (F₁ × F₂) (E₁ ×ᵇ E₂) IB where
  contMDiffOn_coordChangeL := by
    rintro _ _ ⟨e₁, e₂, i₁, i₂, rfl⟩ ⟨e₁', e₂', i₁', i₂', rfl⟩
    refine ContMDiffOn.congr ?_ (e₁.coordChangeL_prod 𝕜 e₁' e₂ e₂')
    refine ContMDiffOn.clm_prodMap ?_ ?_
    · refine (contMDiffOn_coordChangeL e₁ e₁').mono ?_
      simp only [Trivialization.prod_baseSet, mfld_simps]
      mfld_set_tac
    · refine (contMDiffOn_coordChangeL e₂ e₂').mono ?_
      simp only [Trivialization.prod_baseSet, mfld_simps]
      mfld_set_tac

end Prod

end WithTopology

/-! ### Prebundle construction for `C^n` vector bundles -/

namespace VectorPrebundle

variable [forall x, TopologicalSpace (E x)]

variable (IB) in
/--
Definition of `IsContMDiff` / `IsContMDiff` 的定义

English:
class IsContMDiff
  parameters: (a : VectorPrebundle 𝕜 F E) (n : Nat∞ω)
  axioms and operations (1):
    - exists_contMDiffCoordChange : forallᵉ (e in a.pretrivializationAtlas) (e' in a.pretrivializationAtlas), exists f : B -> F ->L[𝕜] F, ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n f (e.baseSet inter e'.baseSet) ∧ forall (b : B) (_ : b in e.baseSet inter e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2

中文:
类 IsContMDiff
  参数: (a : VectorPrebundle 𝕜 F E) (n : 自然数∞ω)
  公理与运算 (1 个):
    - exists_contMDiffCoordChange : 对任意ᵉ (e in a.pretrivializationAtlas) (e' in a.pretrivializationAtlas), 存在 f : B -> F ->L[𝕜] F, ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n f (e.baseSet inter e'.baseSet) ∧ 对任意 (b : B) (_ : b in e.baseSet inter e'.baseSet) (v : F), f b v = (e' ⟨b, e.symm b v⟩).2
-/
class IsContMDiff (a : VectorPrebundle 𝕜 F E) (n : Nat∞ω) : Prop where
  exists_contMDiffCoordChange :
    forallᵉ (e in a.pretrivializationAtlas) (e' in a.pretrivializationAtlas),
      exists f : B -> F ->L[𝕜] F,
        ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n f (e.baseSet inter e'.baseSet) ∧
          forall (b : B) (_ : b in e.baseSet inter e'.baseSet) (v : F),
            f b v = (e' ⟨b, e.symm b v⟩).2

variable (a : VectorPrebundle 𝕜 F E) [ha : a.IsContMDiff IB n] {e e' : Pretrivialization F (π F E)}

variable (IB n) in
/--
Definition of `contMDiffCoordChange` / `contMDiffCoordChange` 的定义

English:
definition contMDiffCoordChange
  signature: (he : e in a.pretrivializationAtlas)
  body: Classical.choose (ha.exists_contMDiffCoordChange e he e' he') b

中文:
定义 contMDiffCoordChange
  签名: (he : e in a.pretrivializationAtlas)
  定义体: Classical.choose (ha.exists_contMDiffCoordChange e he e' he') b
-/
@[no_expose] noncomputable def contMDiffCoordChange (he : e in a.pretrivializationAtlas)
    (he' : e' in a.pretrivializationAtlas) (b : B) : F ->L[𝕜] F :=
  Classical.choose (ha.exists_contMDiffCoordChange e he e' he') b

/--
theorem `contMDiffOn_contMDiffCoordChange` / 定理 `contMDiffOn_contMDiffCoordChange`

English:
theorem contMDiffOn_contMDiffCoordChange
  statement: (he : e in a.pretrivializationAtlas)
  proof: (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).1

中文:
定理 contMDiffOn_contMDiffCoordChange
  结论: (he : e in a.pretrivializationAtlas)
  证明: (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_contMDiffCoordChange, ha.exists_contMDiffCoordChange
-/
theorem contMDiffOn_contMDiffCoordChange (he : e in a.pretrivializationAtlas)
    (he' : e' in a.pretrivializationAtlas) :
    ContMDiffOn IB 𝓘(𝕜, F ->L[𝕜] F) n (a.contMDiffCoordChange n IB he he')
      (e.baseSet inter e'.baseSet) :=
  (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).1

/--
theorem `contMDiffCoordChange_apply` / 定理 `contMDiffCoordChange_apply`

English:
theorem contMDiffCoordChange_apply
  statement: (he : e in a.pretrivializationAtlas)
  proof: (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).2 b hb v

中文:
定理 contMDiffCoordChange_apply
  结论: (he : e in a.pretrivializationAtlas)
  证明: (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).2 b hb v

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_contMDiffCoordChange, ha.exists_contMDiffCoordChange
-/
theorem contMDiffCoordChange_apply (he : e in a.pretrivializationAtlas)
    (he' : e' in a.pretrivializationAtlas) {b : B} (hb : b in e.baseSet inter e'.baseSet) (v : F) :
    a.contMDiffCoordChange n IB he he' b v = (e' ⟨b, e.symm b v⟩).2 :=
  (Classical.choose_spec (ha.exists_contMDiffCoordChange e he e' he')).2 b hb v

/--
theorem `mk_contMDiffCoordChange` / 定理 `mk_contMDiffCoordChange`

English:
theorem mk_contMDiffCoordChange
  statement: (he : e in a.pretrivializationAtlas)
  proof: by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.contMDiffCoordChange_apply he he' hb v

中文:
定理 mk_contMDiffCoordChange
  结论: (he : e in a.pretrivializationAtlas)
  证明: by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.contMDiffCoordChange_apply he he' hb v

Depends on / 依赖: a.contMDiffCoordChange_apply, coe_fst, contMDiffCoordChange_apply, e.mk_symm, e.proj_symm_apply, mk_symm, proj_symm_apply
-/
theorem mk_contMDiffCoordChange (he : e in a.pretrivializationAtlas)
    (he' : e' in a.pretrivializationAtlas) {b : B} (hb : b in e.baseSet inter e'.baseSet) (v : F) :
    (b, a.contMDiffCoordChange n IB he he' b v) = e' ⟨b, e.symm b v⟩ := by
  ext
  · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]; exact hb.2
  · exact a.contMDiffCoordChange_apply he he' hb v

variable (IB) in
/--
theorem `contMDiffVectorBundle` / 定理 `contMDiffVectorBundle`

English:
theorem contMDiffVectorBundle
  statement: @ContMDiffVectorBundle n
  proof: letI := a.totalSpaceTopology; letI := a.toFiberBundle; letI := a.toVectorBundle
  { contMDiffOn_coordChangeL := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.contMDiffOn_contMDiffCoordChange he he').congr ?_
      intro b hb
      ext v
      rw [a.contMDiffCoordChange_apply he he'

中文:
定理 contMDiffVectorBundle
  结论: @ContMDiffVectorBundle n
  证明: letI := a.totalSpaceTopology; letI := a.toFiberBundle; letI := a.toVectorBundle
  { contMDiffOn_coordChangeL := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.contMDiffOn_contMDiffCoordChange he he').congr ?_
      intro b hb
      ext v
      rw [a.contMDiffCoordChange_apply he he'

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, Trivialization, Trivialization.coordChangeL_apply, a.contMDiffCoordChange_apply, a.contMDiffOn_contMDiffCoordChange, a.toFiberBundle, a.toVectorBundle, a.totalSpaceTopology, coe_coe, contMDiffCoordChange_apply, contMDiffOn_contMDiffCoordChange, contMDiffOn_coordChangeL, coordChangeL_apply, exacts, toFiberBundle, toVectorBundle, totalSpaceTopology
-/
theorem contMDiffVectorBundle : @ContMDiffVectorBundle n
    _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ a.totalSpaceTopology _ a.toFiberBundle a.toVectorBundle :=
  letI := a.totalSpaceTopology; letI := a.toFiberBundle; letI := a.toVectorBundle
  { contMDiffOn_coordChangeL := by
      rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
      refine (a.contMDiffOn_contMDiffCoordChange he he').congr ?_
      intro b hb
      ext v
      rw [a.contMDiffCoordChange_apply he he' hb v]; rw [ContinuousLinearEquiv.coe_coe]; rw [Trivialization.coordChangeL_apply]
      exacts [rfl, hb] }

end VectorPrebundle
