/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-! # Homs of `C^n` vector bundles over the same base space

Here we show that the bundle of continuous linear maps is a `C^n` vector bundle. We also show
that applying a smooth family of linear maps to a smooth family of vectors gives a smooth
result, in several versions.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
Indeed, semilinear maps are typically not smooth. For instance, complex conjugation is not
`ℂ`-differentiable.
-/

public section

noncomputable section

open Bundle Set OpenPartialHomeomorph ContinuousLinearMap Pretrivialization

open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ M : Type*} {n : WithTop Nat∞}
  {E₁ : B -> Type*} {E₂ : B -> Type*} [NontriviallyNormedField 𝕜]
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, TopologicalSpace (E₁ x)] [forall x, AddCommGroup (E₂ x)]
  [forall x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [forall x, TopologicalSpace (E₂ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

local notation "LE₁E₂" => TotalSpace (F₁ ->L[𝕜] F₂) (fun (b : B) => E₁ b ->L[𝕜] E₂ b)

section

/--
theorem `contMDiffOn_continuousLinearMapCoordChange` / 定理 `contMDiffOn_continuousLinearMapCoordChange`

English:
theorem contMDiffOn_continuousLinearMapCoordChange
  proof: by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

中文:
定理 contMDiffOn_continuousLinearMapCoordChange
  证明: by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

Depends on / 依赖: cle_arrowCongr, contMDiffOn_coordChangeL, mfld_set_tac
-/
theorem contMDiffOn_continuousLinearMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    CMDiff[e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)] n
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂') := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hom_chart` / 定理 `hom_chart`

English:
theorem hom_chart
  given: (y₀ y : LE₁E₂)
  proof: by
  rw [FiberBundle.chartedSpace_chartAt]; rw [trans_apply]; rw [OpenPartialHomeomorph.prod_apply]; rw [Trivialization.coe_coe]; rw [OpenPartialHomeomorph.refl_apply]; rw [Function.id_def]; rw [hom_trivializationAt_apply]

中文:
定理 hom_chart
  条件: (y₀ y : LE₁E₂)
  证明: by
  rw [FiberBundle.chartedSpace_chartAt]; rw [trans_apply]; rw [OpenPartialHomeomorph.prod_apply]; rw [Trivialization.coe_coe]; rw [OpenPartialHomeomorph.refl_apply]; rw [Function.id_def]; rw [hom_trivializationAt_apply]

Depends on / 依赖: FiberBundle, FiberBundle.chartedSpace_chartAt, Function, Function.id_def, OpenPartialHomeomorph, OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, Trivialization, Trivialization.coe_coe, chartedSpace_chartAt, coe_coe, hom_trivializationAt_apply, id_def, prod_apply, refl_apply, trans_apply
-/
theorem hom_chart (y₀ y : LE₁E₂) :
    chartAt (ModelProd HB (F₁ ->L[𝕜] F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt]; rw [trans_apply]; rw [OpenPartialHomeomorph.prod_apply]; rw [Trivialization.coe_coe]; rw [OpenPartialHomeomorph.refl_apply]; rw [Function.id_def]; rw [hom_trivializationAt_apply]

/--
theorem `contMDiffWithinAt_hom_bundle` / 定理 `contMDiffWithinAt_hom_bundle`

English:
theorem contMDiffWithinAt_hom_bundle
  given: (f : M -> LE₁E₂) {s : Set M} {x₀ : M}
  proof: contMDiffWithinAt_totalSpace

中文:
定理 contMDiffWithinAt_hom_bundle
  条件: (f : M -> LE₁E₂) {s : 集合 M} {x₀ : M}
  证明: contMDiffWithinAt_totalSpace

Depends on / 依赖: contMDiffWithinAt_totalSpace
-/
theorem contMDiffWithinAt_hom_bundle (f : M -> LE₁E₂) {s : Set M} {x₀ : M} :
    CMDiffAt[s] n f x₀ ↔
      CMDiffAt[s] n (fun x => (f x).1) x₀ ∧
        CMDiffAt[s] n
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffWithinAt_totalSpace

/--
theorem `contMDiffAt_hom_bundle` / 定理 `contMDiffAt_hom_bundle`

English:
theorem contMDiffAt_hom_bundle
  given: (f : M -> LE₁E₂) {x₀ : M}
  proof: contMDiffAt_totalSpace

中文:
定理 contMDiffAt_hom_bundle
  条件: (f : M -> LE₁E₂) {x₀ : M}
  证明: contMDiffAt_totalSpace

Depends on / 依赖: contMDiffAt_totalSpace
-/
theorem contMDiffAt_hom_bundle (f : M -> LE₁E₂) {x₀ : M} :
    CMDiffAt n f x₀ ↔
      CMDiffAt n (fun x => (f x).1) x₀ ∧ CMDiffAt n
        (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_totalSpace

end

section

/--
theorem `mdifferentiableOn_continuousLinearMapCoordChange` / 定理 `mdifferentiableOn_continuousLinearMapCoordChange`

English:
theorem mdifferentiableOn_continuousLinearMapCoordChange
  proof: by
.mdifferentiableOn one_ne_zero have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := 1)
.mdifferentiableOn one_ne_zero have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := 1)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

中文:
定理 mdifferentiableOn_continuousLinearMapCoordChange
  证明: by
.mdifferentiableOn one_ne_zero have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := 1)
.mdifferentiableOn one_ne_zero have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := 1)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

Depends on / 依赖: cle_arrowCongr, contMDiffOn_coordChangeL, mdifferentiableOn, mfld_set_tac, one_ne_zero
-/
theorem mdifferentiableOn_continuousLinearMapCoordChange
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDiff[e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)]
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂') := by
.mdifferentiableOn one_ne_zero have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := 1)
.mdifferentiableOn one_ne_zero have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := 1)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]

/--
theorem `mdifferentiableWithinAt_hom_bundle` / 定理 `mdifferentiableWithinAt_hom_bundle`

English:
theorem mdifferentiableWithinAt_hom_bundle
  given: (f : M -> LE₁E₂) {s : Set M} {x₀ : M}
  proof: mdifferentiableWithinAt_totalSpace IB ..

中文:
定理 mdifferentiableWithinAt_hom_bundle
  条件: (f : M -> LE₁E₂) {s : 集合 M} {x₀ : M}
  证明: mdifferentiableWithinAt_totalSpace IB ..

Depends on / 依赖: mdifferentiableWithinAt_totalSpace
-/
theorem mdifferentiableWithinAt_hom_bundle (f : M -> LE₁E₂) {s : Set M} {x₀ : M} :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x => (f x).1) x₀ ∧
        MDiffAt[s]
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..

/--
theorem `mdifferentiableAt_hom_bundle` / 定理 `mdifferentiableAt_hom_bundle`

English:
theorem mdifferentiableAt_hom_bundle
  given: (f : M -> LE₁E₂) {x₀ : M}
  proof: mdifferentiableAt_totalSpace ..

中文:
定理 mdifferentiableAt_hom_bundle
  条件: (f : M -> LE₁E₂) {x₀ : M}
  证明: mdifferentiableAt_totalSpace ..

Depends on / 依赖: mdifferentiableAt_totalSpace
-/
theorem mdifferentiableAt_hom_bundle (f : M -> LE₁E₂) {x₀ : M} :
    MDiffAt f x₀ ↔
      MDiffAt (fun x => (f x).1) x₀ ∧
        MDiffAt (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableAt_totalSpace ..

end

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

/--
Instance `Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff` / 实例 `Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff`

English:
instance Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff
  signature: :
  body: by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩

中文:
实例 Bundle.连续线性映射.vectorPrebundle.isContMDiff
  签名: :
  定义体: by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩

Depends on / 依赖: RingHom, RingHom.id, contMDiffOn_continuousLinearMapCoordChange, continuousLinearMapCoordChange, continuousLinearMapCoordChange_apply
-/
instance Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩

/--
Instance `ContMDiffVectorBundle.continuousLinearMap` / 实例 `ContMDiffVectorBundle.continuousLinearMap`

English:
instance ContMDiffVectorBundle.continuousLinearMap
  signature: :
  body: (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

中文:
实例 余ntMDiffVectorBundle.continuousLinearMap
  签名: :
  定义体: (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

Depends on / 依赖: Bundle, Bundle.ContinuousLinearMap.vectorPrebundle, ContinuousLinearMap, RingHom, RingHom.id, contMDiffVectorBundle, vectorPrebundle
-/
instance ContMDiffVectorBundle.continuousLinearMap :
    ContMDiffVectorBundle n (F₁ ->L[𝕜] F₂) ((fun (b : B) => E₁ b ->L[𝕜] E₂ b)) IB :=
  (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end

section symmL

variable {𝕜 B F₁ : Type*} [NontriviallyNormedField 𝕜] {n : WithTop Nat∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {E₁ : B -> Type*} [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, TopologicalSpace (E₁ x)]
  [forall x, IsTopologicalAddGroup (E₁ x)] [forall x, ContinuousSMul 𝕜 (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

/--
lemma `Bundle.Trivialization.contMDiffAt_symmL` / 引理 `Bundle.Trivialization.contMDiffAt_symmL`

English:
lemma Bundle.Trivialization.contMDiffAt_symmL
  statement: [ContMDiffVectorBundle n F₁ E₁ IB]
  proof: by
  have hx' : x in (trivializationAt F₁ E₁ x).baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  refine contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_coordChangeL hx hx').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx,
    (trivializationAt F₁ E₁ x).open_baseSet.mem_nhds hx'] with b hb hb'
  ext v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    coordChangeL_apply' e _ ⟨hb, hb'⟩, coe_linearMapAt_of_mem _ hb',
    e.symmL_apply hb, e.mk_symm hb]

中文:
引理 Bundle.Trivialization.contMDiffAt_symmL
  结论: [余ntMDiffVectorBundle n F₁ E₁ IB]
  证明: by
  have hx' : x in (trivializationAt F₁ E₁ x).baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  refine contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_coordChangeL hx hx').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx,
    (trivializationAt F₁ E₁ x).open_baseSet.mem_nhds hx'] with b hb hb'
  ext v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    coordChangeL_apply' e _ ⟨hb, hb'⟩, coe_linearMapAt_of_mem _ hb',
    e.symmL_apply hb, e.mk_symm hb]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.inCoordinates, baseSet, coe_linearMapAt_of_mem, congr_of_eventuallyEq, contMDiffAt_coordChangeL, contMDiffAt_id, contMDiffAt_totalSpace, contMDiffAt_totalSpace.mpr, coordChangeL_apply, e.mk_symm, e.open_baseSet.mem_nhds, e.symmL_apply, filter_upwards, hom_trivializationAt_apply, inCoordinates, mem_baseSet_trivializationAt, mem_nhds, mk_symm, open_baseSet
-/
lemma Bundle.Trivialization.contMDiffAt_symmL [ContMDiffVectorBundle n F₁ E₁ IB]
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ -> B)) [MemTrivializationAtlas e]
    {x : B} (hx : x in e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ ->L[𝕜] F₁)) n
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₁) m (e.symmL 𝕜 m)) x := by
  have hx' : x in (trivializationAt F₁ E₁ x).baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  refine contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_coordChangeL hx hx').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx,
    (trivializationAt F₁ E₁ x).open_baseSet.mem_nhds hx'] with b hb hb'
  ext v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    coordChangeL_apply' e _ ⟨hb, hb'⟩, coe_linearMapAt_of_mem _ hb',
    e.symmL_apply hb, e.mk_symm hb]

/--
lemma `Bundle.Trivialization.contMDiffOn_symmL` / 引理 `Bundle.Trivialization.contMDiffOn_symmL`

English:
lemma Bundle.Trivialization.contMDiffOn_symmL
  statement: [ContMDiffVectorBundle n F₁ E₁ IB]
  proof: fun _ hx => (e.contMDiffAt_symmL hx).contMDiffWithinAt

中文:
引理 Bundle.Trivialization.contMDiffOn_symmL
  结论: [余ntMDiffVectorBundle n F₁ E₁ IB]
  证明: fun _ hx => (e.contMDiffAt_symmL hx).contMDiffWithinAt

Depends on / 依赖: contMDiffAt_symmL, contMDiffWithinAt, e.contMDiffAt_symmL
-/
lemma Bundle.Trivialization.contMDiffOn_symmL [ContMDiffVectorBundle n F₁ E₁ IB]
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ -> B)) [MemTrivializationAtlas e] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ ->L[𝕜] F₁)) n
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₁) m (e.symmL 𝕜 m)) e.baseSet :=
  fun _ hx => (e.contMDiffAt_symmL hx).contMDiffWithinAt

end symmL

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
  {n : WithTop Nat∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M -> B₁} {b₂ : M -> B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) ->L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/--
lemma `ContMDiffWithinAt.clm_apply_of_inCoordinates` / 引理 `ContMDiffWithinAt.clm_apply_of_inCoordinates`

English:
lemma ContMDiffWithinAt.clm_apply_of_inCoordinates
  proof: by
  rw [← contMDiffWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContMDiffWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp [*]

中文:
引理 ContMDiffWithinAt.clm_apply_of_inCoordinates
  证明: by
  rw [← contMDiffWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContMDiffWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp [*]

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.clm_apply, FiberBundle, FiberBundle.mem_baseSet_trivializationAt, baseSet, clm_apply, congr_of_eventuallyEq_of_mem, contMDiffWithinAt_insert_self, contMDiffWithinAt_totalSpace, continuousWithinAt, insert, mem_baseSet_trivializationAt, mem_insert, mem_nhds, open_baseSet, open_baseSet.mem_nhds, trivializationAt
-/
lemma ContMDiffWithinAt.clm_apply_of_inCoordinates
    (hϕ : CMDiffAt[s] n
      (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : CMDiffAt[s] n (fun m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt[s] n b₂ m₀) :
    CMDiffAt[s] n (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContMDiffWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp [*]

/--
lemma `ContMDiffAt.clm_apply_of_inCoordinates` / 引理 `ContMDiffAt.clm_apply_of_inCoordinates`

English:
lemma ContMDiffAt.clm_apply_of_inCoordinates
  proof: by
  rw [← contMDiffWithinAt_univ] at hϕ hv hb₂ ⊢
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

中文:
引理 ContMDiffAt.clm_apply_of_inCoordinates
  证明: by
  rw [← contMDiffWithinAt_univ] at hϕ hv hb₂ ⊢
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.clm_apply_of_inCoordinates, clm_apply_of_inCoordinates, contMDiffWithinAt_univ
-/
lemma ContMDiffAt.clm_apply_of_inCoordinates
    (hϕ : CMDiffAt n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : CMDiffAt n (fun m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt n b₂ m₀) :
    CMDiffAt n (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_univ] at hϕ hv hb₂ ⊢
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end

section

/- Declare a manifold `B` (with model `IB : HB → EB`),
and three vector bundles `E₁`, `E₂` and `E₃` over `B` (with model fibers `F₁`, `F₂` and `F₃`).

Also a second manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 B F₁ F₂ F₃ M : Type*} [NontriviallyNormedField 𝕜] {n : WithTop Nat∞}
  {E₁ : B -> Type*}
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, TopologicalSpace (E₁ x)]
  {E₂ : B -> Type*} [forall x, AddCommGroup (E₂ x)]
  [forall x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [forall x, TopologicalSpace (E₂ x)]
  {E₃ : B -> Type*} [forall x, AddCommGroup (E₃ x)]
  [forall x, Module 𝕜 (E₃ x)] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [forall x, TopologicalSpace (E₃ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b : M -> B} {v : forall x, E₁ (b x)} {s : Set M} {x : M}

section OneVariable

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : forall x, (E₁ (b x) ->L[𝕜] E₂ (b x))}

/--
lemma `ContMDiffWithinAt.clm_bundle_apply` / 引理 `ContMDiffWithinAt.clm_bundle_apply`

English:
lemma ContMDiffWithinAt.clm_bundle_apply
  proof: by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

中文:
引理 ContMDiffWithinAt.clm_bundle_apply
  证明: by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1
-/
lemma ContMDiffWithinAt.clm_bundle_apply
    (hϕ : CMDiffAt[s] n
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : CMDiffAt[s] n (fun m => TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt[s] n (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/--
lemma `ContMDiffAt.clm_bundle_apply` / 引理 `ContMDiffAt.clm_bundle_apply`

English:
lemma ContMDiffAt.clm_bundle_apply
  proof: ContMDiffWithinAt.clm_bundle_apply hϕ hv

中文:
引理 ContMDiffAt.clm_bundle_apply
  证明: ContMDiffWithinAt.clm_bundle_apply hϕ hv
-/
lemma ContMDiffAt.clm_bundle_apply
    (hϕ : CMDiffAt n
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : CMDiffAt n (fun m => TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt n (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  ContMDiffWithinAt.clm_bundle_apply hϕ hv

/--
lemma `ContMDiffOn.clm_bundle_apply` / 引理 `ContMDiffOn.clm_bundle_apply`

English:
lemma ContMDiffOn.clm_bundle_apply
  proof: fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)

中文:
引理 ContMDiffOn.clm_bundle_apply
  证明: fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)
-/
lemma ContMDiffOn.clm_bundle_apply
    (hϕ : CMDiff[s] n
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : CMDiff[s] n (fun m => TotalSpace.mk' F₁ (b m) (v m))) :
    CMDiff[s] n (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)

/--
lemma `ContMDiff.clm_bundle_apply` / 引理 `ContMDiff.clm_bundle_apply`

English:
lemma ContMDiff.clm_bundle_apply
  proof: fun x => (hϕ x).clm_bundle_apply (hv x)

中文:
引理 ContMDiff.clm_bundle_apply
  证明: fun x => (hϕ x).clm_bundle_apply (hv x)
-/
lemma ContMDiff.clm_bundle_apply
    (hϕ : CMDiff n
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : CMDiff n (fun m => TotalSpace.mk' F₁ (b m) (v m))) :
    CMDiff n (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x => (hϕ x).clm_bundle_apply (hv x)

end OneVariable

section OneVariable'

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : forall x, (E₁ (b x) ->L[𝕜] E₂ (b x))}

/--
lemma `MDifferentiableWithinAt.clm_bundle_apply` / 引理 `MDifferentiableWithinAt.clm_bundle_apply`

English:
lemma MDifferentiableWithinAt.clm_bundle_apply
  proof: by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

中文:
引理 MDifferentiableWithinAt.clm_bundle_apply
  证明: by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1
-/
lemma MDifferentiableWithinAt.clm_bundle_apply
    (hϕ : MDiffAt[s]
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDiffAt[s] (fun m => TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDiffAt[s] (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/--
lemma `MDifferentiableAt.clm_bundle_apply` / 引理 `MDifferentiableAt.clm_bundle_apply`

English:
lemma MDifferentiableAt.clm_bundle_apply
  proof: MDifferentiableWithinAt.clm_bundle_apply hϕ hv

中文:
引理 MDifferentiableAt.clm_bundle_apply
  证明: MDifferentiableWithinAt.clm_bundle_apply hϕ hv
-/
lemma MDifferentiableAt.clm_bundle_apply
    (hϕ : MDiffAt
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDiffAt (fun m => TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDiffAt (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply hϕ hv

/--
lemma `MDifferentiableOn.clm_bundle_apply` / 引理 `MDifferentiableOn.clm_bundle_apply`

English:
lemma MDifferentiableOn.clm_bundle_apply
  proof: fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)

中文:
引理 MDifferentiableOn.clm_bundle_apply
  证明: fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)
-/
lemma MDifferentiableOn.clm_bundle_apply
    (hϕ : MDiff[s]
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDiff[s] (fun m => TotalSpace.mk' F₁ (b m) (v m))) :
    MDiff[s] (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)

/--
lemma `MDifferentiable.clm_bundle_apply` / 引理 `MDifferentiable.clm_bundle_apply`

English:
lemma MDifferentiable.clm_bundle_apply
  proof: fun x => (hϕ x).clm_bundle_apply (hv x)

中文:
引理 MDifferentiable.clm_bundle_apply
  证明: fun x => (hϕ x).clm_bundle_apply (hv x)
-/
lemma MDifferentiable.clm_bundle_apply
    (hϕ : MDiff
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDiff (fun m => TotalSpace.mk' F₁ (b m) (v m))) :
    MDiff (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x => (hϕ x).clm_bundle_apply (hv x)

end OneVariable'

section TwoVariables

variable [forall x, IsTopologicalAddGroup (E₃ x)] [forall x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : forall x, (E₁ (b x) ->L[𝕜] E₂ (b x) ->L[𝕜] E₃ (b x))} {w : forall x, E₂ (b x)}

/--
lemma `ContMDiffWithinAt.clm_bundle_apply₂` / 引理 `ContMDiffWithinAt.clm_bundle_apply₂`

English:
lemma ContMDiffWithinAt.clm_bundle_apply₂
  proof: .clm_bundle_apply hw hψ.clm_bundle_apply hv

中文:
引理 ContMDiffWithinAt.clm_bundle_apply₂
  证明: .clm_bundle_apply hw hψ.clm_bundle_apply hv
-/
lemma ContMDiffWithinAt.clm_bundle_apply₂
    (hψ : CMDiffAt[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : CMDiffAt[s] n (fun m => TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : CMDiffAt[s] n (fun m => TotalSpace.mk' F₂ (b m) (w m)) x) :
    CMDiffAt[s] n (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
.clm_bundle_apply hw hψ.clm_bundle_apply hv

/--
lemma `ContMDiffAt.clm_bundle_apply₂` / 引理 `ContMDiffAt.clm_bundle_apply₂`

English:
lemma ContMDiffAt.clm_bundle_apply₂
  proof: ContMDiffWithinAt.clm_bundle_apply₂ hψ hv hw

中文:
引理 ContMDiffAt.clm_bundle_apply₂
  证明: ContMDiffWithinAt.clm_bundle_apply₂ hψ hv hw
-/
lemma ContMDiffAt.clm_bundle_apply₂
    (hψ : CMDiffAt n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : CMDiffAt n (fun m => TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : CMDiffAt n (fun m => TotalSpace.mk' F₂ (b m) (w m)) x) :
    CMDiffAt n (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  ContMDiffWithinAt.clm_bundle_apply₂ hψ hv hw

/--
lemma `ContMDiffOn.clm_bundle_apply₂` / 引理 `ContMDiffOn.clm_bundle_apply₂`

English:
lemma ContMDiffOn.clm_bundle_apply₂
  proof: fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

中文:
引理 ContMDiffOn.clm_bundle_apply₂
  证明: fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)
-/
lemma ContMDiffOn.clm_bundle_apply₂
    (hψ : CMDiff[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : CMDiff[s] n (fun m => TotalSpace.mk' F₁ (b m) (v m)))
    (hw : CMDiff[s] n (fun m => TotalSpace.mk' F₂ (b m) (w m))) :
    CMDiff[s] n (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/--
lemma `ContMDiff.clm_bundle_apply₂` / 引理 `ContMDiff.clm_bundle_apply₂`

English:
lemma ContMDiff.clm_bundle_apply₂
  proof: fun x => (hψ x).clm_bundle_apply₂ (hv x) (hw x)

中文:
引理 ContMDiff.clm_bundle_apply₂
  证明: fun x => (hψ x).clm_bundle_apply₂ (hv x) (hw x)
-/
lemma ContMDiff.clm_bundle_apply₂
    (hψ : CMDiff n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : CMDiff n (fun m => TotalSpace.mk' F₁ (b m) (v m)))
    (hw : CMDiff n (fun m => TotalSpace.mk' F₂ (b m) (w m))) :
    CMDiff n (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x => (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables

section TwoVariables'

variable [forall x, IsTopologicalAddGroup (E₃ x)] [forall x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : forall x, (E₁ (b x) ->L[𝕜] E₂ (b x) ->L[𝕜] E₃ (b x))} {w : forall x, E₂ (b x)}

/--
lemma `MDifferentiableWithinAt.clm_bundle_apply₂` / 引理 `MDifferentiableWithinAt.clm_bundle_apply₂`

English:
lemma MDifferentiableWithinAt.clm_bundle_apply₂
  proof: .clm_bundle_apply hw hψ.clm_bundle_apply hv

中文:
引理 MDifferentiableWithinAt.clm_bundle_apply₂
  证明: .clm_bundle_apply hw hψ.clm_bundle_apply hv
-/
lemma MDifferentiableWithinAt.clm_bundle_apply₂
    (hψ : MDiffAt[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDiffAt[s] (fun m => TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDiffAt[s] (fun m => TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDiffAt[s] (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
.clm_bundle_apply hw hψ.clm_bundle_apply hv

/--
lemma `MDifferentiableAt.clm_bundle_apply₂` / 引理 `MDifferentiableAt.clm_bundle_apply₂`

English:
lemma MDifferentiableAt.clm_bundle_apply₂
  proof: MDifferentiableWithinAt.clm_bundle_apply₂ hψ hv hw

中文:
引理 MDifferentiableAt.clm_bundle_apply₂
  证明: MDifferentiableWithinAt.clm_bundle_apply₂ hψ hv hw
-/
lemma MDifferentiableAt.clm_bundle_apply₂
    (hψ : MDiffAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDiffAt (fun m => TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDiffAt (fun m => TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDiffAt (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply₂ hψ hv hw

/--
lemma `MDifferentiableOn.clm_bundle_apply₂` / 引理 `MDifferentiableOn.clm_bundle_apply₂`

English:
lemma MDifferentiableOn.clm_bundle_apply₂
  proof: fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

中文:
引理 MDifferentiableOn.clm_bundle_apply₂
  证明: fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)
-/
lemma MDifferentiableOn.clm_bundle_apply₂
    (hψ : MDiff[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDiff[s] (fun m => TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDiff[s] (fun m => TotalSpace.mk' F₂ (b m) (w m))) :
    MDiff[s] (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/--
lemma `MDifferentiable.clm_bundle_apply₂` / 引理 `MDifferentiable.clm_bundle_apply₂`

English:
lemma MDifferentiable.clm_bundle_apply₂
  proof: fun x => (hψ x).clm_bundle_apply₂ (hv x) (hw x)

中文:
引理 MDifferentiable.clm_bundle_apply₂
  证明: fun x => (hψ x).clm_bundle_apply₂ (hv x) (hw x)
-/
lemma MDifferentiable.clm_bundle_apply₂
    (hψ : MDiff (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDiff (fun m => TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDiff (fun m => TotalSpace.mk' F₂ (b m) (w m))) :
    MDiff (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x => (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables'

end
