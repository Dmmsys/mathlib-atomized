/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The vector bundle of continuous alternating multilinear maps

We define the topological vector bundle of continuous alternating maps
between two vector bundles over the same base.

Consider topological vector bundles with fibers `E₁ x`, `E₂ x`, `x : B`,
with model fibers `F₁` and `F₂`, and a finite index type `ι`.
If `F₁` and `F₂` are normed spaces over a nontrivially normed field `𝕜`,
then we define a vector bundle with fiber `E₁ x [⋀^ι]→L[𝕜] E₂ x`
with model fiber `F₁ [⋀^ι]→L[𝕜] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ [⋀^ι]→L[𝕜] F₂` using the `VectorPrebundle` construction.
-/

@[expose] public section


noncomputable section

open Bundle Set Topology
open scoped Bundle

/-!
### Continuous alternating map between fibers written in coordinates
-/

namespace ContinuousAlternatingMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B₁ : Type*} (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ -> Type*} [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)]
  [TopologicalSpace B₁] [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {B₂ : Type*} (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ -> Type*} [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜 (E₂ x)]
  [TopologicalSpace B₂] [TopologicalSpace (TotalSpace F₂ E₂)] [forall x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/--
Definition of `inCoordinates` / `inCoordinates` 的定义

English:
definition inCoordinates
  signature: (x₀ x : B₁) (y₀ y : B₂) (ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y)
  body: .compContinuousAlternatingMap .continuousLinearMapAt 𝕜 y trivializationAt F₂ E₂ y₀
.compContinuousLinearMap (trivializationAt F₁ E₁ x₀).symmL 𝕜 x ϕ

中文:
定义 inCoordinates
  签名: (x₀ x : B₁) (y₀ y : B₂) (ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y)
  定义体: .compContinuousAlternatingMap .continuousLinearMapAt 𝕜 y trivializationAt F₂ E₂ y₀
.compContinuousLinearMap (trivializationAt F₁ E₁ x₀).symmL 𝕜 x ϕ

Depends on / 依赖: compContinuousAlternatingMap, compContinuousLinearMap, continuousLinearMapAt, trivializationAt
-/
def inCoordinates (x₀ x : B₁) (y₀ y : B₂) (ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y) :
    F₁ [⋀^ι]->L[𝕜] F₂ :=
.compContinuousAlternatingMap .continuousLinearMapAt 𝕜 y trivializationAt F₂ E₂ y₀
.compContinuousLinearMap (trivializationAt F₁ E₁ x₀).symmL 𝕜 x ϕ

/--
theorem `inCoordinates_eq` / 定理 `inCoordinates_eq`

English:
theorem inCoordinates_eq
  statement: {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y}
  proof: by
  ext
  simp [inCoordinates, *, Function.comp_def]

中文:
定理 inCoordinates_eq
  结论: {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y}
  证明: by
  ext
  simp [inCoordinates, *, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, inCoordinates
-/
theorem inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x [⋀^ι]->L[𝕜] E₂ y}
    (hx : x in (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y in (trivializationAt F₂ E₂ y₀).baseSet) :
    inCoordinates F₁ F₂ x₀ x y₀ y ϕ =
      (((trivializationAt F₂ E₂ y₀).continuousLinearEquivAt 𝕜 y hy : E₂ y ->L[𝕜] F₂)
.compContinuousLinearMap .compContinuousAlternatingMap ϕ
          (((trivializationAt F₁ E₁ x₀).continuousLinearEquivAt 𝕜 x hx).symm : F₁ ->L[𝕜] E₁ x)) := by
  ext
  simp [inCoordinates, *, Function.comp_def]

end ContinuousAlternatingMap

open ContinuousAlternatingMap (inCoordinates)

/-!
### Pretrivialization of the bundle of continuous alternating maps
-/

namespace Bundle.Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B -> Type*}
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B -> Type*}
  [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable (𝕜 ι) in
/--
Definition of `continuousAlternatingMapCoordChange` / `continuousAlternatingMapCoordChange` 的定义

English:
definition continuousAlternatingMapCoordChange
  signature: (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  body: (e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) (ι := ι)

中文:
定义 continuousAlternatingMapCoordChange
  签名: (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  定义体: (e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) (ι := ι)

Depends on / 依赖: continuousAlternatingMapCongr, coordChangeL, symm.continuousAlternatingMapCongr
-/
def continuousAlternatingMapCoordChange (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    (F₁ [⋀^ι]->L[𝕜] F₂) ->L[𝕜] (F₁ [⋀^ι]->L[𝕜] F₂) :=
  (e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) (ι := ι)

variable [forall x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [forall x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

/--
theorem `continuousOn_continuousAlternatingMapCoordChange` / 定理 `continuousOn_continuousAlternatingMapCoordChange`

English:
theorem continuousOn_continuousAlternatingMapCoordChange
  proof: by
  cases nonempty_fintype ι
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · refine map_continuous (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι :

中文:
定理 continuousOn_continuousAlternatingMapCoordChange
  证明: by
  cases nonempty_fintype ι
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · refine map_continuous (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι :

Depends on / 依赖: ContinuousAlternatingMap, ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn, ContinuousLinearEquiv, ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm, ContinuousLinearMap, ContinuousLinearMap.compContinuousAlternatingMapCLM, clm_comp, coe_continuousAlternatingMapCongr, compContinuousAlternatingMapCLM, comp_continuousOn, continuousAlternatingMapCoordChange, continuousOn_coordChange, continuous_compContinuousLinearMapCLM, map_continuous, mfld_set_tac, nonempty_fintype, symm_symm, unfoldPartialApp
-/
theorem continuousOn_continuousAlternatingMapCoordChange
    [Finite ι]
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)) := by
  cases nonempty_fintype ι
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · refine map_continuous (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι := ι) 𝕜 F₁ F₂ F₂)
.comp_continuousOn ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)
    mfld_set_tac
  · refine ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn ?_
.mono (by mfld_set_tac) exact continuousOn_coordChange 𝕜 e₁' e₁

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

variable (𝕜 ι e₁ e₁' e₂ e₂') in
/--
Definition of `continuousAlternatingMap` / `continuousAlternatingMap` 的定义

English:
definition continuousAlternatingMap
  signature: :
  body: ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.symmL 𝕜 p.1⟩
invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet inter e₂.base

中文:
定义 continuousAlternatingMap
  签名: :
  定义体: ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.symmL 𝕜 p.1⟩
invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet inter e₂.base

Depends on / 依赖: compContinuousAlternatingMap, continuousLinearMapAt
-/
def continuousAlternatingMap :
    Pretrivialization (F₁ [⋀^ι]->L[𝕜] F₂) (π (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) where
toFun p := ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.symmL 𝕜 p.1⟩
invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h => h.1
  left_inv' := by
    rintro ⟨x, L⟩ ⟨h₁, h₂⟩
    simp only [TotalSpace.mk_inj]
    ext v
    simp [Function.comp_def, h₁, h₂]
  right_inv' := by
    rintro ⟨x, f⟩ ⟨⟨h₁, h₂⟩, -⟩
    simp only [Prod.mk_right_inj]
    ext v
    simp [Function.comp_def, h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet inter e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/--
Instance `continuousAlternatingMap.isLinear` / 实例 `continuousAlternatingMap.isLinear`

English:
instance continuousAlternatingMap.isLinear
  body: { map_add L L' := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun']
      map_smul c L := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun'] }

中文:
实例 continuousAlternatingMap.isLinear
  定义体: { map_add L L' := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun']
      map_smul c L := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun'] }

Depends on / 依赖: Pretrivialization, Pretrivialization.toFun, continuousAlternatingMap, map_add, map_smul
-/
instance continuousAlternatingMap.isLinear
    [forall x, ContinuousAdd (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
    { map_add L L' := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun']
      map_smul c L := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun'] }

/--
theorem `continuousAlternatingMap_apply` / 定理 `continuousAlternatingMap_apply`

English:
theorem continuousAlternatingMap_apply
  proof: rfl

中文:
定理 continuousAlternatingMap_apply
  证明: rfl
-/
theorem continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) :
    continuousAlternatingMap 𝕜 ι e₁ e₂ p =
⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.symmL 𝕜 p.1⟩ :=
  rfl

/--
theorem `continuousAlternatingMap_symm_apply` / 定理 `continuousAlternatingMap_symm_apply`

English:
theorem continuousAlternatingMap_symm_apply
  given: (p : B × (F₁ [⋀^ι]->L[𝕜] F₂))
  proof: rfl

中文:
定理 continuousAlternatingMap_symm_apply
  条件: (p : B × (F₁ [⋀^ι]->L[𝕜] F₂))
  证明: rfl
-/
theorem continuousAlternatingMap_symm_apply (p : B × (F₁ [⋀^ι]->L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p =
⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap
p.2.compContinuousLinearMap e₁.continuousLinearMapAt 𝕜 p.1⟩ :=
  rfl

/--
theorem `continuousAlternatingMap_symm_apply'` / 定理 `continuousAlternatingMap_symm_apply'`

English:
theorem continuousAlternatingMap_symm_apply'
  statement: {b : B} (hb : b in e₁.baseSet inter e₂.baseSet)
  proof: by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

中文:
定理 continuousAlternatingMap_symm_apply'
  结论: {b : B} (hb : b in e₁.baseSet inter e₂.baseSet)
  证明: by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

Depends on / 依赖: Pretrivialization, Pretrivialization.symm_apply, symm_apply
-/
theorem continuousAlternatingMap_symm_apply' {b : B} (hb : b in e₁.baseSet inter e₂.baseSet)
    (L : F₁ [⋀^ι]->L[𝕜] F₂) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L =
      ((e₂.symmL 𝕜 b).compContinuousAlternatingMap <|
L.compContinuousLinearMap e₁.continuousLinearMapAt 𝕜 b) := by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

/--
theorem `continuousAlternatingMapCoordChange_apply` / 定理 `continuousAlternatingMapCoordChange_apply`

English:
theorem continuousAlternatingMapCoordChange_apply
  statement: (b : B)
  proof: by
  ext v
  simp only [mem_inter_iff] at hb
  simp [continuousAlternatingMapCoordChange, continuousAlternatingMap_apply,
    Function.comp_def, Trivialization.coordChangeL_apply,
    continuousAlternatingMap_symm_apply' hb.left, hb]

中文:
定理 continuousAlternatingMapCoordChange_apply
  结论: (b : B)
  证明: by
  ext v
  simp only [mem_inter_iff] at hb
  simp [continuousAlternatingMapCoordChange, continuousAlternatingMap_apply,
    Function.comp_def, Trivialization.coordChangeL_apply,
    continuousAlternatingMap_symm_apply' hb.left, hb]

Depends on / 依赖: Function, Function.comp_def, Trivialization, Trivialization.coordChangeL_apply, comp_def, continuousAlternatingMapCoordChange, continuousAlternatingMap_apply, continuousAlternatingMap_symm_apply, coordChangeL_apply, hb.left, mem_inter_iff
-/
theorem continuousAlternatingMapCoordChange_apply (b : B)
    (hb : b in e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)) (L : F₁ [⋀^ι]->L[𝕜] F₂) :
    continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L =
      (continuousAlternatingMap 𝕜 ι e₁' e₂'
        ⟨b, (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L⟩).2 := by
  ext v
  simp only [mem_inter_iff] at hb
  simp [continuousAlternatingMapCoordChange, continuousAlternatingMap_apply,
    Function.comp_def, Trivialization.coordChangeL_apply,
    continuousAlternatingMap_symm_apply' hb.left, hb]

end Bundle.Pretrivialization

/-!
### Vector (pre)bundle structure
-/

namespace Bundle.ContinuousAlternatingMap

open Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B -> Type*}
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [forall x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B -> Type*}
  [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [forall x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]

variable (𝕜 ι F₁ E₁ F₂ E₂) in
/--
Definition of `vectorPrebundle` / `vectorPrebundle` 的定义

English:
definition vectorPrebundle
  signature: :
  body: {e | exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_

中文:
定义 vectorPrebundle
  签名: :
  定义体: {e | exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_

Depends on / 依赖: MemTrivializationAtlas, Pretrivialization, Pretrivialization.continuousAlternatingMap, Trivialization, continuousAlternatingMap, infer_instance, mem_baseSet_triv, mem_baseSet_trivializationAt, mem_base_pretrivializationAt, pretrivializationAt, pretrivialization_linear, trivializationAt
-/
def vectorPrebundle :
    VectorPrebundle 𝕜 (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) where
  pretrivializationAtlas :=
    {e | exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.continuousAlternatingMap 𝕜 ι
    (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousOn_continuousAlternatingMapCoordChange,
      continuousAlternatingMapCoordChange_apply⟩
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, continuousAlternatingMap_apply, isInducing_const_prod]
    let L₁ : E₁ b ≃L[𝕜] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    convert! (L₁.continuousAlternatingMapCongr L₂).toHomeomorph.isInducing
    ext f
    simp [Trivialization.linearMapAt_def_of_mem _ (mem_baseSet_trivializationAt _ _ _), L₁, L₂,
      Function.comp_def, mem_baseSet_trivializationAt]

/--
Instance `instTopologicalSpaceTotalSpace` / 实例 `instTopologicalSpaceTotalSpace`

English:
instance instTopologicalSpaceTotalSpace
  signature: :
  body: (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

中文:
实例 instTopologicalSpaceTotalSpace
  签名: :
  定义体: (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

Depends on / 依赖: totalSpaceTopology, vectorPrebundle
-/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

/--
Instance `instFiberBundle` / 实例 `instFiberBundle`

English:
instance instFiberBundle
  signature: :
  body: (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

中文:
实例 instFiberBundle
  签名: :
  定义体: (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

Depends on / 依赖: toFiberBundle, vectorPrebundle
-/
instance instFiberBundle :
    FiberBundle (F₁ [⋀^ι]->L[𝕜] F₂) fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

/--
Instance `instVectorBundle` / 实例 `instVectorBundle`

English:
instance instVectorBundle
  signature: : VectorBundle 𝕜 (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)
  body: (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

中文:
实例 instVectorBundle
  签名: : 向量丛 𝕜 (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)
  定义体: (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

Depends on / 依赖: toVectorBundle, vectorPrebundle
-/
instance instVectorBundle : VectorBundle 𝕜 (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

end Bundle.ContinuousAlternatingMap

/-!
### Trivialization of the bundle of continuous alternating maps
-/

namespace Bundle.Trivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B -> Type*}
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [forall x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B -> Type*}
  [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [forall x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]

variable {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

variable (𝕜 ι e₁ e₂) in
/--
Definition of `continuousAlternatingMap` / `continuousAlternatingMap` 的定义

English:
definition continuousAlternatingMap
  signature: :
  body: VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

中文:
定义 continuousAlternatingMap
  签名: :
  定义体: VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

Depends on / 依赖: VectorPrebundle, VectorPrebundle.trivializationOfMemPretrivializationAtlas, trivializationOfMemPretrivializationAtlas
-/
def continuousAlternatingMap :
    Trivialization (F₁ [⋀^ι]->L[𝕜] F₂) (π (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

/--
Instance `memTrivializationAtlas_continuousAlternatingMap` / 实例 `memTrivializationAtlas_continuousAlternatingMap`

English:
instance memTrivializationAtlas_continuousAlternatingMap
  signature: :
  body: ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

@[simp]

中文:
实例 memTrivializationAtlas_continuousAlternatingMap
  签名: :
  定义体: ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

@[simp]

Depends on / 依赖: infer_instance
-/
instance memTrivializationAtlas_continuousAlternatingMap :
    MemTrivializationAtlas
      (e₁.continuousAlternatingMap 𝕜 ι e₂ :
        Trivialization (F₁ [⋀^ι]->L[𝕜] F₂) (π (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x))) :=
  ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

@[simp]
/--
theorem `baseSet_continuousAlternatingMap` / 定理 `baseSet_continuousAlternatingMap`

English:
theorem baseSet_continuousAlternatingMap
  proof: rfl

中文:
定理 baseSet_continuousAlternatingMap
  证明: rfl
-/
theorem baseSet_continuousAlternatingMap :
    (e₁.continuousAlternatingMap 𝕜 ι e₂).baseSet = e₁.baseSet inter e₂.baseSet :=
  rfl

/--
theorem `continuousAlternatingMap_apply` / 定理 `continuousAlternatingMap_apply`

English:
theorem continuousAlternatingMap_apply
  proof: rfl

中文:
定理 continuousAlternatingMap_apply
  证明: rfl
-/
theorem continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) :
    e₁.continuousAlternatingMap 𝕜 ι e₂ p =
.compContinuousAlternatingMap p.2 ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1 : _ ->L[𝕜] _)
.compContinuousLinearMap (e₁.symmL 𝕜 p.1 : F₁ ->L[𝕜] E₁ p.1)⟩ :=
  rfl

end Bundle.Trivialization

/-!
### Lemmas about `trivializationAt` for the bundle of continuous alternating maps
-/

namespace FiberBundle

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B -> Type*}
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [forall x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B -> Type*}
  [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [forall x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]

/--
theorem `trivializationAt_continuousAlternatingMap` / 定理 `trivializationAt_continuousAlternatingMap`

English:
theorem trivializationAt_continuousAlternatingMap
  given: (x₀ : B)
  proof: rfl

中文:
定理 trivializationAt_continuousAlternatingMap
  条件: (x₀ : B)
  证明: rfl
-/
theorem trivializationAt_continuousAlternatingMap (x₀ : B) :
    trivializationAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀ =
    (trivializationAt F₁ E₁ x₀).continuousAlternatingMap 𝕜 ι (trivializationAt F₂ E₂ x₀) := rfl

/--
theorem `trivializationAt_continuousAlternatingMap_apply` / 定理 `trivializationAt_continuousAlternatingMap_apply`

English:
theorem trivializationAt_continuousAlternatingMap_apply
  statement: (x₀ : B)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_continuousAlternatingMap_apply
  结论: (x₀ : B)
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_continuousAlternatingMap_apply (x₀ : B)
    (x : TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) :
    trivializationAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ F₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_continuousAlternatingMap_source` / 定理 `trivializationAt_continuousAlternatingMap_source`

English:
theorem trivializationAt_continuousAlternatingMap_source
  given: (x₀ : B)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trivializationAt_continuousAlternatingMap_source
  条件: (x₀ : B)
  证明: rfl

@[simp, mfld_simps]
-/
theorem trivializationAt_continuousAlternatingMap_source (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀).source =
      π (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
/--
theorem `trivializationAt_continuousAlternatingMap_target` / 定理 `trivializationAt_continuousAlternatingMap_target`

English:
theorem trivializationAt_continuousAlternatingMap_target
  given: (x₀ : B)
  proof: rfl

@[simp]

中文:
定理 trivializationAt_continuousAlternatingMap_target
  条件: (x₀ : B)
  证明: rfl

@[simp]
-/
theorem trivializationAt_continuousAlternatingMap_target (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
/--
theorem `trivializationAt_continuousAlternatingMap_baseSet` / 定理 `trivializationAt_continuousAlternatingMap_baseSet`

English:
theorem trivializationAt_continuousAlternatingMap_baseSet
  given: (x₀ : B)
  proof: rfl

中文:
定理 trivializationAt_continuousAlternatingMap_baseSet
  条件: (x₀ : B)
  证明: rfl
-/
theorem trivializationAt_continuousAlternatingMap_baseSet (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

end FiberBundle

/-!
### Continuity of maps to the total space of the bundle of continuous alternating maps
-/

section Continuity

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B -> Type*}
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [forall x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B -> Type*}
  [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [forall x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x₀ : X}


/--
theorem `continuousWithinAt_continuousAlternatingMap_bundle` / 定理 `continuousWithinAt_continuousAlternatingMap_bundle`

English:
theorem continuousWithinAt_continuousAlternatingMap_bundle
  proof: FiberBundle.continuousWithinAt_totalSpace ..

中文:
定理 continuousWithinAt_continuousAlternatingMap_bundle
  证明: FiberBundle.continuousWithinAt_totalSpace ..

Depends on / 依赖: FiberBundle, FiberBundle.continuousWithinAt_totalSpace, continuousWithinAt_totalSpace
-/
theorem continuousWithinAt_continuousAlternatingMap_bundle
    (f : X -> TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x => inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..

/--
theorem `continuousAt_continuousAlternatingMap_bundle` / 定理 `continuousAt_continuousAlternatingMap_bundle`

English:
theorem continuousAt_continuousAlternatingMap_bundle
  proof: FiberBundle.continuousAt_totalSpace ..

中文:
定理 continuousAt_continuousAlternatingMap_bundle
  证明: FiberBundle.continuousAt_totalSpace ..

Depends on / 依赖: FiberBundle, FiberBundle.continuousAt_totalSpace, continuousAt_totalSpace
-/
theorem continuousAt_continuousAlternatingMap_bundle
    (f : X -> TotalSpace (F₁ [⋀^ι]->L[𝕜] F₂) (fun x => E₁ x [⋀^ι]->L[𝕜] E₂ x)) :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).1) x₀ ∧
        ContinuousAt
          (fun x => inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

end Continuity

end
