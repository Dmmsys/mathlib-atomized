/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# The vector bundle of continuous (semi)linear maps

We define the (topological) vector bundle of continuous (semi)linear maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, normed spaces `F₁` and `F₂`, and a ring-homomorphism `σ` between
their respective scalar fields, we define a vector bundle with fiber `E₁ x →SL[σ] E₂ x`.
If the `E₁` and `E₂` are vector bundles with model fibers `F₁` and `F₂`, then this will be a
vector bundle with fiber `F₁ →SL[σ] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ →SL[𝕜] F₂` using the `VectorPrebundle` construction. This is
a bit awkward because it introduces a dependence on the normed space structure of the model fibers,
rather than just their topological vector space structure; it is not clear whether this is
necessary.

Similar constructions should be possible (but are yet to be formalized) for tensor products of
topological vector bundles, exterior algebras, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.
-/

@[expose] public section


noncomputable section

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

variable {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {𝕜₂ : Type*} [NontriviallyNormedField 𝕜₂]
  (σ : 𝕜₁ ->+* 𝕜₂)

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁] (E₁ : B -> Type*)
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜₁ (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂] (E₂ : B -> Type*)
  [forall x, AddCommGroup (E₂ x)] [forall x, Module 𝕜₂ (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Bundle.Pretrivialization

/--
Definition of `continuousLinearMapCoordChange` / `continuousLinearMapCoordChange` 的定义

English:
definition continuousLinearMapCoordChange
  signature: [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂]
  body: ((e₁'.coordChangeL 𝕜₁ e₁ b).symm.arrowCongrSL (e₂.coordChangeL 𝕜₂ e₂' b) :
    (F₁ ->SL[σ] F₂) ≃L[𝕜₂] F₁ ->SL[σ] F₂)

中文:
定义 continuousLinearMapCoordChange
  签名: [e₁.是线性 𝕜₁] [e₁'.是线性 𝕜₁] [e₂.是线性 𝕜₂]
  定义体: ((e₁'.coordChangeL 𝕜₁ e₁ b).symm.arrowCongrSL (e₂.coordChangeL 𝕜₂ e₂' b) :
    (F₁ ->SL[σ] F₂) ≃L[𝕜₂] F₁ ->SL[σ] F₂)

Depends on / 依赖: arrowCongrSL, coordChangeL, symm.arrowCongrSL
-/
def continuousLinearMapCoordChange [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂]
    [e₂'.IsLinear 𝕜₂] (b : B) : (F₁ ->SL[σ] F₂) ->L[𝕜₂] F₁ ->SL[σ] F₂ :=
  ((e₁'.coordChangeL 𝕜₁ e₁ b).symm.arrowCongrSL (e₂.coordChangeL 𝕜₂ e₂' b) :
    (F₁ ->SL[σ] F₂) ≃L[𝕜₂] F₁ ->SL[σ] F₂)

variable {σ e₁ e₁' e₂ e₂'}
variable [forall x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [forall x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `continuousOn_continuousLinearMapCoordChange` / 定理 `continuousOn_continuousLinearMapCoordChange`

English:
theorem continuousOn_continuousLinearMapCoordChange
  statement: [RingHomIsometric σ]
  proof: by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).continuous
  have h₃ := continuousOn_coordChange 𝕜₁ e₁' e₁
  have h₄ := continuousOn_coordChange 𝕜₂ e₂ e₂'
  refine ((h₁.comp_continuousOn (h₄.mono ?_)).clm_comp (h₂.comp_continuousOn (h₃.mono ?_))).congr ?_
  · mfld_set_tac
  · mfld_set_tac
  · intro b _
    ext L v
    dsimp [continuousLinearMapCoordChange]

中文:
定理 continuousOn_continuousLinearMapCoordChange
  结论: [RingHomIsometric σ]
  证明: by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).continuous
  have h₃ := continuousOn_coordChange 𝕜₁ e₁' e₁
  have h₄ := continuousOn_coordChange 𝕜₂ e₂ e₂'
  refine ((h₁.comp_continuousOn (h₄.mono ?_)).clm_comp (h₂.comp_continuousOn (h₃.mono ?_))).congr ?_
  · mfld_set_tac
  · mfld_set_tac
  · intro b _
    ext L v
    dsimp [continuousLinearMapCoordChange]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip, RingHom, RingHom.id, clm_comp, compSL, comp_continuousOn, continuous, continuousLinearMapCoordChange, continuousOn_coordChange, mfld_set_tac
-/
theorem continuousOn_continuousLinearMapCoordChange [RingHomIsometric σ]
    [VectorBundle 𝕜₁ F₁ E₁] [VectorBundle 𝕜₂ F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂')
      (e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)) := by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).continuous
  have h₃ := continuousOn_coordChange 𝕜₁ e₁' e₁
  have h₄ := continuousOn_coordChange 𝕜₂ e₂ e₂'
  refine ((h₁.comp_continuousOn (h₄.mono ?_)).clm_comp (h₂.comp_continuousOn (h₃.mono ?_))).congr ?_
  · mfld_set_tac
  · mfld_set_tac
  · intro b _
    ext L v
    dsimp [continuousLinearMapCoordChange]

variable (σ e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂] [e₂'.IsLinear 𝕜₂]

/--
Definition of `continuousLinearMap` / `continuousLinearMap` 的定义

English:
definition continuousLinearMap
  signature: :
  body: ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩
  invFun p := ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h => h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ => by
    simp only [TotalSpace.mk_inj]
    ext (v : E₁ x)
    dsimp only [comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt]; rw [Trivialization.symmL_continuousLinearMapAt]
    exacts [h₁, h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ => by
    simp only [Prod.mk_right_inj]
    ext v
    dsimp only [comp_apply]
    rw [Trivialization.continuousLinearMapAt_symmL]; rw [Trivialization.continuousLinearMapAt_symmL]
    exacts [h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet inter e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

中文:
定义 continuousLinearMap
  签名: :
  定义体: ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩
  invFun p := ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h => h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ => by
    simp only [TotalSpace.mk_inj]
    ext (v : E₁ x)
    dsimp only [comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt]; rw [Trivialization.symmL_continuousLinearMapAt]
    exacts [h₁, h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ => by
    simp only [Prod.mk_right_inj]
    ext v
    dsimp only [comp_apply]
    rw [Trivialization.continuousLinearMapAt_symmL]; rw [Trivialization.continuousLinearMapAt_symmL]
    exacts [h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet inter e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

Depends on / 依赖: continuousLinearMapAt
-/
def continuousLinearMap :
    Pretrivialization (F₁ ->SL[σ] F₂) (π (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) where
  toFun p := ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩
  invFun p := ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h => h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ => by
    simp only [TotalSpace.mk_inj]
    ext (v : E₁ x)
    dsimp only [comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt]; rw [Trivialization.symmL_continuousLinearMapAt]
    exacts [h₁, h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ => by
    simp only [Prod.mk_right_inj]
    ext v
    dsimp only [comp_apply]
    rw [Trivialization.continuousLinearMapAt_symmL]; rw [Trivialization.continuousLinearMapAt_symmL]
    exacts [h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet inter e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215):
-- TODO: see if Lean 4 can generate this instance without a hint
/--
Instance `continuousLinearMap.isLinear` / 实例 `continuousLinearMap.isLinear`

English:
instance continuousLinearMap.isLinear
  signature: [forall x, ContinuousAdd (E₂ x)] [forall x, ContinuousSMul 𝕜₂ (E₂ x)]
  body: { map_add L L' := by simp [continuousLinearMap, Pretrivialization.toFun']
      map_smul c L := by simp [continuousLinearMap, Pretrivialization.toFun'] }

中文:
实例 continuousLinearMap.isLinear
  签名: [对任意 x, 连续加法 (E₂ x)] [对任意 x, 连续标量乘法 𝕜₂ (E₂ x)]
  定义体: { map_add L L' := by simp [continuousLinearMap, Pretrivialization.toFun']
      map_smul c L := by simp [continuousLinearMap, Pretrivialization.toFun'] }

Depends on / 依赖: Pretrivialization, Pretrivialization.toFun, continuousLinearMap, map_add, map_smul
-/
instance continuousLinearMap.isLinear [forall x, ContinuousAdd (E₂ x)] [forall x, ContinuousSMul 𝕜₂ (E₂ x)] :
    (Pretrivialization.continuousLinearMap σ e₁ e₂).IsLinear 𝕜₂ where
  linear x _ :=
    { map_add L L' := by simp [continuousLinearMap, Pretrivialization.toFun']
      map_smul c L := by simp [continuousLinearMap, Pretrivialization.toFun'] }

/--
theorem `continuousLinearMap_apply` / 定理 `continuousLinearMap_apply`

English:
theorem continuousLinearMap_apply
  given: (p : TotalSpace (F₁ ->SL[σ] F₂) fun x => E₁ x ->SL[σ] E₂ x)
  proof: rfl

中文:
定理 continuousLinearMap_apply
  条件: (p : 全空间 (F₁ ->SL[σ] F₂) fun x => E₁ x ->SL[σ] E₂ x)
  证明: rfl
-/
theorem continuousLinearMap_apply (p : TotalSpace (F₁ ->SL[σ] F₂) fun x => E₁ x ->SL[σ] E₂ x) :
    (continuousLinearMap σ e₁ e₂) p =
      ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩ :=
  rfl

/--
theorem `continuousLinearMap_symm_apply` / 定理 `continuousLinearMap_symm_apply`

English:
theorem continuousLinearMap_symm_apply
  given: (p : B × (F₁ ->SL[σ] F₂))
  proof: rfl

中文:
定理 continuousLinearMap_symm_apply
  条件: (p : B × (F₁ ->SL[σ] F₂))
  证明: rfl
-/
theorem continuousLinearMap_symm_apply (p : B × (F₁ ->SL[σ] F₂)) :
    (continuousLinearMap σ e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩ :=
  rfl

/--
theorem `continuousLinearMap_symm_apply'` / 定理 `continuousLinearMap_symm_apply'`

English:
theorem continuousLinearMap_symm_apply'
  statement: {b : B} (hb : b in e₁.baseSet inter e₂.baseSet)
  proof: by
  rw [symm_apply]
  · rfl
  · exact hb

中文:
定理 continuousLinearMap_symm_apply'
  结论: {b : B} (hb : b in e₁.baseSet inter e₂.baseSet)
  证明: by
  rw [symm_apply]
  · rfl
  · exact hb

Depends on / 依赖: symm_apply
-/
theorem continuousLinearMap_symm_apply' {b : B} (hb : b in e₁.baseSet inter e₂.baseSet)
    (L : F₁ ->SL[σ] F₂) :
    (continuousLinearMap σ e₁ e₂).symm b L =
      (e₂.symmL 𝕜₂ b).comp (L.comp <| e₁.continuousLinearMapAt 𝕜₁ b) := by
  rw [symm_apply]
  · rfl
  · exact hb

/--
theorem `continuousLinearMapCoordChange_apply` / 定理 `continuousLinearMapCoordChange_apply`

English:
theorem continuousLinearMapCoordChange_apply
  statement: (b : B)
  proof: by
  ext v
  simp_rw [continuousLinearMapCoordChange, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongrSL_apply, continuousLinearMap_apply,
    continuousLinearMap_symm_apply' σ e₁ e₂ hb.1, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, Trivialization.continuousLinearMapAt_apply]
  rw [e₂.symmL_apply hb.1.2]; rw [e₁'.symmL_apply hb.2.1]; rw [e₂.coordChangeL_apply e₂']; rw [e₁'.coordChangeL_apply e₁]; rw [e₁.coe_linearMapAt_of_mem hb.1.1]; rw [e₂'.coe_linearMapAt_of_mem hb.2.2]
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]

中文:
定理 continuousLinearMapCoordChange_apply
  结论: (b : B)
  证明: by
  ext v
  simp_rw [continuousLinearMapCoordChange, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongrSL_apply, continuousLinearMap_apply,
    continuousLinearMap_symm_apply' σ e₁ e₂ hb.1, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, Trivialization.continuousLinearMapAt_apply]
  rw [e₂.symmL_apply hb.1.2]; rw [e₁'.symmL_apply hb.2.1]; rw [e₂.coordChangeL_apply e₂']; rw [e₁'.coordChangeL_apply e₁]; rw [e₁.coe_linearMapAt_of_mem hb.1.1]; rw [e₂'.coe_linearMapAt_of_mem hb.2.2]
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.arrowCongrSL_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm, Trivialization, Trivialization.continuousLinearMapAt_apply, arrowCongrSL_apply, coe_coe, coe_linearMapAt_, coe_linearMapAt_of_mem, comp_apply, continuousLinearMapAt_apply, continuousLinearMapCoordChange, continuousLinearMap_apply, continuousLinearMap_symm_apply, coordChangeL_apply, simp_rw, symmL_apply, symm_symm
-/
theorem continuousLinearMapCoordChange_apply (b : B)
    (hb : b in e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)) (L : F₁ ->SL[σ] F₂) :
    continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂' b L =
      (continuousLinearMap σ e₁' e₂' ⟨b, (continuousLinearMap σ e₁ e₂).symm b L⟩).2 := by
  ext v
  simp_rw [continuousLinearMapCoordChange, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongrSL_apply, continuousLinearMap_apply,
    continuousLinearMap_symm_apply' σ e₁ e₂ hb.1, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, Trivialization.continuousLinearMapAt_apply]
  rw [e₂.symmL_apply hb.1.2]; rw [e₁'.symmL_apply hb.2.1]; rw [e₂.coordChangeL_apply e₂']; rw [e₁'.coordChangeL_apply e₁]; rw [e₁.coe_linearMapAt_of_mem hb.1.1]; rw [e₂'.coe_linearMapAt_of_mem hb.2.2]
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]

end Bundle.Pretrivialization

open Pretrivialization

variable (F₁ E₁ F₂ E₂)
variable [forall x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]
variable [forall x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]
variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜₂ (E₂ x)]
variable [RingHomIsometric σ]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Bundle.ContinuousLinearMap.vectorPrebundle` / `Bundle.ContinuousLinearMap.vectorPrebundle` 的定义

English:
definition Bundle.ContinuousLinearMap.vectorPrebundle
  signature: :
  body: {e | exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousLinearMap σ e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousLinearMap σ (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂',
      continuousOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply σ e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing := by
    intro b
    let L₁ : E₁ b ≃L[𝕜₁] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜₁ b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜₂] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜₂ b
        (mem_baseSet_trivializationAt _ _ _)
    let φ : (E₁ b ->SL[σ] E₂ b) ≃L[𝕜₂] F₁ ->SL[σ] F₂ := L₁.arrowCongrSL L₂
    have : IsInducing fun x => (b, φ x) := isInducing_const_prod.mpr φ.toHomeomorph.isInducing
    convert! this
    ext f
    dsimp [Pretrivialization.continuousLinearMap_apply]
    simp only [Trivialization.symmL_apply, mem_baseSet_trivializationAt,
      Trivialization.linearMapAt_def_of_mem]
    rfl

中文:
定义 Bundle.连续线性映射.vectorPrebundle
  签名: :
  定义体: {e | exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousLinearMap σ e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousLinearMap σ (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂',
      continuousOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply σ e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing := by
    intro b
    let L₁ : E₁ b ≃L[𝕜₁] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜₁ b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜₂] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜₂ b
        (mem_baseSet_trivializationAt _ _ _)
    let φ : (E₁ b ->SL[σ] E₂ b) ≃L[𝕜₂] F₁ ->SL[σ] F₂ := L₁.arrowCongrSL L₂
    have : IsInducing fun x => (b, φ x) := isInducing_const_prod.mpr φ.toHomeomorph.isInducing
    convert! this
    ext f
    dsimp [Pretrivialization.continuousLinearMap_apply]
    simp only [Trivialization.symmL_apply, mem_baseSet_trivializationAt,
      Trivialization.linearMapAt_def_of_mem]
    rfl

Depends on / 依赖: MemTrivializationAtlas, Pretrivialization, Pretrivialization.continuousLinearMap, Trivialization, continuousLinearMap, infer_instance, mem_baseSet_trivializationAt, mem_base_pretrivializationAt, pretrivializationAt, pretrivialization_linear, trivializationAt
-/
def Bundle.ContinuousLinearMap.vectorPrebundle :
    VectorPrebundle 𝕜₂ (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) where
  pretrivializationAtlas :=
    {e | exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousLinearMap σ e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousLinearMap σ (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂',
      continuousOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply σ e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing := by
    intro b
    let L₁ : E₁ b ≃L[𝕜₁] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜₁ b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜₂] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜₂ b
        (mem_baseSet_trivializationAt _ _ _)
    let φ : (E₁ b ->SL[σ] E₂ b) ≃L[𝕜₂] F₁ ->SL[σ] F₂ := L₁.arrowCongrSL L₂
    have : IsInducing fun x => (b, φ x) := isInducing_const_prod.mpr φ.toHomeomorph.isInducing
    convert! this
    ext f
    dsimp [Pretrivialization.continuousLinearMap_apply]
    simp only [Trivialization.symmL_apply, mem_baseSet_trivializationAt,
      Trivialization.linearMapAt_def_of_mem]
    rfl

/--
Instance `Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace` / 实例 `Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace`

English:
instance Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
  signature: :
  body: (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology

中文:
实例 Bundle.连续线性映射.topologicalSpaceTotalSpace
  签名: :
  定义体: (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology

Depends on / 依赖: Bundle, Bundle.ContinuousLinearMap.vectorPrebundle, ContinuousLinearMap, totalSpaceTopology, vectorPrebundle
-/
instance Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology

/--
Instance `Bundle.ContinuousLinearMap.fiberBundle` / 实例 `Bundle.ContinuousLinearMap.fiberBundle`

English:
instance Bundle.ContinuousLinearMap.fiberBundle
  signature: :
  body: (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toFiberBundle

中文:
实例 Bundle.连续线性映射.fiberBundle
  签名: :
  定义体: (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toFiberBundle

Depends on / 依赖: Bundle, Bundle.ContinuousLinearMap.vectorPrebundle, ContinuousLinearMap, toFiberBundle, vectorPrebundle
-/
instance Bundle.ContinuousLinearMap.fiberBundle :
    FiberBundle (F₁ ->SL[σ] F₂) fun x => E₁ x ->SL[σ] E₂ x :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toFiberBundle

/--
Instance `Bundle.ContinuousLinearMap.vectorBundle` / 实例 `Bundle.ContinuousLinearMap.vectorBundle`

English:
instance Bundle.ContinuousLinearMap.vectorBundle
  signature: :
  body: (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toVectorBundle

中文:
实例 Bundle.连续线性映射.vectorBundle
  签名: :
  定义体: (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toVectorBundle

Depends on / 依赖: Bundle, Bundle.ContinuousLinearMap.vectorPrebundle, ContinuousLinearMap, toVectorBundle, vectorPrebundle
-/
instance Bundle.ContinuousLinearMap.vectorBundle :
    VectorBundle 𝕜₂ (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toVectorBundle

variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂] {F₁ E₁ F₂ E₂}

/--
Definition of `Bundle.Trivialization.continuousLinearMap` / `Bundle.Trivialization.continuousLinearMap` 的定义

English:
definition Bundle.Trivialization.continuousLinearMap
  signature: :
  body: VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

中文:
定义 Bundle.Trivialization.continuousLinearMap
  签名: :
  定义体: VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

Depends on / 依赖: VectorPrebundle, VectorPrebundle.trivializationOfMemPretrivializationAtlas, trivializationOfMemPretrivializationAtlas
-/
def Bundle.Trivialization.continuousLinearMap :
    Trivialization (F₁ ->SL[σ] F₂) (π (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

/--
Instance `Bundle.ContinuousLinearMap.memTrivializationAtlas` / 实例 `Bundle.ContinuousLinearMap.memTrivializationAtlas`

English:
instance Bundle.ContinuousLinearMap.memTrivializationAtlas
  signature: :
  body: ⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩

中文:
实例 Bundle.连续线性映射.memTrivializationAtlas
  签名: :
  定义体: ⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩

Depends on / 依赖: infer_instance
-/
instance Bundle.ContinuousLinearMap.memTrivializationAtlas :
    MemTrivializationAtlas
      (e₁.continuousLinearMap σ e₂ :
        Trivialization (F₁ ->SL[σ] F₂) (π (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x))) where
  out := ⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩

variable {e₁ e₂}

@[simp]
/--
theorem `Bundle.Trivialization.baseSet_continuousLinearMap` / 定理 `Bundle.Trivialization.baseSet_continuousLinearMap`

English:
theorem Bundle.Trivialization.baseSet_continuousLinearMap
  proof: rfl

中文:
定理 Bundle.Trivialization.baseSet_continuousLinearMap
  证明: rfl
-/
theorem Bundle.Trivialization.baseSet_continuousLinearMap :
    (e₁.continuousLinearMap σ e₂).baseSet = e₁.baseSet inter e₂.baseSet :=
  rfl

/--
theorem `Bundle.Trivialization.continuousLinearMap_apply` / 定理 `Bundle.Trivialization.continuousLinearMap_apply`

English:
theorem Bundle.Trivialization.continuousLinearMap_apply
  proof: rfl

中文:
定理 Bundle.Trivialization.continuousLinearMap_apply
  证明: rfl
-/
theorem Bundle.Trivialization.continuousLinearMap_apply
    (p : TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) :
    e₁.continuousLinearMap σ e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜₂ p.1 : _ ->L[𝕜₂] _).comp
        (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ ->L[𝕜₁] E₁ p.1) : F₁ ->SL[σ] E₂ p.1)⟩ :=
  rfl

/--
theorem `hom_trivializationAt` / 定理 `hom_trivializationAt`

English:
theorem hom_trivializationAt
  given: (x₀ : B)
  proof: rfl

中文:
定理 hom_trivializationAt
  条件: (x₀ : B)
  证明: rfl
-/
theorem hom_trivializationAt (x₀ : B) :
    trivializationAt (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) x₀ =
    (trivializationAt F₁ E₁ x₀).continuousLinearMap σ (trivializationAt F₂ E₂ x₀) := rfl

/--
theorem `hom_trivializationAt_apply` / 定理 `hom_trivializationAt_apply`

English:
theorem hom_trivializationAt_apply
  statement: (x₀ : B)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 hom_trivializationAt_apply
  结论: (x₀ : B)
  证明: rfl

@[simp, mfld_simps]
-/
theorem hom_trivializationAt_apply (x₀ : B)
    (x : TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) :
    trivializationAt (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl

@[simp, mfld_simps]
/--
theorem `hom_trivializationAt_source` / 定理 `hom_trivializationAt_source`

English:
theorem hom_trivializationAt_source
  given: (x₀ : B)
  proof: rfl

@[simp, mfld_simps]

中文:
定理 hom_trivializationAt_source
  条件: (x₀ : B)
  证明: rfl

@[simp, mfld_simps]
-/
theorem hom_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) x₀).source =
      π (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
/--
theorem `hom_trivializationAt_target` / 定理 `hom_trivializationAt_target`

English:
theorem hom_trivializationAt_target
  given: (x₀ : B)
  proof: rfl

@[simp]

中文:
定理 hom_trivializationAt_target
  条件: (x₀ : B)
  证明: rfl

@[simp]
-/
theorem hom_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
/--
theorem `hom_trivializationAt_baseSet` / 定理 `hom_trivializationAt_baseSet`

English:
theorem hom_trivializationAt_baseSet
  given: (x₀ : B)
  proof: rfl

中文:
定理 hom_trivializationAt_baseSet
  条件: (x₀ : B)
  证明: rfl
-/
theorem hom_trivializationAt_baseSet (x₀ : B) :
    (trivializationAt (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

/--
theorem `continuousWithinAt_hom_bundle` / 定理 `continuousWithinAt_hom_bundle`

English:
theorem continuousWithinAt_hom_bundle
  statement: {M : Type*} [TopologicalSpace M]
  proof: FiberBundle.continuousWithinAt_totalSpace ..

中文:
定理 continuousWithinAt_hom_bundle
  结论: {M : 类型} [拓扑空间 M]
  证明: FiberBundle.continuousWithinAt_totalSpace ..

Depends on / 依赖: FiberBundle, FiberBundle.continuousWithinAt_totalSpace, continuousWithinAt_totalSpace
-/
theorem continuousWithinAt_hom_bundle {M : Type*} [TopologicalSpace M]
    (f : M -> TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) {s : Set M} {x₀ : M} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..

/--
theorem `continuousAt_hom_bundle` / 定理 `continuousAt_hom_bundle`

English:
theorem continuousAt_hom_bundle
  statement: {M : Type*} [TopologicalSpace M]
  proof: FiberBundle.continuousAt_totalSpace ..

中文:
定理 continuousAt_hom_bundle
  结论: {M : 类型} [拓扑空间 M]
  证明: FiberBundle.continuousAt_totalSpace ..

Depends on / 依赖: FiberBundle, FiberBundle.continuousAt_totalSpace, continuousAt_totalSpace
-/
theorem continuousAt_hom_bundle {M : Type*} [TopologicalSpace M]
    (f : M -> TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) {x₀ : M} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).1) x₀ ∧
        ContinuousAt
          (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

section

/- Declare two bases spaces `B₁` and `B₂` and two vector bundles `E₁` and `E₂` respectively
over `B₁` and `B₂` (with model fibers `F₁` and `F₂`).

Also a third space `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ -> Type*} {E₂ : B₂ -> Type*} [NontriviallyNormedField 𝕜]
  [forall x, AddCommGroup (E₁ x)] [forall x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [forall x, TopologicalSpace (E₁ x)] [forall x, AddCommGroup (E₂ x)]
  [forall x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [forall x, TopologicalSpace (E₂ x)]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace M]
  {n : WithTop Nat∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M -> B₁} {b₂ : M -> B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) ->L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/--
lemma `ContinuousWithinAt.clm_apply_of_inCoordinates` / 引理 `ContinuousWithinAt.clm_apply_of_inCoordinates`

English:
lemma ContinuousWithinAt.clm_apply_of_inCoordinates
  proof: by
  rw [← continuousWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContinuousWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm using by simp [inCoordinates_eq hm h'm, hm]

中文:
引理 ContinuousWithinAt.clm_apply_of_inCoordinates
  证明: by
  rw [← continuousWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContinuousWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm using by simp [inCoordinates_eq hm h'm, hm]

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.clm_apply, FiberBundle, FiberBundle.continuousWithinAt_totalSpace, FiberBundle.mem_baseSet_trivializationAt, baseSet, clm_apply, congr_of_eventuallyEq_of_mem, continuousWithinAt_insert_self, continuousWithinAt_totalSpace, insert, mem_baseSet_trivializationAt, mem_insert, mem_nhds, open_baseSet, open_baseSet.mem_nhds, trivializationAt
-/
lemma ContinuousWithinAt.clm_apply_of_inCoordinates
    (hϕ : ContinuousWithinAt
      (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : ContinuousWithinAt (fun m => (v m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : ContinuousWithinAt b₂ s m₀) :
    ContinuousWithinAt (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) s m₀ := by
  rw [← continuousWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContinuousWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : forallᶠ m in 𝓝[insert m₀ s] m₀, b₁ m in (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : forallᶠ m in 𝓝[insert m₀ s] m₀, b₂ m in (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm using by simp [inCoordinates_eq hm h'm, hm]


/--
lemma `ContinuousAt.clm_apply_of_inCoordinates` / 引理 `ContinuousAt.clm_apply_of_inCoordinates`

English:
lemma ContinuousAt.clm_apply_of_inCoordinates
  proof: by
  rw [← continuousWithinAt_univ] at hϕ hv hb₂ ⊢
  exact hϕ.clm_apply_of_inCoordinates hv hb₂

中文:
引理 ContinuousAt.clm_apply_of_inCoordinates
  证明: by
  rw [← continuousWithinAt_univ] at hϕ hv hb₂ ⊢
  exact hϕ.clm_apply_of_inCoordinates hv hb₂

Depends on / 依赖: clm_apply_of_inCoordinates, continuousWithinAt_univ
-/
lemma ContinuousAt.clm_apply_of_inCoordinates
    (hϕ : ContinuousAt
      (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ContinuousAt (fun m => (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : ContinuousAt b₂ m₀) :
    ContinuousAt (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← continuousWithinAt_univ] at hϕ hv hb₂ ⊢
  exact hϕ.clm_apply_of_inCoordinates hv hb₂

end

section

/- Declare a base space `B` and three vector bundles `E₁`, `E₂` and `E₃` over `B`
(with model fibers `F₁`, `F₂` and `F₃`).

Also a second space `M`, which will be the source of all our maps.
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
  [TopologicalSpace B] [TopologicalSpace M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b : M -> B} {v : forall x, E₁ (b x)} {s : Set M} {x : M}

section OneVariable

variable [forall x, IsTopologicalAddGroup (E₂ x)] [forall x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : forall x, (E₁ (b x) ->L[𝕜] E₂ (b x))}

/--
lemma `ContinuousWithinAt.clm_bundle_apply` / 引理 `ContinuousWithinAt.clm_bundle_apply`

English:
lemma ContinuousWithinAt.clm_bundle_apply
  proof: by
  simp only [continuousWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

中文:
引理 ContinuousWithinAt.clm_bundle_apply
  证明: by
  simp only [continuousWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1
-/
lemma ContinuousWithinAt.clm_bundle_apply
    (hϕ : ContinuousWithinAt
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m))
      s x)
    (hv : ContinuousWithinAt (fun m => TotalSpace.mk' F₁ (b m) (v m)) s x) :
    ContinuousWithinAt
      (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x := by
  simp only [continuousWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/--
lemma `ContinuousAt.clm_bundle_apply` / 引理 `ContinuousAt.clm_bundle_apply`

English:
lemma ContinuousAt.clm_bundle_apply
  proof: by
  simp only [← continuousWithinAt_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

中文:
引理 ContinuousAt.clm_bundle_apply
  证明: by
  simp only [← continuousWithinAt_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv
-/
lemma ContinuousAt.clm_bundle_apply
    (hϕ : ContinuousAt
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : ContinuousAt (fun m => TotalSpace.mk' F₁ (b m) (v m)) x) :
    ContinuousAt (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [← continuousWithinAt_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

/--
lemma `ContinuousOn.clm_bundle_apply` / 引理 `ContinuousOn.clm_bundle_apply`

English:
lemma ContinuousOn.clm_bundle_apply
  proof: fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)

中文:
引理 ContinuousOn.clm_bundle_apply
  证明: fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)
-/
lemma ContinuousOn.clm_bundle_apply
    (hϕ : ContinuousOn
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)) s)
    (hv : ContinuousOn (fun m => TotalSpace.mk' F₁ (b m) (v m)) s) :
    ContinuousOn (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s :=
  fun x hx => (hϕ x hx).clm_bundle_apply (hv x hx)

/--
lemma `Continuous.clm_bundle_apply` / 引理 `Continuous.clm_bundle_apply`

English:
lemma Continuous.clm_bundle_apply
  proof: by
  simp only [← continuousOn_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

中文:
引理 连续.clm_bundle_apply
  证明: by
  simp only [← continuousOn_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv
-/
lemma Continuous.clm_bundle_apply
    (hϕ : Continuous
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : Continuous (fun m => TotalSpace.mk' F₁ (b m) (v m))) :
    Continuous (fun m => TotalSpace.mk' F₂ (b m) (ϕ m (v m))) := by
  simp only [← continuousOn_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

end OneVariable

section TwoVariables

variable [forall x, IsTopologicalAddGroup (E₃ x)] [forall x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : forall x, (E₁ (b x) ->L[𝕜] E₂ (b x) ->L[𝕜] E₃ (b x))} {w : forall x, E₂ (b x)}

/--
lemma `ContinuousWithinAt.clm_bundle_apply₂` / 引理 `ContinuousWithinAt.clm_bundle_apply₂`

English:
lemma ContinuousWithinAt.clm_bundle_apply₂
  proof: (hψ.clm_bundle_apply hv).clm_bundle_apply hw

中文:
引理 ContinuousWithinAt.clm_bundle_apply₂
  证明: (hψ.clm_bundle_apply hv).clm_bundle_apply hw
-/
lemma ContinuousWithinAt.clm_bundle_apply₂
    (hψ : ContinuousWithinAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) s x)
    (hv : ContinuousWithinAt (fun m => TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m => TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContinuousWithinAt (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s x :=
  (hψ.clm_bundle_apply hv).clm_bundle_apply hw

/--
lemma `ContinuousAt.clm_bundle_apply₂` / 引理 `ContinuousAt.clm_bundle_apply₂`

English:
lemma ContinuousAt.clm_bundle_apply₂
  proof: (hψ.clm_bundle_apply hv).clm_bundle_apply hw

中文:
引理 ContinuousAt.clm_bundle_apply₂
  证明: (hψ.clm_bundle_apply hv).clm_bundle_apply hw
-/
lemma ContinuousAt.clm_bundle_apply₂
    (hψ : ContinuousAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : ContinuousAt (fun m => TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContinuousAt (fun m => TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContinuousAt (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  (hψ.clm_bundle_apply hv).clm_bundle_apply hw

/--
lemma `ContinuousOn.clm_bundle_apply₂` / 引理 `ContinuousOn.clm_bundle_apply₂`

English:
lemma ContinuousOn.clm_bundle_apply₂
  proof: fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

中文:
引理 ContinuousOn.clm_bundle_apply₂
  证明: fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)
-/
lemma ContinuousOn.clm_bundle_apply₂
    (hψ : ContinuousOn
      (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)) s)
    (hv : ContinuousOn (fun m => TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContinuousOn (fun m => TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContinuousOn (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s :=
  fun x hx => (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/--
lemma `Continuous.clm_bundle_apply₂` / 引理 `Continuous.clm_bundle_apply₂`

English:
lemma Continuous.clm_bundle_apply₂
  proof: by
  simp only [← continuousOn_univ] at hψ hv hw ⊢
  exact hψ.clm_bundle_apply₂ hv hw

中文:
引理 连续.clm_bundle_apply₂
  证明: by
  simp only [← continuousOn_univ] at hψ hv hw ⊢
  exact hψ.clm_bundle_apply₂ hv hw
-/
lemma Continuous.clm_bundle_apply₂
    (hψ : Continuous (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
      (E := fun (x : B) => (E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : Continuous (fun m => TotalSpace.mk' F₁ (b m) (v m)))
    (hw : Continuous (fun m => TotalSpace.mk' F₂ (b m) (w m))) :
    Continuous (fun m => TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) := by
  simp only [← continuousOn_univ] at hψ hv hw ⊢
  exact hψ.clm_bundle_apply₂ hv hw

/--
theorem `inCoordinates_apply_eq₂` / 定理 `inCoordinates_apply_eq₂`

English:
theorem inCoordinates_apply_eq₂
  proof: by
  rw [inCoordinates_eq h₁x (by simp [h₂x]; rw [h₃x])]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply, h₂x]

中文:
定理 inCoordinates_apply_eq₂
  证明: by
  rw [inCoordinates_eq h₁x (by simp [h₂x]; rw [h₃x])]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply, h₂x]

Depends on / 依赖: Trivialization, Trivialization.continuousLinearMap_apply, continuousLinearMap_apply, hom_trivializationAt, inCoordinates_eq
-/
theorem inCoordinates_apply_eq₂
    {x₀ x : B} {ϕ : E₁ x ->L[𝕜] E₂ x ->L[𝕜] E₃ x} {v : F₁} {w : F₂}
    (h₁x : x in (trivializationAt F₁ E₁ x₀).baseSet)
    (h₂x : x in (trivializationAt F₂ E₂ x₀).baseSet)
    (h₃x : x in (trivializationAt F₃ E₃ x₀).baseSet) :
    inCoordinates F₁ E₁ (F₂ ->L[𝕜] F₃) (fun x => E₂ x ->L[𝕜] E₃ x) x₀ x x₀ x ϕ v w =
    (trivializationAt F₃ E₃ x₀).linearMapAt 𝕜 x
      (ϕ ((trivializationAt F₁ E₁ x₀).symm x v) ((trivializationAt F₂ E₂ x₀).symm x w)) := by
  rw [inCoordinates_eq h₁x (by simp [h₂x]; rw [h₃x])]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply, h₂x]

end TwoVariables

end
