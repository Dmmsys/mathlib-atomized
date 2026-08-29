/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Injective seminorm on the tensor of a finite family of normed spaces.

The purpose of this file is to develop the theory of the injective tensor norm.

A first formalization turned out not to capture the common mathematical definition and is
now deprecated. See

https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/injectiveSeminorm/with/568798633

## Main definitions

* `PiTensorProduct.toDualContinuousMultilinearMap`: The `𝕜`-linear map from
  `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending `x` to the map
  `f ↦ f x`.

## TODO

* Reimplement `injectiveSeminorm`.

-/

@[expose] public section

-- These explicit universe variables are required by `injectiveSeminorm`, which
-- has been marked as deprecated on 2026-06-10. TBD: delete the variables after the
-- deprecated material has been removed or re-implemented.
universe uι u𝕜 uE

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι -> Type uE} [forall i, SeminormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

namespace PiTensorProduct

section seminorm

variable (F) in
/-- The linear map from `⨂[𝕜] i, Eᵢ` to `ContinuousMultilinearMap 𝕜 E F →L[𝕜] F` sending
`x` in `⨂[𝕜] i, Eᵢ` to the map `f ↦ f.lift x`. -/
@[simps!]
/--
Definition of `toDualContinuousMultilinearMap` / `toDualContinuousMultilinearMap` 的定义

English:
definition toDualContinuousMultilinearMap
  signature: :
  body: LinearMap.mkContinuous
    (lift.toLinearMap.flip x ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear) ‖x‖
    (fun f => by simpa [mul_comm] using norm_eval_le_projectiveSeminorm f x)
  map_add' x y := by
    ext; simp
  map_smul' a x := by
    ext; simp

中文:
定义 toDualContinuousMultilinearMap
  签名: :
  定义体: LinearMap.mkContinuous
    (lift.toLinearMap.flip x ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear) ‖x‖
    (fun f => by simpa [mul_comm] using norm_eval_le_projectiveSeminorm f x)
  map_add' x y := by
    ext; simp
  map_smul' a x := by
    ext; simp

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, mkContinuous
-/
noncomputable def toDualContinuousMultilinearMap :
    (⨂[𝕜] i, E i) ->ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F ->L[𝕜] F where
  toFun x := LinearMap.mkContinuous
    (lift.toLinearMap.flip x ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear) ‖x‖
    (fun f => by simpa [mul_comm] using norm_eval_le_projectiveSeminorm f x)
  map_add' x y := by
    ext; simp
  map_smul' a x := by
    ext; simp

/--
theorem `toDualContinuousMultilinearMap_le_projectiveSeminorm` / 定理 `toDualContinuousMultilinearMap_le_projectiveSeminorm`

English:
theorem toDualContinuousMultilinearMap_le_projectiveSeminorm
  given: (x : ⨂[𝕜] i, E i)
  proof: by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (by positivity)

中文:
定理 toDualContinuousMultilinearMap_le_projectiveSeminorm
  条件: (x : ⨂[𝕜] i, E i)
  证明: by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (by positivity)

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, LinearMap.mkContinuous_norm_le, coe_mk, mkContinuous_norm_le, toDualContinuousMultilinearMap
-/
theorem toDualContinuousMultilinearMap_le_projectiveSeminorm (x : ⨂[𝕜] i, E i) :
    ‖toDualContinuousMultilinearMap F x‖ <= ‖x‖ := by
  simp only [toDualContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  apply LinearMap.mkContinuous_norm_le _ (by positivity)

/-- The injective seminorm on `⨂[𝕜] i, Eᵢ`. Morally, it sends `x` in `⨂[𝕜] i, Eᵢ` to the
`sup` of the operator norms of the `PiTensorProduct.toDualContinuousMultilinearMap F x`, for all
normed vector spaces `F`. In fact, we only take in the same universe as `⨂[𝕜] i, Eᵢ`, and then
prove in `PiTensorProduct.norm_eval_le_injectiveSeminorm` that this gives the same result.
-/
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
noncomputable irreducible_def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | exists (G : Type (max uι u𝕜 uE)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G ->L[𝕜] G))
  (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}

@[deprecated "no replacement" (since := "2026-06-10")]
/--
lemma `dualSeminorms_bounded` / 引理 `dualSeminorms_bounded`

English:
lemma dualSeminorms_bounded
  statement: BddAbove {p | exists (G : Type (max uι u𝕜 uE))
  proof: by
  use projectiveSeminorm
  simp only [mem_upperBounds, Set.mem_ofPred_eq, forall_exists_index]
  intro p G _ _ hp x
  simpa [hp] using! toDualContinuousMultilinearMap_le_projectiveSeminorm _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm

中文:
引理 dualSeminorms_bounded
  结论: BddAbove {p | 存在 (G : 类型 (最大值 uι u𝕜 uE))
  证明: by
  use projectiveSeminorm
  simp only [mem_upperBounds, Set.mem_ofPred_eq, forall_exists_index]
  intro p G _ _ hp x
  simpa [hp] using! toDualContinuousMultilinearMap_le_projectiveSeminorm _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm

Depends on / 依赖: Set.mem_ofPred_eq, forall_exists_index, mem_ofPred_eq, mem_upperBounds, projectiveSeminorm, toDualContinuousMultilinearMap_le_projectiveSeminorm
-/
lemma dualSeminorms_bounded : BddAbove {p | exists (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G ->L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))} := by
  use projectiveSeminorm
  simp only [mem_upperBounds, Set.mem_ofPred_eq, forall_exists_index]
  intro p G _ _ hp x
  simpa [hp] using! toDualContinuousMultilinearMap_le_projectiveSeminorm _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/--
theorem `injectiveSeminorm_apply` / 定理 `injectiveSeminorm_apply`

English:
theorem injectiveSeminorm_apply
  given: (x : ⨂[𝕜] i, E i)
  proof: by
  simpa only [injectiveSeminorm, Set.coe_ofPred, Set.mem_ofPred_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

中文:
定理 injectiveSeminorm_apply
  条件: (x : ⨂[𝕜] i, E i)
  证明: by
  simpa only [injectiveSeminorm, Set.coe_ofPred, Set.mem_ofPred_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

Depends on / 依赖: Seminorm, Seminorm.sSup_apply, Set.coe_ofPred, Set.mem_ofPred_eq, coe_ofPred, dualSeminorms_bounded, injectiveSeminorm, mem_ofPred_eq, sSup_apply
-/
theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | exists (G : Type (max uι u𝕜 uE))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G ->L[𝕜] G))
    (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E))}, p.1 x := by
  simpa only [injectiveSeminorm, Set.coe_ofPred, Set.mem_ofPred_eq]
    using Seminorm.sSup_apply dualSeminorms_bounded

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] instSeminormedAddCommGroup in
@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/--
theorem `norm_eval_le_injectiveSeminorm` / 定理 `norm_eval_le_injectiveSeminorm`

English:
theorem norm_eval_le_injectiveSeminorm
  given: (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i)
  proof: by
    /- If `F` were in `Type (max uι u𝕜 uE)` (which is the type of `⨂[𝕜] i, E i`), then the
    property that we want to prove would hold by definition of `injectiveSeminorm`. This is
    not necessarily true, but we will show that there exists a normed vector space `G` in
    `Type (max uι u𝕜 uE)

中文:
定理 norm_eval_le_injectiveSeminorm
  条件: (f : 连续多重线性映射 𝕜 E F) (x : ⨂[𝕜] i, E i)
  证明: by
    /- If `F` were in `Type (max uι u𝕜 uE)` (which is the type of `⨂[𝕜] i, E i`), then the
    property that we want to prove would hold by definition of `injectiveSeminorm`. This is
    not necessarily true, but we will show that there exists a normed vector space `G` in
    `Type (max uι u𝕜 uE)
-/
theorem norm_eval_le_injectiveSeminorm (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ <= ‖f‖ * injectiveSeminorm x := by
    /- If `F` were in `Type (max uι u𝕜 uE)` (which is the type of `⨂[𝕜] i, E i`), then the
    property that we want to prove would hold by definition of `injectiveSeminorm`. This is
    not necessarily true, but we will show that there exists a normed vector space `G` in
    `Type (max uι u𝕜 uE)` and an injective isometry from `G` to `F` such that `f` factors
    through a continuous multilinear map `f'` from `E = Π i, E i` to `G`, to which we can apply
    the definition of `injectiveSeminorm`. The desired inequality for `f` then follows
    immediately.
    The idea is very simple: the multilinear map `f` corresponds by `PiTensorProduct.lift`
    to a linear map from `⨂[𝕜] i, E i` to `F`, say `l`. We want to take `G` to be the image of
    `l`, with the norm induced from that of `F`; to make sure that we are in the correct universe,
    it is actually more convenient to take `G` equal to the coimage of `l` (i.e. the quotient
    of `⨂[𝕜] i, E i` by the kernel of `l`), which is canonically isomorphic to its image by
    `LinearMap.quotKerEquivRange`. -/
  set G := (⨂[𝕜] i, E i) ⧸ LinearMap.ker (lift f.toMultilinearMap)
  set G' := LinearMap.range (lift f.toMultilinearMap)
  set e := LinearMap.quotKerEquivRange (lift f.toMultilinearMap)
  let := SeminormedAddCommGroup.induced G G' e
  let := NormedSpace.induced 𝕜 G G' e
  set f'₀ := lift.symm (e.symm.toLinearMap ∘ₗ LinearMap.rangeRestrict (lift f.toMultilinearMap))
  have hf'₀ : forall (x : Π (i : ι), E i), ‖f'₀ x‖ <= ‖f‖ * ∏ i, ‖x i‖ := fun x => by
    change ‖e (f'₀ x)‖ <= _
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, Submodule.coe_norm,
        LinearMap.codRestrict_apply, lift.tprod, ContinuousMultilinearMap.coe_coe, e, f'₀]
    exact f.le_opNorm x
  set f' := MultilinearMap.mkContinuous f'₀ ‖f‖ hf'₀
  have hnorm : ‖f'‖ <= ‖f‖ := (f'.opNorm_le_iff (norm_nonneg f)).mpr hf'₀
  have heq : e (lift f'.toMultilinearMap x) = lift f.toMultilinearMap x := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod =>
      simp only [lift_symm, map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, SetLike.val_smul,
      LinearMap.codRestrict_apply, f', f'₀]
    | add _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  suffices h : ‖lift f'.toMultilinearMap x‖ <= ‖f'‖ * injectiveSeminorm x by
    change ‖(e (lift f'.toMultilinearMap x)).1‖ <= _ at h
    rw [heq] at h
    exact h.trans (by gcongr)
  have hle : Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G ->L[𝕜] G))
      (toDualContinuousMultilinearMap G (𝕜 := 𝕜) (E := E)) <= injectiveSeminorm := by
    simp only [injectiveSeminorm]
    refine le_csSup dualSeminorms_bounded ?_
    rw [Set.mem_ofPred]
    existsi G, inferInstance, inferInstance
    rfl
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hle x) (norm_nonneg f'))
  simp only [Seminorm.comp_apply, coe_normSeminorm, ← toDualContinuousMultilinearMap_apply_apply]
  rw [mul_comm]
  exact ContinuousLinearMap.le_opNorm _ _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/--
theorem `injectiveSeminorm_le_projectiveSeminorm` / 定理 `injectiveSeminorm_le_projectiveSeminorm`

English:
theorem injectiveSeminorm_le_projectiveSeminorm
  proof: by
  rw [injectiveSeminorm]
  refine csSup_le ?_ ?_
  · existsi 0
    simp only [Set.mem_ofPred_eq]
    existsi PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    rw [Subsingleton.elim (toDualContinuousMultilinearMap PUnit.{(m

中文:
定理 injectiveSeminorm_le_projectiveSeminorm
  证明: by
  rw [injectiveSeminorm]
  refine csSup_le ?_ ?_
  · existsi 0
    simp only [Set.mem_ofPred_eq]
    existsi PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    rw [Subsingleton.elim (toDualContinuousMultilinearMap PUnit.{(m

Depends on / 依赖: Seminorm, Seminorm.comp_apply, Seminorm.zero_apply, Set.mem_ofPred_eq, Subsingleton, Subsingleton.elim, coe_normSeminorm, comp_apply, csSup_le, existsi, injectiveSeminorm, mem_ofPred_eq, norm_zero, projectiveSeminorm, toDualContinuousMultilinearMap, zero_apply
-/
theorem injectiveSeminorm_le_projectiveSeminorm :
    injectiveSeminorm (𝕜 := 𝕜) (E := E) <= projectiveSeminorm := by
  rw [injectiveSeminorm]
  refine csSup_le ?_ ?_
  · existsi 0
    simp only [Set.mem_ofPred_eq]
    existsi PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    rw [Subsingleton.elim (toDualContinuousMultilinearMap PUnit.{(max (max uE uι) u𝕜) + 1} x) 0]; rw [norm_zero]
  · intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    obtain ⟨G, _, _, h⟩ := hp
    rw [h]; intro x; simp only [Seminorm.comp_apply, coe_normSeminorm]
    exact toDualContinuousMultilinearMap_le_projectiveSeminorm _

@[deprecated
  "`injectiveSeminorm` is deprecated in favor of the extensionally equal `projectiveSeminorm`"
  (since := "2026-06-10")]
/--
theorem `injectiveSeminorm_tprod_le` / 定理 `injectiveSeminorm_tprod_le`

English:
theorem injectiveSeminorm_tprod_le
  given: (m : Π (i : ι), E i)
  proof: le_trans (injectiveSeminorm_le_projectiveSeminorm _) (projectiveSeminorm_tprod_le m)

中文:
定理 injectiveSeminorm_tprod_le
  条件: (m : Π (i : ι), E i)
  证明: le_trans (injectiveSeminorm_le_projectiveSeminorm _) (projectiveSeminorm_tprod_le m)

Depends on / 依赖: injectiveSeminorm_le_projectiveSeminorm, le_trans, projectiveSeminorm_tprod_le
-/
theorem injectiveSeminorm_tprod_le (m : Π (i : ι), E i) :
    injectiveSeminorm (⨂ₜ[𝕜] i, m i) <= ∏ i, ‖m i‖ :=
  le_trans (injectiveSeminorm_le_projectiveSeminorm _) (projectiveSeminorm_tprod_le m)

end seminorm

end PiTensorProduct
