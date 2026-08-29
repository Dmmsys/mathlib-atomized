/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, David Gross, Davood Haji Taghi Tehrani
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Projective seminorm on the tensor of a finite family of normed spaces.

Let `𝕜` be a normed field and `E` be a family of normed `𝕜`-vector spaces `Eᵢ`,
indexed by a finite type `ι`. We define a seminorm on `⨂[𝕜] i, Eᵢ`, which we call the
"projective seminorm". For `x` an element of `⨂[𝕜] i, Eᵢ`, its projective seminorm is the
infimum over all expressions of `x` as `∑ j, ⨂ₜ[𝕜] mⱼ i` (with the `mⱼ` ∈ `Π i, Eᵢ`)
of `∑ j, Π i, ‖mⱼ i‖`.

In particular, every norm `‖.‖` on `⨂[𝕜] i, Eᵢ` satisfying `‖⨂ₜ[𝕜] i, m i‖ ≤ Π i, ‖m i‖`
for every `m` in `Π i, Eᵢ` is bounded above by the projective seminorm.

## Main definitions

* `PiTensorProduct.projectiveSeminorm`: The projective seminorm on `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.liftEquiv`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as a continuous linear equivalence.
* `PiTensorProduct.liftIsometry`: The bijection between `ContinuousMultilinearMap 𝕜 E F`
  and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`, as an isometric linear equivalence.
* `PiTensorProduct.tprodL`: The canonical continuous multilinear map from `E = Πᵢ Eᵢ`
  to `⨂[𝕜] i, Eᵢ`.
* `PiTensorProduct.mapL`: The continuous linear map from `⨂[𝕜] i, Eᵢ` to `⨂[𝕜] i, E'ᵢ`
  induced by a family of continuous linear maps `Eᵢ →L[𝕜] E'ᵢ`.
* `PiTensorProduct.mapLMultilinear`: The continuous multilinear map from
  `Πᵢ (Eᵢ →L[𝕜] E'ᵢ)` to `(⨂[𝕜] i, Eᵢ) →L[𝕜] (⨂[𝕜] i, E'ᵢ)` sending a family
  `f` to `PiTensorProduct.mapL f`.

## Main results

* `PiTensorProduct.norm_eval_le_projectiveSeminorm`: If `f` is a continuous multilinear map on
  `E = Π i, Eᵢ` and `x` is in `⨂[𝕜] i, Eᵢ`, then `‖f.lift x‖ ≤ projectiveSeminorm x * ‖f‖`.
* `PiTensorProduct.mapL_opNorm`: If `f` is a family of continuous linear maps
  `fᵢ : Eᵢ →L[𝕜] Fᵢ`, then `‖PiTensorProduct.mapL f‖ ≤ ∏ i, ‖fᵢ‖`.
* `PiTensorProduct.opNorm_mapLMultilinear_le` : If `F` is a normed vecteor space, then
  `‖mapLMultilinear 𝕜 E F‖ ≤ 1`.

## TODO
* If the base field is `ℝ` or `ℂ` (or more generally if the injection of `Eᵢ` into its bidual is
  an isometry for every `i`), then we have `projectiveSeminorm ⨂ₜ[𝕜] i, mᵢ = Π i, ‖mᵢ‖`.
* If all `Eᵢ` are separated and satisfy `SeparatingDual`, then the seminorm on
  `⨂[𝕜] i, Eᵢ` is a norm.
* Adapt the remaining functoriality constructions/properties from `PiTensorProduct`.

-/

@[expose] public section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable {E : ι -> Type*} [forall i, SeminormedAddCommGroup (E i)]

open scoped TensorProduct

namespace PiTensorProduct

section NormedField

variable [NormedField 𝕜]

/--
Definition of `projectiveSeminormAux` / `projectiveSeminormAux` 的定义

English:
definition projectiveSeminormAux
  signature: : FreeAddMonoid (𝕜 × Π i, E i) -> Real
  body: fun p => (p.toList.map (fun p => ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum

中文:
定义 projectiveSeminormAux
  签名: : FreeAddMonoid (𝕜 × Π i, E i) -> 实数
  定义体: fun p => (p.toList.map (fun p => ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum

Depends on / 依赖: p.toList.map, toList
-/
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) -> Real :=
  fun p => (p.toList.map (fun p => ‖p.1‖ * ∏ i, ‖p.2 i‖)).sum

/--
theorem `projectiveSeminormAux_nonneg` / 定理 `projectiveSeminormAux_nonneg`

English:
theorem projectiveSeminormAux_nonneg
  given: (p : FreeAddMonoid (𝕜 × Π i, E i))
  proof: by
  refine List.sum_nonneg fun a => ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x m _ h
  simpa [← h] using by positivity

中文:
定理 projectiveSeminormAux_nonneg
  条件: (p : FreeAddMonoid (𝕜 × Π i, E i))
  证明: by
  refine List.sum_nonneg fun a => ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x m _ h
  simpa [← h] using by positivity

Depends on / 依赖: List.mem_map, List.sum_nonneg, Prod.exists, and_imp, forall_exists_index, mem_map, sum_nonneg
-/
theorem projectiveSeminormAux_nonneg (p : FreeAddMonoid (𝕜 × Π i, E i)) :
    0 <= projectiveSeminormAux p := by
  refine List.sum_nonneg fun a => ?_
  simp only [List.mem_map, Prod.exists, forall_exists_index, and_imp]
  intro x m _ h
  simpa [← h] using by positivity

/--
theorem `projectiveSeminormAux_add_le` / 定理 `projectiveSeminormAux_add_le`

English:
theorem projectiveSeminormAux_add_le
  given: (p q : FreeAddMonoid (𝕜 × Π i, E i))
  proof: by
  simp [projectiveSeminormAux]

中文:
定理 projectiveSeminormAux_add_le
  条件: (p q : FreeAddMonoid (𝕜 × Π i, E i))
  证明: by
  simp [projectiveSeminormAux]

Depends on / 依赖: projectiveSeminormAux
-/
theorem projectiveSeminormAux_add_le (p q : FreeAddMonoid (𝕜 × Π i, E i)) :
    projectiveSeminormAux (p + q) <= projectiveSeminormAux p + projectiveSeminormAux q := by
  simp [projectiveSeminormAux]

/--
theorem `projectiveSeminormAux_smul` / 定理 `projectiveSeminormAux_smul`

English:
theorem projectiveSeminormAux_smul
  given: (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜)
  proof: by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

中文:
定理 projectiveSeminormAux_smul
  条件: (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜)
  证明: by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

Depends on / 依赖: Function, Function.comp_def, List.sum_map_mul_left, comp_def, mul_assoc, projectiveSeminormAux, sum_map_mul_left
-/
theorem projectiveSeminormAux_smul (p : FreeAddMonoid (𝕜 × Π i, E i)) (a : 𝕜) :
    projectiveSeminormAux (p.map (fun (y : 𝕜 × Π i, E i) => (a * y.1, y.2))) =
    ‖a‖ * projectiveSeminormAux p := by
  simp [projectiveSeminormAux, Function.comp_def, mul_assoc, List.sum_map_mul_left]

variable [forall i, NormedSpace 𝕜 (E i)]

/--
theorem `bddBelow_projectiveSemiNormAux` / 定理 `bddBelow_projectiveSemiNormAux`

English:
theorem bddBelow_projectiveSemiNormAux
  given: (x : ⨂[𝕜] i, E i)
  proof: ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩

中文:
定理 bddBelow_projectiveSemiNormAux
  条件: (x : ⨂[𝕜] i, E i)
  证明: ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩

Depends on / 依赖: mem_lowerBounds, projectiveSeminormAux_nonneg
-/
theorem bddBelow_projectiveSemiNormAux (x : ⨂[𝕜] i, E i) :
    BddBelow (Set.range (fun (p : lifts x) => projectiveSeminormAux p.1)) :=
  ⟨0, by simp [mem_lowerBounds, projectiveSeminormAux_nonneg]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Norm (⨂[𝕜] i, E i)
  body: ⟨fun x => iInf (fun (p : lifts x) => projectiveSeminormAux p.val)⟩

中文:
实例 :
  签名: Norm (⨂[𝕜] i, E i)
  定义体: ⟨fun x => iInf (fun (p : lifts x) => projectiveSeminormAux p.val)⟩

Depends on / 依赖: p.val, projectiveSeminormAux
-/
noncomputable instance : Norm (⨂[𝕜] i, E i) :=
  ⟨fun x => iInf (fun (p : lifts x) => projectiveSeminormAux p.val)⟩

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (x : ⨂[𝕜] i, E i)
  proof: rfl

@[deprecated (since := "2026-06-10")] alias projectiveSeminormFun := norm

中文:
定理 norm_def
  条件: (x : ⨂[𝕜] i, E i)
  证明: rfl

@[deprecated (since := "2026-06-10")] alias projectiveSeminormFun := norm
-/
theorem norm_def (x : ⨂[𝕜] i, E i) :
    ‖x‖ = iInf (fun (p : lifts x) => projectiveSeminormAux p.val) := rfl

@[deprecated (since := "2026-06-10")] alias projectiveSeminormFun := norm

/--
theorem `projectiveSeminorm_zero` / 定理 `projectiveSeminorm_zero`

English:
theorem projectiveSeminorm_zero
  statement: ‖(0 : ⨂[𝕜] i, E i)‖ = 0
  proof: le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p => projectiveSeminormAux_nonneg p.val))

中文:
定理 projectiveSeminorm_zero
  结论: ‖(0 : ⨂[𝕜] i, E i)‖ = 0
  证明: le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p => projectiveSeminormAux_nonneg p.val))

Depends on / 依赖: bddBelow_projectiveSemiNormAux, ciInf_le, le_antisymm, le_ciInf, lifts_zero, p.val, projectiveSeminormAux_nonneg
-/
theorem projectiveSeminorm_zero : ‖(0 : ⨂[𝕜] i, E i)‖ = 0 :=
  le_antisymm (ciInf_le (bddBelow_projectiveSemiNormAux _) ⟨0, lifts_zero⟩)
    (le_ciInf (fun p => projectiveSeminormAux_nonneg p.val))

/--
theorem `projectiveSeminorm_add_le` / 定理 `projectiveSeminorm_add_le`

English:
theorem projectiveSeminorm_add_le
  given: (x y : ⨂[𝕜] i, E i)
  statement: ‖x + y‖ <= ‖x‖ + ‖y‖
  proof: le_ciInf_add_ciInf (fun p q => ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))

中文:
定理 projectiveSeminorm_add_le
  条件: (x y : ⨂[𝕜] i, E i)
  结论: ‖x + y‖ <= ‖x‖ + ‖y‖
  证明: le_ciInf_add_ciInf (fun p q => ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))

Depends on / 依赖: bddBelow_projectiveSemiNormAux, ciInf_le_of_le, le_ciInf_add_ciInf, lifts_add, projectiveSeminormAux_add_le
-/
theorem projectiveSeminorm_add_le (x y : ⨂[𝕜] i, E i) : ‖x + y‖ <= ‖x‖ + ‖y‖ :=
  le_ciInf_add_ciInf (fun p q => ciInf_le_of_le (bddBelow_projectiveSemiNormAux _)
    ⟨p.1 + q.1, lifts_add p.2 q.2⟩ (projectiveSeminormAux_add_le p.1 q.1))

/--
theorem `projectiveSeminorm_smul_le` / 定理 `projectiveSeminorm_smul_le`

English:
theorem projectiveSeminorm_smul_le
  given: (a : 𝕜) (x : ⨂[𝕜] i, E i)
  statement: ‖a • x‖ <= ‖a‖ * ‖x‖
  proof: by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p => ?_
  simpa [projectiveSeminormAux_smul] using
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

中文:
定理 projectiveSeminorm_smul_le
  条件: (a : 𝕜) (x : ⨂[𝕜] i, E i)
  结论: ‖a • x‖ <= ‖a‖ * ‖x‖
  证明: by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p => ?_
  simpa [projectiveSeminormAux_smul] using
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

Depends on / 依赖: Real.mul_iInf_of_nonneg, bddBelow_projectiveSemiNormAux, ciInf_le_of_le, le_ciInf, le_refl, lifts_smul, mul_iInf_of_nonneg, norm_def, norm_nonneg, projectiveSeminormAux_smul
-/
theorem projectiveSeminorm_smul_le (a : 𝕜) (x : ⨂[𝕜] i, E i) : ‖a • x‖ <= ‖a‖ * ‖x‖ := by
  simp only [norm_def, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun p => ?_
  simpa [projectiveSeminormAux_smul] using
    ciInf_le_of_le (bddBelow_projectiveSemiNormAux _) ⟨_, lifts_smul p.2 a⟩ (le_refl _)

/--
Definition of `projectiveSeminorm` / `projectiveSeminorm` 的定义

English:
definition projectiveSeminorm
  signature: : Seminorm 𝕜 (⨂[𝕜] i, E i)
  body: .ofSMulLE
    norm projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le

中文:
定义 projectiveSeminorm
  签名: : Seminorm 𝕜 (⨂[𝕜] i, E i)
  定义体: .ofSMulLE
    norm projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le

Depends on / 依赖: ofSMulLE
-/
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) := .ofSMulLE
    norm projectiveSeminorm_zero projectiveSeminorm_add_le projectiveSeminorm_smul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeminormedAddCommGroup (⨂[𝕜] i, E i)
  body: fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

中文:
实例 :
  签名: SeminormedAddCommGroup (⨂[𝕜] i, E i)
  定义体: fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, fast_instance, projectiveSeminorm, projectiveSeminorm.toAddGroupSeminorm, toAddGroupSeminorm, toSeminormedAddCommGroup
-/
noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  fast_instance% AddGroupSeminorm.toSeminormedAddCommGroup projectiveSeminorm.toAddGroupSeminorm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedSpace 𝕜 (⨂[𝕜] i, E i)
  body: ⟨projectiveSeminorm_smul_le⟩

@[deprecated norm_def (since := "2026-06-10")]

中文:
实例 :
  签名: NormedSpace 𝕜 (⨂[𝕜] i, E i)
  定义体: ⟨projectiveSeminorm_smul_le⟩

@[deprecated norm_def (since := "2026-06-10")]

Depends on / 依赖: projectiveSeminorm_smul_le
-/
noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) := ⟨projectiveSeminorm_smul_le⟩

@[deprecated norm_def (since := "2026-06-10")]
/--
theorem `projectiveSeminorm_apply` / 定理 `projectiveSeminorm_apply`

English:
theorem projectiveSeminorm_apply
  given: (x : ⨂[𝕜] i, E i)
  proof: rfl

中文:
定理 projectiveSeminorm_apply
  条件: (x : ⨂[𝕜] i, E i)
  证明: rfl
-/
theorem projectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    projectiveSeminorm x = iInf (fun (p : lifts x) => projectiveSeminormAux p.1) := rfl

/--
theorem `projectiveSeminorm_tprod_le` / 定理 `projectiveSeminorm_tprod_le`

English:
theorem projectiveSeminorm_tprod_le
  given: (m : Π i, E i)
  proof: by
   have hle := ciInf_le (bddBelow_projectiveSemiNormAux (⨂ₜ[𝕜] i, m i))
    ⟨FreeAddMonoid.of (1, m), by simp [mem_lifts_iff]⟩
   grw [norm_def, hle]
   simp [projectiveSeminormAux]

中文:
定理 projectiveSeminorm_tprod_le
  条件: (m : Π i, E i)
  证明: by
   have hle := ciInf_le (bddBelow_projectiveSemiNormAux (⨂ₜ[𝕜] i, m i))
    ⟨FreeAddMonoid.of (1, m), by simp [mem_lifts_iff]⟩
   grw [norm_def, hle]
   simp [projectiveSeminormAux]

Depends on / 依赖: FreeAddMonoid, FreeAddMonoid.of, bddBelow_projectiveSemiNormAux, ciInf_le, mem_lifts_iff, norm_def, projectiveSeminormAux
-/
theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    ‖(⨂ₜ[𝕜] i, m i)‖ <= ∏ i, ‖m i‖ := by
   have hle := ciInf_le (bddBelow_projectiveSemiNormAux (⨂ₜ[𝕜] i, m i))
    ⟨FreeAddMonoid.of (1, m), by simp [mem_lifts_iff]⟩
   grw [norm_def, hle]
   simp [projectiveSeminormAux]

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [forall i, NormedSpace 𝕜 (E i)]

/--
theorem `norm_eval_le_projectiveSeminorm` / 定理 `norm_eval_le_projectiveSeminorm`

English:
theorem norm_eval_le_projectiveSeminorm
  statement: {G : Type*} [SeminormedAddCommGroup G]
  proof: by
  rw [norm_def]; rw [mul_comm]; rw [Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ => ?_
  rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
 

中文:
定理 norm_eval_le_projectiveSeminorm
  结论: {G : 类型} [SeminormedAddCommGroup G]
  证明: by
  rw [norm_def]; rw [mul_comm]; rw [Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ => ?_
  rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
 

Depends on / 依赖: List.Forall, List.smul_sum, List.sum_map_hom, Multiset, Multiset.sum_coe, Real.iInf_mul_of_nonneg, f.le_opNorm, iInf_mul_of_nonneg, le_ciInf, le_opNorm, mem_lifts_iff, mul_assoc, mul_comm, mul_le_mul_of_nonneg_left, norm_def, norm_multiset_sum_le, norm_nonneg, norm_smul, projectiveSeminormAux, smul_eq_mul
-/
theorem norm_eval_le_projectiveSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ <= ‖f‖ * ‖x‖ := by
  rw [norm_def]; rw [mul_comm]; rw [Real.iInf_mul_of_nonneg (norm_nonneg _)]
  refine le_ciInf fun ⟨p, hp⟩ => ?_
  rw! [← ((mem_lifts_iff x p).mp hp), ← List.sum_map_hom, ← Multiset.sum_coe]
  grw [norm_multiset_sum_le]
  simp only [mul_comm, ← smul_eq_mul, List.smul_sum, projectiveSeminormAux]
  refine List.Forall₂.sum_le_sum ?_
  simpa [norm_smul, ← mul_assoc, mul_comm ‖f‖ _] using
    fun a m _ => mul_le_mul_of_nonneg_left (f.le_opNorm _) (norm_nonneg _)

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F)

/-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`.
-/
@[simps]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F where
  body: LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x =>
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x =>
    ContinuousLinearMap.le_opNorm_of_le _ (projectiveS

中文:
定义 liftEquiv
  签名: : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F where
  定义体: LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x =>
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x =>
    ContinuousLinearMap.le_opNorm_of_le _ (projectiveS

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, f.toMultilinearMap, mkContinuous, toMultilinearMap
-/
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖ fun x =>
    norm_eval_le_projectiveSeminorm f x
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ fun x =>
    ContinuousLinearMap.le_opNorm_of_le _ (projectiveSeminorm_tprod_le x)
  left_inv f := by ext; simp
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    ext; simp

/--
Definition of `liftIsometry` / `liftIsometry` 的定义

English:
definition liftIsometry
  signature: : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F
  body: LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 E F)
  (fun f => LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
  (fun f => by
      rw [liftEquiv_symm_apply]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

中文:
定义 liftIsometry
  签名: : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F
  定义体: LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 E F)
  (fun f => LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
  (fun f => by
      rw [liftEquiv_symm_apply]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ofBounds, LinearMap, LinearMap.mkContinuous_norm_le, MultilinearMap, MultilinearMap.mkContinuous_norm_le, liftEquiv, liftEquiv_symm_apply, mkContinuous_norm_le, norm_eval_le_projectiveSeminorm, norm_nonneg, ofBounds
-/
noncomputable def liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) ->L[𝕜] F :=
  LinearIsometryEquiv.ofBounds (liftEquiv 𝕜 E F)
  (fun f => LinearMap.mkContinuous_norm_le _ (norm_nonneg f) (norm_eval_le_projectiveSeminorm f))
  (fun f => by
      rw [liftEquiv_symm_apply]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 E F}

@[simp]
/--
theorem `liftIsometry_apply_apply` / 定理 `liftIsometry_apply_apply`

English:
theorem liftIsometry_apply_apply
  given: (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i)
  proof: by
  simp [LinearIsometryEquiv.ofBounds, liftIsometry]

中文:
定理 liftIsometry_apply_apply
  条件: (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i)
  证明: by
  simp [LinearIsometryEquiv.ofBounds, liftIsometry]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ofBounds, liftIsometry, ofBounds
-/
theorem liftIsometry_apply_apply (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    liftIsometry 𝕜 E F f x = lift f.toMultilinearMap x := by
  simp [LinearIsometryEquiv.ofBounds, liftIsometry]

variable (𝕜) in
/-- The canonical continuous multilinear map from `E = Πᵢ Eᵢ` to `⨂[𝕜] i, Eᵢ`. -/
@[simps! toFun]
/--
Definition of `tprodL` / `tprodL` 的定义

English:
definition tprodL
  signature: : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i)
  body: (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]

中文:
定义 tprodL
  签名: : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i)
  定义体: (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, liftIsometry
-/
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  (liftIsometry 𝕜 E _).symm (ContinuousLinearMap.id 𝕜 _)

@[simp]
/--
theorem `tprodL_coe` / 定理 `tprodL_coe`

English:
theorem tprodL_coe
  statement: (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E)
  proof: by
  ext; simp

@[simp]

中文:
定理 tprodL_coe
  结论: (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E)
  证明: by
  ext; simp

@[simp]
-/
theorem tprodL_coe : (tprodL 𝕜).toMultilinearMap = tprod 𝕜 (s := E) := by
  ext; simp

@[simp]
/--
theorem `liftIsometry_symm_apply` / 定理 `liftIsometry_symm_apply`

English:
theorem liftIsometry_symm_apply
  given: (l : (⨂[𝕜] i, E i) ->L[𝕜] F)
  proof: by
  rfl

@[simp]

中文:
定理 liftIsometry_symm_apply
  条件: (l : (⨂[𝕜] i, E i) ->L[𝕜] F)
  证明: by
  rfl

@[simp]
-/
theorem liftIsometry_symm_apply (l : (⨂[𝕜] i, E i) ->L[𝕜] F) :
    (liftIsometry 𝕜 E F).symm l = l.compContinuousMultilinearMap (tprodL 𝕜) := by
  rfl

@[simp]
/--
theorem `liftIsometry_tprodL` / 定理 `liftIsometry_tprodL`

English:
theorem liftIsometry_tprodL
  proof: by
  ext; simp

中文:
定理 liftIsometry_tprodL
  证明: by
  ext; simp
-/
theorem liftIsometry_tprodL :
    liftIsometry 𝕜 E _ (tprodL 𝕜) = ContinuousLinearMap.id 𝕜 (⨂[𝕜] i, E i) := by
  ext; simp

section map

variable {E' E'' : ι -> Type*}
variable [forall i, SeminormedAddCommGroup (E' i)] [forall i, NormedSpace 𝕜 (E' i)]
variable [forall i, SeminormedAddCommGroup (E'' i)] [forall i, NormedSpace 𝕜 (E'' i)]
variable (g : Π i, E' i ->L[𝕜] E'' i) (f : Π i, E i ->L[𝕜] E' i)

/--
Definition of `mapL` / `mapL` 的定义

English:
definition mapL
  signature: : (⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E' i
  body: liftIsometry 𝕜 E _ (tprodL 𝕜).compContinuousLinearMap f

@[simp]

中文:
定义 mapL
  签名: : (⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E' i
  定义体: liftIsometry 𝕜 E _ (tprodL 𝕜).compContinuousLinearMap f

@[simp]

Depends on / 依赖: compContinuousLinearMap, liftIsometry, tprodL
-/
noncomputable def mapL : (⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E' i :=
liftIsometry 𝕜 E _ (tprodL 𝕜).compContinuousLinearMap f

@[simp]
/--
theorem `mapL_coe` / 定理 `mapL_coe`

English:
theorem mapL_coe
  statement: (mapL f).toLinearMap = map (fun i => (f i).toLinearMap)
  proof: by
  ext; simp [mapL]

@[simp]

中文:
定理 mapL_coe
  结论: (mapL f).toLinearMap = map (fun i => (f i).toLinearMap)
  证明: by
  ext; simp [mapL]

@[simp]
-/
theorem mapL_coe : (mapL f).toLinearMap = map (fun i => (f i).toLinearMap) := by
  ext; simp [mapL]

@[simp]
/--
theorem `mapL_apply` / 定理 `mapL_apply`

English:
theorem mapL_apply
  given: (x : ⨂[𝕜] i, E i)
  statement: mapL f x = map (fun i => (f i).toLinearMap) x
  proof: by
  rfl

中文:
定理 mapL_apply
  条件: (x : ⨂[𝕜] i, E i)
  结论: mapL f x = map (fun i => (f i).toLinearMap) x
  证明: by
  rfl
-/
theorem mapL_apply (x : ⨂[𝕜] i, E i) : mapL f x = map (fun i => (f i).toLinearMap) x := by
  rfl

/-- Given submodules `pᵢ ⊆ Eᵢ`, this is the natural map: `⨂[𝕜] i, pᵢ → ⨂[𝕜] i, Eᵢ`.
This is the continuous version of `PiTensorProduct.mapIncl`. -/
@[simp]
/--
Definition of `mapLIncl` / `mapLIncl` 的定义

English:
definition mapLIncl
  signature: (p : Π i, Submodule 𝕜 (E i))
  body: mapL fun (i : ι) => (p i).subtypeL

中文:
定义 mapLIncl
  签名: (p : Π i, Submodule 𝕜 (E i))
  定义体: mapL fun (i : ι) => (p i).subtypeL

Depends on / 依赖: subtypeL
-/
noncomputable def mapLIncl (p : Π i, Submodule 𝕜 (E i)) : (⨂[𝕜] i, p i) ->L[𝕜] ⨂[𝕜] i, E i :=
  mapL fun (i : ι) => (p i).subtypeL

/--
theorem `mapL_comp` / 定理 `mapL_comp`

English:
theorem mapL_comp
  statement: mapL (fun (i : ι) => g i ∘L f i) = mapL g ∘L mapL f
  proof: by
  apply ContinuousLinearMap.coe_injective
  ext; simp

中文:
定理 mapL_comp
  结论: mapL (fun (i : ι) => g i ∘L f i) = mapL g ∘L mapL f
  证明: by
  apply ContinuousLinearMap.coe_injective
  ext; simp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_injective, coe_injective
-/
theorem mapL_comp : mapL (fun (i : ι) => g i ∘L f i) = mapL g ∘L mapL f := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

/--
theorem `liftIsometry_comp_mapL` / 定理 `liftIsometry_comp_mapL`

English:
theorem liftIsometry_comp_mapL
  given: (h : ContinuousMultilinearMap 𝕜 E' F)
  proof: by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]

中文:
定理 liftIsometry_comp_mapL
  条件: (h : ContinuousMultilinearMap 𝕜 E' F)
  证明: by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_injective, coe_injective
-/
theorem liftIsometry_comp_mapL (h : ContinuousMultilinearMap 𝕜 E' F) :
    liftIsometry 𝕜 E' F h ∘L mapL f = liftIsometry 𝕜 E F (h.compContinuousLinearMap f) := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
/--
theorem `mapL_id` / 定理 `mapL_id`

English:
theorem mapL_id
  statement: mapL (fun i => ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _
  proof: by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]

中文:
定理 mapL_id
  结论: mapL (fun i => ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _
  证明: by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_injective, coe_injective
-/
theorem mapL_id : mapL (fun i => ContinuousLinearMap.id 𝕜 (E i)) = ContinuousLinearMap.id _ _ := by
  apply ContinuousLinearMap.coe_injective
  ext; simp

@[simp]
/--
theorem `mapL_one` / 定理 `mapL_one`

English:
theorem mapL_one
  statement: mapL (fun (i : ι) => (1 : E i ->L[𝕜] E i)) = 1
  proof: mapL_id

中文:
定理 mapL_one
  结论: mapL (fun (i : ι) => (1 : E i ->L[𝕜] E i)) = 1
  证明: mapL_id

Depends on / 依赖: mapL_id
-/
theorem mapL_one : mapL (fun (i : ι) => (1 : E i ->L[𝕜] E i)) = 1 :=
  mapL_id

/--
theorem `mapL_mul` / 定理 `mapL_mul`

English:
theorem mapL_mul
  given: (f₁ f₂ : Π i, E i ->L[𝕜] E i)
  proof: mapL_comp f₁ f₂

中文:
定理 mapL_mul
  条件: (f₁ f₂ : Π i, E i ->L[𝕜] E i)
  证明: mapL_comp f₁ f₂

Depends on / 依赖: mapL_comp
-/
theorem mapL_mul (f₁ f₂ : Π i, E i ->L[𝕜] E i) :
    mapL (fun i => f₁ i * f₂ i) = mapL f₁ * mapL f₂ :=
  mapL_comp f₁ f₂

/-- Upgrading `PiTensorProduct.mapL` to a `MonoidHom` when `E = E'`. -/
@[simps]
/--
Definition of `mapLMonoidHom` / `mapLMonoidHom` 的定义

English:
definition mapLMonoidHom
  signature: : (Π i, E i ->L[𝕜] E i) ->* ((⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E i) where
  body: mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]

中文:
定义 mapLMonoidHom
  签名: : (Π i, E i ->L[𝕜] E i) ->* ((⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E i) where
  定义体: mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]
-/
noncomputable def mapLMonoidHom : (Π i, E i ->L[𝕜] E i) ->* ((⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E i) where
  toFun := mapL
  map_one' := mapL_one
  map_mul' := mapL_mul

@[simp]
/--
theorem `mapL_pow` / 定理 `mapL_pow`

English:
theorem mapL_pow
  given: (f : Π i, E i ->L[𝕜] E i) (n : Nat)
  proof: MonoidHom.map_pow mapLMonoidHom f n

中文:
定理 mapL_pow
  条件: (f : Π i, E i ->L[𝕜] E i) (n : 自然数)
  证明: MonoidHom.map_pow mapLMonoidHom f n
-/
protected theorem mapL_pow (f : Π i, E i ->L[𝕜] E i) (n : Nat) :
    mapL (f ^ n) = mapL f ^ n := MonoidHom.map_pow mapLMonoidHom f n

-- We redeclare `ι` here, and later dependent arguments,
-- to avoid the `[Fintype ι]` assumption present throughout the rest of the file.
open Function in
/--
theorem `mapL_add_smul_aux` / 定理 `mapL_add_smul_aux`

English:
theorem mapL_add_smul_aux
  statement: {ι : Type*}
  proof: by
  grind

中文:
定理 mapL_add_smul_aux
  结论: {ι : 类型}
  证明: by
  grind
-/
private theorem mapL_add_smul_aux {ι : Type*}
    {E : ι -> Type*} [forall i, SeminormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
    {E' : ι -> Type*} [forall i, SeminormedAddCommGroup (E' i)] [forall i, NormedSpace 𝕜 (E' i)]
    (f : (i : ι) -> E i ->L[𝕜] E' i) [DecidableEq ι] (i : ι) (u : E i ->L[𝕜] E' i) :
    (fun j => (update f i u j).toLinearMap) =
      update (fun j => (f j).toLinearMap) i u.toLinearMap := by
  grind

open Function in
/--
theorem `mapL_add` / 定理 `mapL_add`

English:
theorem mapL_add
  given: [DecidableEq ι] (i : ι) (u v : E i ->L[𝕜] E' i)
  proof: by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]

中文:
定理 mapL_add
  条件: [DecidableEq ι] (i : ι) (u v : E i ->L[𝕜] E' i)
  证明: by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]
-/
protected theorem mapL_add [DecidableEq ι] (i : ι) (u v : E i ->L[𝕜] E' i) :
    mapL (update f i (u + v)) = mapL (update f i u) + mapL (update f i v) := by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_add]

open Function in
/--
theorem `mapL_smul` / 定理 `mapL_smul`

English:
theorem mapL_smul
  given: [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i ->L[𝕜] E' i)
  proof: by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]

中文:
定理 mapL_smul
  条件: [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i ->L[𝕜] E' i)
  证明: by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]
-/
protected theorem mapL_smul [DecidableEq ι] (i : ι) (c : 𝕜) (u : E i ->L[𝕜] E' i) :
    mapL (update f i (c • u)) = c • mapL (update f i u) := by
  ext
  simp [mapL_add_smul_aux, PiTensorProduct.map_update_smul]

/--
theorem `opNorm_mapL` / 定理 `opNorm_mapL`

English:
theorem opNorm_mapL
  statement: ‖mapL f‖ <= ∏ i, ‖f i‖
  proof: by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x => ?_
  apply le_trans (norm_eval_le_projectiveSeminorm ..) (mul_le_mul_of_nonneg_right _ (norm_nonneg x))
  refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m => ?_
  apply le_trans (projectiveSeminorm_

中文:
定理 opNorm_mapL
  结论: ‖mapL f‖ <= ∏ i, ‖f i‖
  证明: by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x => ?_
  apply le_trans (norm_eval_le_projectiveSeminorm ..) (mul_le_mul_of_nonneg_right _ (norm_nonneg x))
  refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m => ?_
  apply le_trans (projectiveSeminorm_

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_opNorm, ContinuousLinearMap.opNorm_le_iff, ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_iff, Finset, Finset.prod_mul_distrib, le_opNorm, le_trans, mul_le_mul_of_nonneg_right, norm_eval_le_projectiveSeminorm, norm_nonneg, opNorm_le_iff, prod_mul_distrib, projectiveSeminorm_tprod_le
-/
theorem opNorm_mapL : ‖mapL f‖ <= ∏ i, ‖f i‖ := by
  refine (ContinuousLinearMap.opNorm_le_iff (by positivity)).mpr fun x => ?_
  apply le_trans (norm_eval_le_projectiveSeminorm ..) (mul_le_mul_of_nonneg_right _ (norm_nonneg x))
  refine (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr fun m => ?_
  apply le_trans (projectiveSeminorm_tprod_le fun i => f i (m i))
  rw [← Finset.prod_mul_distrib]
  gcongr
  exact ContinuousLinearMap.le_opNorm _ _

variable (𝕜 E E')

/-- The tensor of a family of linear maps from `Eᵢ` to `E'ᵢ`, as a continuous multilinear map of
the family. -/
@[simps! toFun_apply]
/--
Definition of `mapLMultilinear` / `mapLMultilinear` 的定义

English:
definition mapLMultilinear
  signature: : ContinuousMultilinearMap 𝕜 (fun (i : ι) => E i ->L[𝕜] E' i)
  body: MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ => PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ => PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f => by rw [one_mul]; exact opNorm_mapL f)

中文:
定义 mapLMultilinear
  签名: : ContinuousMultilinearMap 𝕜 (fun (i : ι) => E i ->L[𝕜] E' i)
  定义体: MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ => PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ => PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f => by rw [one_mul]; exact opNorm_mapL f)

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuous, PiTensorProduct, PiTensorProduct.mapL_add, PiTensorProduct.mapL_smul, mapL_add, mapL_smul, map_update_add, map_update_smul, mkContinuous, one_mul, opNorm_mapL
-/
noncomputable def mapLMultilinear : ContinuousMultilinearMap 𝕜 (fun (i : ι) => E i ->L[𝕜] E' i)
    ((⨂[𝕜] i, E i) ->L[𝕜] ⨂[𝕜] i, E' i) :=
  MultilinearMap.mkContinuous
  { toFun := mapL
    map_update_smul' := fun _ _ _ _ => PiTensorProduct.mapL_smul _ _ _ _
    map_update_add' := fun _ _ _ _ => PiTensorProduct.mapL_add _ _ _ _ }
  1 (fun f => by rw [one_mul]; exact opNorm_mapL f)

variable {𝕜 E E'}

/--
theorem `opNorm_mapLMultilinear_le` / 定理 `opNorm_mapLMultilinear_le`

English:
theorem opNorm_mapLMultilinear_le
  statement: ‖mapLMultilinear 𝕜 E E'‖ <= 1
  proof: MultilinearMap.mkContinuous_norm_le _ zero_le_one _

中文:
定理 opNorm_mapLMultilinear_le
  结论: ‖mapLMultilinear 𝕜 E E'‖ <= 1
  证明: MultilinearMap.mkContinuous_norm_le _ zero_le_one _

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuous_norm_le, mkContinuous_norm_le, zero_le_one
-/
theorem opNorm_mapLMultilinear_le : ‖mapLMultilinear 𝕜 E E'‖ <= 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

end map

end NontriviallyNormedField

end PiTensorProduct
