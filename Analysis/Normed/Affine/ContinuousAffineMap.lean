/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.MetricSpace.TransferInstance
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Norm on the continuous affine maps between normed vector spaces.

We define a norm on the space of continuous affine maps between normed vector spaces by defining the
norm of `f : V →ᴬ[𝕜] W` to be `‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a
linear isometry: `(V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

* `ContinuousAffineMap.hasNorm`
* `ContinuousAffineMap.norm_comp_le`
* `ContinuousAffineMap.toConstProdContinuousLinearMap`

-/

@[expose] public section


namespace ContinuousAffineMap

variable {𝕜 R V W W₂ Q : Type*}

section Seminormed

variable [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [SeminormedAddCommGroup W₂]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]
variable [PseudoMetricSpace Q] [NormedAddTorsor W Q]

variable (f : V ->ᴬ[𝕜] W)

/--
Instance `hasNorm` / 实例 `hasNorm`

English:
instance hasNorm
  signature: : Norm (V ->ᴬ[𝕜] W)
  body: ⟨fun f => max ‖f 0‖ ‖f.contLinear‖⟩

中文:
实例 hasNorm
  签名: : 范数 (V ->ᴬ[𝕜] W)
  定义体: ⟨fun f => max ‖f 0‖ ‖f.contLinear‖⟩

Depends on / 依赖: contLinear, f.contLinear
-/
noncomputable instance hasNorm : Norm (V ->ᴬ[𝕜] W) :=
  ⟨fun f => max ‖f 0‖ ‖f.contLinear‖⟩

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  statement: ‖f‖ = max ‖f 0‖ ‖f.contLinear‖
  proof: rfl

中文:
定理 norm_def
  结论: ‖f‖ = 最大值 ‖f 0‖ ‖f.contLinear‖
  证明: rfl
-/
theorem norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ :=
  rfl

/--
theorem `norm_contLinear_le` / 定理 `norm_contLinear_le`

English:
theorem norm_contLinear_le
  statement: ‖f.contLinear‖ <= ‖f‖
  proof: le_max_right _ _

中文:
定理 norm_contLinear_le
  结论: ‖f.contLinear‖ <= ‖f‖
  证明: le_max_right _ _

Depends on / 依赖: le_max_right
-/
theorem norm_contLinear_le : ‖f.contLinear‖ <= ‖f‖ :=
  le_max_right _ _

/--
theorem `norm_image_zero_le` / 定理 `norm_image_zero_le`

English:
theorem norm_image_zero_le
  statement: ‖f 0‖ <= ‖f‖
  proof: le_max_left _ _

@[simp]

中文:
定理 norm_image_zero_le
  结论: ‖f 0‖ <= ‖f‖
  证明: le_max_left _ _

@[simp]

Depends on / 依赖: le_max_left
-/
theorem norm_image_zero_le : ‖f 0‖ <= ‖f‖ :=
  le_max_left _ _

@[simp]
/--
theorem `norm_eq` / 定理 `norm_eq`

English:
theorem norm_eq
  given: (h : f 0 = 0)
  statement: ‖f‖ = ‖f.contLinear‖
  proof: calc
    ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ := by rw [norm_def]
    _ = max 0 ‖f.contLinear‖ := by rw [h, norm_zero]
    _ = ‖f.contLinear‖ := max_eq_right (norm_nonneg _)

中文:
定理 norm_eq
  条件: (h : f 0 = 0)
  结论: ‖f‖ = ‖f.contLinear‖
  证明: calc
    ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ := by rw [norm_def]
    _ = max 0 ‖f.contLinear‖ := by rw [h, norm_zero]
    _ = ‖f.contLinear‖ := max_eq_right (norm_nonneg _)

Depends on / 依赖: contLinear, f.contLinear, max_eq_right, norm_def, norm_nonneg, norm_zero
-/
theorem norm_eq (h : f 0 = 0) : ‖f‖ = ‖f.contLinear‖ :=
  calc
    ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ := by rw [norm_def]
    _ = max 0 ‖f.contLinear‖ := by rw [h, norm_zero]
    _ = ‖f.contLinear‖ := max_eq_right (norm_nonneg _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (V ->ᴬ[𝕜] Q)
  body: (decompEquiv 𝕜 V Q).pseudometricSpace

中文:
实例 :
  签名: 伪度量空间 (V ->ᴬ[𝕜] Q)
  定义体: (decompEquiv 𝕜 V Q).pseudometricSpace

Depends on / 依赖: decompEquiv, pseudometricSpace
-/
noncomputable instance : PseudoMetricSpace (V ->ᴬ[𝕜] Q) :=
  (decompEquiv 𝕜 V Q).pseudometricSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeminormedAddCommGroup (V ->ᴬ[𝕜] W)
  body: dist_eq_norm_neg_add (E := W × (V ->L[𝕜] W)) _ _

中文:
实例 :
  签名: SeminormedAddComm群 (V ->ᴬ[𝕜] W)
  定义体: dist_eq_norm_neg_add (E := W × (V ->L[𝕜] W)) _ _

Depends on / 依赖: dist_eq_norm_neg_add
-/
noncomputable instance : SeminormedAddCommGroup (V ->ᴬ[𝕜] W) where
  dist_eq _ _ := dist_eq_norm_neg_add (E := W × (V ->L[𝕜] W)) _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddTorsor (V ->ᴬ[𝕜] W) (V ->ᴬ[𝕜] Q)
  body: dist_eq_norm_vsub (P := Q × (V ->L[𝕜] W)) _ _ _

中文:
实例 :
  签名: NormedAddTorsor (V ->ᴬ[𝕜] W) (V ->ᴬ[𝕜] Q)
  定义体: dist_eq_norm_vsub (P := Q × (V ->L[𝕜] W)) _ _ _

Depends on / 依赖: dist_eq_norm_vsub
-/
noncomputable instance : NormedAddTorsor (V ->ᴬ[𝕜] W) (V ->ᴬ[𝕜] Q) where
  dist_eq_norm' _ _ := dist_eq_norm_vsub (P := Q × (V ->L[𝕜] W)) _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedSpace 𝕜 (V ->ᴬ[𝕜] W)
  body: norm_smul_le t (f 0, f.contLinear)

中文:
实例 :
  签名: 赋范空间 𝕜 (V ->ᴬ[𝕜] W)
  定义体: norm_smul_le t (f 0, f.contLinear)

Depends on / 依赖: contLinear, f.contLinear, norm_smul_le
-/
noncomputable instance : NormedSpace 𝕜 (V ->ᴬ[𝕜] W) where
  norm_smul_le t f := norm_smul_le t (f 0, f.contLinear)

/--
theorem `norm_comp_le` / 定理 `norm_comp_le`

English:
theorem norm_comp_le
  given: (g : W₂ ->ᴬ[𝕜] V)
  statement: ‖f.comp g‖ <= ‖f‖ * ‖g‖ + ‖f 0‖
  proof: by
  rw [norm_def]; rw [max_le_iff]
  constructor
  · calc
      ‖f.comp g 0‖ = ‖f (g 0)‖ := by simp
      _ = ‖f.contLinear (g 0) + f 0‖ := by rw [f.decomp]; simp
      _ <= ‖f.contLinear‖ * ‖g 0‖ + ‖f 0‖ := by grw [norm_add_le, f.contLinear.le_opNorm]
      _ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by grw [f.norm_contLinear_le, g.norm_image_zero_le]
  · calc
      ‖(f.comp g).contLinear‖ <= ‖f.contLinear‖ * ‖g.contLinear‖ :=
        (g.comp_contLinear f).symm ▸ f.contLinear.opNorm_comp_le _
      _ <= ‖f‖ * ‖g‖ := by grw [f.norm_contLinear_le, g.norm_contLinear_le]
      _ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by rw [le_add_iff_nonneg_right]; apply norm_nonneg

中文:
定理 norm_comp_le
  条件: (g : W₂ ->ᴬ[𝕜] V)
  结论: ‖f.comp g‖ <= ‖f‖ * ‖g‖ + ‖f 0‖
  证明: by
  rw [norm_def]; rw [max_le_iff]
  constructor
  · calc
      ‖f.comp g 0‖ = ‖f (g 0)‖ := by simp
      _ = ‖f.contLinear (g 0) + f 0‖ := by rw [f.decomp]; simp
      _ <= ‖f.contLinear‖ * ‖g 0‖ + ‖f 0‖ := by grw [norm_add_le, f.contLinear.le_opNorm]
      _ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by grw [f.norm_contLinear_le, g.norm_image_zero_le]
  · calc
      ‖(f.comp g).contLinear‖ <= ‖f.contLinear‖ * ‖g.contLinear‖ :=
        (g.comp_contLinear f).symm ▸ f.contLinear.opNorm_comp_le _
      _ <= ‖f‖ * ‖g‖ := by grw [f.norm_contLinear_le, g.norm_contLinear_le]
      _ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by rw [le_add_iff_nonneg_right]; apply norm_nonneg

Depends on / 依赖: comp_contLinear, contLinear, decomp, f.comp, f.contLinear, f.contLinear.le_opNorm, f.contLinear.opNorm_comp_le, f.decomp, f.norm_contLinear_le, g.comp_contLinear, g.contLinear, g.norm_contLinea, g.norm_image_zero_le, le_opNorm, max_le_iff, norm_add_le, norm_contLinea, norm_contLinear_le, norm_def, norm_image_zero_le
-/
theorem norm_comp_le (g : W₂ ->ᴬ[𝕜] V) : ‖f.comp g‖ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by
  rw [norm_def]; rw [max_le_iff]
  constructor
  · calc
      ‖f.comp g 0‖ = ‖f (g 0)‖ := by simp
      _ = ‖f.contLinear (g 0) + f 0‖ := by rw [f.decomp]; simp
      _ <= ‖f.contLinear‖ * ‖g 0‖ + ‖f 0‖ := by grw [norm_add_le, f.contLinear.le_opNorm]
      _ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by grw [f.norm_contLinear_le, g.norm_image_zero_le]
  · calc
      ‖(f.comp g).contLinear‖ <= ‖f.contLinear‖ * ‖g.contLinear‖ :=
        (g.comp_contLinear f).symm ▸ f.contLinear.opNorm_comp_le _
      _ <= ‖f‖ * ‖g‖ := by grw [f.norm_contLinear_le, g.norm_contLinear_le]
      _ <= ‖f‖ * ‖g‖ + ‖f 0‖ := by rw [le_add_iff_nonneg_right]; apply norm_nonneg

variable (𝕜 R V W) [Ring R] [Module R W] [ContinuousConstSMul R W] [SMulCommClass 𝕜 R W]

/--
Definition of `decompLinearIsometryEquiv` / `decompLinearIsometryEquiv` 的定义

English:
definition decompLinearIsometryEquiv
  signature: : (V ->ᴬ[𝕜] W) ≃ₗᵢ[R] W × (V ->L[𝕜] W) where
  body: decompLinearEquiv 𝕜 R V W
  norm_map' _ := rfl

@[simp]

中文:
定义 decompLinearIsometryEquiv
  签名: : (V ->ᴬ[𝕜] W) ≃ₗᵢ[R] W × (V ->L[𝕜] W) where
  定义体: decompLinearEquiv 𝕜 R V W
  norm_map' _ := rfl

@[simp]

Depends on / 依赖: decompLinearEquiv
-/
def decompLinearIsometryEquiv : (V ->ᴬ[𝕜] W) ≃ₗᵢ[R] W × (V ->L[𝕜] W) where
  __ := decompLinearEquiv 𝕜 R V W
  norm_map' _ := rfl

@[simp]
/--
theorem `fst_decompLinearIsometryEquiv` / 定理 `fst_decompLinearIsometryEquiv`

English:
theorem fst_decompLinearIsometryEquiv
  given: (f : V ->ᴬ[𝕜] W)
  proof: rfl

@[simp]

中文:
定理 fst_decompLinearIsometryEquiv
  条件: (f : V ->ᴬ[𝕜] W)
  证明: rfl

@[simp]
-/
theorem fst_decompLinearIsometryEquiv (f : V ->ᴬ[𝕜] W) :
    (decompLinearIsometryEquiv 𝕜 R V W f).1 = f 0 :=
  rfl

@[simp]
/--
theorem `snd_decompLinearIsometryEquiv` / 定理 `snd_decompLinearIsometryEquiv`

English:
theorem snd_decompLinearIsometryEquiv
  given: (f : V ->ᴬ[𝕜] W)
  proof: rfl

@[simp]

中文:
定理 snd_decompLinearIsometryEquiv
  条件: (f : V ->ᴬ[𝕜] W)
  证明: rfl

@[simp]
-/
theorem snd_decompLinearIsometryEquiv (f : V ->ᴬ[𝕜] W) :
    (decompLinearIsometryEquiv 𝕜 R V W f).2 = f.contLinear :=
  rfl

@[simp]
/--
theorem `decompLinearIsometryEquiv_symm_apply` / 定理 `decompLinearIsometryEquiv_symm_apply`

English:
theorem decompLinearIsometryEquiv_symm_apply
  given: (p : W × (V ->L[𝕜] W)) (x : V)
  proof: rfl

@[simp]

中文:
定理 decompLinearIsometryEquiv_symm_apply
  条件: (p : W × (V ->L[𝕜] W)) (x : V)
  证明: rfl

@[simp]
-/
theorem decompLinearIsometryEquiv_symm_apply (p : W × (V ->L[𝕜] W)) (x : V) :
    (decompLinearIsometryEquiv 𝕜 R V W).symm p x = p.2 x + p.1 :=
  rfl

@[simp]
/--
theorem `decompLinearIsometryEquiv_symm_contLinear` / 定理 `decompLinearIsometryEquiv_symm_contLinear`

English:
theorem decompLinearIsometryEquiv_symm_contLinear
  given: (p : W × (V ->L[𝕜] W))
  proof: by
  rw [decompLinearIsometryEquiv]; rw [← LinearIsometryEquiv.coe_symm_toLinearEquiv]; rw [decompLinearEquiv_symm_contLinear]

@[deprecated decompLinearIsometryEquiv (since := "2026-03-03"),
  inherit_doc decompLinearIsometryEquiv]

中文:
定理 decompLinearIsometryEquiv_symm_contLinear
  条件: (p : W × (V ->L[𝕜] W))
  证明: by
  rw [decompLinearIsometryEquiv]; rw [← LinearIsometryEquiv.coe_symm_toLinearEquiv]; rw [decompLinearEquiv_symm_contLinear]

@[deprecated decompLinearIsometryEquiv (since := "2026-03-03"),
  inherit_doc decompLinearIsometryEquiv]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv, coe_symm_toLinearEquiv, decompLinearEquiv_symm_contLinear, decompLinearIsometryEquiv
-/
theorem decompLinearIsometryEquiv_symm_contLinear (p : W × (V ->L[𝕜] W)) :
    ((decompLinearIsometryEquiv 𝕜 R V W).symm p).contLinear = p.2 := by
  rw [decompLinearIsometryEquiv]; rw [← LinearIsometryEquiv.coe_symm_toLinearEquiv]; rw [decompLinearEquiv_symm_contLinear]

@[deprecated decompLinearIsometryEquiv (since := "2026-03-03"),
  inherit_doc decompLinearIsometryEquiv]
/--
Definition of `toConstProdContinuousLinearMap` / `toConstProdContinuousLinearMap` 的定义

English:
abbreviation toConstProdContinuousLinearMap
  body: decompLinearIsometryEquiv 𝕜 𝕜 V W

@[deprecated fst_decompLinearIsometryEquiv (since := "2026-03-03")]

中文:
缩写 toConstProdContinuousLinearMap
  定义体: decompLinearIsometryEquiv 𝕜 𝕜 V W

@[deprecated fst_decompLinearIsometryEquiv (since := "2026-03-03")]

Depends on / 依赖: decompLinearIsometryEquiv
-/
abbrev toConstProdContinuousLinearMap := decompLinearIsometryEquiv 𝕜 𝕜 V W

@[deprecated fst_decompLinearIsometryEquiv (since := "2026-03-03")]
/--
theorem `toConstProdContinuousLinearMap_fst` / 定理 `toConstProdContinuousLinearMap_fst`

English:
theorem toConstProdContinuousLinearMap_fst
  given: (f : V ->ᴬ[𝕜] W)
  proof: rfl

@[deprecated snd_decompLinearIsometryEquiv (since := "2026-03-03")]

中文:
定理 toConstProdContinuousLinearMap_fst
  条件: (f : V ->ᴬ[𝕜] W)
  证明: rfl

@[deprecated snd_decompLinearIsometryEquiv (since := "2026-03-03")]
-/
theorem toConstProdContinuousLinearMap_fst (f : V ->ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).fst = f 0 :=
  rfl

@[deprecated snd_decompLinearIsometryEquiv (since := "2026-03-03")]
/--
theorem `toConstProdContinuousLinearMap_snd` / 定理 `toConstProdContinuousLinearMap_snd`

English:
theorem toConstProdContinuousLinearMap_snd
  given: (f : V ->ᴬ[𝕜] W)
  proof: rfl

中文:
定理 toConstProdContinuousLinearMap_snd
  条件: (f : V ->ᴬ[𝕜] W)
  证明: rfl
-/
theorem toConstProdContinuousLinearMap_snd (f : V ->ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).snd = f.contLinear :=
  rfl

end Seminormed

section Normed

variable [NormedAddCommGroup V] [NormedAddCommGroup W]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
variable [MetricSpace Q] [NormedAddTorsor W Q]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace (V ->ᴬ[𝕜] Q)
  body: (decompEquiv 𝕜 V Q).metricSpace

中文:
实例 :
  签名: 度量空间 (V ->ᴬ[𝕜] Q)
  定义体: (decompEquiv 𝕜 V Q).metricSpace

Depends on / 依赖: decompEquiv, metricSpace
-/
noncomputable instance : MetricSpace (V ->ᴬ[𝕜] Q) :=
  (decompEquiv 𝕜 V Q).metricSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddCommGroup (V ->ᴬ[𝕜] W)
  body: inferInstance
  __ : MetricSpace (V ->ᴬ[𝕜] W) := inferInstance

中文:
实例 :
  签名: 赋范交换加群 (V ->ᴬ[𝕜] W)
  定义体: inferInstance
  __ : MetricSpace (V ->ᴬ[𝕜] W) := inferInstance
-/
noncomputable instance : NormedAddCommGroup (V ->ᴬ[𝕜] W) where
  __ : SeminormedAddCommGroup (V ->ᴬ[𝕜] W) := inferInstance
  __ : MetricSpace (V ->ᴬ[𝕜] W) := inferInstance

end Normed

end ContinuousAffineMap
