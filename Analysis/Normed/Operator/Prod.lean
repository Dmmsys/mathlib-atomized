/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Operator norm: Cartesian products

Interaction of operator norm with Cartesian products.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]

open Set Real Metric ContinuousLinearMap

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

/--
lemma `norm_fst_le` / 引理 `norm_fst_le`

English:
lemma norm_fst_le
  statement: ‖fst 𝕜 E F‖ <= 1
  proof: opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ => by simpa only [one_mul] using! le_max_left ‖e‖ ‖f‖)

中文:
引理 norm_fst_le
  结论: ‖fst 𝕜 E F‖ <= 1
  证明: opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ => by simpa only [one_mul] using! le_max_left ‖e‖ ‖f‖)

Depends on / 依赖: le_max_left, one_mul, opNorm_le_bound, zero_le_one
-/
lemma norm_fst_le : ‖fst 𝕜 E F‖ <= 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ => by simpa only [one_mul] using! le_max_left ‖e‖ ‖f‖)

/--
lemma `norm_snd_le` / 引理 `norm_snd_le`

English:
lemma norm_snd_le
  statement: ‖snd 𝕜 E F‖ <= 1
  proof: opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ => by simpa only [one_mul] using! le_max_right ‖e‖ ‖f‖)

中文:
引理 norm_snd_le
  结论: ‖snd 𝕜 E F‖ <= 1
  证明: opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ => by simpa only [one_mul] using! le_max_right ‖e‖ ‖f‖)

Depends on / 依赖: le_max_right, one_mul, opNorm_le_bound, zero_le_one
-/
lemma norm_snd_le : ‖snd 𝕜 E F‖ <= 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ => by simpa only [one_mul] using! le_max_right ‖e‖ ‖f‖)

end FirstSecond

section OpNorm

@[simp]
/--
theorem `opNorm_prod` / 定理 `opNorm_prod`

English:
theorem opNorm_prod
  given: (f : E ->L[𝕜] F) (g : E ->L[𝕜] G)
  statement: ‖f.prod g‖ = ‖(f, g)‖
  proof: le_antisymm
      (opNorm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_opNorm f x) (le_opNorm g x)) <|
    max_le
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_left _ _).trans 

中文:
定理 opNorm_prod
  条件: (f : E ->L[𝕜] F) (g : E ->L[𝕜] G)
  结论: ‖f.乘积 g‖ = ‖(f, g)‖
  证明: le_antisymm
      (opNorm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_opNorm f x) (le_opNorm g x)) <|
    max_le
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_left _ _).trans 

Depends on / 依赖: Prod.norm_def, f.prod, le_antisymm, le_max_left, le_max_right, le_opNorm, max_le, max_le_max, max_mul_of_nonneg, norm_def, norm_nonneg, opNorm_le_bound, prod_apply
-/
theorem opNorm_prod (f : E ->L[𝕜] F) (g : E ->L[𝕜] G) : ‖f.prod g‖ = ‖(f, g)‖ :=
  le_antisymm
      (opNorm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_opNorm f x) (le_opNorm g x)) <|
    max_le
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_left _ _).trans ((f.prod g).le_opNorm x))
      (opNorm_le_bound _ (norm_nonneg _) fun x =>
        (le_max_right _ _).trans ((f.prod g).le_opNorm x))


@[simp]
/--
theorem `opNNNorm_prod` / 定理 `opNNNorm_prod`

English:
theorem opNNNorm_prod
  given: (f : E ->L[𝕜] F) (g : E ->L[𝕜] G)
  statement: ‖f.prod g‖₊ = ‖(f, g)‖₊
  proof: Subtype.ext opNorm_prod f g

中文:
定理 opNNNorm_prod
  条件: (f : E ->L[𝕜] F) (g : E ->L[𝕜] G)
  结论: ‖f.乘积 g‖₊ = ‖(f, g)‖₊
  证明: Subtype.ext opNorm_prod f g

Depends on / 依赖: Subtype, Subtype.ext, opNorm_prod
-/
theorem opNNNorm_prod (f : E ->L[𝕜] F) (g : E ->L[𝕜] G) : ‖f.prod g‖₊ = ‖(f, g)‖₊ :=
Subtype.ext opNorm_prod f g


/--
Definition of `prodₗᵢ` / `prodₗᵢ` 的定义

English:
definition prodₗᵢ
  signature: (R : Type*)
  body: ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩

中文:
定义 prodₗᵢ
  签名: (R : 类型)
  定义体: ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩

Depends on / 依赖: opNorm_prod
-/
noncomputable def prodₗᵢ (R : Type*)
    [Semiring R] [Module R F] [Module R G] [ContinuousConstSMul R F]
    [ContinuousConstSMul R G] [SMulCommClass 𝕜 R F] [SMulCommClass 𝕜 R G] :
    (E ->L[𝕜] F) × (E ->L[𝕜] G) ≃ₗᵢ[R] E ->L[𝕜] F × G :=
  ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩

end OpNorm


section Prod

variable (𝕜)
variable (M₁ M₂ M₃ M₄ : Type*)
  [SeminormedAddCommGroup M₁] [NormedSpace 𝕜 M₁]
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂]
  [SeminormedAddCommGroup M₃] [NormedSpace 𝕜 M₃]
  [SeminormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

/--
Definition of `prodMapL` / `prodMapL` 的定义

English:
definition prodMapL
  signature: : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) ->L[𝕜] M₁ × M₃ ->L[𝕜] M₂ × M₄
  body: ContinuousLinearMap.copy
    (have Φ₁ : (M₁ ->L[𝕜] M₂) ->L[𝕜] M₁ ->L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ ->L[𝕜] M₄) ->L[𝕜] M₃ ->L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜

中文:
定义 prodMapL
  签名: : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) ->L[𝕜] M₁ × M₃ ->L[𝕜] M₂ × M₄
  定义体: ContinuousLinearMap.copy
    (have Φ₁ : (M₁ ->L[𝕜] M₂) ->L[𝕜] M₁ ->L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ ->L[𝕜] M₄) ->L[𝕜] M₃ ->L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compL, ContinuousLinearMap.copy, ContinuousLinearMap.fst, ContinuousLinearMap.inl, ContinuousLinearMap.inr, ContinuousLinearMap.snd
-/
noncomputable def prodMapL : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) ->L[𝕜] M₁ × M₃ ->L[𝕜] M₂ × M₄ :=
  ContinuousLinearMap.copy
    (have Φ₁ : (M₁ ->L[𝕜] M₂) ->L[𝕜] M₁ ->L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ ->L[𝕜] M₄) ->L[𝕜] M₃ ->L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜 M₂ M₄)
    have Φ₁' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₁ (M₂ × M₄)).flip (ContinuousLinearMap.fst 𝕜 M₁ M₃)
    have Φ₂' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₃ (M₂ × M₄)).flip (ContinuousLinearMap.snd 𝕜 M₁ M₃)
    have Ψ₁ : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) ->L[𝕜] M₁ ->L[𝕜] M₂ :=
      ContinuousLinearMap.fst 𝕜 (M₁ ->L[𝕜] M₂) (M₃ ->L[𝕜] M₄)
    have Ψ₂ : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) ->L[𝕜] M₃ ->L[𝕜] M₄ :=
      ContinuousLinearMap.snd 𝕜 (M₁ ->L[𝕜] M₂) (M₃ ->L[𝕜] M₄)
    Φ₁' ∘L Φ₁ ∘L Ψ₁ + Φ₂' ∘L Φ₂ ∘L Ψ₂)
    (fun p : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄) => p.1.prodMap p.2) (by
      apply funext
      rintro ⟨φ, ψ⟩
      refine ContinuousLinearMap.ext fun ⟨x₁, x₂⟩ => ?_
      simp)

variable {M₁ M₂ M₃ M₄}

@[simp]
/--
theorem `prodMapL_apply` / 定理 `prodMapL_apply`

English:
theorem prodMapL_apply
  given: (p : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄))
  proof: rfl

中文:
定理 prodMapL_apply
  条件: (p : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄))
  证明: rfl
-/
theorem prodMapL_apply (p : (M₁ ->L[𝕜] M₂) × (M₃ ->L[𝕜] M₄)) :
    ContinuousLinearMap.prodMapL 𝕜 M₁ M₂ M₃ M₄ p = p.1.prodMap p.2 :=
  rfl

variable {X : Type*} [TopologicalSpace X]

/--
theorem `_root_.Continuous.prod_mapL` / 定理 `_root_.Continuous.prod_mapL`

English:
theorem _root_.Continuous.prod_mapL
  statement: {f : X -> M₁ ->L[𝕜] M₂} {g : X -> M₃ ->L[𝕜] M₄} (hf : Continuous f)
  proof: (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)

中文:
定理 _root_.连续.prod_mapL
  结论: {f : X -> M₁ ->L[𝕜] M₂} {g : X -> M₃ ->L[𝕜] M₄} (hf : 连续 f)
  证明: (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)

Depends on / 依赖: continuous, continuous.comp, hf.prodMk, prodMapL, prodMk
-/
theorem _root_.Continuous.prod_mapL {f : X -> M₁ ->L[𝕜] M₂} {g : X -> M₃ ->L[𝕜] M₄} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).prodMap (g x) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)

/--
theorem `_root_.Continuous.prod_map_equivL` / 定理 `_root_.Continuous.prod_map_equivL`

English:
theorem _root_.Continuous.prod_map_equivL
  statement: {f : X -> M₁ ≃L[𝕜] M₂} {g : X -> M₃ ≃L[𝕜] M₄}
  proof: (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)

中文:
定理 _root_.连续.prod_map_equivL
  结论: {f : X -> M₁ ≃L[𝕜] M₂} {g : X -> M₃ ≃L[𝕜] M₄}
  证明: (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)

Depends on / 依赖: continuous, continuous.comp, hf.prodMk, prodMapL, prodMk
-/
theorem _root_.Continuous.prod_map_equivL {f : X -> M₁ ≃L[𝕜] M₂} {g : X -> M₃ ≃L[𝕜] M₄}
    (hf : Continuous fun x => (f x : M₁ ->L[𝕜] M₂)) (hg : Continuous fun x => (g x : M₃ ->L[𝕜] M₄)) :
    Continuous fun x => ((f x).prodCongr (g x) : M₁ × M₃ ->L[𝕜] M₂ × M₄) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp (hf.prodMk hg)

/--
theorem `_root_.ContinuousOn.prod_mapL` / 定理 `_root_.ContinuousOn.prod_mapL`

English:
theorem _root_.ContinuousOn.prod_mapL
  statement: {f : X -> M₁ ->L[𝕜] M₂} {g : X -> M₃ ->L[𝕜] M₄} {s : Set X}
  proof: ((prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prodMk hg) :)

中文:
定理 _root_.ContinuousOn.prod_mapL
  结论: {f : X -> M₁ ->L[𝕜] M₂} {g : X -> M₃ ->L[𝕜] M₄} {s : 集合 X}
  证明: ((prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prodMk hg) :)

Depends on / 依赖: comp_continuousOn, continuous, continuous.comp_continuousOn, hf.prodMk, prodMapL, prodMk
-/
theorem _root_.ContinuousOn.prod_mapL {f : X -> M₁ ->L[𝕜] M₂} {g : X -> M₃ ->L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).prodMap (g x)) s :=
  ((prodMapL 𝕜 M₁ M₂ M₃ M₄).continuous.comp_continuousOn (hf.prodMk hg) :)

/--
theorem `_root_.ContinuousOn.prod_map_equivL` / 定理 `_root_.ContinuousOn.prod_map_equivL`

English:
theorem _root_.ContinuousOn.prod_map_equivL
  statement: {f : X -> M₁ ≃L[𝕜] M₂} {g : X -> M₃ ≃L[𝕜] M₄} {s : Set X}
  proof: hf.prod_mapL _ hg

中文:
定理 _root_.ContinuousOn.prod_map_equivL
  结论: {f : X -> M₁ ≃L[𝕜] M₂} {g : X -> M₃ ≃L[𝕜] M₄} {s : 集合 X}
  证明: hf.prod_mapL _ hg

Depends on / 依赖: hf.prod_mapL, prod_mapL
-/
theorem _root_.ContinuousOn.prod_map_equivL {f : X -> M₁ ≃L[𝕜] M₂} {g : X -> M₃ ≃L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn (fun x => (f x : M₁ ->L[𝕜] M₂)) s)
    (hg : ContinuousOn (fun x => (g x : M₃ ->L[𝕜] M₄)) s) :
    ContinuousOn (fun x => ((f x).prodCongr (g x) : M₁ × M₃ ->L[𝕜] M₂ × M₄)) s :=
  hf.prod_mapL _ hg

end Prod

end ContinuousLinearMap

end SemiNormed

section Normed

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

/--
lemma `norm_fst` / 引理 `norm_fst`

English:
lemma norm_fst
  statement: [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  refine le_antisymm (norm_fst_le ..) ?_
  let ⟨e, he⟩ := exists_ne (0 : E)
  have : ‖e‖ <= _ * max ‖e‖ ‖(0 : F)‖ := (fst 𝕜 E F).le_opNorm (e, 0)
  rw [norm_zero]; rw [max_eq_left (norm_nonneg e)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr he), one_mul]

中文:
引理 norm_fst
  结论: [赋范交换加群 E] [赋范空间 𝕜 E]
  证明: by
  refine le_antisymm (norm_fst_le ..) ?_
  let ⟨e, he⟩ := exists_ne (0 : E)
  have : ‖e‖ <= _ * max ‖e‖ ‖(0 : F)‖ := (fst 𝕜 E F).le_opNorm (e, 0)
  rw [norm_zero]; rw [max_eq_left (norm_nonneg e)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr he), one_mul]
-/
@[simp] lemma norm_fst [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial E] :
    ‖fst 𝕜 E F‖ = 1 := by
  refine le_antisymm (norm_fst_le ..) ?_
  let ⟨e, he⟩ := exists_ne (0 : E)
  have : ‖e‖ <= _ * max ‖e‖ ‖(0 : F)‖ := (fst 𝕜 E F).le_opNorm (e, 0)
  rw [norm_zero]; rw [max_eq_left (norm_nonneg e)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr he), one_mul]

/--
lemma `norm_snd` / 引理 `norm_snd`

English:
lemma norm_snd
  statement: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  refine le_antisymm (norm_snd_le ..) ?_
  let ⟨f, hf⟩ := exists_ne (0 : F)
  have : ‖f‖ <= _ * max ‖(0 : E)‖ ‖f‖ := (snd 𝕜 E F).le_opNorm (0, f)
  rw [norm_zero]; rw [max_eq_right (norm_nonneg f)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hf), one_mul]

中文:
引理 norm_snd
  结论: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: by
  refine le_antisymm (norm_snd_le ..) ?_
  let ⟨f, hf⟩ := exists_ne (0 : F)
  have : ‖f‖ <= _ * max ‖(0 : E)‖ ‖f‖ := (snd 𝕜 E F).le_opNorm (0, f)
  rw [norm_zero]; rw [max_eq_right (norm_nonneg f)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hf), one_mul]
-/
@[simp] lemma norm_snd [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Nontrivial F] :
    ‖snd 𝕜 E F‖ = 1 := by
  refine le_antisymm (norm_snd_le ..) ?_
  let ⟨f, hf⟩ := exists_ne (0 : F)
  have : ‖f‖ <= _ * max ‖(0 : E)‖ ‖f‖ := (snd 𝕜 E F).le_opNorm (0, f)
  rw [norm_zero]; rw [max_eq_right (norm_nonneg f)] at this
  rwa [← mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hf), one_mul]

end FirstSecond

end ContinuousLinearMap

end Normed
