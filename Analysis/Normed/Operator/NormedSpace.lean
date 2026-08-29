/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Operator norm for maps on normed spaces

This file contains statements about operator norm for which it really matters that the
underlying space has a norm (rather than just a seminorm).
-/

@[expose] public section

suppress_compilation

open Topology
open scoped NNReal

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₁ 𝕜₂ 𝕜₃ E F Fₗ G : Type*}

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₃ : 𝕜₂ ->+* 𝕜₃} (f : E ->SL[σ₁₂] F)

namespace LinearIsometry
section
variable [NontrivialTopology E] [RingHomIsometric σ₁₂]

/--
lemma `norm_toContinuousLinearMap` / 引理 `norm_toContinuousLinearMap`

English:
lemma norm_toContinuousLinearMap
  given: (f : E ->ₛₗᵢ[σ₁₂] F)
  statement: ‖f.toContinuousLinearMap‖ = 1
  proof: f.toContinuousLinearMap.homothety_norm by simp

中文:
引理 norm_toContinuousLinearMap
  条件: (f : E ->ₛₗᵢ[σ₁₂] F)
  结论: ‖f.toContinuousLinearMap‖ = 1
  证明: f.toContinuousLinearMap.homothety_norm by simp
-/
@[simp] lemma norm_toContinuousLinearMap (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ = 1 :=
f.toContinuousLinearMap.homothety_norm by simp

/--
lemma `nnnorm_toContinuousLinearMap` / 引理 `nnnorm_toContinuousLinearMap`

English:
lemma nnnorm_toContinuousLinearMap
  given: (f : E ->ₛₗᵢ[σ₁₂] F)
  statement: ‖f.toContinuousLinearMap‖₊ = 1
  proof: Subtype.ext f.norm_toContinuousLinearMap

中文:
引理 nnnorm_toContinuousLinearMap
  条件: (f : E ->ₛₗᵢ[σ₁₂] F)
  结论: ‖f.toContinuousLinearMap‖₊ = 1
  证明: Subtype.ext f.norm_toContinuousLinearMap
-/
@[simp] lemma nnnorm_toContinuousLinearMap (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖₊ = 1 :=
  Subtype.ext f.norm_toContinuousLinearMap

/--
lemma `enorm_toContinuousLinearMap` / 引理 `enorm_toContinuousLinearMap`

English:
lemma enorm_toContinuousLinearMap
  given: (f : E ->ₛₗᵢ[σ₁₂] F)
  statement: ‖f.toContinuousLinearMap‖ₑ = 1
  proof: congrArg _ f.nnnorm_toContinuousLinearMap

中文:
引理 enorm_toContinuousLinearMap
  条件: (f : E ->ₛₗᵢ[σ₁₂] F)
  结论: ‖f.toContinuousLinearMap‖ₑ = 1
  证明: congrArg _ f.nnnorm_toContinuousLinearMap
-/
@[simp] lemma enorm_toContinuousLinearMap (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ₑ = 1 :=
  congrArg _ f.nnnorm_toContinuousLinearMap

end

variable {σ₁₃ : 𝕜 ->+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/--
lemma `norm_toContinuousLinearMap_comp` / 引理 `norm_toContinuousLinearMap_comp`

English:
lemma norm_toContinuousLinearMap_comp
  statement: [RingHomIsometric σ₁₂] (f : F ->ₛₗᵢ[σ₂₃] G)
  proof: (f.toContinuousLinearMap.comp g).opNorm_ext g fun x => by simp

中文:
引理 norm_toContinuousLinearMap_comp
  结论: [RingHomIsometric σ₁₂] (f : F ->ₛₗᵢ[σ₂₃] G)
  证明: (f.toContinuousLinearMap.comp g).opNorm_ext g fun x => by simp

Depends on / 依赖: f.toContinuousLinearMap.comp, opNorm_ext, toContinuousLinearMap
-/
lemma norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F ->ₛₗᵢ[σ₂₃] G)
    {g : E ->SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖ :=
  (f.toContinuousLinearMap.comp g).opNorm_ext g fun x => by simp

/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] (a : F ->ₛₗᵢ[σ₂₃] G)
  body: a.toContinuousLinearMap.comp f
  map_add' f g := by simp
  map_smul' c f := by simp
  norm_map' f := by simp [a.norm_toContinuousLinearMap_comp]

中文:
定义 postcomp
  签名: [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] (a : F ->ₛₗᵢ[σ₂₃] G)
  定义体: a.toContinuousLinearMap.comp f
  map_add' f g := by simp
  map_smul' c f := by simp
  norm_map' f := by simp [a.norm_toContinuousLinearMap_comp]

Depends on / 依赖: a.toContinuousLinearMap.comp, toContinuousLinearMap
-/
def postcomp [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] (a : F ->ₛₗᵢ[σ₂₃] G) :
    (E ->SL[σ₁₂] F) ->ₛₗᵢ[σ₂₃] (E ->SL[σ₁₃] G) where
  toFun f := a.toContinuousLinearMap.comp f
  map_add' f g := by simp
  map_smul' c f := by simp
  norm_map' f := by simp [a.norm_toContinuousLinearMap_comp]

end LinearIsometry

namespace LinearIsometryEquiv
variable [NontrivialTopology E] {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₁ : 𝕜₂ ->+* 𝕜}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [RingHomIsometric σ₁₂]

/--
lemma `norm_toContinuousLinearMap` / 引理 `norm_toContinuousLinearMap`

English:
lemma norm_toContinuousLinearMap
  given: (e : E ≃ₛₗᵢ[σ₁₂] F)
  proof: e.toLinearIsometry.norm_toContinuousLinearMap

中文:
引理 norm_toContinuousLinearMap
  条件: (e : E ≃ₛₗᵢ[σ₁₂] F)
  证明: e.toLinearIsometry.norm_toContinuousLinearMap
-/
@[simp] lemma norm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ = 1 :=
  e.toLinearIsometry.norm_toContinuousLinearMap

/--
lemma `nnnorm_toContinuousLinearMap` / 引理 `nnnorm_toContinuousLinearMap`

English:
lemma nnnorm_toContinuousLinearMap
  given: (e : E ≃ₛₗᵢ[σ₁₂] F)
  proof: e.toLinearIsometry.nnnorm_toContinuousLinearMap

中文:
引理 nnnorm_toContinuousLinearMap
  条件: (e : E ≃ₛₗᵢ[σ₁₂] F)
  证明: e.toLinearIsometry.nnnorm_toContinuousLinearMap
-/
@[simp] lemma nnnorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖₊ = 1 :=
  e.toLinearIsometry.nnnorm_toContinuousLinearMap

/--
lemma `enorm_toContinuousLinearMap` / 引理 `enorm_toContinuousLinearMap`

English:
lemma enorm_toContinuousLinearMap
  given: (e : E ≃ₛₗᵢ[σ₁₂] F)
  proof: e.toLinearIsometry.enorm_toContinuousLinearMap

中文:
引理 enorm_toContinuousLinearMap
  条件: (e : E ≃ₛₗᵢ[σ₁₂] F)
  证明: e.toLinearIsometry.enorm_toContinuousLinearMap
-/
@[simp] lemma enorm_toContinuousLinearMap (e : E ≃ₛₗᵢ[σ₁₂] F) :
    ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ₑ = 1 :=
  e.toLinearIsometry.enorm_toContinuousLinearMap

end LinearIsometryEquiv
end SeminormedAddCommGroup

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₃ : 𝕜₂ ->+* 𝕜₃} (f : E ->SL[σ₁₂] F)

namespace LinearMap

/--
theorem `bound_of_shell` / 定理 `bound_of_shell`

English:
theorem bound_of_shell
  statement: [RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F) {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜}
  proof: by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)

中文:
定理 bound_of_shell
  结论: [RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F) {ε C : 实数} (ε_pos : 0 < ε) {c : 𝕜}
  证明: by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.bound_of_shell_semi_normed, bound_of_shell_semi_normed, norm_ne_zero_iff
-/
theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F) {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f x‖ <= C * ‖x‖) (x : E) :
    ‖f x‖ <= C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)

/--
theorem `bound_of_ball_bound` / 定理 `bound_of_ball_bound`

English:
theorem bound_of_ball_bound
  statement: {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] Fₗ)
  proof: by
  obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial 𝕜 _
  use c * (‖k‖ / r)
  intro z
  refine bound_of_shell _ r_pos hk (fun x hko hxo => ?_) _
  calc
    ‖f x‖ <= c := h _ (mem_ball_zero_iff.mpr hxo)
    _ <= c * (‖x‖ * ‖k‖ / r) := le_mul_of_one_le_right ?_ ?_
    _ = _ := by ring
  · exac

中文:
定理 bound_of_ball_bound
  结论: {r : 实数} (r_pos : 0 < r) (c : 实数) (f : E ->ₗ[𝕜] Fₗ)
  证明: by
  obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial 𝕜 _
  use c * (‖k‖ / r)
  intro z
  refine bound_of_shell _ r_pos hk (fun x hko hxo => ?_) _
  calc
    ‖f x‖ <= c := h _ (mem_ball_zero_iff.mpr hxo)
    _ <= c * (‖x‖ * ‖k‖ / r) := le_mul_of_one_le_right ?_ ?_
    _ = _ := by ring
  · exac

Depends on / 依赖: NontriviallyNormedField, NontriviallyNormedField.non_trivial, bound_of_shell, le_mul_of_one_le_right, le_trans, mem_ball_zero_iff, mem_ball_zero_iff.mpr, non_trivial, norm_nonneg, one_le_div, r_pos, zero_lt_one, zero_lt_one.trans
-/
theorem bound_of_ball_bound {r : Real} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] Fₗ)
    (h : forall z in Metric.ball (0 : E) r, ‖f z‖ <= c) : exists C, forall z : E, ‖f z‖ <= C * ‖z‖ := by
  obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial 𝕜 _
  use c * (‖k‖ / r)
  intro z
  refine bound_of_shell _ r_pos hk (fun x hko hxo => ?_) _
  calc
    ‖f x‖ <= c := h _ (mem_ball_zero_iff.mpr hxo)
    _ <= c * (‖x‖ * ‖k‖ / r) := le_mul_of_one_le_right ?_ ?_
    _ = _ := by ring
  · exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos]))
  · rw [div_le_iff₀ (zero_lt_one.trans hk)] at hko
    exact (one_le_div r_pos).mpr hko

/--
theorem `antilipschitz_of_comap_nhds_le` / 定理 `antilipschitz_of_comap_nhds_le`

English:
theorem antilipschitz_of_comap_nhds_le
  statement: [h : RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F)
  proof: by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to Real>=0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.

中文:
定理 antilipschitz_of_comap_nhds_le
  结论: [h : RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F)
  证明: by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to Real>=0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.antilipschitz_of_bound, Filter, Filter.tendsto_pure_pure, NormedField, NormedField.exists_one_lt_norm, Set.mem_preimage, Set.subset_def, Specializes, Specializes.eq, antilipschitz_of_bound, exists_one_lt_norm, le_basis_iff, le_coma, mem_ball_zero_iff, mem_preimage, mono_right, nhds_basis_ball, nhds_basis_ball.comap, one_pos
-/
theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E ->ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f <= 𝓝 0) : exists K, AntilipschitzWith K f := by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to Real>=0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩
  by_cases hx : f x = 0
  · rw [← hx] at hf
    obtain rfl : x = 0 := Specializes.eq (specializes_iff_pure.2 <|
      ((Filter.tendsto_pure_pure _ _).mono_right (pure_le_nhds _)).le_comap.trans hf)
    exact norm_zero.trans_le (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hc₀ : c != 0 := norm_pos_iff.1 (one_pos.trans hc)
  rw [← h.1] at hc
  rcases rescale_to_shell_zpow hc ε0 hx with ⟨n, -, hlt, -, hle⟩
  simp only [← map_zpow₀, h.1, ← map_smulₛₗ] at hlt hle
  calc
    ‖x‖ = ‖c ^ n‖⁻¹ * ‖c ^ n • x‖ := by
      rwa [← norm_inv, ← norm_smul, inv_smul_smul₀ (zpow_ne_zero _ _)]
    _ <= ‖c ^ n‖⁻¹ * 1 := by gcongr; exact (hε _ hlt).le
    _ <= ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]

end LinearMap

namespace ContinuousLinearMap

open Set Real

/--
theorem `opNorm_zero_iff` / 定理 `opNorm_zero_iff`

English:
theorem opNorm_zero_iff
  given: [RingHomIsometric σ₁₂]
  statement: ‖f‖ = 0 ↔ f = 0
  proof: Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ <= ‖f‖ * ‖x‖ := le_opNorm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact opNorm_zero)

中文:
定理 opNorm_zero_iff
  条件: [RingHomIsometric σ₁₂]
  结论: ‖f‖ = 0 ↔ f = 0
  证明: Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ <= ‖f‖ * ‖x‖ := le_opNorm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact opNorm_zero)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, Iff.intro, le_opNorm, norm_le_zero_iff, opNorm_zero, zero_mul
-/
theorem opNorm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ <= ‖f‖ * ‖x‖ := le_opNorm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact opNorm_zero)

/--
Instance `toNormedAddCommGroup` / 实例 `toNormedAddCommGroup`

English:
instance toNormedAddCommGroup
  signature: [RingHomIsometric σ₁₂]
  body: NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp

中文:
实例 toNormedAddCommGroup
  签名: [RingHomIsometric σ₁₂]
  定义体: NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp

Depends on / 依赖: NormedAddCommGroup, NormedAddCommGroup.ofSeparation, ofSeparation, opNorm_zero_iff
-/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E ->SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp

/--
Instance `toNormedRing` / 实例 `toNormedRing`

English:
instance toNormedRing
  signature: : NormedRing (E ->L[𝕜] E) where
  body: toNormedAddCommGroup
  __ := toSeminormedRing

中文:
实例 toNormedRing
  签名: : 赋范环 (E ->L[𝕜] E) where
  定义体: toNormedAddCommGroup
  __ := toSeminormedRing

Depends on / 依赖: toNormedAddCommGroup
-/
instance toNormedRing : NormedRing (E ->L[𝕜] E) where
  __ := toNormedAddCommGroup
  __ := toSeminormedRing

/--
theorem `antilipschitz_of_isEmbedding` / 定理 `antilipschitz_of_isEmbedding`

English:
theorem antilipschitz_of_isEmbedding
  given: (f : E ->L[𝕜] Fₗ) (hf : IsEmbedding f)
  proof: f.toLinearMap.antilipschitz_of_comap_nhds_le map_zero f ▸ (hf.nhds_eq_comap 0).ge

中文:
定理 antilipschitz_of_isEmbedding
  条件: (f : E ->L[𝕜] Fₗ) (hf : 是嵌入 f)
  证明: f.toLinearMap.antilipschitz_of_comap_nhds_le map_zero f ▸ (hf.nhds_eq_comap 0).ge

Depends on / 依赖: antilipschitz_of_comap_nhds_le, f.toLinearMap.antilipschitz_of_comap_nhds_le, hf.nhds_eq_comap, map_zero, nhds_eq_comap, toLinearMap
-/
theorem antilipschitz_of_isEmbedding (f : E ->L[𝕜] Fₗ) (hf : IsEmbedding f) :
    exists K, AntilipschitzWith K f :=
f.toLinearMap.antilipschitz_of_comap_nhds_le map_zero f ▸ (hf.nhds_eq_comap 0).ge

end ContinuousLinearMap

end

namespace ContinuousLinearMap
variable
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ]
  [NontriviallyNormedField 𝕜₁] [NormedSpace 𝕜₁ E]
  [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜₂ F]
  [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {σ₂₁ : 𝕜₂ ->+* 𝕜₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : 𝕜₂ ->+* 𝕜₃} {σ₃₂ : 𝕜₃ ->+* 𝕜₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : 𝕜₁ ->+* 𝕜₃} [RingHomIsometric σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
/--
theorem `norm_smulRightL` / 定理 `norm_smulRightL`

English:
theorem norm_smulRightL
  given: (c : StrongDual 𝕜 E) [Nontrivial Fₗ]
  statement: ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖
  proof: ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply

中文:
定理 norm_smulRightL
  条件: (c : StrongDual 𝕜 E) [非平凡 Fₗ]
  结论: ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖
  证明: ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.homothety_norm, c.norm_smulRight_apply, homothety_norm, norm_smulRight_apply
-/
theorem norm_smulRightL (c : StrongDual 𝕜 E) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply

/--
lemma `norm_smulRightL_le` / 引理 `norm_smulRightL_le`

English:
lemma norm_smulRightL_le
  statement: ‖smulRightL 𝕜 E Fₗ‖ <= 1
  proof: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

中文:
引理 norm_smulRightL_le
  结论: ‖smulRightL 𝕜 E Fₗ‖ <= 1
  证明: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, zero_le_one
-/
lemma norm_smulRightL_le : ‖smulRightL 𝕜 E Fₗ‖ <= 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-! ### Composition with isometries -/

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNNNorm_comp_linearIsometryEquiv` / 引理 `opNNNorm_comp_linearIsometryEquiv`

English:
lemma opNNNorm_comp_linearIsometryEquiv
  statement: [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
  proof: eq_of_forall_ge_iff fun r => by simp [opNNNorm_le_iff, ← e.forall_congr_right]

中文:
引理 opNNNorm_comp_linearIsometryEquiv
  结论: [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
  证明: eq_of_forall_ge_iff fun r => by simp [opNNNorm_le_iff, ← e.forall_congr_right]

Depends on / 依赖: e.forall_congr_right, eq_of_forall_ge_iff, forall_congr_right, opNNNorm_le_iff
-/
lemma opNNNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E ->SL[σ₁₂] F)‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r => by simp [opNNNorm_le_iff, ← e.forall_congr_right]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNNNorm_linearIsometryEquiv_comp` / 引理 `opNNNorm_linearIsometryEquiv_comp`

English:
lemma opNNNorm_linearIsometryEquiv_comp
  statement: [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
  proof: eq_of_forall_ge_iff fun r => by simp [opNNNorm_le_iff]

中文:
引理 opNNNorm_linearIsometryEquiv_comp
  结论: [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
  证明: eq_of_forall_ge_iff fun r => by simp [opNNNorm_le_iff]

Depends on / 依赖: eq_of_forall_ge_iff, opNNNorm_le_iff
-/
lemma opNNNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E ->SL[σ₁₂] F) : ‖(e : F ->SL[σ₂₃] G).comp f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun r => by simp [opNNNorm_le_iff]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNorm_comp_linearIsometryEquiv` / 引理 `opNorm_comp_linearIsometryEquiv`

English:
lemma opNorm_comp_linearIsometryEquiv
  statement: [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
  proof: by simp [← coe_nnnorm]

中文:
引理 opNorm_comp_linearIsometryEquiv
  结论: [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
  证明: by simp [← coe_nnnorm]

Depends on / 依赖: coe_nnnorm
-/
lemma opNorm_comp_linearIsometryEquiv [RingHomIsometric σ₂₃] (f : F ->SL[σ₂₃] G)
    (e : E ≃ₛₗᵢ[σ₁₂] F) : ‖f.comp (e : E ->SL[σ₁₂] F)‖ = ‖f‖ := by simp [← coe_nnnorm]

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNorm_linearIsometryEquiv_comp` / 引理 `opNorm_linearIsometryEquiv_comp`

English:
lemma opNorm_linearIsometryEquiv_comp
  statement: [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
  proof: by simp [← coe_nnnorm]

中文:
引理 opNorm_linearIsometryEquiv_comp
  结论: [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
  证明: by simp [← coe_nnnorm]

Depends on / 依赖: coe_nnnorm
-/
lemma opNorm_linearIsometryEquiv_comp [RingHomIsometric σ₁₂] (e : F ≃ₛₗᵢ[σ₂₃] G)
    (f : E ->SL[σ₁₂] F) : ‖(e : F ->SL[σ₂₃] G).comp f‖ = ‖f‖ := by simp [← coe_nnnorm]

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNNNorm_mul_linearIsometryEquiv` / 引理 `opNNNorm_mul_linearIsometryEquiv`

English:
lemma opNNNorm_mul_linearIsometryEquiv
  given: (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E)
  statement: ‖f * e‖₊ = ‖f‖₊
  proof: opNNNorm_comp_linearIsometryEquiv ..

中文:
引理 opNNNorm_mul_linearIsometryEquiv
  条件: (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E)
  结论: ‖f * e‖₊ = ‖f‖₊
  证明: opNNNorm_comp_linearIsometryEquiv ..

Depends on / 依赖: opNNNorm_comp_linearIsometryEquiv
-/
lemma opNNNorm_mul_linearIsometryEquiv (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖₊ = ‖f‖₊ :=
  opNNNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNNNorm_linearIsometryEquiv_mul` / 引理 `opNNNorm_linearIsometryEquiv_mul`

English:
lemma opNNNorm_linearIsometryEquiv_mul
  given: (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E)
  statement: ‖e * f‖₊ = ‖f‖₊
  proof: opNNNorm_linearIsometryEquiv_comp ..

中文:
引理 opNNNorm_linearIsometryEquiv_mul
  条件: (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E)
  结论: ‖e * f‖₊ = ‖f‖₊
  证明: opNNNorm_linearIsometryEquiv_comp ..

Depends on / 依赖: opNNNorm_linearIsometryEquiv_comp
-/
lemma opNNNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E) : ‖e * f‖₊ = ‖f‖₊ :=
  opNNNorm_linearIsometryEquiv_comp ..

/-- Precomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNorm_mul_linearIsometryEquiv` / 引理 `opNorm_mul_linearIsometryEquiv`

English:
lemma opNorm_mul_linearIsometryEquiv
  given: (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E)
  statement: ‖f * e‖ = ‖f‖
  proof: opNorm_comp_linearIsometryEquiv ..

中文:
引理 opNorm_mul_linearIsometryEquiv
  条件: (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E)
  结论: ‖f * e‖ = ‖f‖
  证明: opNorm_comp_linearIsometryEquiv ..

Depends on / 依赖: opNorm_comp_linearIsometryEquiv
-/
lemma opNorm_mul_linearIsometryEquiv (f : E ->L[𝕜] E) (e : E ≃ₗᵢ[𝕜] E) : ‖f * e‖ = ‖f‖ :=
  opNorm_comp_linearIsometryEquiv ..

/-- Postcomposition with a linear isometry preserves the operator norm. -/
@[simp]
/--
lemma `opNorm_linearIsometryEquiv_mul` / 引理 `opNorm_linearIsometryEquiv_mul`

English:
lemma opNorm_linearIsometryEquiv_mul
  given: (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E)
  statement: ‖e * f‖ = ‖f‖
  proof: opNorm_linearIsometryEquiv_comp ..

中文:
引理 opNorm_linearIsometryEquiv_mul
  条件: (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E)
  结论: ‖e * f‖ = ‖f‖
  证明: opNorm_linearIsometryEquiv_comp ..

Depends on / 依赖: opNorm_linearIsometryEquiv_comp
-/
lemma opNorm_linearIsometryEquiv_mul (e : E ≃ₗᵢ[𝕜] E) (f : E ->L[𝕜] E) : ‖e * f‖ = ‖f‖ :=
  opNorm_linearIsometryEquiv_comp ..

end ContinuousLinearMap

namespace Submodule

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/--
theorem `norm_subtypeL` / 定理 `norm_subtypeL`

English:
theorem norm_subtypeL
  given: (K : Submodule 𝕜 E) [Nontrivial K]
  statement: ‖K.subtypeL‖ = 1
  proof: K.subtypeₗᵢ.norm_toContinuousLinearMap

中文:
定理 norm_subtypeL
  条件: (K : 子模 𝕜 E) [非平凡 K]
  结论: ‖K.subtypeL‖ = 1
  证明: K.subtypeₗᵢ.norm_toContinuousLinearMap

Depends on / 依赖: K.subtype, norm_toContinuousLinearMap
-/
theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap

end Submodule

namespace ContinuousLinearEquiv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]

section

variable [RingHomIsometric σ₂₁]

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  given: (e : E ≃SL[σ₁₂] F)
  proof: e.symm.lipschitz.to_rightInverse e.left_inv

中文:
定理 antilipschitz
  条件: (e : E ≃SL[σ₁₂] F)
  证明: e.symm.lipschitz.to_rightInverse e.left_inv
-/
protected theorem antilipschitz (e : E ≃SL[σ₁₂] F) :
    AntilipschitzWith ‖(e.symm : F ->SL[σ₂₁] E)‖₊ e :=
  e.symm.lipschitz.to_rightInverse e.left_inv

/--
theorem `one_le_norm_mul_norm_symm` / 定理 `one_le_norm_mul_norm_symm`

English:
theorem one_le_norm_mul_norm_symm
  given: [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F)
  proof: by
  rw [mul_comm]
  convert! (e.symm : F ->SL[σ₂₁] E).opNorm_comp_le (e : E ->SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe]; rw [ContinuousLinearMap.norm_id]

中文:
定理 one_le_norm_mul_norm_symm
  条件: [RingHomIsometric σ₁₂] [非平凡 E] (e : E ≃SL[σ₁₂] F)
  证明: by
  rw [mul_comm]
  convert! (e.symm : F ->SL[σ₂₁] E).opNorm_comp_le (e : E ->SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe]; rw [ContinuousLinearMap.norm_id]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_id, coe_symm_comp_coe, convert, e.coe_symm_comp_coe, e.symm, mul_comm, norm_id, opNorm_comp_le
-/
theorem one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    1 <= ‖(e : E ->SL[σ₁₂] F)‖ * ‖(e.symm : F ->SL[σ₂₁] E)‖ := by
  rw [mul_comm]
  convert! (e.symm : F ->SL[σ₂₁] E).opNorm_comp_le (e : E ->SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe]; rw [ContinuousLinearMap.norm_id]

/--
theorem `norm_pos` / 定理 `norm_pos`

English:
theorem norm_pos
  given: [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F)
  proof: pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

中文:
定理 norm_pos
  条件: [RingHomIsometric σ₁₂] [非平凡 E] (e : E ≃SL[σ₁₂] F)
  证明: pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

Depends on / 依赖: e.one_le_norm_mul_norm_symm, lt_of_lt_of_le, norm_nonneg, one_le_norm_mul_norm_symm, pos_of_mul_pos_left, zero_lt_one
-/
theorem norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e : E ->SL[σ₁₂] F)‖ :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

/--
theorem `norm_symm_pos` / 定理 `norm_symm_pos`

English:
theorem norm_symm_pos
  given: [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F)
  proof: pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)

中文:
定理 norm_symm_pos
  条件: [RingHomIsometric σ₁₂] [非平凡 E] (e : E ≃SL[σ₁₂] F)
  证明: pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)

Depends on / 依赖: e.one_le_norm_mul_norm_symm, norm_nonneg, one_le_norm_mul_norm_symm, pos_of_mul_pos_right, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F ->SL[σ₂₁] E)‖ :=
  pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)

/--
theorem `nnnorm_symm_pos` / 定理 `nnnorm_symm_pos`

English:
theorem nnnorm_symm_pos
  given: [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F)
  proof: e.norm_symm_pos

中文:
定理 nnnorm_symm_pos
  条件: [RingHomIsometric σ₁₂] [非平凡 E] (e : E ≃SL[σ₁₂] F)
  证明: e.norm_symm_pos

Depends on / 依赖: e.norm_symm_pos, norm_symm_pos
-/
theorem nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F ->SL[σ₂₁] E)‖₊ :=
  e.norm_symm_pos

/--
theorem `subsingleton_or_norm_symm_pos` / 定理 `subsingleton_or_norm_symm_pos`

English:
theorem subsingleton_or_norm_symm_pos
  given: [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F)
  proof: by
  rcases subsingleton_or_nontrivial E with (_i | _i)
  · left
    infer_instance
  · right
    exact e.norm_symm_pos

中文:
定理 subsingleton_or_norm_symm_pos
  条件: [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F)
  证明: by
  rcases subsingleton_or_nontrivial E with (_i | _i)
  · left
    infer_instance
  · right
    exact e.norm_symm_pos

Depends on / 依赖: e.norm_symm_pos, infer_instance, norm_symm_pos, subsingleton_or_nontrivial
-/
theorem subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖ := by
  rcases subsingleton_or_nontrivial E with (_i | _i)
  · left
    infer_instance
  · right
    exact e.norm_symm_pos

/--
theorem `subsingleton_or_nnnorm_symm_pos` / 定理 `subsingleton_or_nnnorm_symm_pos`

English:
theorem subsingleton_or_nnnorm_symm_pos
  given: [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F)
  proof: subsingleton_or_norm_symm_pos e

中文:
定理 subsingleton_or_nnnorm_symm_pos
  条件: [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F)
  证明: subsingleton_or_norm_symm_pos e

Depends on / 依赖: subsingleton_or_norm_symm_pos
-/
theorem subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖₊ :=
  subsingleton_or_norm_symm_pos e

variable (𝕜)

@[simp]
/--
theorem `coord_norm` / 定理 `coord_norm`

English:
theorem coord_norm
  given: (x : E) (h : x != 0)
  statement: ‖coord 𝕜 x h‖ = ‖x‖⁻¹
  proof: by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  have : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h) _

中文:
定理 coord_norm
  条件: (x : E) (h : x != 0)
  结论: ‖coord 𝕜 x h‖ = ‖x‖⁻¹
  证明: by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  have : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h) _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.homothety_norm, LinearEquiv, LinearEquiv.toSpanNonzeroSingleton_homothety, Nontrivial, Submodule, Submodule.nontrivial_span_singleton, homothety_inverse, homothety_norm, nontrivial_span_singleton, norm_pos_iff, norm_pos_iff.mpr, toSpanNonzeroSingleton_homothety
-/
theorem coord_norm (x : E) (h : x != 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹ := by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  have : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact ContinuousLinearMap.homothety_norm _ fun y =>
    homothety_inverse _ hx _ (LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x h) _

end

end ContinuousLinearEquiv

end Normed

/--
Definition of `IsCoercive` / `IsCoercive` 的定义

English:
definition IsCoercive
  signature: [SeminormedAddCommGroup E] [NormedSpace Real E] (B : E ->L[Real] E ->L[Real] Real)
  body: exists C, 0 < C ∧ forall u, C * ‖u‖ * ‖u‖ <= B u u

中文:
定义 IsCoercive
  签名: [SeminormedAddComm群 E] [赋范空间 实数 E] (B : E ->L[实数] E ->L[实数] 实数)
  定义体: exists C, 0 < C ∧ forall u, C * ‖u‖ * ‖u‖ <= B u u
-/
def IsCoercive [SeminormedAddCommGroup E] [NormedSpace Real E] (B : E ->L[Real] E ->L[Real] Real) : Prop :=
  exists C, 0 < C ∧ forall u, C * ‖u‖ * ‖u‖ <= B u u

section Equicontinuous

variable {ι : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 ->+* 𝕜₂}
  [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] (f : ι -> E ->SL[σ₁₂] F)

/--
theorem `NormedSpace.equicontinuous_TFAE` / 定理 `NormedSpace.equicontinuous_TFAE`

English:
theorem NormedSpace.equicontinuous_TFAE
  statement: List.TFAE
  proof: by
  -- `1 ↔ 2 ↔ 3` follows from `uniformEquicontinuous_of_equicontinuousAt_zero`
  tfae_have 1 -> 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 -> 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 -> 1 := fun H => H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we j

中文:
定理 赋范空间.equicontinuous_TFAE
  结论: 列表.TFAE
  证明: by
  -- `1 ↔ 2 ↔ 3` follows from `uniformEquicontinuous_of_equicontinuousAt_zero`
  tfae_have 1 -> 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 -> 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 -> 1 := fun H => H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we j
-/
protected theorem NormedSpace.equicontinuous_TFAE : List.TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      exists C, forall i x, ‖f i x‖ <= C * ‖x‖,
      exists C >= 0, forall i x, ‖f i x‖ <= C * ‖x‖,
      exists C, forall i, ‖f i‖ <= C,
      exists C >= 0, forall i, ‖f i‖ <= C,
      BddAbove (Set.range (‖f ·‖)),
      (⨆ i, (‖f i‖₊ : ENNReal)) < ⊤ ] := by
  -- `1 ↔ 2 ↔ 3` follows from `uniformEquicontinuous_of_equicontinuousAt_zero`
  tfae_have 1 -> 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 -> 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 -> 1 := fun H => H 0
  -- `4 ↔ 5 ↔ 6 ↔ 7 ↔ 8 ↔ 9` is morally trivial, we just have to use a lot of rewriting
  -- and `congr` lemmas
  tfae_have 4 ↔ 5 := by
    rw [exists_ge_and_iff_exists]
exact fun C₁ C₂ hC => forall₂_imp fun i x => le_trans' by gcongr
  tfae_have 5 ↔ 7 := by
    refine exists_congr (fun C => and_congr_right fun hC => forall_congr' fun i => ?_)
    rw [ContinuousLinearMap.opNorm_le_iff hC]
  tfae_have 7 ↔ 8 := by
    simp_rw [bddAbove_iff_exists_ge (0 : Real), Set.forall_mem_range]
  tfae_have 6 ↔ 8 := by
    simp_rw [bddAbove_def, Set.forall_mem_range]
  tfae_have 8 ↔ 9 := by
    rw [ENNReal.iSup_coe_lt_top]; rw [← NNReal.bddAbove_coe]; rw [← Set.range_comp]
    rfl
  -- `3 ↔ 4` is the interesting part of the result. It is essentially a combination of
  -- `WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm` which turns
  -- equicontinuity into existence of some continuous seminorm and
  -- `Seminorm.bound_of_continuous_normedSpace` which characterize such seminorms.
  tfae_have 3 ↔ 4 := by
    refine ((norm_withSeminorms 𝕜₂ F).uniformEquicontinuous_iff_exists_continuous_seminorm _).trans
      ?_
    rw [forall_const]
    constructor
    · intro ⟨p, hp, hpf⟩
      rcases p.bound_of_continuous_normedSpace hp with ⟨C, -, hC⟩
      exact ⟨C, fun i x => (hpf i x).trans (hC x)⟩
    · intro ⟨C, hC⟩
      refine ⟨C.toNNReal • normSeminorm 𝕜 E,
        ((norm_withSeminorms 𝕜 E).continuous_seminorm 0).const_smul C.toNNReal, fun i x => ?_⟩
      exact (hC i x).trans (mul_le_mul_of_nonneg_right (C.le_coe_toNNReal) (norm_nonneg x))
  tfae_finish

end Equicontinuous

section single

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : ι -> Type*)

/--
Definition of `LinearIsometry.single` / `LinearIsometry.single` 的定义

English:
definition LinearIsometry.single
  signature: [forall i, SeminormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
  body: (LinearMap.single 𝕜 E i).toLinearIsometry (.single i)

中文:
定义 线性等距.single
  签名: [对任意 i, SeminormedAddComm群 (E i)] [对任意 i, 赋范空间 𝕜 (E i)]
  定义体: (LinearMap.single 𝕜 E i).toLinearIsometry (.single i)
-/
protected def LinearIsometry.single [forall i, SeminormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
    (i : ι) : E i ->ₗᵢ[𝕜] Π j, E j :=
  (LinearMap.single 𝕜 E i).toLinearIsometry (.single i)

/--
lemma `ContinuousLinearMap.norm_single_le_one` / 引理 `ContinuousLinearMap.norm_single_le_one`

English:
lemma ContinuousLinearMap.norm_single_le_one
  statement: [forall i, SeminormedAddCommGroup (E i)]
  proof: (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap_le

中文:
引理 连续线性映射.norm_single_le_one
  结论: [对任意 i, SeminormedAddComm群 (E i)]
  证明: (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap_le

Depends on / 依赖: LinearIsometry, LinearIsometry.single, norm_toContinuousLinearMap_le, single
-/
lemma ContinuousLinearMap.norm_single_le_one [forall i, SeminormedAddCommGroup (E i)]
    [forall i, NormedSpace 𝕜 (E i)] (i : ι) :
    ‖ContinuousLinearMap.single 𝕜 E i‖ <= 1 :=
  (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap_le

/--
lemma `ContinuousLinearMap.norm_single` / 引理 `ContinuousLinearMap.norm_single`

English:
lemma ContinuousLinearMap.norm_single
  statement: [forall i, SeminormedAddCommGroup (E i)]
  proof: (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap

中文:
引理 连续线性映射.norm_single
  结论: [对任意 i, SeminormedAddComm群 (E i)]
  证明: (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap

Depends on / 依赖: LinearIsometry, LinearIsometry.single, norm_toContinuousLinearMap, single
-/
lemma ContinuousLinearMap.norm_single [forall i, SeminormedAddCommGroup (E i)]
    [forall i, NormedSpace 𝕜 (E i)] (i : ι) [NontrivialTopology (E i)] :
    ‖ContinuousLinearMap.single 𝕜 E i‖ = 1 :=
  (LinearIsometry.single 𝕜 E i).norm_toContinuousLinearMap

end single

section inl_inr

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E F : Type*)

/--
Definition of `LinearIsometry.inl` / `LinearIsometry.inl` 的定义

English:
definition LinearIsometry.inl
  signature: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  body: (LinearMap.inl 𝕜 E F).toLinearIsometry .inl

@[simp]

中文:
定义 线性等距.inl
  签名: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  定义体: (LinearMap.inl 𝕜 E F).toLinearIsometry .inl

@[simp]
-/
protected def LinearIsometry.inl [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : E ->ₗᵢ[𝕜] E × F :=
  (LinearMap.inl 𝕜 E F).toLinearIsometry .inl

@[simp]
/--
lemma `LinearIsometry.inl_apply` / 引理 `LinearIsometry.inl_apply`

English:
lemma LinearIsometry.inl_apply
  statement: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: rfl

中文:
引理 线性等距.inl_apply
  结论: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: rfl
-/
lemma LinearIsometry.inl_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (x : E) :
    LinearIsometry.inl 𝕜 E F x = (x, 0) := rfl

/--
Definition of `LinearIsometry.inr` / `LinearIsometry.inr` 的定义

English:
definition LinearIsometry.inr
  signature: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  body: (LinearMap.inr 𝕜 E F).toLinearIsometry .inr

@[simp]

中文:
定义 线性等距.inr
  签名: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  定义体: (LinearMap.inr 𝕜 E F).toLinearIsometry .inr

@[simp]
-/
protected def LinearIsometry.inr [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] : F ->ₗᵢ[𝕜] E × F :=
  (LinearMap.inr 𝕜 E F).toLinearIsometry .inr

@[simp]
/--
lemma `LinearIsometry.inr_apply` / 引理 `LinearIsometry.inr_apply`

English:
lemma LinearIsometry.inr_apply
  statement: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: rfl

中文:
引理 线性等距.inr_apply
  结论: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: rfl
-/
lemma LinearIsometry.inr_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (y : F) :
    LinearIsometry.inr 𝕜 E F y = (0, y) := rfl

/--
lemma `ContinuousLinearMap.norm_inl_le_one` / 引理 `ContinuousLinearMap.norm_inl_le_one`

English:
lemma ContinuousLinearMap.norm_inl_le_one
  statement: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap_le

中文:
引理 连续线性映射.norm_inl_le_one
  结论: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap_le

Depends on / 依赖: LinearIsometry, LinearIsometry.inl, norm_toContinuousLinearMap_le
-/
lemma ContinuousLinearMap.norm_inl_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inl 𝕜 E F‖ <= 1 :=
  (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap_le

/--
lemma `ContinuousLinearMap.norm_inr_le_one` / 引理 `ContinuousLinearMap.norm_inr_le_one`

English:
lemma ContinuousLinearMap.norm_inr_le_one
  statement: [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap_le

中文:
引理 连续线性映射.norm_inr_le_one
  结论: [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap_le

Depends on / 依赖: LinearIsometry, LinearIsometry.inr, norm_toContinuousLinearMap_le
-/
lemma ContinuousLinearMap.norm_inr_le_one [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inr 𝕜 E F‖ <= 1 :=
  (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap_le

/--
lemma `ContinuousLinearMap.norm_inl` / 引理 `ContinuousLinearMap.norm_inl`

English:
lemma ContinuousLinearMap.norm_inl
  statement: [SeminormedAddCommGroup E] [NontrivialTopology E]
  proof: (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap

中文:
引理 连续线性映射.norm_inl
  结论: [SeminormedAddComm群 E] [非平凡拓扑 E]
  证明: (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap

Depends on / 依赖: LinearIsometry, LinearIsometry.inl, norm_toContinuousLinearMap
-/
lemma ContinuousLinearMap.norm_inl [SeminormedAddCommGroup E] [NontrivialTopology E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    ‖ContinuousLinearMap.inl 𝕜 E F‖ = 1 :=
  (LinearIsometry.inl 𝕜 E F).norm_toContinuousLinearMap

/--
lemma `ContinuousLinearMap.norm_inr` / 引理 `ContinuousLinearMap.norm_inr`

English:
lemma ContinuousLinearMap.norm_inr
  statement: [SeminormedAddCommGroup E]
  proof: (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap

中文:
引理 连续线性映射.norm_inr
  结论: [SeminormedAddComm群 E]
  证明: (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap

Depends on / 依赖: LinearIsometry, LinearIsometry.inr, norm_toContinuousLinearMap
-/
lemma ContinuousLinearMap.norm_inr [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NontrivialTopology F] :
    ‖ContinuousLinearMap.inr 𝕜 E F‖ = 1 :=
  (LinearIsometry.inr 𝕜 E F).norm_toContinuousLinearMap

end inl_inr
