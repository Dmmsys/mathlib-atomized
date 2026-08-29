/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Properties of pointwise scalar multiplication of sets in normed spaces.

We explore the relationships between scalar multiplication of sets in vector spaces, and the norm.
Notably, we express arbitrary balls as rescaling of other balls, and we show that the
multiplication of bounded sets remain bounded.
-/

public section

open Metric Set
open scoped Pointwise Topology

variable {𝕜 E : Type*}

section SMulZeroClass

variable [SeminormedAddCommGroup 𝕜] [SeminormedAddCommGroup E]
variable [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
theorem `ediam_smul_le` / 定理 `ediam_smul_le`

English:
theorem ediam_smul_le
  given: (c : 𝕜) (s : Set E)
  statement: ediam (c • s) <= ‖c‖₊ • ediam s
  proof: (lipschitzWith_smul c).ediam_image_le s

中文:
定理 ediam_smul_le
  条件: (c : 𝕜) (s : 集合 E)
  结论: ediam (c • s) <= ‖c‖₊ • ediam s
  证明: (lipschitzWith_smul c).ediam_image_le s

Depends on / 依赖: ediam_image_le, lipschitzWith_smul
-/
theorem ediam_smul_le (c : 𝕜) (s : Set E) : ediam (c • s) <= ‖c‖₊ • ediam s :=
  (lipschitzWith_smul c).ediam_image_le s

end SMulZeroClass

section DivisionRing

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [NormSMulClass 𝕜 E]

/--
theorem `ediam_smul₀` / 定理 `ediam_smul₀`

English:
theorem ediam_smul₀
  given: (c : 𝕜) (s : Set E)
  statement: ediam (c • s) = ‖c‖₊ • ediam s
  proof: by
  refine le_antisymm (ediam_smul_le c s) ?_
  obtain rfl | hc := eq_or_ne c 0
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [zero_smul_set hs, ← Set.singleton_zero]
  · have := (lipschitzWith_smul c⁻¹).ediam_image_le (c • s)
    rwa [← smul_eq_mul, ← ENNReal.smul_def, Set.image_smul, inv_smul_smul₀ hc s, nnnorm_inv,
      le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this

中文:
定理 ediam_smul₀
  条件: (c : 𝕜) (s : 集合 E)
  结论: ediam (c • s) = ‖c‖₊ • ediam s
  证明: by
  refine le_antisymm (ediam_smul_le c s) ?_
  obtain rfl | hc := eq_or_ne c 0
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [zero_smul_set hs, ← Set.singleton_zero]
  · have := (lipschitzWith_smul c⁻¹).ediam_image_le (c • s)
    rwa [← smul_eq_mul, ← ENNReal.smul_def, Set.image_smul, inv_smul_smul₀ hc s, nnnorm_inv,
      le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this

Depends on / 依赖: ENNReal, ENNReal.smul_def, Set.image_smul, Set.singleton_zero, ediam_image_le, ediam_smul_le, eq_empty_or_nonempty, eq_or_ne, image_smul, le_antisymm, le_inv_smul_iff_of_pos, lipschitzWith_smul, nnnorm_inv, nnnorm_pos, s.eq_empty_or_nonempty, singleton_zero, smul_def, smul_eq_mul, zero_smul_set
-/
theorem ediam_smul₀ (c : 𝕜) (s : Set E) : ediam (c • s) = ‖c‖₊ • ediam s := by
  refine le_antisymm (ediam_smul_le c s) ?_
  obtain rfl | hc := eq_or_ne c 0
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [zero_smul_set hs, ← Set.singleton_zero]
  · have := (lipschitzWith_smul c⁻¹).ediam_image_le (c • s)
    rwa [← smul_eq_mul, ← ENNReal.smul_def, Set.image_smul, inv_smul_smul₀ hc s, nnnorm_inv,
      le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this

/--
theorem `diam_smul₀` / 定理 `diam_smul₀`

English:
theorem diam_smul₀
  given: (c : 𝕜) (x : Set E)
  statement: diam (c • x) = ‖c‖ * diam x
  proof: by
  simp_rw [diam, ediam_smul₀, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm, smul_eq_mul]

中文:
定理 diam_smul₀
  条件: (c : 𝕜) (x : 集合 E)
  结论: diam (c • x) = ‖c‖ * diam x
  证明: by
  simp_rw [diam, ediam_smul₀, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm, smul_eq_mul]

Depends on / 依赖: ENNReal, ENNReal.toReal_smul, NNReal, NNReal.smul_def, coe_nnnorm, simp_rw, smul_def, smul_eq_mul, toReal_smul
-/
theorem diam_smul₀ (c : 𝕜) (x : Set E) : diam (c • x) = ‖c‖ * diam x := by
  simp_rw [diam, ediam_smul₀, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm, smul_eq_mul]

/--
theorem `infEDist_smul₀` / 定理 `infEDist_smul₀`

English:
theorem infEDist_smul₀
  given: {c : 𝕜} (hc : c != 0) (s : Set E) (x : E)
  proof: by
  simp_rw [infEDist]
  have : Function.Surjective ((c • ·) : E -> E) :=
    Function.RightInverse.surjective (smul_inv_smul₀ hc)
  trans ⨅ (y) (_ : y in s), ‖c‖₊ • edist x y
  · refine (this.iInf_congr _ fun y => ?_).symm
    simp_rw [smul_mem_smul_set_iff₀ hc, edist_smul₀]
  · have : (‖c‖₊ : ENNReal) != 0 := by simp [hc]
    simp_rw [ENNReal.smul_def, smul_eq_mul, ENNReal.mul_iInf_of_ne this ENNReal.coe_ne_top]

@[deprecated (since := "2026-01-08")] alias infEdist_smul₀ := infEDist_smul₀

中文:
定理 infEDist_smul₀
  条件: {c : 𝕜} (hc : c != 0) (s : 集合 E) (x : E)
  证明: by
  simp_rw [infEDist]
  have : Function.Surjective ((c • ·) : E -> E) :=
    Function.RightInverse.surjective (smul_inv_smul₀ hc)
  trans ⨅ (y) (_ : y in s), ‖c‖₊ • edist x y
  · refine (this.iInf_congr _ fun y => ?_).symm
    simp_rw [smul_mem_smul_set_iff₀ hc, edist_smul₀]
  · have : (‖c‖₊ : ENNReal) != 0 := by simp [hc]
    simp_rw [ENNReal.smul_def, smul_eq_mul, ENNReal.mul_iInf_of_ne this ENNReal.coe_ne_top]

@[deprecated (since := "2026-01-08")] alias infEdist_smul₀ := infEDist_smul₀

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.mul_iInf_of_ne, ENNReal.smul_def, Function, Function.RightInverse.surjective, Function.Surjective, RightInverse, Surjective, coe_ne_top, iInf_congr, infEDist, mul_iInf_of_ne, simp_rw, smul_def, smul_eq_mul, surjective, this.iInf_congr
-/
theorem infEDist_smul₀ {c : 𝕜} (hc : c != 0) (s : Set E) (x : E) :
    infEDist (c • x) (c • s) = ‖c‖₊ • infEDist x s := by
  simp_rw [infEDist]
  have : Function.Surjective ((c • ·) : E -> E) :=
    Function.RightInverse.surjective (smul_inv_smul₀ hc)
  trans ⨅ (y) (_ : y in s), ‖c‖₊ • edist x y
  · refine (this.iInf_congr _ fun y => ?_).symm
    simp_rw [smul_mem_smul_set_iff₀ hc, edist_smul₀]
  · have : (‖c‖₊ : ENNReal) != 0 := by simp [hc]
    simp_rw [ENNReal.smul_def, smul_eq_mul, ENNReal.mul_iInf_of_ne this ENNReal.coe_ne_top]

@[deprecated (since := "2026-01-08")] alias infEdist_smul₀ := infEDist_smul₀

/--
theorem `infDist_smul₀` / 定理 `infDist_smul₀`

English:
theorem infDist_smul₀
  given: {c : 𝕜} (hc : c != 0) (s : Set E) (x : E)
  proof: by
  simp_rw [Metric.infDist, infEDist_smul₀ hc s, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm,
    smul_eq_mul]

中文:
定理 infDist_smul₀
  条件: {c : 𝕜} (hc : c != 0) (s : 集合 E) (x : E)
  证明: by
  simp_rw [Metric.infDist, infEDist_smul₀ hc s, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm,
    smul_eq_mul]

Depends on / 依赖: ENNReal, ENNReal.toReal_smul, Metric, Metric.infDist, NNReal, NNReal.smul_def, coe_nnnorm, infDist, simp_rw, smul_def, smul_eq_mul, toReal_smul
-/
theorem infDist_smul₀ {c : 𝕜} (hc : c != 0) (s : Set E) (x : E) :
    Metric.infDist (c • x) (c • s) = ‖c‖ * Metric.infDist x s := by
  simp_rw [Metric.infDist, infEDist_smul₀ hc s, ENNReal.toReal_smul, NNReal.smul_def, coe_nnnorm,
    smul_eq_mul]

end DivisionRing


variable [NormedField 𝕜]

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `smul_ball` / 定理 `smul_ball`

English:
theorem smul_ball
  given: {c : 𝕜} (hc : c != 0) (x : E) (r : Real)
  statement: c • ball x r = ball (c • x) (‖c‖ * r)
  proof: by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hc), mul_comm _ r, dist_smul₀]

中文:
定理 smul_ball
  条件: {c : 𝕜} (hc : c != 0) (x : E) (r : 实数)
  结论: c • ball x r = ball (c • x) (‖c‖ * r)
  证明: by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hc), mul_comm _ r, dist_smul₀]

Depends on / 依赖: conv_lhs, div_eq_inv_mul, mul_comm, norm_pos_iff
-/
theorem smul_ball {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • ball x r = ball (c • x) (‖c‖ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp [← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hc), mul_comm _ r, dist_smul₀]

/--
theorem `smul_unitBall` / 定理 `smul_unitBall`

English:
theorem smul_unitBall
  given: {c : 𝕜} (hc : c != 0)
  statement: c • ball (0 : E) (1 : Real) = ball (0 : E) ‖c‖
  proof: by
  rw [_root_.smul_ball hc]; rw [smul_zero]; rw [mul_one]

中文:
定理 smul_unitBall
  条件: {c : 𝕜} (hc : c != 0)
  结论: c • ball (0 : E) (1 : 实数) = ball (0 : E) ‖c‖
  证明: by
  rw [_root_.smul_ball hc]; rw [smul_zero]; rw [mul_one]

Depends on / 依赖: _root_, _root_.smul_ball, mul_one, smul_ball, smul_zero
-/
theorem smul_unitBall {c : 𝕜} (hc : c != 0) : c • ball (0 : E) (1 : Real) = ball (0 : E) ‖c‖ := by
  rw [_root_.smul_ball hc]; rw [smul_zero]; rw [mul_one]

/--
theorem `smul_sphere'` / 定理 `smul_sphere'`

English:
theorem smul_sphere'
  given: {c : 𝕜} (hc : c != 0) (x : E) (r : Real)
  proof: by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [mem_sphere, dist_smul₀, norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne',
    mul_comm r]

中文:
定理 smul_sphere'
  条件: {c : 𝕜} (hc : c != 0) (x : E) (r : 实数)
  证明: by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [mem_sphere, dist_smul₀, norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne',
    mul_comm r]

Depends on / 依赖: conv_lhs, div_eq_iff, div_eq_inv_mul, mem_sphere, mul_comm, norm_inv, norm_pos_iff
-/
theorem smul_sphere' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) :
    c • sphere x r = sphere (c • x) (‖c‖ * r) := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hc]
  conv_lhs => rw [← inv_smul_smul₀ hc x]
  simp only [mem_sphere, dist_smul₀, norm_inv, ← div_eq_inv_mul, div_eq_iff (norm_pos_iff.2 hc).ne',
    mul_comm r]

/--
theorem `smul_closedBall'` / 定理 `smul_closedBall'`

English:
theorem smul_closedBall'
  given: {c : 𝕜} (hc : c != 0) (x : E) (r : Real)
  proof: by
  simp only [← ball_union_sphere, Set.smul_set_union, _root_.smul_ball hc, smul_sphere' hc]

中文:
定理 smul_closedBall'
  条件: {c : 𝕜} (hc : c != 0) (x : E) (r : 实数)
  证明: by
  simp only [← ball_union_sphere, Set.smul_set_union, _root_.smul_ball hc, smul_sphere' hc]

Depends on / 依赖: Set.smul_set_union, _root_, _root_.smul_ball, ball_union_sphere, smul_ball, smul_set_union, smul_sphere
-/
theorem smul_closedBall' {c : 𝕜} (hc : c != 0) (x : E) (r : Real) :
    c • closedBall x r = closedBall (c • x) (‖c‖ * r) := by
  simp only [← ball_union_sphere, Set.smul_set_union, _root_.smul_ball hc, smul_sphere' hc]

/--
theorem `set_smul_sphere_zero` / 定理 `set_smul_sphere_zero`

English:
theorem set_smul_sphere_zero
  given: {s : Set 𝕜} (hs : 0 ∉ s) (r : Real)
  proof: calc
    s • sphere (0 : E) r = ⋃ c in s, c • sphere (0 : E) r := iUnion_smul_left_image.symm
    _ = ⋃ c in s, sphere (0 : E) (‖c‖ * r) := iUnion₂_congr fun c hc => by
      rw [smul_sphere' (ne_of_mem_of_not_mem hc hs)]; rw [smul_zero]
    _ = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) := by ext; simp [eq_comm]

中文:
定理 set_smul_sphere_zero
  条件: {s : 集合 𝕜} (hs : 0 ∉ s) (r : 实数)
  证明: calc
    s • sphere (0 : E) r = ⋃ c in s, c • sphere (0 : E) r := iUnion_smul_left_image.symm
    _ = ⋃ c in s, sphere (0 : E) (‖c‖ * r) := iUnion₂_congr fun c hc => by
      rw [smul_sphere' (ne_of_mem_of_not_mem hc hs)]; rw [smul_zero]
    _ = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) := by ext; simp [eq_comm]

Depends on / 依赖: eq_comm, iUnion_smul_left_image, iUnion_smul_left_image.symm, ne_of_mem_of_not_mem, smul_sphere, smul_zero, sphere
-/
theorem set_smul_sphere_zero {s : Set 𝕜} (hs : 0 ∉ s) (r : Real) :
    s • sphere (0 : E) r = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) :=
  calc
    s • sphere (0 : E) r = ⋃ c in s, c • sphere (0 : E) r := iUnion_smul_left_image.symm
    _ = ⋃ c in s, sphere (0 : E) (‖c‖ * r) := iUnion₂_congr fun c hc => by
      rw [smul_sphere' (ne_of_mem_of_not_mem hc hs)]; rw [smul_zero]
    _ = (‖·‖) ⁻¹' ((‖·‖ * r) '' s) := by ext; simp [eq_comm]

/--
theorem `Bornology.IsBounded.smul₀` / 定理 `Bornology.IsBounded.smul₀`

English:
theorem Bornology.IsBounded.smul₀
  given: {s : Set E} (hs : IsBounded s) (c : 𝕜)
  statement: IsBounded (c • s)
  proof: (lipschitzWith_smul c).isBounded_image hs

中文:
定理 有界结构.IsBounded.smul₀
  条件: {s : 集合 E} (hs : IsBounded s) (c : 𝕜)
  结论: IsBounded (c • s)
  证明: (lipschitzWith_smul c).isBounded_image hs

Depends on / 依赖: isBounded_image, lipschitzWith_smul
-/
theorem Bornology.IsBounded.smul₀ {s : Set E} (hs : IsBounded s) (c : 𝕜) : IsBounded (c • s) :=
  (lipschitzWith_smul c).isBounded_image hs

/--
theorem `eventually_singleton_add_smul_subset` / 定理 `eventually_singleton_add_smul_subset`

English:
theorem eventually_singleton_add_smul_subset
  statement: {x : E} {s : Set E} (hs : Bornology.IsBounded s)
  proof: by
  obtain ⟨ε, εpos, hε⟩ : exists ε : Real, 0 < ε ∧ closedBall x ε subseteq u := nhds_basis_closedBall.mem_iff.1 hu
  obtain ⟨R, Rpos, hR⟩ : exists R : Real, 0 < R ∧ s subseteq closedBall 0 R := hs.subset_closedBall_lt 0 0
  have : Metric.closedBall (0 : 𝕜) (ε / R) in 𝓝 (0 : 𝕜) := closedBall_mem_nhds _ (div_pos εpos Rpos)
  filter_upwards [this] with r hr
  simp only [image_add_left, singleton_add]
  intro y hy
  obtain ⟨z, zs, hz⟩ : exists z : E, z in s ∧ r • z = -x + y := by simpa [mem_smul_set] using hy
  have I : ‖r • z‖ <= ε :=
    calc
      ‖r • z‖ = ‖r‖ * ‖z‖ := norm_smul _ _
      _ <= ε / R * R := by
        gcongr
        exacts [mem_closedBall_zero_iff.1 hr, mem_closedBall_zero_iff.1 (hR zs)]
      _ = ε := by field
  have : y = x + r • z := by simp only [hz, add_neg_cancel_left]
  apply hε
  simpa only [this, dist_eq_norm, add_sub_cancel_left, mem_closedBall] using I

中文:
定理 eventually_singleton_add_smul_subset
  结论: {x : E} {s : 集合 E} (hs : 有界结构.IsBounded s)
  证明: by
  obtain ⟨ε, εpos, hε⟩ : exists ε : Real, 0 < ε ∧ closedBall x ε subseteq u := nhds_basis_closedBall.mem_iff.1 hu
  obtain ⟨R, Rpos, hR⟩ : exists R : Real, 0 < R ∧ s subseteq closedBall 0 R := hs.subset_closedBall_lt 0 0
  have : Metric.closedBall (0 : 𝕜) (ε / R) in 𝓝 (0 : 𝕜) := closedBall_mem_nhds _ (div_pos εpos Rpos)
  filter_upwards [this] with r hr
  simp only [image_add_left, singleton_add]
  intro y hy
  obtain ⟨z, zs, hz⟩ : exists z : E, z in s ∧ r • z = -x + y := by simpa [mem_smul_set] using hy
  have I : ‖r • z‖ <= ε :=
    calc
      ‖r • z‖ = ‖r‖ * ‖z‖ := norm_smul _ _
      _ <= ε / R * R := by
        gcongr
        exacts [mem_closedBall_zero_iff.1 hr, mem_closedBall_zero_iff.1 (hR zs)]
      _ = ε := by field
  have : y = x + r • z := by simp only [hz, add_neg_cancel_left]
  apply hε
  simpa only [this, dist_eq_norm, add_sub_cancel_left, mem_closedBall] using I

Depends on / 依赖: Metric, Metric.closedBall, closedBall, closedBall_mem_nhds, div_pos, filter_upwards, hs.subset_closedBall_lt, image_add_left, mem_iff, mem_smul_set, nhds_basis_closedBall, nhds_basis_closedBall.mem_iff, singleton_add, subset_closedBall_lt, subseteq
-/
theorem eventually_singleton_add_smul_subset {x : E} {s : Set E} (hs : Bornology.IsBounded s)
    {u : Set E} (hu : u in 𝓝 x) : forallᶠ r in 𝓝 (0 : 𝕜), {x} + r • s subseteq u := by
  obtain ⟨ε, εpos, hε⟩ : exists ε : Real, 0 < ε ∧ closedBall x ε subseteq u := nhds_basis_closedBall.mem_iff.1 hu
  obtain ⟨R, Rpos, hR⟩ : exists R : Real, 0 < R ∧ s subseteq closedBall 0 R := hs.subset_closedBall_lt 0 0
  have : Metric.closedBall (0 : 𝕜) (ε / R) in 𝓝 (0 : 𝕜) := closedBall_mem_nhds _ (div_pos εpos Rpos)
  filter_upwards [this] with r hr
  simp only [image_add_left, singleton_add]
  intro y hy
  obtain ⟨z, zs, hz⟩ : exists z : E, z in s ∧ r • z = -x + y := by simpa [mem_smul_set] using hy
  have I : ‖r • z‖ <= ε :=
    calc
      ‖r • z‖ = ‖r‖ * ‖z‖ := norm_smul _ _
      _ <= ε / R * R := by
        gcongr
        exacts [mem_closedBall_zero_iff.1 hr, mem_closedBall_zero_iff.1 (hR zs)]
      _ = ε := by field
  have : y = x + r • z := by simp only [hz, add_neg_cancel_left]
  apply hε
  simpa only [this, dist_eq_norm, add_sub_cancel_left, mem_closedBall] using I

variable [NormedSpace Real E] {x y z : E} {δ ε : Real}

/--
theorem `smul_unitBall_of_pos` / 定理 `smul_unitBall_of_pos`

English:
theorem smul_unitBall_of_pos
  given: {r : Real} (hr : 0 < r)
  statement: r • ball (0 : E) 1 = ball (0 : E) r
  proof: by
  rw [smul_unitBall hr.ne']; rw [Real.norm_of_nonneg hr.le]

中文:
定理 smul_unitBall_of_pos
  条件: {r : 实数} (hr : 0 < r)
  结论: r • ball (0 : E) 1 = ball (0 : E) r
  证明: by
  rw [smul_unitBall hr.ne']; rw [Real.norm_of_nonneg hr.le]

Depends on / 依赖: Real.norm_of_nonneg, hr.le, hr.ne, norm_of_nonneg, smul_unitBall
-/
theorem smul_unitBall_of_pos {r : Real} (hr : 0 < r) : r • ball (0 : E) 1 = ball (0 : E) r := by
  rw [smul_unitBall hr.ne']; rw [Real.norm_of_nonneg hr.le]

/--
lemma `Ioo_smul_sphere_zero` / 引理 `Ioo_smul_sphere_zero`

English:
lemma Ioo_smul_sphere_zero
  given: {a b r : Real} (ha : 0 <= a) (hr : 0 < r)
  proof: by
  have : EqOn (‖·‖) id (Ioo a b) := fun x hx => abs_of_pos (ha.trans_lt hx.1)
  rw [set_smul_sphere_zero (by simp [ha.not_gt]), ← image_image (· * r), this.image_eq, image_id,
    image_mul_right_Ioo _ _ hr]
  ext x; simp [and_comm]

中文:
引理 Ioo_smul_sphere_zero
  条件: {a b r : 实数} (ha : 0 <= a) (hr : 0 < r)
  证明: by
  have : EqOn (‖·‖) id (Ioo a b) := fun x hx => abs_of_pos (ha.trans_lt hx.1)
  rw [set_smul_sphere_zero (by simp [ha.not_gt]), ← image_image (· * r), this.image_eq, image_id,
    image_mul_right_Ioo _ _ hr]
  ext x; simp [and_comm]

Depends on / 依赖: abs_of_pos, and_comm, ha.not_gt, ha.trans_lt, image_eq, image_id, image_image, image_mul_right_Ioo, not_gt, set_smul_sphere_zero, this.image_eq, trans_lt
-/
lemma Ioo_smul_sphere_zero {a b r : Real} (ha : 0 <= a) (hr : 0 < r) :
    Ioo a b • sphere (0 : E) r = ball 0 (b * r) \ closedBall 0 (a * r) := by
  have : EqOn (‖·‖) id (Ioo a b) := fun x hx => abs_of_pos (ha.trans_lt hx.1)
  rw [set_smul_sphere_zero (by simp [ha.not_gt]), ← image_image (· * r), this.image_eq, image_id,
    image_mul_right_Ioo _ _ hr]
  ext x; simp [and_comm]

-- This is also true for `ℚ`-normed spaces
/--
theorem `exists_dist_eq` / 定理 `exists_dist_eq`

English:
theorem exists_dist_eq
  given: (x z : E) {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  proof: by
  use a • x + b • z
  nth_rw 1 [← one_smul Real x]
  nth_rw 4 [← one_smul Real z]
  simp [dist_eq_norm, ← hab, add_smul, ← smul_sub, norm_smul_of_nonneg, ha, hb]

中文:
定理 存在_dist_eq
  条件: (x z : E) {a b : 实数} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
  证明: by
  use a • x + b • z
  nth_rw 1 [← one_smul Real x]
  nth_rw 4 [← one_smul Real z]
  simp [dist_eq_norm, ← hab, add_smul, ← smul_sub, norm_smul_of_nonneg, ha, hb]

Depends on / 依赖: add_smul, dist_eq_norm, norm_smul_of_nonneg, nth_rw, one_smul, smul_sub
-/
theorem exists_dist_eq (x z : E) {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    exists y, dist x y = b * dist x z ∧ dist y z = a * dist x z := by
  use a • x + b • z
  nth_rw 1 [← one_smul Real x]
  nth_rw 4 [← one_smul Real z]
  simp [dist_eq_norm, ← hab, add_smul, ← smul_sub, norm_smul_of_nonneg, ha, hb]

/--
theorem `exists_dist_le_le` / 定理 `exists_dist_le_le`

English:
theorem exists_dist_le_le
  given: (hδ : 0 <= δ) (hε : 0 <= ε) (h : dist x z <= ε + δ)
  proof: by
  obtain rfl | hε' := hε.eq_or_lt
  · exact ⟨z, by rwa [zero_add] at h, (dist_self _).le⟩
  have hεδ := add_pos_of_pos_of_nonneg hε' hδ
  refine (exists_dist_eq x z (div_nonneg hε <| add_nonneg hε hδ)
(div_nonneg hδ <| add_nonneg hε hδ) by
      rw [← add_div]; rw [div_self hεδ.ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_le_one hεδ] at h
  exact ⟨mul_le_of_le_one_left hδ h, mul_le_of_le_one_left hε h⟩

中文:
定理 存在_dist_le_le
  条件: (hδ : 0 <= δ) (hε : 0 <= ε) (h : dist x z <= ε + δ)
  证明: by
  obtain rfl | hε' := hε.eq_or_lt
  · exact ⟨z, by rwa [zero_add] at h, (dist_self _).le⟩
  have hεδ := add_pos_of_pos_of_nonneg hε' hδ
  refine (exists_dist_eq x z (div_nonneg hε <| add_nonneg hε hδ)
(div_nonneg hδ <| add_nonneg hε hδ) by
      rw [← add_div]; rw [div_self hεδ.ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_le_one hεδ] at h
  exact ⟨mul_le_of_le_one_left hδ h, mul_le_of_le_one_left hε h⟩

Depends on / 依赖: add_div, add_nonneg, add_pos_of_pos_of_nonneg, dist_self, div_le_one, div_mul_comm, div_nonneg, div_self, eq_or_lt, exists_dist_eq, mul_le_of_le_one_left, zero_add
-/
theorem exists_dist_le_le (hδ : 0 <= δ) (hε : 0 <= ε) (h : dist x z <= ε + δ) :
    exists y, dist x y <= δ ∧ dist y z <= ε := by
  obtain rfl | hε' := hε.eq_or_lt
  · exact ⟨z, by rwa [zero_add] at h, (dist_self _).le⟩
  have hεδ := add_pos_of_pos_of_nonneg hε' hδ
  refine (exists_dist_eq x z (div_nonneg hε <| add_nonneg hε hδ)
(div_nonneg hδ <| add_nonneg hε hδ) by
      rw [← add_div]; rw [div_self hεδ.ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_le_one hεδ] at h
  exact ⟨mul_le_of_le_one_left hδ h, mul_le_of_le_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
/--
theorem `exists_dist_le_lt` / 定理 `exists_dist_le_lt`

English:
theorem exists_dist_le_lt
  given: (hδ : 0 <= δ) (hε : 0 < ε) (h : dist x z < ε + δ)
  proof: by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ)
(div_nonneg hδ <| add_nonneg hε.le hδ) by
      rw [← add_div]; rw [div_self (add_pos_of_pos_of_nonneg hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_lt_one (add_pos_of_pos_of_nonneg hε hδ)] at h
  exact ⟨mul_le_of_le_one_left hδ h.le, mul_lt_of_lt_one_left hε h⟩

中文:
定理 存在_dist_le_lt
  条件: (hδ : 0 <= δ) (hε : 0 < ε) (h : dist x z < ε + δ)
  证明: by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ)
(div_nonneg hδ <| add_nonneg hε.le hδ) by
      rw [← add_div]; rw [div_self (add_pos_of_pos_of_nonneg hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_lt_one (add_pos_of_pos_of_nonneg hε hδ)] at h
  exact ⟨mul_le_of_le_one_left hδ h.le, mul_lt_of_lt_one_left hε h⟩

Depends on / 依赖: add_div, add_nonneg, add_pos_of_pos_of_nonneg, div_lt_one, div_mul_comm, div_nonneg, div_self, exists_dist_eq, h.le, mul_le_of_le_one_left, mul_lt_of_lt_one_left
-/
theorem exists_dist_le_lt (hδ : 0 <= δ) (hε : 0 < ε) (h : dist x z < ε + δ) :
    exists y, dist x y <= δ ∧ dist y z < ε := by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ)
(div_nonneg hδ <| add_nonneg hε.le hδ) by
      rw [← add_div]; rw [div_self (add_pos_of_pos_of_nonneg hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_lt_one (add_pos_of_pos_of_nonneg hε hδ)] at h
  exact ⟨mul_le_of_le_one_left hδ h.le, mul_lt_of_lt_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
/--
theorem `exists_dist_lt_le` / 定理 `exists_dist_lt_le`

English:
theorem exists_dist_lt_le
  given: (hδ : 0 < δ) (hε : 0 <= ε) (h : dist x z < ε + δ)
  proof: by
  obtain ⟨y, yz, xy⟩ :=
    exists_dist_le_lt hε hδ (show dist z x < δ + ε by simpa only [dist_comm, add_comm] using h)
  exact ⟨y, by simp [dist_comm x y, dist_comm y z, *]⟩

中文:
定理 存在_dist_lt_le
  条件: (hδ : 0 < δ) (hε : 0 <= ε) (h : dist x z < ε + δ)
  证明: by
  obtain ⟨y, yz, xy⟩ :=
    exists_dist_le_lt hε hδ (show dist z x < δ + ε by simpa only [dist_comm, add_comm] using h)
  exact ⟨y, by simp [dist_comm x y, dist_comm y z, *]⟩

Depends on / 依赖: add_comm, dist_comm, exists_dist_le_lt
-/
theorem exists_dist_lt_le (hδ : 0 < δ) (hε : 0 <= ε) (h : dist x z < ε + δ) :
    exists y, dist x y < δ ∧ dist y z <= ε := by
  obtain ⟨y, yz, xy⟩ :=
    exists_dist_le_lt hε hδ (show dist z x < δ + ε by simpa only [dist_comm, add_comm] using h)
  exact ⟨y, by simp [dist_comm x y, dist_comm y z, *]⟩

-- This is also true for `ℚ`-normed spaces
/--
theorem `exists_dist_lt_lt` / 定理 `exists_dist_lt_lt`

English:
theorem exists_dist_lt_lt
  given: (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ)
  proof: by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ.le)
(div_nonneg hδ.le <| add_nonneg hε.le hδ.le) by
      rw [← add_div]; rw [div_self (add_pos hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_lt_one (add_pos hε hδ)] at h
  exact ⟨mul_lt_of_lt_one_left hδ h, mul_lt_of_lt_one_left hε h⟩

中文:
定理 存在_dist_lt_lt
  条件: (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ)
  证明: by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ.le)
(div_nonneg hδ.le <| add_nonneg hε.le hδ.le) by
      rw [← add_div]; rw [div_self (add_pos hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_lt_one (add_pos hε hδ)] at h
  exact ⟨mul_lt_of_lt_one_left hδ h, mul_lt_of_lt_one_left hε h⟩

Depends on / 依赖: add_div, add_nonneg, add_pos, div_lt_one, div_mul_comm, div_nonneg, div_self, exists_dist_eq, mul_lt_of_lt_one_left
-/
theorem exists_dist_lt_lt (hδ : 0 < δ) (hε : 0 < ε) (h : dist x z < ε + δ) :
    exists y, dist x y < δ ∧ dist y z < ε := by
  refine (exists_dist_eq x z (div_nonneg hε.le <| add_nonneg hε.le hδ.le)
(div_nonneg hδ.le <| add_nonneg hε.le hδ.le) by
      rw [← add_div]; rw [div_self (add_pos hε hδ).ne']).imp
    fun y hy => ?_
  rw [hy.1]; rw [hy.2]; rw [div_mul_comm]; rw [div_mul_comm ε]
  rw [← div_lt_one (add_pos hε hδ)] at h
  exact ⟨mul_lt_of_lt_one_left hδ h, mul_lt_of_lt_one_left hε h⟩

-- This is also true for `ℚ`-normed spaces
/--
theorem `disjoint_ball_ball_iff` / 定理 `disjoint_ball_ball_iff`

English:
theorem disjoint_ball_ball_iff
  given: (hδ : 0 < δ) (hε : 0 < ε)
  proof: by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_ball⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_lt hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

中文:
定理 disjoint_ball_ball_iff
  条件: (hδ : 0 < δ) (hε : 0 < ε)
  证明: by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_ball⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_lt hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

Depends on / 依赖: add_comm, ball_disjoint_ball, dist_comm, exists_dist_lt_lt, h.le_bot, le_bot, le_of_not_gt
-/
theorem disjoint_ball_ball_iff (hδ : 0 < δ) (hε : 0 < ε) :
    Disjoint (ball x δ) (ball y ε) ↔ δ + ε <= dist x y := by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_ball⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_lt hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

-- This is also true for `ℚ`-normed spaces
/--
theorem `disjoint_ball_closedBall_iff` / 定理 `disjoint_ball_closedBall_iff`

English:
theorem disjoint_ball_closedBall_iff
  given: (hδ : 0 < δ) (hε : 0 <= ε)
  proof: by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

中文:
定理 disjoint_ball_closedBall_iff
  条件: (hδ : 0 < δ) (hε : 0 <= ε)
  证明: by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

Depends on / 依赖: add_comm, ball_disjoint_closedBall, dist_comm, exists_dist_lt_le, h.le_bot, le_bot, le_of_not_gt
-/
theorem disjoint_ball_closedBall_iff (hδ : 0 < δ) (hε : 0 <= ε) :
    Disjoint (ball x δ) (closedBall y ε) ↔ δ + ε <= dist x y := by
  refine ⟨fun h => le_of_not_gt fun hxy => ?_, ball_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_lt_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

-- This is also true for `ℚ`-normed spaces
/--
theorem `disjoint_closedBall_ball_iff` / 定理 `disjoint_closedBall_ball_iff`

English:
theorem disjoint_closedBall_ball_iff
  given: (hδ : 0 <= δ) (hε : 0 < ε)
  proof: by
  rw [disjoint_comm]; rw [disjoint_ball_closedBall_iff hε hδ]; rw [add_comm]; rw [dist_comm]

中文:
定理 disjoint_closedBall_ball_iff
  条件: (hδ : 0 <= δ) (hε : 0 < ε)
  证明: by
  rw [disjoint_comm]; rw [disjoint_ball_closedBall_iff hε hδ]; rw [add_comm]; rw [dist_comm]

Depends on / 依赖: add_comm, disjoint_ball_closedBall_iff, disjoint_comm, dist_comm
-/
theorem disjoint_closedBall_ball_iff (hδ : 0 <= δ) (hε : 0 < ε) :
    Disjoint (closedBall x δ) (ball y ε) ↔ δ + ε <= dist x y := by
  rw [disjoint_comm]; rw [disjoint_ball_closedBall_iff hε hδ]; rw [add_comm]; rw [dist_comm]

/--
theorem `disjoint_closedBall_closedBall_iff` / 定理 `disjoint_closedBall_closedBall_iff`

English:
theorem disjoint_closedBall_closedBall_iff
  given: (hδ : 0 <= δ) (hε : 0 <= ε)
  proof: by
  refine ⟨fun h => lt_of_not_ge fun hxy => ?_, closedBall_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_le_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

中文:
定理 disjoint_closedBall_closedBall_iff
  条件: (hδ : 0 <= δ) (hε : 0 <= ε)
  证明: by
  refine ⟨fun h => lt_of_not_ge fun hxy => ?_, closedBall_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_le_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

Depends on / 依赖: add_comm, closedBall_disjoint_closedBall, dist_comm, exists_dist_le_le, h.le_bot, le_bot, lt_of_not_ge
-/
theorem disjoint_closedBall_closedBall_iff (hδ : 0 <= δ) (hε : 0 <= ε) :
    Disjoint (closedBall x δ) (closedBall y ε) ↔ δ + ε < dist x y := by
  refine ⟨fun h => lt_of_not_ge fun hxy => ?_, closedBall_disjoint_closedBall⟩
  rw [add_comm] at hxy
  obtain ⟨z, hxz, hzy⟩ := exists_dist_le_le hδ hε hxy
  rw [dist_comm] at hxz
  exact h.le_bot ⟨hxz, hzy⟩

open EMetric ENNReal

@[simp]
/--
theorem `infEDist_thickening` / 定理 `infEDist_thickening`

English:
theorem infEDist_thickening
  given: (hδ : 0 < δ) (s : Set E) (x : E)
  proof: by
  obtain hs | hs := lt_or_ge (infEDist x s) (ENNReal.ofReal δ)
  · rw [infEDist_zero_of_mem, tsub_eq_zero_of_le hs.le]
    exact hs
  refine (tsub_le_iff_right.2 infEDist_le_infEDist_thickening_add).antisymm' ?_
  refine le_sub_of_add_le_right ofReal_ne_top ?_
  refine le_infEDist.2 fun z hz => le_of_forall_gt fun r h => ?_
  cases r with
  | top =>
exact add_lt_top.2 ⟨lt_top_iff_ne_top.2 infEDist_ne_top ⟨z, self_subset_thickening hδ _ hz⟩,
      ofReal_lt_top⟩
  | coe r =>
    have hr : 0 < ↑r - δ := by
      refine sub_pos_of_lt ?_
      have := hs.trans_lt ((infEDist_le_edist_of_mem hz).trans_lt h)
      rw [ofReal_eq_coe_nnreal hδ.le] at this
      exact mod_cast this
    rw [edist_lt_coe]; rw [← dist_lt_coe]; rw [← add_sub_cancel δ ↑r] at h
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hr hδ h
    refine (ENNReal.add_lt_add_right ofReal_ne_top <|
      infEDist_lt_iff.2 ⟨_, mem_thickening_iff.2 ⟨_, hz, hyz⟩, edist_lt_ofReal.2 hxy⟩).trans_le ?_
    rw [← ofReal_add hr.le hδ.le]; rw [sub_add_cancel]; rw [ofReal_coe_nnreal]

@[deprecated (since := "2026-01-08")]
alias infEdist_thickening := infEDist_thickening

@[simp]

中文:
定理 infEDist_thickening
  条件: (hδ : 0 < δ) (s : 集合 E) (x : E)
  证明: by
  obtain hs | hs := lt_or_ge (infEDist x s) (ENNReal.ofReal δ)
  · rw [infEDist_zero_of_mem, tsub_eq_zero_of_le hs.le]
    exact hs
  refine (tsub_le_iff_right.2 infEDist_le_infEDist_thickening_add).antisymm' ?_
  refine le_sub_of_add_le_right ofReal_ne_top ?_
  refine le_infEDist.2 fun z hz => le_of_forall_gt fun r h => ?_
  cases r with
  | top =>
exact add_lt_top.2 ⟨lt_top_iff_ne_top.2 infEDist_ne_top ⟨z, self_subset_thickening hδ _ hz⟩,
      ofReal_lt_top⟩
  | coe r =>
    have hr : 0 < ↑r - δ := by
      refine sub_pos_of_lt ?_
      have := hs.trans_lt ((infEDist_le_edist_of_mem hz).trans_lt h)
      rw [ofReal_eq_coe_nnreal hδ.le] at this
      exact mod_cast this
    rw [edist_lt_coe]; rw [← dist_lt_coe]; rw [← add_sub_cancel δ ↑r] at h
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hr hδ h
    refine (ENNReal.add_lt_add_right ofReal_ne_top <|
      infEDist_lt_iff.2 ⟨_, mem_thickening_iff.2 ⟨_, hz, hyz⟩, edist_lt_ofReal.2 hxy⟩).trans_le ?_
    rw [← ofReal_add hr.le hδ.le]; rw [sub_add_cancel]; rw [ofReal_coe_nnreal]

@[deprecated (since := "2026-01-08")]
alias infEdist_thickening := infEDist_thickening

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, add_lt_top, antisymm, hs.le, infEDist, infEDist_le_infEDist_thickening_add, infEDist_ne_top, infEDist_zero_of_mem, le_infEDist, le_of_forall_gt, le_sub_of_add_le_right, lt_or_ge, lt_top_iff_ne_top, ofReal, ofReal_lt_top, ofReal_ne_top, self_subset_thickening, sub_pos_of, tsub_eq_zero_of_le
-/
theorem infEDist_thickening (hδ : 0 < δ) (s : Set E) (x : E) :
    infEDist x (thickening δ s) = infEDist x s - ENNReal.ofReal δ := by
  obtain hs | hs := lt_or_ge (infEDist x s) (ENNReal.ofReal δ)
  · rw [infEDist_zero_of_mem, tsub_eq_zero_of_le hs.le]
    exact hs
  refine (tsub_le_iff_right.2 infEDist_le_infEDist_thickening_add).antisymm' ?_
  refine le_sub_of_add_le_right ofReal_ne_top ?_
  refine le_infEDist.2 fun z hz => le_of_forall_gt fun r h => ?_
  cases r with
  | top =>
exact add_lt_top.2 ⟨lt_top_iff_ne_top.2 infEDist_ne_top ⟨z, self_subset_thickening hδ _ hz⟩,
      ofReal_lt_top⟩
  | coe r =>
    have hr : 0 < ↑r - δ := by
      refine sub_pos_of_lt ?_
      have := hs.trans_lt ((infEDist_le_edist_of_mem hz).trans_lt h)
      rw [ofReal_eq_coe_nnreal hδ.le] at this
      exact mod_cast this
    rw [edist_lt_coe]; rw [← dist_lt_coe]; rw [← add_sub_cancel δ ↑r] at h
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hr hδ h
    refine (ENNReal.add_lt_add_right ofReal_ne_top <|
      infEDist_lt_iff.2 ⟨_, mem_thickening_iff.2 ⟨_, hz, hyz⟩, edist_lt_ofReal.2 hxy⟩).trans_le ?_
    rw [← ofReal_add hr.le hδ.le]; rw [sub_add_cancel]; rw [ofReal_coe_nnreal]

@[deprecated (since := "2026-01-08")]
alias infEdist_thickening := infEDist_thickening

@[simp]
/--
theorem `thickening_thickening` / 定理 `thickening_thickening`

English:
theorem thickening_thickening
  given: (hε : 0 < ε) (hδ : 0 < δ) (s : Set E)
  proof: (thickening_thickening_subset _ _ _).antisymm fun x => by
    simp_rw [mem_thickening_iff]
    rintro ⟨z, hz, hxz⟩
    rw [add_comm] at hxz
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hε hδ hxz
    exact ⟨y, ⟨_, hz, hyz⟩, hxy⟩

@[simp]

中文:
定理 thickening_thickening
  条件: (hε : 0 < ε) (hδ : 0 < δ) (s : 集合 E)
  证明: (thickening_thickening_subset _ _ _).antisymm fun x => by
    simp_rw [mem_thickening_iff]
    rintro ⟨z, hz, hxz⟩
    rw [add_comm] at hxz
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hε hδ hxz
    exact ⟨y, ⟨_, hz, hyz⟩, hxy⟩

@[simp]

Depends on / 依赖: add_comm, antisymm, exists_dist_lt_lt, mem_thickening_iff, simp_rw, thickening_thickening_subset
-/
theorem thickening_thickening (hε : 0 < ε) (hδ : 0 < δ) (s : Set E) :
    thickening ε (thickening δ s) = thickening (ε + δ) s :=
  (thickening_thickening_subset _ _ _).antisymm fun x => by
    simp_rw [mem_thickening_iff]
    rintro ⟨z, hz, hxz⟩
    rw [add_comm] at hxz
    obtain ⟨y, hxy, hyz⟩ := exists_dist_lt_lt hε hδ hxz
    exact ⟨y, ⟨_, hz, hyz⟩, hxy⟩

@[simp]
/--
theorem `cthickening_thickening` / 定理 `cthickening_thickening`

English:
theorem cthickening_thickening
  given: (hε : 0 <= ε) (hδ : 0 < δ) (s : Set E)
  proof: (cthickening_thickening_subset hε _ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ.le, infEDist_thickening hδ]
    exact tsub_le_iff_right.2

中文:
定理 cthickening_thickening
  条件: (hε : 0 <= ε) (hδ : 0 < δ) (s : 集合 E)
  证明: (cthickening_thickening_subset hε _ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ.le, infEDist_thickening hδ]
    exact tsub_le_iff_right.2

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, antisymm, cthickening_thickening_subset, infEDist_thickening, mem_cthickening_iff, ofReal_add, simp_rw, tsub_le_iff_right
-/
theorem cthickening_thickening (hε : 0 <= ε) (hδ : 0 < δ) (s : Set E) :
    cthickening ε (thickening δ s) = cthickening (ε + δ) s :=
  (cthickening_thickening_subset hε _ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ.le, infEDist_thickening hδ]
    exact tsub_le_iff_right.2

-- Note: `interior (cthickening δ s) ≠ thickening δ s` in general
@[simp]
/--
theorem `closure_thickening` / 定理 `closure_thickening`

English:
theorem closure_thickening
  given: (hδ : 0 < δ) (s : Set E)
  proof: by
  rw [← cthickening_zero]; rw [cthickening_thickening le_rfl hδ]; rw [zero_add]

@[simp]

中文:
定理 closure_thickening
  条件: (hδ : 0 < δ) (s : 集合 E)
  证明: by
  rw [← cthickening_zero]; rw [cthickening_thickening le_rfl hδ]; rw [zero_add]

@[simp]

Depends on / 依赖: cthickening_thickening, cthickening_zero, le_rfl, zero_add
-/
theorem closure_thickening (hδ : 0 < δ) (s : Set E) :
    closure (thickening δ s) = cthickening δ s := by
  rw [← cthickening_zero]; rw [cthickening_thickening le_rfl hδ]; rw [zero_add]

@[simp]
/--
theorem `infEDist_cthickening` / 定理 `infEDist_cthickening`

English:
theorem infEDist_cthickening
  given: (δ : Real) (s : Set E) (x : E)
  proof: by
  obtain hδ | hδ := le_or_gt δ 0
  · rw [cthickening_of_nonpos hδ, infEDist_closure, ofReal_of_nonpos hδ, tsub_zero]
  · rw [← closure_thickening hδ, infEDist_closure, infEDist_thickening hδ]

@[deprecated (since := "2026-01-08")]
alias infEdist_cthickening := infEDist_cthickening

@[simp]

中文:
定理 infEDist_cthickening
  条件: (δ : 实数) (s : 集合 E) (x : E)
  证明: by
  obtain hδ | hδ := le_or_gt δ 0
  · rw [cthickening_of_nonpos hδ, infEDist_closure, ofReal_of_nonpos hδ, tsub_zero]
  · rw [← closure_thickening hδ, infEDist_closure, infEDist_thickening hδ]

@[deprecated (since := "2026-01-08")]
alias infEdist_cthickening := infEDist_cthickening

@[simp]

Depends on / 依赖: closure_thickening, cthickening_of_nonpos, infEDist_closure, infEDist_thickening, le_or_gt, ofReal_of_nonpos, tsub_zero
-/
theorem infEDist_cthickening (δ : Real) (s : Set E) (x : E) :
    infEDist x (cthickening δ s) = infEDist x s - ENNReal.ofReal δ := by
  obtain hδ | hδ := le_or_gt δ 0
  · rw [cthickening_of_nonpos hδ, infEDist_closure, ofReal_of_nonpos hδ, tsub_zero]
  · rw [← closure_thickening hδ, infEDist_closure, infEDist_thickening hδ]

@[deprecated (since := "2026-01-08")]
alias infEdist_cthickening := infEDist_cthickening

@[simp]
/--
theorem `thickening_cthickening` / 定理 `thickening_cthickening`

English:
theorem thickening_cthickening
  given: (hε : 0 < ε) (hδ : 0 <= δ) (s : Set E)
  proof: by
  obtain rfl | hδ := hδ.eq_or_lt
  · rw [cthickening_zero, thickening_closure, add_zero]
  · rw [← closure_thickening hδ, thickening_closure, thickening_thickening hε hδ]

@[simp]

中文:
定理 thickening_cthickening
  条件: (hε : 0 < ε) (hδ : 0 <= δ) (s : 集合 E)
  证明: by
  obtain rfl | hδ := hδ.eq_or_lt
  · rw [cthickening_zero, thickening_closure, add_zero]
  · rw [← closure_thickening hδ, thickening_closure, thickening_thickening hε hδ]

@[simp]

Depends on / 依赖: add_zero, closure_thickening, cthickening_zero, eq_or_lt, thickening_closure, thickening_thickening
-/
theorem thickening_cthickening (hε : 0 < ε) (hδ : 0 <= δ) (s : Set E) :
    thickening ε (cthickening δ s) = thickening (ε + δ) s := by
  obtain rfl | hδ := hδ.eq_or_lt
  · rw [cthickening_zero, thickening_closure, add_zero]
  · rw [← closure_thickening hδ, thickening_closure, thickening_thickening hε hδ]

@[simp]
/--
theorem `cthickening_cthickening` / 定理 `cthickening_cthickening`

English:
theorem cthickening_cthickening
  given: (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set E)
  proof: (cthickening_cthickening_subset hε hδ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ, infEDist_cthickening]
    exact tsub_le_iff_right.2

@[simp]

中文:
定理 cthickening_cthickening
  条件: (hε : 0 <= ε) (hδ : 0 <= δ) (s : 集合 E)
  证明: (cthickening_cthickening_subset hε hδ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ, infEDist_cthickening]
    exact tsub_le_iff_right.2

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, antisymm, cthickening_cthickening_subset, infEDist_cthickening, mem_cthickening_iff, ofReal_add, simp_rw, tsub_le_iff_right
-/
theorem cthickening_cthickening (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set E) :
    cthickening ε (cthickening δ s) = cthickening (ε + δ) s :=
  (cthickening_cthickening_subset hε hδ _).antisymm fun x => by
    simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ, infEDist_cthickening]
    exact tsub_le_iff_right.2

@[simp]
/--
theorem `thickening_ball` / 定理 `thickening_ball`

English:
theorem thickening_ball
  given: (hε : 0 < ε) (hδ : 0 < δ) (x : E)
  proof: by
  rw [← thickening_singleton]; rw [thickening_thickening hε hδ]; rw [thickening_singleton]

@[simp]

中文:
定理 thickening_ball
  条件: (hε : 0 < ε) (hδ : 0 < δ) (x : E)
  证明: by
  rw [← thickening_singleton]; rw [thickening_thickening hε hδ]; rw [thickening_singleton]

@[simp]

Depends on / 依赖: thickening_singleton, thickening_thickening
-/
theorem thickening_ball (hε : 0 < ε) (hδ : 0 < δ) (x : E) :
    thickening ε (ball x δ) = ball x (ε + δ) := by
  rw [← thickening_singleton]; rw [thickening_thickening hε hδ]; rw [thickening_singleton]

@[simp]
/--
theorem `thickening_closedBall` / 定理 `thickening_closedBall`

English:
theorem thickening_closedBall
  given: (hε : 0 < ε) (hδ : 0 <= δ) (x : E)
  proof: by
  rw [← cthickening_singleton _ hδ]; rw [thickening_cthickening hε hδ]; rw [thickening_singleton]

@[simp]

中文:
定理 thickening_closedBall
  条件: (hε : 0 < ε) (hδ : 0 <= δ) (x : E)
  证明: by
  rw [← cthickening_singleton _ hδ]; rw [thickening_cthickening hε hδ]; rw [thickening_singleton]

@[simp]

Depends on / 依赖: cthickening_singleton, thickening_cthickening, thickening_singleton
-/
theorem thickening_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (x : E) :
    thickening ε (closedBall x δ) = ball x (ε + δ) := by
  rw [← cthickening_singleton _ hδ]; rw [thickening_cthickening hε hδ]; rw [thickening_singleton]

@[simp]
/--
theorem `cthickening_ball` / 定理 `cthickening_ball`

English:
theorem cthickening_ball
  given: (hε : 0 <= ε) (hδ : 0 < δ) (x : E)
  proof: by
  rw [← thickening_singleton]; rw [cthickening_thickening hε hδ]; rw [cthickening_singleton _ (add_nonneg hε hδ.le)]

@[simp]

中文:
定理 cthickening_ball
  条件: (hε : 0 <= ε) (hδ : 0 < δ) (x : E)
  证明: by
  rw [← thickening_singleton]; rw [cthickening_thickening hε hδ]; rw [cthickening_singleton _ (add_nonneg hε hδ.le)]

@[simp]

Depends on / 依赖: add_nonneg, cthickening_singleton, cthickening_thickening, thickening_singleton
-/
theorem cthickening_ball (hε : 0 <= ε) (hδ : 0 < δ) (x : E) :
    cthickening ε (ball x δ) = closedBall x (ε + δ) := by
  rw [← thickening_singleton]; rw [cthickening_thickening hε hδ]; rw [cthickening_singleton _ (add_nonneg hε hδ.le)]

@[simp]
/--
theorem `cthickening_closedBall` / 定理 `cthickening_closedBall`

English:
theorem cthickening_closedBall
  given: (hε : 0 <= ε) (hδ : 0 <= δ) (x : E)
  proof: by
  rw [← cthickening_singleton _ hδ]; rw [cthickening_cthickening hε hδ]; rw [cthickening_singleton _ (add_nonneg hε hδ)]

中文:
定理 cthickening_closedBall
  条件: (hε : 0 <= ε) (hδ : 0 <= δ) (x : E)
  证明: by
  rw [← cthickening_singleton _ hδ]; rw [cthickening_cthickening hε hδ]; rw [cthickening_singleton _ (add_nonneg hε hδ)]

Depends on / 依赖: add_nonneg, cthickening_cthickening, cthickening_singleton
-/
theorem cthickening_closedBall (hε : 0 <= ε) (hδ : 0 <= δ) (x : E) :
    cthickening ε (closedBall x δ) = closedBall x (ε + δ) := by
  rw [← cthickening_singleton _ hδ]; rw [cthickening_cthickening hε hδ]; rw [cthickening_singleton _ (add_nonneg hε hδ)]

/--
theorem `ball_add_ball` / 定理 `ball_add_ball`

English:
theorem ball_add_ball
  given: (hε : 0 < ε) (hδ : 0 < δ) (a b : E)
  proof: by
  rw [ball_add]; rw [thickening_ball hε hδ b]; rw [Metric.vadd_ball]; rw [vadd_eq_add]

中文:
定理 ball_add_ball
  条件: (hε : 0 < ε) (hδ : 0 < δ) (a b : E)
  证明: by
  rw [ball_add]; rw [thickening_ball hε hδ b]; rw [Metric.vadd_ball]; rw [vadd_eq_add]

Depends on / 依赖: Metric, Metric.vadd_ball, ball_add, thickening_ball, vadd_ball, vadd_eq_add
-/
theorem ball_add_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) :
    ball a ε + ball b δ = ball (a + b) (ε + δ) := by
  rw [ball_add]; rw [thickening_ball hε hδ b]; rw [Metric.vadd_ball]; rw [vadd_eq_add]

/--
theorem `ball_sub_ball` / 定理 `ball_sub_ball`

English:
theorem ball_sub_ball
  given: (hε : 0 < ε) (hδ : 0 < δ) (a b : E)
  proof: by
  simp_rw [sub_eq_add_neg, neg_ball, ball_add_ball hε hδ]

中文:
定理 ball_sub_ball
  条件: (hε : 0 < ε) (hδ : 0 < δ) (a b : E)
  证明: by
  simp_rw [sub_eq_add_neg, neg_ball, ball_add_ball hε hδ]

Depends on / 依赖: ball_add_ball, neg_ball, simp_rw, sub_eq_add_neg
-/
theorem ball_sub_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) :
    ball a ε - ball b δ = ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_ball, ball_add_ball hε hδ]

/--
theorem `ball_add_closedBall` / 定理 `ball_add_closedBall`

English:
theorem ball_add_closedBall
  given: (hε : 0 < ε) (hδ : 0 <= δ) (a b : E)
  proof: by
  rw [ball_add]; rw [thickening_closedBall hε hδ b]; rw [Metric.vadd_ball]; rw [vadd_eq_add]

中文:
定理 ball_add_closedBall
  条件: (hε : 0 < ε) (hδ : 0 <= δ) (a b : E)
  证明: by
  rw [ball_add]; rw [thickening_closedBall hε hδ b]; rw [Metric.vadd_ball]; rw [vadd_eq_add]

Depends on / 依赖: Metric, Metric.vadd_ball, ball_add, thickening_closedBall, vadd_ball, vadd_eq_add
-/
theorem ball_add_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (a b : E) :
    ball a ε + closedBall b δ = ball (a + b) (ε + δ) := by
  rw [ball_add]; rw [thickening_closedBall hε hδ b]; rw [Metric.vadd_ball]; rw [vadd_eq_add]

/--
theorem `ball_sub_closedBall` / 定理 `ball_sub_closedBall`

English:
theorem ball_sub_closedBall
  given: (hε : 0 < ε) (hδ : 0 <= δ) (a b : E)
  proof: by
  simp_rw [sub_eq_add_neg, neg_closedBall, ball_add_closedBall hε hδ]

中文:
定理 ball_sub_closedBall
  条件: (hε : 0 < ε) (hδ : 0 <= δ) (a b : E)
  证明: by
  simp_rw [sub_eq_add_neg, neg_closedBall, ball_add_closedBall hε hδ]

Depends on / 依赖: ball_add_closedBall, neg_closedBall, simp_rw, sub_eq_add_neg
-/
theorem ball_sub_closedBall (hε : 0 < ε) (hδ : 0 <= δ) (a b : E) :
    ball a ε - closedBall b δ = ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_closedBall, ball_add_closedBall hε hδ]

/--
theorem `closedBall_add_ball` / 定理 `closedBall_add_ball`

English:
theorem closedBall_add_ball
  given: (hε : 0 <= ε) (hδ : 0 < δ) (a b : E)
  proof: by
  rw [add_comm]; rw [ball_add_closedBall hδ hε b]; rw [add_comm]; rw [add_comm δ]

中文:
定理 closedBall_add_ball
  条件: (hε : 0 <= ε) (hδ : 0 < δ) (a b : E)
  证明: by
  rw [add_comm]; rw [ball_add_closedBall hδ hε b]; rw [add_comm]; rw [add_comm δ]

Depends on / 依赖: add_comm, ball_add_closedBall
-/
theorem closedBall_add_ball (hε : 0 <= ε) (hδ : 0 < δ) (a b : E) :
    closedBall a ε + ball b δ = ball (a + b) (ε + δ) := by
  rw [add_comm]; rw [ball_add_closedBall hδ hε b]; rw [add_comm]; rw [add_comm δ]

/--
theorem `closedBall_sub_ball` / 定理 `closedBall_sub_ball`

English:
theorem closedBall_sub_ball
  given: (hε : 0 <= ε) (hδ : 0 < δ) (a b : E)
  proof: by
  simp_rw [sub_eq_add_neg, neg_ball, closedBall_add_ball hε hδ]

中文:
定理 closedBall_sub_ball
  条件: (hε : 0 <= ε) (hδ : 0 < δ) (a b : E)
  证明: by
  simp_rw [sub_eq_add_neg, neg_ball, closedBall_add_ball hε hδ]

Depends on / 依赖: closedBall_add_ball, neg_ball, simp_rw, sub_eq_add_neg
-/
theorem closedBall_sub_ball (hε : 0 <= ε) (hδ : 0 < δ) (a b : E) :
    closedBall a ε - ball b δ = ball (a - b) (ε + δ) := by
  simp_rw [sub_eq_add_neg, neg_ball, closedBall_add_ball hε hδ]

/--
theorem `closedBall_add_closedBall` / 定理 `closedBall_add_closedBall`

English:
theorem closedBall_add_closedBall
  given: [ProperSpace E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b : E)
  proof: by
  rw [(isCompact_closedBall _ _).add_closedBall hδ b]; rw [cthickening_closedBall hδ hε a]; rw [Metric.vadd_closedBall]; rw [vadd_eq_add]; rw [add_comm]; rw [add_comm δ]

中文:
定理 closedBall_add_closedBall
  条件: [真空间 E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b : E)
  证明: by
  rw [(isCompact_closedBall _ _).add_closedBall hδ b]; rw [cthickening_closedBall hδ hε a]; rw [Metric.vadd_closedBall]; rw [vadd_eq_add]; rw [add_comm]; rw [add_comm δ]

Depends on / 依赖: Metric, Metric.vadd_closedBall, add_closedBall, add_comm, cthickening_closedBall, isCompact_closedBall, vadd_closedBall, vadd_eq_add
-/
theorem closedBall_add_closedBall [ProperSpace E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b : E) :
    closedBall a ε + closedBall b δ = closedBall (a + b) (ε + δ) := by
  rw [(isCompact_closedBall _ _).add_closedBall hδ b]; rw [cthickening_closedBall hδ hε a]; rw [Metric.vadd_closedBall]; rw [vadd_eq_add]; rw [add_comm]; rw [add_comm δ]

/--
theorem `closedBall_sub_closedBall` / 定理 `closedBall_sub_closedBall`

English:
theorem closedBall_sub_closedBall
  given: [ProperSpace E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b : E)
  proof: by
  rw [sub_eq_add_neg]; rw [neg_closedBall]; rw [closedBall_add_closedBall hε hδ]; rw [sub_eq_add_neg]

中文:
定理 closedBall_sub_closedBall
  条件: [真空间 E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b : E)
  证明: by
  rw [sub_eq_add_neg]; rw [neg_closedBall]; rw [closedBall_add_closedBall hε hδ]; rw [sub_eq_add_neg]

Depends on / 依赖: closedBall_add_closedBall, neg_closedBall, sub_eq_add_neg
-/
theorem closedBall_sub_closedBall [ProperSpace E] (hε : 0 <= ε) (hδ : 0 <= δ) (a b : E) :
    closedBall a ε - closedBall b δ = closedBall (a - b) (ε + δ) := by
  rw [sub_eq_add_neg]; rw [neg_closedBall]; rw [closedBall_add_closedBall hε hδ]; rw [sub_eq_add_neg]

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `smul_closedBall` / 定理 `smul_closedBall`

English:
theorem smul_closedBall
  given: (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [hr, zero_smul_set, Set.singleton_zero, nonempty_closedBall]
  · exact smul_closedBall' hc x r

中文:
定理 smul_closedBall
  条件: (c : 𝕜) (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [hr, zero_smul_set, Set.singleton_zero, nonempty_closedBall]
  · exact smul_closedBall' hc x r

Depends on / 依赖: Set.singleton_zero, eq_or_ne, nonempty_closedBall, singleton_zero, smul_closedBall, zero_smul_set
-/
theorem smul_closedBall (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r) :
    c • closedBall x r = closedBall (c • x) (‖c‖ * r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [hr, zero_smul_set, Set.singleton_zero, nonempty_closedBall]
  · exact smul_closedBall' hc x r

/--
theorem `smul_unitClosedBall` / 定理 `smul_unitClosedBall`

English:
theorem smul_unitClosedBall
  given: (c : 𝕜)
  statement: c • closedBall (0 : E) (1 : Real) = closedBall (0 : E) ‖c‖
  proof: by
  rw [_root_.smul_closedBall _ _ zero_le_one]; rw [smul_zero]; rw [mul_one]

中文:
定理 smul_unitClosedBall
  条件: (c : 𝕜)
  结论: c • closedBall (0 : E) (1 : 实数) = closedBall (0 : E) ‖c‖
  证明: by
  rw [_root_.smul_closedBall _ _ zero_le_one]; rw [smul_zero]; rw [mul_one]

Depends on / 依赖: _root_, _root_.smul_closedBall, mul_one, smul_closedBall, smul_zero, zero_le_one
-/
theorem smul_unitClosedBall (c : 𝕜) : c • closedBall (0 : E) (1 : Real) = closedBall (0 : E) ‖c‖ := by
  rw [_root_.smul_closedBall _ _ zero_le_one]; rw [smul_zero]; rw [mul_one]

variable [NormedSpace Real E]

/--
theorem `smul_unitClosedBall_of_nonneg` / 定理 `smul_unitClosedBall_of_nonneg`

English:
theorem smul_unitClosedBall_of_nonneg
  given: {r : Real} (hr : 0 <= r)
  proof: by
  rw [smul_unitClosedBall]; rw [Real.norm_of_nonneg hr]

中文:
定理 smul_unitClosedBall_of_nonneg
  条件: {r : 实数} (hr : 0 <= r)
  证明: by
  rw [smul_unitClosedBall]; rw [Real.norm_of_nonneg hr]

Depends on / 依赖: Real.norm_of_nonneg, norm_of_nonneg, smul_unitClosedBall
-/
theorem smul_unitClosedBall_of_nonneg {r : Real} (hr : 0 <= r) :
    r • closedBall (0 : E) 1 = closedBall (0 : E) r := by
  rw [smul_unitClosedBall]; rw [Real.norm_of_nonneg hr]

/--
theorem `smul_sphere` / 定理 `smul_sphere`

English:
theorem smul_sphere
  given: [Nontrivial E] (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [zero_smul_set, Set.singleton_zero, hr]
  · exact smul_sphere' hc x r

中文:
定理 smul_sphere
  条件: [非平凡 E] (c : 𝕜) (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [zero_smul_set, Set.singleton_zero, hr]
  · exact smul_sphere' hc x r

Depends on / 依赖: Set.singleton_zero, eq_or_ne, singleton_zero, smul_sphere, zero_smul_set
-/
theorem smul_sphere [Nontrivial E] (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r) :
    c • sphere x r = sphere (c • x) (‖c‖ * r) := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp [zero_smul_set, Set.singleton_zero, hr]
  · exact smul_sphere' hc x r

/--
theorem `affinity_unitBall` / 定理 `affinity_unitBall`

English:
theorem affinity_unitBall
  given: {r : Real} (hr : 0 < r) (x : E)
  statement: x +ᵥ r • ball (0 : E) 1 = ball x r
  proof: by
  rw [smul_unitBall_of_pos hr]; rw [vadd_ball_zero]

中文:
定理 affinity_unitBall
  条件: {r : 实数} (hr : 0 < r) (x : E)
  结论: x +ᵥ r • ball (0 : E) 1 = ball x r
  证明: by
  rw [smul_unitBall_of_pos hr]; rw [vadd_ball_zero]

Depends on / 依赖: smul_unitBall_of_pos, vadd_ball_zero
-/
theorem affinity_unitBall {r : Real} (hr : 0 < r) (x : E) : x +ᵥ r • ball (0 : E) 1 = ball x r := by
  rw [smul_unitBall_of_pos hr]; rw [vadd_ball_zero]

/--
theorem `affinity_unitClosedBall` / 定理 `affinity_unitClosedBall`

English:
theorem affinity_unitClosedBall
  given: {r : Real} (hr : 0 <= r) (x : E)
  proof: by
  rw [smul_unitClosedBall]; rw [Real.norm_of_nonneg hr]; rw [vadd_closedBall_zero]

中文:
定理 affinity_unitClosedBall
  条件: {r : 实数} (hr : 0 <= r) (x : E)
  证明: by
  rw [smul_unitClosedBall]; rw [Real.norm_of_nonneg hr]; rw [vadd_closedBall_zero]

Depends on / 依赖: Real.norm_of_nonneg, norm_of_nonneg, smul_unitClosedBall, vadd_closedBall_zero
-/
theorem affinity_unitClosedBall {r : Real} (hr : 0 <= r) (x : E) :
    x +ᵥ r • closedBall (0 : E) 1 = closedBall x r := by
  rw [smul_unitClosedBall]; rw [Real.norm_of_nonneg hr]; rw [vadd_closedBall_zero]

end NormedAddCommGroup
