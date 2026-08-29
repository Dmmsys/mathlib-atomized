/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Uniform convergence of Eisenstein series

We show that the sum of `eisSummand` converges locally uniformly on `ℍ` to the Eisenstein series
of weight `k` and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.

## Outline of argument

The key lemma `r_mul_max_le` shows that, for `z ∈ ℍ` and `c, d ∈ ℤ` (not both zero),
`|c z + d|` is bounded below by `r z * max (|c|, |d|)`, where `r z` is an explicit function of `z`
(independent of `c, d`) satisfying `0 < r z < 1` for all `z`.

We then show in `summable_one_div_rpow_max` that the sum of `max (|c|, |d|) ^ (-k)` over
`(c, d) ∈ ℤ × ℤ` is convergent for `2 < k`. This is proved by decomposing `ℤ × ℤ` using the
`Finset.box` lemmas.
-/

public section

noncomputable section

open Complex UpperHalfPlane Set Finset CongruenceSubgroup Topology

open scoped UpperHalfPlane

variable (z : ℍ)

namespace EisensteinSeries

/--
theorem `eisensteinSeries_tendstoLocallyUniformly` / 定理 `eisensteinSeries_tendstoLocallyUniformly`

English:
theorem eisensteinSeries_tendstoLocallyUniformly
  given: {k : Int} (hk : 3 <= k) {N : Nat} (a : Fin 2 -> ZMod N)
  proof: by
  have hk' : (2 : Real) < k := by norm_cast
  have p_sum : Summable fun x : gammaSet N 1 a => ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (· in gammaSet N 1 a)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, eisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB,

中文:
定理 eisensteinSeries_tendstoLocallyUniformly
  条件: {k : 整数} (hk : 3 <= k) {N : 自然数} (a : 有限集 2 -> ZMod N)
  证明: by
  have hk' : (2 : Real) < k := by norm_cast
  have p_sum : Summable fun x : gammaSet N 1 a => ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (· in gammaSet N 1 a)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, eisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB,

Depends on / 依赖: Summable, eisSummand, eisensteinSeries, gammaSet, mod_cast, mul_left, norm_, one_div, p_sum, p_sum.mul_left, subset_verticalStrip_of_isCompact, subtype, summable_one_div_norm_rpow, tendstoLocallyUniformly_iff_forall_isCompact, tendstoUniformlyOn_tsum, x.val, zpow_neg
-/
theorem eisensteinSeries_tendstoLocallyUniformly {k : Int} (hk : 3 <= k) {N : Nat} (a : Fin 2 -> ZMod N) :
    TendstoLocallyUniformly (fun (s : Finset (gammaSet N 1 a)) => (∑ x in s, eisSummand k x ·))
      (eisensteinSeries a k ·) Filter.atTop := by
  have hk' : (2 : Real) < k := by norm_cast
  have p_sum : Summable fun x : gammaSet N 1 a => ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (· in gammaSet N 1 a)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, eisensteinSeries]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : Real))
    (fun p z hz => ?_)).mono HABK
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p hB hz

/--
lemma `eisensteinSeries_tendstoLocallyUniformlyOn` / 引理 `eisensteinSeries_tendstoLocallyUniformlyOn`

English:
lemma eisensteinSeries_tendstoLocallyUniformlyOn
  statement: {k : Int} {N : Nat} (hk : 3 <= k)
  proof: by
  rw [← upperHalfPlaneSet]; rw [← range_coe]; rw [← image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinSeries_tendstoLocallyUniformly hk
  · simp only [Is

中文:
引理 eisensteinSeries_tendstoLocallyUniformlyOn
  结论: {k : 整数} {N : 自然数} (hk : 3 <= k)
  证明: by
  rw [← upperHalfPlaneSet]; rw [← range_coe]; rw [← image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinSeries_tendstoLocallyUniformly hk
  · simp only [Is

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.toOpenPartialHomeomorph_target, OpenPartialHomeomorph, OpenPartialHomeomorph.continuousOn_symm, Set.mem_univ, Set.top_eq_univ, TendstoLocallyUniformlyOn, TendstoLocallyUniformlyOn.comp, continuousOn_symm, eisensteinSeries_tendstoLocallyUniformly, forall_const, image_univ, mapsTo_range_iff, mem_univ, range_coe, tendstoLocallyUniformlyOn_univ, toOpenPartialHomeomorph_target, top_eq_univ, upperHalfPlaneSet
-/
lemma eisensteinSeries_tendstoLocallyUniformlyOn {k : Int} {N : Nat} (hk : 3 <= k)
    (a : Fin 2 -> ZMod N) : TendstoLocallyUniformlyOn (fun (s : Finset (gammaSet N 1 a)) =>
      ↑ₕ(fun (z : ℍ) => ∑ x in s, eisSummand k x z)) (↑ₕ(eisensteinSeriesSIF a k))
          Filter.atTop {z : Complex | 0 < z.im} := by
  rw [← upperHalfPlaneSet]; rw [← range_coe]; rw [← image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinSeries_tendstoLocallyUniformly hk
  · simp only [IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ, mapsTo_range_iff,
    Set.mem_univ, forall_const]

end EisensteinSeries
