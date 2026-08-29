/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Proper nontrivially normed fields

Nontrivially normed fields are `ProperSpaces` when they are `WeaklyLocallyCompact`.

## Main results

* `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`

## Implementation details

This is a special case of `ProperSpace.of_locallyCompactSpace` from
`Mathlib/Analysis/Normed/Module/FiniteDimension.lean`, specialized to be on the field itself
with a proof that requires fewer imports.
-/

public section

assert_not_exists FiniteDimensional

open Metric Filter

/--
lemma `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace` / 引理 `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`

English:
lemma ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
  proof: by
  rcases exists_isCompact_closedBall (0 : 𝕜) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC n : IsCompact (closedBall (0 : 𝕜) (‖c‖ ^ n * r)) := by
have : c ^ n != 0 := pow_ne_zero _ fun h => by simp [h, zero_le_one.not_gt] at hc
    convert! hr.smul (c ^ n)
    ext
    simp only [mem_closedBall, dist_zero_right, Set.mem_smul_set_iff_inv_smul_mem₀ this,
      smul_eq_mul, norm_mul, norm_inv, norm_pow,
      inv_mul_le_iff₀ (by simpa only [norm_pow] using norm_pos_iff.mpr this)]
  have hTop : Tendsto (fun n => ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)

中文:
引理 真空间.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
  证明: by
  rcases exists_isCompact_closedBall (0 : 𝕜) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC n : IsCompact (closedBall (0 : 𝕜) (‖c‖ ^ n * r)) := by
have : c ^ n != 0 := pow_ne_zero _ fun h => by simp [h, zero_le_one.not_gt] at hc
    convert! hr.smul (c ^ n)
    ext
    simp only [mem_closedBall, dist_zero_right, Set.mem_smul_set_iff_inv_smul_mem₀ this,
      smul_eq_mul, norm_mul, norm_inv, norm_pow,
      inv_mul_le_iff₀ (by simpa only [norm_pow] using norm_pos_iff.mpr this)]
  have hTop : Tendsto (fun n => ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)

Depends on / 依赖: IsCompact, NormedField, NormedField.exists_one_lt_norm, Set.mem_smul_set_iff_inv_smul_mem, closedBall, convert, dist_zero_right, exists_isCompact_closedBall, exists_one_lt_norm, hr.smul, mem_closedBall, norm_inv, norm_mul, norm_pos_iff, norm_pos_iff.mpr, norm_pow, not_gt, pow_ne_zero, smul_eq_mul, zero_le_one
-/
lemma ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [WeaklyLocallyCompactSpace 𝕜] :
    ProperSpace 𝕜 := by
  rcases exists_isCompact_closedBall (0 : 𝕜) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC n : IsCompact (closedBall (0 : 𝕜) (‖c‖ ^ n * r)) := by
have : c ^ n != 0 := pow_ne_zero _ fun h => by simp [h, zero_le_one.not_gt] at hc
    convert! hr.smul (c ^ n)
    ext
    simp only [mem_closedBall, dist_zero_right, Set.mem_smul_set_iff_inv_smul_mem₀ this,
      smul_eq_mul, norm_mul, norm_inv, norm_pow,
      inv_mul_le_iff₀ (by simpa only [norm_pow] using norm_pos_iff.mpr this)]
  have hTop : Tendsto (fun n => ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)
