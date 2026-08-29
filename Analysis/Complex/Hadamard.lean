/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Hadamard three-lines Theorem

In this file we present a proof of Hadamard's three-lines Theorem.

## Main result

- `norm_le_interp_of_mem_verticalClosedStrip` :
  Hadamard three-line theorem: If `f` is a bounded function, continuous on
  `re ⁻¹' [l, u]` and differentiable on `re ⁻¹' (l, u)`, then for
  `M(x) := sup ((norm ∘ f) '' re ⁻¹' {x})`, that is `M(x)` is the supremum of the absolute value
  of `f` along the vertical lines `re z = x`, we have that `∀ z ∈ re ⁻¹' [l, u]` the inequality
  `‖f(z)‖ ≤ M(0) ^ (1 - ((z.re - l) / (u - l))) * M(1) ^ ((z.re - l) / (u - l))` holds.
  This can be seen to be equivalent to the statement
  that `log M(re z)` is a convex function on `[0, 1]`.

- `norm_le_interp_of_mem_verticalClosedStrip'` :
  Variant of the above lemma in simpler terms. In particular, it makes no mention of the helper
  functions defined in this file.

## Main definitions

- `Complex.HadamardThreeLines.verticalStrip` :
    The vertical strip defined by : `re ⁻¹' Ioo a b`

- `Complex.HadamardThreeLines.verticalClosedStrip` :
    The vertical strip defined by : `re ⁻¹' Icc a b`

- `Complex.HadamardThreeLines.sSupNormIm` :
    The supremum function on vertical lines defined by : `sSup {|f(z)| : z.re = x}`

- `Complex.HadamardThreeLines.interpStrip` :
    The interpolation between the `sSupNormIm` on the edges of the vertical strip `re⁻¹ [0, 1]`.

- `Complex.HadamardThreeLines.interpStrip` :
    The interpolation between the `sSupNormIm` on the edges of any vertical strip.

- `Complex.HadamardThreeLines.invInterpStrip` :
    Inverse of the interpolation between the `sSupNormIm` on the edges of the
    vertical strip `re⁻¹ [0, 1]`.

- `Complex.HadamardThreeLines.F` :
    Function defined by `f` times `invInterpStrip`. Convenient form for proofs.

## Note

The proof follows from Phragmén-Lindelöf when both frontiers are not everywhere zero.
We then use a limit argument to cover the case when either of the sides are `0`.
-/

@[expose] public section


open Set Filter Function Complex Topology

namespace Complex
namespace HadamardThreeLines

/--
Definition of `verticalStrip` / `verticalStrip` 的定义

English:
definition verticalStrip
  signature: (a : Real) (b : Real)
  body: re ⁻¹' Ioo a b

中文:
定义 verticalStrip
  签名: (a : 实数) (b : 实数)
  定义体: re ⁻¹' Ioo a b
-/
def verticalStrip (a : Real) (b : Real) : Set Complex := re ⁻¹' Ioo a b

/--
Definition of `verticalClosedStrip` / `verticalClosedStrip` 的定义

English:
definition verticalClosedStrip
  signature: (a : Real) (b : Real)
  body: re ⁻¹' Icc a b

中文:
定义 verticalClosedStrip
  签名: (a : 实数) (b : 实数)
  定义体: re ⁻¹' Icc a b
-/
def verticalClosedStrip (a : Real) (b : Real) : Set Complex := re ⁻¹' Icc a b

/--
Definition of `sSupNormIm` / `sSupNormIm` 的定义

English:
definition sSupNormIm
  signature: {E : Type*} [NormedAddCommGroup E]
  body: sSup ((norm ∘ f) '' re ⁻¹' {x})

中文:
定义 sSupNormIm
  签名: {E : 类型} [赋范交换加群 E]
  定义体: sSup ((norm ∘ f) '' re ⁻¹' {x})
-/
noncomputable def sSupNormIm {E : Type*} [NormedAddCommGroup E]
    (f : Complex -> E) (x : Real) : Real :=
  sSup ((norm ∘ f) '' re ⁻¹' {x})

section invInterpStrip

variable {E : Type*} [NormedAddCommGroup E] (f : Complex -> E) (z : Complex)

/--
Definition of `invInterpStrip` / `invInterpStrip` 的定义

English:
definition invInterpStrip
  signature: (ε : Real)
  body: (ε + sSupNormIm f 0) ^ (z - 1) * (ε + sSupNormIm f 1) ^ (-z)

中文:
定义 inv整数erpStrip
  签名: (ε : 实数)
  定义体: (ε + sSupNormIm f 0) ^ (z - 1) * (ε + sSupNormIm f 1) ^ (-z)

Depends on / 依赖: sSupNormIm
-/
noncomputable def invInterpStrip (ε : Real) : Complex :=
  (ε + sSupNormIm f 0) ^ (z - 1) * (ε + sSupNormIm f 1) ^ (-z)

/--
Definition of `F` / `F` 的定义

English:
definition F
  signature: [NormedSpace Complex E] (ε : Real)
  body: fun z => invInterpStrip f z ε • f z

中文:
定义 F
  签名: [赋范空间 复形 E] (ε : 实数)
  定义体: fun z => invInterpStrip f z ε • f z

Depends on / 依赖: invInterpStrip
-/
noncomputable def F [NormedSpace Complex E] (ε : Real) := fun z => invInterpStrip f z ε • f z

/--
lemma `sSupNormIm_nonneg` / 引理 `sSupNormIm_nonneg`

English:
lemma sSupNormIm_nonneg
  given: (x : Real)
  statement: 0 <= sSupNormIm f x
  proof: by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

中文:
引理 sSupNormIm_nonneg
  条件: (x : 实数)
  结论: 0 <= sSupNormIm f x
  证明: by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

Depends on / 依赖: Real.sSup_nonneg, norm_nonneg, sSup_nonneg
-/
lemma sSupNormIm_nonneg (x : Real) : 0 <= sSupNormIm f x := by
  apply Real.sSup_nonneg
  rintro y ⟨z1, _, hz2⟩
  simp only [← hz2, comp, norm_nonneg]

/--
lemma `sSupNormIm_eps_pos` / 引理 `sSupNormIm_eps_pos`

English:
lemma sSupNormIm_eps_pos
  given: {ε : Real} (hε : ε > 0) (x : Real)
  statement: 0 < ε + sSupNormIm f x
  proof: by
  linarith [sSupNormIm_nonneg f x]

中文:
引理 sSupNormIm_eps_pos
  条件: {ε : 实数} (hε : ε > 0) (x : 实数)
  结论: 0 < ε + sSupNormIm f x
  证明: by
  linarith [sSupNormIm_nonneg f x]

Depends on / 依赖: sSupNormIm_nonneg
-/
lemma sSupNormIm_eps_pos {ε : Real} (hε : ε > 0) (x : Real) : 0 < ε + sSupNormIm f x := by
  linarith [sSupNormIm_nonneg f x]

/--
lemma `norm_invInterpStrip` / 引理 `norm_invInterpStrip`

English:
lemma norm_invInterpStrip
  given: {ε : Real} (hε : ε > 0)
  proof: by
  simp only [invInterpStrip, norm_mul]
  repeat rw [← ofReal_add]
  repeat rw [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp

中文:
引理 norm_inv整数erpStrip
  条件: {ε : 实数} (hε : ε > 0)
  证明: by
  simp only [invInterpStrip, norm_mul]
  repeat rw [← ofReal_add]
  repeat rw [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp

Depends on / 依赖: invInterpStrip, norm_cpow_eq_rpow_re_of_pos, norm_mul, ofReal_add, repeat, sSupNormIm_eps_pos
-/
lemma norm_invInterpStrip {ε : Real} (hε : ε > 0) :
    ‖invInterpStrip f z ε‖ =
    (ε + sSupNormIm f 0) ^ (z.re - 1) * (ε + sSupNormIm f 1) ^ (-z.re) := by
  simp only [invInterpStrip, norm_mul]
  repeat rw [← ofReal_add]
  repeat rw [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _]
  simp

/--
lemma `diffContOnCl_invInterpStrip` / 引理 `diffContOnCl_invInterpStrip`

English:
lemma diffContOnCl_invInterpStrip
  given: {ε : Real} (hε : ε > 0)
  proof: by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const differentiable_id 1) _
    left
    rw [← ofReal_add]; rw [ofReal_ne_zero]
    simp only [ne_eq, ne_of_gt (sSupNormIm_eps_pos f hε 0), not_false_eq_true]
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id)
    apply Or.inl
    rw [← ofReal_add]; rw [ofReal_ne_zero]
    exact (ne_of_gt (sSupNormIm_eps_pos f hε 1))

中文:
引理 diffContOnCl_inv整数erpStrip
  条件: {ε : 实数} (hε : ε > 0)
  证明: by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const differentiable_id 1) _
    left
    rw [← ofReal_add]; rw [ofReal_ne_zero]
    simp only [ne_eq, ne_of_gt (sSupNormIm_eps_pos f hε 0), not_false_eq_true]
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id)
    apply Or.inl
    rw [← ofReal_add]; rw [ofReal_ne_zero]
    exact (ne_of_gt (sSupNormIm_eps_pos f hε 1))

Depends on / 依赖: Differentiable, Differentiable.const_cpow, Differentiable.diffContOnCl, Differentiable.mul, Differentiable.neg, Differentiable.sub_const, Or.inl, const_cpow, diffContOnCl, differentiable_id, ne_eq, ne_of_gt, not_false_eq_true, ofReal_add, ofReal_ne_zero, sSupNormIm_eps_pos, sub_const
-/
lemma diffContOnCl_invInterpStrip {ε : Real} (hε : ε > 0) :
    DiffContOnCl Complex (fun z => invInterpStrip f z ε) (verticalStrip 0 1) := by
  apply Differentiable.diffContOnCl
  apply Differentiable.mul
  · apply Differentiable.const_cpow (Differentiable.sub_const differentiable_id 1) _
    left
    rw [← ofReal_add]; rw [ofReal_ne_zero]
    simp only [ne_eq, ne_of_gt (sSupNormIm_eps_pos f hε 0), not_false_eq_true]
  · apply Differentiable.const_cpow (Differentiable.neg differentiable_id)
    apply Or.inl
    rw [← ofReal_add]; rw [ofReal_ne_zero]
    exact (ne_of_gt (sSupNormIm_eps_pos f hε 1))

/--
lemma `norm_le_sSupNormIm` / 引理 `norm_le_sSupNormIm`

English:
lemma norm_le_sSupNormIm
  statement: (f : Complex -> E) (z : Complex) (hD : z in verticalClosedStrip 0 1)
  proof: by
  refine le_csSup ?_ ?_
  · revert hB; gcongr
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

中文:
引理 norm_le_sSupNormIm
  结论: (f : 复形 -> E) (z : 复形) (hD : z in verticalClosedStrip 0 1)
  证明: by
  refine le_csSup ?_ ?_
  · revert hB; gcongr
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

Depends on / 依赖: le_csSup, mem_image_of_mem, mem_preimage, mem_singleton, preimage_mono, revert, singleton_subset_iff, singleton_subset_iff.mpr
-/
lemma norm_le_sSupNormIm (f : Complex -> E) (z : Complex) (hD : z in verticalClosedStrip 0 1)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ <= sSupNormIm f (z.re) := by
  refine le_csSup ?_ ?_
  · revert hB; gcongr
    exact preimage_mono (singleton_subset_iff.mpr hD)
  · apply mem_image_of_mem (norm ∘ f)
    simp only [mem_preimage, mem_singleton]

/--
lemma `norm_lt_sSupNormIm_eps` / 引理 `norm_lt_sSupNormIm_eps`

English:
lemma norm_lt_sSupNormIm_eps
  statement: (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Complex)
  proof: lt_add_of_pos_of_le hε (norm_le_sSupNormIm f z hD hB)

中文:
引理 norm_lt_sSupNormIm_eps
  结论: (f : 复形 -> E) (ε : 实数) (hε : ε > 0) (z : 复形)
  证明: lt_add_of_pos_of_le hε (norm_le_sSupNormIm f z hD hB)

Depends on / 依赖: lt_add_of_pos_of_le, norm_le_sSupNormIm
-/
lemma norm_lt_sSupNormIm_eps (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Complex)
    (hD : z in verticalClosedStrip 0 1) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ < ε + sSupNormIm f (z.re) :=
  lt_add_of_pos_of_le hε (norm_le_sSupNormIm f z hD hB)

variable [NormedSpace Complex E]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `F_BddAbove` / 引理 `F_BddAbove`

English:
lemma F_BddAbove
  statement: (f : Complex -> E) (ε : Real) (hε : ε > 0)
  proof: by
  -- Rewriting goal
  simp only [F, comp_apply, invInterpStrip]
  rw [bddAbove_def] at *
  rcases hB with ⟨B, hB⟩
  -- Using bound
  use ((max 1 ((ε + sSupNormIm f 0) ^ (-(1 : Real)))) * max 1 ((ε + sSupNormIm f 1) ^ (-(1 : Real)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro z hset
  specialize hB (‖f z‖) (by simpa [image_congr, mem_image, comp_apply] using ⟨z, hset, rfl⟩)
  -- Proof that the bound is correct
  simp only [norm_smul, norm_mul, ← ofReal_add]
  gcongr
    -- Bounding individual terms
  · by_cases hM0_one : 1 <= ε + sSupNormIm f 0
    -- `1 ≤ sSupNormIm f 0`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re, Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
    -- `0 < sSupNormIm f 0 < 1`
    · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re]
      apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
      simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
  · by_cases hM1_one : 1 <= ε + sSupNormIm f 1
    -- `1 ≤ sSupNormIm f 1`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_one_of_one_le_of_nonpos
        hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
    -- `0 < sSupNormIm f 1 < 1`
    · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
        (le_of_lt hM1_one) (neg_le_neg_iff.mpr hset.2)]

中文:
引理 F_BddAbove
  结论: (f : 复形 -> E) (ε : 实数) (hε : ε > 0)
  证明: by
  -- Rewriting goal
  simp only [F, comp_apply, invInterpStrip]
  rw [bddAbove_def] at *
  rcases hB with ⟨B, hB⟩
  -- Using bound
  use ((max 1 ((ε + sSupNormIm f 0) ^ (-(1 : Real)))) * max 1 ((ε + sSupNormIm f 1) ^ (-(1 : Real)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro z hset
  specialize hB (‖f z‖) (by simpa [image_congr, mem_image, comp_apply] using ⟨z, hset, rfl⟩)
  -- Proof that the bound is correct
  simp only [norm_smul, norm_mul, ← ofReal_add]
  gcongr
    -- Bounding individual terms
  · by_cases hM0_one : 1 <= ε + sSupNormIm f 0
    -- `1 ≤ sSupNormIm f 0`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re, Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
    -- `0 < sSupNormIm f 0 < 1`
    · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re]
      apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
      simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
  · by_cases hM1_one : 1 <= ε + sSupNormIm f 1
    -- `1 ≤ sSupNormIm f 1`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_one_of_one_le_of_nonpos
        hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
    -- `0 < sSupNormIm f 1 < 1`
    · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
        (le_of_lt hM1_one) (neg_le_neg_iff.mpr hset.2)]
-/
lemma F_BddAbove (f : Complex -> E) (ε : Real) (hε : ε > 0)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    BddAbove ((norm ∘ (F f ε)) '' verticalClosedStrip 0 1) := by
  -- Rewriting goal
  simp only [F, comp_apply, invInterpStrip]
  rw [bddAbove_def] at *
  rcases hB with ⟨B, hB⟩
  -- Using bound
  use ((max 1 ((ε + sSupNormIm f 0) ^ (-(1 : Real)))) * max 1 ((ε + sSupNormIm f 1) ^ (-(1 : Real)))) * B
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro z hset
  specialize hB (‖f z‖) (by simpa [image_congr, mem_image, comp_apply] using ⟨z, hset, rfl⟩)
  -- Proof that the bound is correct
  simp only [norm_smul, norm_mul, ← ofReal_add]
  gcongr
    -- Bounding individual terms
  · by_cases hM0_one : 1 <= ε + sSupNormIm f 0
    -- `1 ≤ sSupNormIm f 0`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re, Real.rpow_le_one_of_one_le_of_nonpos hM0_one (sub_nonpos.mpr hset.2)]
    -- `0 < sSupNormIm f 0 < 1`
    · rw [not_le] at hM0_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 0), sub_re,
        one_re]
      apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
      simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, hset.1]
  · by_cases hM1_one : 1 <= ε + sSupNormIm f 1
    -- `1 ≤ sSupNormIm f 1`
    · apply le_trans _ (le_max_left _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_one_of_one_le_of_nonpos
        hM1_one (Right.neg_nonpos_iff.mpr hset.1)]
    -- `0 < sSupNormIm f 1 < 1`
    · rw [not_le] at hM1_one; apply le_trans _ (le_max_right _ _)
      simp only [norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε 1),
        neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
        (le_of_lt hM1_one) (neg_le_neg_iff.mpr hset.2)]

/--
lemma `F_edge_le_one` / 引理 `F_edge_le_one`

English:
lemma F_edge_le_one
  statement: (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Complex)
  proof: by
  simp only [F, norm_smul, norm_invInterpStrip f z hε]
  rcases hz with hz0 | hz1
  -- `z.re = 0`
  · simp only [hz0, zero_sub, Real.rpow_neg_one, neg_zero, Real.rpow_zero, mul_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 0)]
    rw [← hz0]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 1), mul_one]
    rw [← hz1]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

中文:
引理 F_edge_le_one
  结论: (f : 复形 -> E) (ε : 实数) (hε : ε > 0) (z : 复形)
  证明: by
  simp only [F, norm_smul, norm_invInterpStrip f z hε]
  rcases hz with hz0 | hz1
  -- `z.re = 0`
  · simp only [hz0, zero_sub, Real.rpow_neg_one, neg_zero, Real.rpow_zero, mul_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 0)]
    rw [← hz0]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 1), mul_one]
    rw [← hz1]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

Depends on / 依赖: norm_invInterpStrip, norm_smul
-/
lemma F_edge_le_one (f : Complex -> E) (ε : Real) (hε : ε > 0) (z : Complex)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z in re ⁻¹' {0, 1}) :
    ‖F f ε z‖ <= 1 := by
  simp only [F, norm_smul, norm_invInterpStrip f z hε]
  rcases hz with hz0 | hz1
  -- `z.re = 0`
  · simp only [hz0, zero_sub, Real.rpow_neg_one, neg_zero, Real.rpow_zero, mul_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 0)]
    rw [← hz0]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, left_mem_Icc, hz0]
  -- `z.re = 1`
  · rw [mem_singleton_iff] at hz1
    simp only [hz1, one_mul, Real.rpow_zero, sub_self, Real.rpow_neg_one,
      inv_mul_le_iff₀ (sSupNormIm_eps_pos f hε 1), mul_one]
    rw [← hz1]
    apply le_of_lt (norm_lt_sSupNormIm_eps f ε hε _ _ hB)
    simp only [verticalClosedStrip, mem_preimage, zero_le_one, hz1, right_mem_Icc]

/--
theorem `norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip` / 定理 `norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip`

English:
theorem norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip
  statement: (f : Complex -> E) (ε : Real) (hε : 0 < ε)
  proof: by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f hε) hd) _
    (fun x hx => F_edge_le_one f ε hε x hB (Or.inl hx))
    (fun x hx => F_edge_le_one f ε hε x hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero]; rw [div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f ε hε hB
  simp only [comp_apply, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro x hx
  simpa using! (hBF x ((preimage_mono Ioo_subset_Icc_self) hx)).trans
    ((le_of_lt (lt_add_one BF)).trans (Real.add_one_le_exp BF))

中文:
定理 norm_mul_inv整数erpStrip_le_one_of_mem_verticalClosedStrip
  结论: (f : 复形 -> E) (ε : 实数) (hε : 0 < ε)
  证明: by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f hε) hd) _
    (fun x hx => F_edge_le_one f ε hε x hB (Or.inl hx))
    (fun x hx => F_edge_le_one f ε hε x hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero]; rw [div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f ε hε hB
  simp only [comp_apply, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro x hx
  simpa using! (hBF x ((preimage_mono Ioo_subset_Icc_self) hx)).trans
    ((le_of_lt (lt_add_one BF)).trans (Real.add_one_le_exp BF))

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_iff, DiffContOnCl, DiffContOnCl.smul, F_BddAbove, F_edge_le_one, Or.inl, Or.inr, PhragmenLindelof, PhragmenLindelof.vertical_strip, Real.pi_pos, and_imp, comp_apply, diffContOnCl_invInterpStrip, div_one, eventually_inf_principal, forall_exists_index, isBigO_iff, mem_image, mem_upperBounds
-/
theorem norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip (f : Complex -> E) (ε : Real) (hε : 0 < ε)
    (z : Complex) (hd : DiffContOnCl Complex f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z in verticalClosedStrip 0 1) :
    ‖F f ε z‖ <= 1 := by
  apply PhragmenLindelof.vertical_strip
    (DiffContOnCl.smul (diffContOnCl_invInterpStrip f hε) hd) _
    (fun x hx => F_edge_le_one f ε hε x hB (Or.inl hx))
    (fun x hx => F_edge_le_one f ε hε x hB (Or.inr hx)) hz.1 hz.2
  use 0
  rw [sub_zero]; rw [div_one]
  refine ⟨ Real.pi_pos, ?_⟩
  obtain ⟨BF, hBF⟩ := F_BddAbove f ε hε hB
  simp only [comp_apply, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hBF
  use BF
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [eventually_inf_principal]
  apply Eventually.of_forall
  intro x hx
  simpa using! (hBF x ((preimage_mono Ioo_subset_Icc_self) hx)).trans
    ((le_of_lt (lt_add_one BF)).trans (Real.add_one_le_exp BF))

end invInterpStrip

-----

variable {E : Type*} [NormedAddCommGroup E] (f : Complex -> E)

/--
Definition of `interpStrip` / `interpStrip` 的定义

English:
definition interpStrip
  signature: (z : Complex)
  body: if sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    then 0
    else sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z

中文:
定义 interpStrip
  签名: (z : 复形)
  定义体: if sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    then 0
    else sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z

Depends on / 依赖: sSupNormIm
-/
noncomputable def interpStrip (z : Complex) : Complex :=
  if sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    then 0
    else sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z

/--
lemma `interpStrip_eq_of_pos` / 引理 `interpStrip_eq_of_pos`

English:
lemma interpStrip_eq_of_pos
  given: (z : Complex) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1)
  proof: by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, if_false, or_false]

中文:
引理 interpStrip_eq_of_pos
  条件: (z : 复形) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1)
  证明: by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, if_false, or_false]

Depends on / 依赖: if_false, interpStrip, ne_of_gt, or_false
-/
lemma interpStrip_eq_of_pos (z : Complex) (h0 : 0 < sSupNormIm f 0) (h1 : 0 < sSupNormIm f 1) :
    interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z := by
  simp only [ne_of_gt h0, ne_of_gt h1, interpStrip, if_false, or_false]

/--
lemma `interpStrip_eq_of_zero` / 引理 `interpStrip_eq_of_zero`

English:
lemma interpStrip_eq_of_zero
  given: (z : Complex) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0)
  proof: if_pos h

中文:
引理 interpStrip_eq_of_zero
  条件: (z : 复形) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0)
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma interpStrip_eq_of_zero (z : Complex) (h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0) :
    interpStrip f z = 0 :=
  if_pos h

/--
lemma `interpStrip_eq_of_mem_verticalStrip` / 引理 `interpStrip_eq_of_mem_verticalStrip`

English:
lemma interpStrip_eq_of_mem_verticalStrip
  given: (z : Complex) (hz : z in verticalStrip 0 1)
  proof: by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  · rw [interpStrip_eq_of_zero _ z h]
    rcases h with h0 | h1
    · simp only [h0, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ne_eq, true_and, ofReal_eq_zero]
      left
      rw [sub_eq_zero]; rw [eq_comm]
      simp only [Complex.ext_iff, one_re, ne_of_lt hz.2, false_and, not_false_eq_true]
    · simp only [h1, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq, true_and]
      right
      rw [eq_comm]
      simp only [Complex.ext_iff, zero_re, ne_of_lt hz.1, false_and, not_false_eq_true]
  · replace h : (0 < sSupNormIm f 0) ∧ (0 < sSupNormIm f 1) :=
      ⟨(lt_of_le_of_ne (sSupNormIm_nonneg f 0) (ne_comm.mp h.1)),
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact interpStrip_eq_of_pos f z h.1 h.2

中文:
引理 interpStrip_eq_of_mem_verticalStrip
  条件: (z : 复形) (hz : z in verticalStrip 0 1)
  证明: by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  · rw [interpStrip_eq_of_zero _ z h]
    rcases h with h0 | h1
    · simp only [h0, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ne_eq, true_and, ofReal_eq_zero]
      left
      rw [sub_eq_zero]; rw [eq_comm]
      simp only [Complex.ext_iff, one_re, ne_of_lt hz.2, false_and, not_false_eq_true]
    · simp only [h1, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq, true_and]
      right
      rw [eq_comm]
      simp only [Complex.ext_iff, zero_re, ne_of_lt hz.1, false_and, not_false_eq_true]
  · replace h : (0 < sSupNormIm f 0) ∧ (0 < sSupNormIm f 1) :=
      ⟨(lt_of_le_of_ne (sSupNormIm_nonneg f 0) (ne_comm.mp h.1)),
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact interpStrip_eq_of_pos f z h.1 h.2

Depends on / 依赖: Complex.ext_iff, cpow_eq_zero_iff, eq_comm, ext_iff, false_and, interpStrip_eq_of_zero, ne_eq, ne_of_lt, not_false_eq_true, ofReal_eq_zero, ofReal_zero, one_re, sSupNormIm, sub_eq_zero, true_and, zero_eq_mul, zero_re
-/
lemma interpStrip_eq_of_mem_verticalStrip (z : Complex) (hz : z in verticalStrip 0 1) :
    interpStrip f z = sSupNormIm f 0 ^ (1 - z) * sSupNormIm f 1 ^ z := by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  · rw [interpStrip_eq_of_zero _ z h]
    rcases h with h0 | h1
    · simp only [h0, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ne_eq, true_and, ofReal_eq_zero]
      left
      rw [sub_eq_zero]; rw [eq_comm]
      simp only [Complex.ext_iff, one_re, ne_of_lt hz.2, false_and, not_false_eq_true]
    · simp only [h1, ofReal_zero, zero_eq_mul, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq, true_and]
      right
      rw [eq_comm]
      simp only [Complex.ext_iff, zero_re, ne_of_lt hz.1, false_and, not_false_eq_true]
  · replace h : (0 < sSupNormIm f 0) ∧ (0 < sSupNormIm f 1) :=
      ⟨(lt_of_le_of_ne (sSupNormIm_nonneg f 0) (ne_comm.mp h.1)),
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) (ne_comm.mp h.2))⟩
    exact interpStrip_eq_of_pos f z h.1 h.2

/--
lemma `diffContOnCl_interpStrip` / 引理 `diffContOnCl_interpStrip`

English:
lemma diffContOnCl_interpStrip
  proof: by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  -- Case everywhere 0
  · eta_expand; simp_rw [interpStrip_eq_of_zero f _ h]; exact diffContOnCl_const
  -- Case nowhere 0
  · rcases h with ⟨h0, h1⟩
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    eta_expand
    simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.const_sub differentiableAt_id 1) _
      left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · apply differentiableAt_id
      · left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]

中文:
引理 diffContOnCl_interpStrip
  证明: by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  -- Case everywhere 0
  · eta_expand; simp_rw [interpStrip_eq_of_zero f _ h]; exact diffContOnCl_const
  -- Case nowhere 0
  · rcases h with ⟨h0, h1⟩
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    eta_expand
    simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.const_sub differentiableAt_id 1) _
      left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · apply differentiableAt_id
      · left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]

Depends on / 依赖: sSupNormIm
-/
lemma diffContOnCl_interpStrip :
    DiffContOnCl Complex (interpStrip f) (verticalStrip 0 1) := by
  by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
  -- Case everywhere 0
  · eta_expand; simp_rw [interpStrip_eq_of_zero f _ h]; exact diffContOnCl_const
  -- Case nowhere 0
  · rcases h with ⟨h0, h1⟩
    rw [ne_comm] at h0 h1
    apply Differentiable.diffContOnCl
    intro z
    eta_expand
    simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
      (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
    refine DifferentiableAt.mul ?_ ?_
    · apply DifferentiableAt.const_cpow (DifferentiableAt.const_sub differentiableAt_id 1) _
      left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]
    · refine DifferentiableAt.const_cpow ?_ ?_
      · apply differentiableAt_id
      · left; simp only [Ne, ofReal_eq_zero]; rwa [eq_comm]

/--
Definition of `interpStrip'` / `interpStrip'` 的定义

English:
definition interpStrip'
  signature: (f : Complex -> E) (l u : Real) (z : Complex)
  body: if sSupNormIm f l = 0 ∨ sSupNormIm f u = 0
    then 0
    else sSupNormIm f l ^ (1 - ((z - l) / (u - l))) * sSupNormIm f u ^ ((z - l) / (u - l))

中文:
定义 interpStrip'
  签名: (f : 复形 -> E) (l u : 实数) (z : 复形)
  定义体: if sSupNormIm f l = 0 ∨ sSupNormIm f u = 0
    then 0
    else sSupNormIm f l ^ (1 - ((z - l) / (u - l))) * sSupNormIm f u ^ ((z - l) / (u - l))

Depends on / 依赖: sSupNormIm
-/
noncomputable def interpStrip' (f : Complex -> E) (l u : Real) (z : Complex) : Complex :=
  if sSupNormIm f l = 0 ∨ sSupNormIm f u = 0
    then 0
    else sSupNormIm f l ^ (1 - ((z - l) / (u - l))) * sSupNormIm f u ^ ((z - l) / (u - l))

/--
Definition of `scale` / `scale` 的定义

English:
definition scale
  signature: (f : Complex -> E) (l u : Real)
  body: fun z => f (l + z • (u - l))

中文:
定义 scale
  签名: (f : 复形 -> E) (l u : 实数)
  定义体: fun z => f (l + z • (u - l))
-/
def scale (f : Complex -> E) (l u : Real) : Complex -> E := fun z => f (l + z • (u - l))

/--
lemma `scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip` / 引理 `scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip`

English:
lemma scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip
  statement: {l u : Real} (hul : l < u) {z : Complex}
  proof: by
  simp only [verticalClosedStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im,
    ofReal_im, sub_self, mul_zero, sub_zero, mem_Icc] at hz ⊢
  constructor <;> nlinarith [hz.1, hz.2, hul]

中文:
引理 scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip
  结论: {l u : 实数} (hul : l < u) {z : 复形}
  证明: by
  simp only [verticalClosedStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im,
    ofReal_im, sub_self, mul_zero, sub_zero, mem_Icc] at hz ⊢
  constructor <;> nlinarith [hz.1, hz.2, hul]

Depends on / 依赖: add_re, mem_Icc, mem_preimage, mul_re, mul_zero, ofReal_im, ofReal_re, sub_im, sub_re, sub_self, sub_zero, verticalClosedStrip
-/
lemma scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip {l u : Real} (hul : l < u) {z : Complex}
    (hz : z in verticalClosedStrip 0 1) : l + z * (u - l) in verticalClosedStrip l u := by
  simp only [verticalClosedStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im,
    ofReal_im, sub_self, mul_zero, sub_zero, mem_Icc] at hz ⊢
  constructor <;> nlinarith [hz.1, hz.2, hul]

/--
lemma `scale_bddAbove` / 引理 `scale_bddAbove`

English:
lemma scale_bddAbove
  statement: {f : Complex -> E} {l u : Real} (hul : l < u)
  proof: by
  refine hB.mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨l + z * (u - l), scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip hul hz, rfl⟩

中文:
引理 scale_bddAbove
  结论: {f : 复形 -> E} {l u : 实数} (hul : l < u)
  证明: by
  refine hB.mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨l + z * (u - l), scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip hul hz, rfl⟩

Depends on / 依赖: hB.mono, scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip
-/
lemma scale_bddAbove {f : Complex -> E} {l u : Real} (hul : l < u)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    BddAbove ((norm ∘ scale f l u) '' verticalClosedStrip 0 1) := by
  refine hB.mono ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨l + z * (u - l), scale_id_mem_verticalClosedStrip_of_mem_verticalClosedStrip hul hz, rfl⟩

/--
lemma `scale_bound_left` / 引理 `scale_bound_left`

English:
lemma scale_bound_left
  given: {f : Complex -> E} {l u a : Real} (ha : forall z in re ⁻¹' {l}, ‖f z‖ <= a)
  proof: by
  simp only [mem_preimage, mem_singleton_iff, scale, smul_eq_mul]
  intro z hz
  exact ha (↑l + z * (↑u - ↑l)) (by simp [hz])

中文:
引理 scale_bound_left
  条件: {f : 复形 -> E} {l u a : 实数} (ha : 对任意 z in re ⁻¹' {l}, ‖f z‖ <= a)
  证明: by
  simp only [mem_preimage, mem_singleton_iff, scale, smul_eq_mul]
  intro z hz
  exact ha (↑l + z * (↑u - ↑l)) (by simp [hz])

Depends on / 依赖: mem_preimage, mem_singleton_iff, smul_eq_mul
-/
lemma scale_bound_left {f : Complex -> E} {l u a : Real} (ha : forall z in re ⁻¹' {l}, ‖f z‖ <= a) :
    forall z in re ⁻¹' {0}, ‖scale f l u z‖ <= a := by
  simp only [mem_preimage, mem_singleton_iff, scale, smul_eq_mul]
  intro z hz
  exact ha (↑l + z * (↑u - ↑l)) (by simp [hz])

/--
lemma `scale_bound_right` / 引理 `scale_bound_right`

English:
lemma scale_bound_right
  given: {f : Complex -> E} {l u b : Real} (hb : forall z in re ⁻¹' {u}, ‖f z‖ <= b)
  proof: by
  simp only [scale, mem_preimage, mem_singleton_iff, smul_eq_mul]
  intro z hz
  exact hb (↑l + z * (↑u - ↑l)) (by simp [hz])

中文:
引理 scale_bound_right
  条件: {f : 复形 -> E} {l u b : 实数} (hb : 对任意 z in re ⁻¹' {u}, ‖f z‖ <= b)
  证明: by
  simp only [scale, mem_preimage, mem_singleton_iff, smul_eq_mul]
  intro z hz
  exact hb (↑l + z * (↑u - ↑l)) (by simp [hz])

Depends on / 依赖: mem_preimage, mem_singleton_iff, smul_eq_mul
-/
lemma scale_bound_right {f : Complex -> E} {l u b : Real} (hb : forall z in re ⁻¹' {u}, ‖f z‖ <= b) :
    forall z in re ⁻¹' {1}, ‖scale f l u z‖ <= b := by
  simp only [scale, mem_preimage, mem_singleton_iff, smul_eq_mul]
  intro z hz
  exact hb (↑l + z * (↑u - ↑l)) (by simp [hz])

/--
lemma `sSupNormIm_scale_left` / 引理 `sSupNormIm_scale_left`

English:
lemma sSupNormIm_scale_left
  given: (f : Complex -> E) {l u : Real} (hul : l < u)
  proof: by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {0} = f '' re ⁻¹' {l} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp [hz₁, hz₂]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        rw [Complex.div_re]; rw [Complex.normSq_ofReal]; rw [Complex.ofReal_re]
        simp [hz₁]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp [hz₂]
  rw [this]

中文:
引理 sSupNormIm_scale_left
  条件: (f : 复形 -> E) {l u : 实数} (hul : l < u)
  证明: by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {0} = f '' re ⁻¹' {l} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp [hz₁, hz₂]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        rw [Complex.div_re]; rw [Complex.normSq_ofReal]; rw [Complex.ofReal_re]
        simp [hz₁]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp [hz₂]
  rw [this]

Depends on / 依赖: Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, div_mul_comm, div_re, div_self, image_comp, mem_image, mem_preimage, mem_singleton_iff, normSq_ofReal, ofReal_re, sSupNormIm, simp_rw, smul_eq_mul
-/
lemma sSupNormIm_scale_left (f : Complex -> E) {l u : Real} (hul : l < u) :
    sSupNormIm (scale f l u) 0 = sSupNormIm f l := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {0} = f '' re ⁻¹' {l} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp [hz₁, hz₂]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        rw [Complex.div_re]; rw [Complex.normSq_ofReal]; rw [Complex.ofReal_re]
        simp [hz₁]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp [hz₂]
  rw [this]

/--
lemma `sSupNormIm_scale_right` / 引理 `sSupNormIm_scale_right`

English:
lemma sSupNormIm_scale_right
  given: (f : Complex -> E) {l u : Real} (hul : l < u)
  proof: by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {1} = f '' re ⁻¹' {u} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp only [add_re, ofReal_re, mul_re, hz₁, sub_re, one_mul, sub_im, ofReal_im, sub_self,
        mul_zero, sub_zero, add_sub_cancel, hz₂, and_self]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        grind [Complex.div_re, Complex.normSq_ofReal, sub_re, ofReal_re, ofReal_im, mul_eq_zero]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp only [one_mul, add_sub_cancel, hz₂]
  rw [this]

中文:
引理 sSupNormIm_scale_right
  条件: (f : 复形 -> E) {l u : 实数} (hul : l < u)
  证明: by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {1} = f '' re ⁻¹' {u} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp only [add_re, ofReal_re, mul_re, hz₁, sub_re, one_mul, sub_im, ofReal_im, sub_self,
        mul_zero, sub_zero, add_sub_cancel, hz₂, and_self]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        grind [Complex.div_re, Complex.normSq_ofReal, sub_re, ofReal_re, ofReal_im, mul_eq_zero]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp only [one_mul, add_sub_cancel, hz₂]
  rw [this]

Depends on / 依赖: Complex.div_re, add_re, add_sub_cancel, and_self, div_re, image_comp, mem_image, mem_preimage, mem_singleton_iff, mul_re, mul_zero, ofReal_im, ofReal_re, one_mul, sSupNormIm, simp_rw, smul_eq_mul, sub_im, sub_re, sub_self
-/
lemma sSupNormIm_scale_right (f : Complex -> E) {l u : Real} (hul : l < u) :
    sSupNormIm (scale f l u) 1 = sSupNormIm f u := by
  simp_rw [sSupNormIm, image_comp]
  have : scale f l u '' re ⁻¹' {1} = f '' re ⁻¹' {u} := by
    ext e
    simp only [scale, smul_eq_mul, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ↑l + z * (↑u - ↑l)
      simp only [add_re, ofReal_re, mul_re, hz₁, sub_re, one_mul, sub_im, ofReal_im, sub_self,
        mul_zero, sub_zero, add_sub_cancel, hz₂, and_self]
    · intro h
      obtain ⟨z, hz₁, hz₂⟩ := h
      use ((z - l) / (u - l))
      constructor
      · norm_cast
        grind [Complex.div_re, Complex.normSq_ofReal, sub_re, ofReal_re, ofReal_im, mul_eq_zero]
      · rw [div_mul_comm, div_self (by norm_cast; linarith)]
        simp only [one_mul, add_sub_cancel, hz₂]
  rw [this]

/--
lemma `interpStrip_scale` / 引理 `interpStrip_scale`

English:
lemma interpStrip_scale
  given: (f : Complex -> E) {l u : Real} (hul : l < u) (z : Complex)
  statement: interpStrip (scale f l u)
  proof: by
  simp only [interpStrip, interpStrip']
  simp_rw [sSupNormIm_scale_left f hul, sSupNormIm_scale_right f hul]

中文:
引理 interpStrip_scale
  条件: (f : 复形 -> E) {l u : 实数} (hul : l < u) (z : 复形)
  结论: interpStrip (scale f l u)
  证明: by
  simp only [interpStrip, interpStrip']
  simp_rw [sSupNormIm_scale_left f hul, sSupNormIm_scale_right f hul]

Depends on / 依赖: interpStrip, sSupNormIm_scale_left, sSupNormIm_scale_right, simp_rw
-/
lemma interpStrip_scale (f : Complex -> E) {l u : Real} (hul : l < u) (z : Complex) : interpStrip (scale f l u)
    ((z - ↑l) / (↑u - ↑l)) = interpStrip' f l u z := by
  simp only [interpStrip, interpStrip']
  simp_rw [sSupNormIm_scale_left f hul, sSupNormIm_scale_right f hul]

variable [NormedSpace Complex E]

/--
lemma `norm_le_interpStrip_of_mem_verticalClosedStrip_eps` / 引理 `norm_le_interpStrip_of_mem_verticalClosedStrip_eps`

English:
lemma norm_le_interpStrip_of_mem_verticalClosedStrip_eps
  statement: (ε : Real) (hε : ε > 0) (z : Complex)
  proof: by
  simp only [norm_mul, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _,
    sub_re, one_re]
  rw [← mul_inv_le_iff₀']; rw [← one_mul (((ε + sSupNormIm f 1) ^ z.re))]; rw [← mul_inv_le_iff₀]; rw [← Real.rpow_neg_one]; rw [← Real.rpow_neg_one]
  · simp only [← Real.rpow_mul (le_of_lt (sSupNormIm_eps_pos f hε _)),
    mul_neg, mul_one, neg_sub, mul_assoc]
    simpa [F, norm_invInterpStrip _ _ hε, norm_smul, mul_comm] using
      norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip f ε hε z hd hB hz
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) z.re]
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) (1 - z.re)]

中文:
引理 norm_le_interpStrip_of_mem_verticalClosedStrip_eps
  结论: (ε : 实数) (hε : ε > 0) (z : 复形)
  证明: by
  simp only [norm_mul, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _,
    sub_re, one_re]
  rw [← mul_inv_le_iff₀']; rw [← one_mul (((ε + sSupNormIm f 1) ^ z.re))]; rw [← mul_inv_le_iff₀]; rw [← Real.rpow_neg_one]; rw [← Real.rpow_neg_one]
  · simp only [← Real.rpow_mul (le_of_lt (sSupNormIm_eps_pos f hε _)),
    mul_neg, mul_one, neg_sub, mul_assoc]
    simpa [F, norm_invInterpStrip _ _ hε, norm_smul, mul_comm] using
      norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip f ε hε z hd hB hz
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) z.re]
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) (1 - z.re)]

Depends on / 依赖: Real.rpow_mul, Real.rpow_neg_one, le_of_lt, mul_assoc, mul_comm, mul_neg, mul_one, neg_sub, norm_cpow_eq_rpow_re_of_pos, norm_invInterpStrip, norm_mul, norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip, norm_smul, ofReal_add, one_mul, one_re, rpow_mul, rpow_neg_one, sSupNormIm, sSupNormIm_eps_pos
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip_eps (ε : Real) (hε : ε > 0) (z : Complex)
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hd : DiffContOnCl Complex f (verticalStrip 0 1)) (hz : z in verticalClosedStrip 0 1) :
    ‖f z‖ <= ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : Complex)‖ := by
  simp only [norm_mul, ← ofReal_add, norm_cpow_eq_rpow_re_of_pos (sSupNormIm_eps_pos f hε _) _,
    sub_re, one_re]
  rw [← mul_inv_le_iff₀']; rw [← one_mul (((ε + sSupNormIm f 1) ^ z.re))]; rw [← mul_inv_le_iff₀]; rw [← Real.rpow_neg_one]; rw [← Real.rpow_neg_one]
  · simp only [← Real.rpow_mul (le_of_lt (sSupNormIm_eps_pos f hε _)),
    mul_neg, mul_one, neg_sub, mul_assoc]
    simpa [F, norm_invInterpStrip _ _ hε, norm_smul, mul_comm] using
      norm_mul_invInterpStrip_le_one_of_mem_verticalClosedStrip f ε hε z hd hB hz
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) z.re]
  · simp only [Real.rpow_pos_of_pos (sSupNormIm_eps_pos f hε _) (1 - z.re)]

/--
lemma `eventuallyle` / 引理 `eventuallyle`

English:
lemma eventuallyle
  statement: (z : Complex) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
  proof: by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using
    norm_le_interpStrip_of_mem_verticalClosedStrip_eps f ε hε z hB hd
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))

中文:
引理 eventuallyle
  结论: (z : 复形) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
  证明: by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using
    norm_le_interpStrip_of_mem_verticalClosedStrip_eps f ε hε z hB hd
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))

Depends on / 依赖: Ioo_subset_Icc_self, filter_upwards, mem_of_mem_of_subset, norm_le_interpStrip_of_mem_verticalClosedStrip_eps, preimage_mono, self_mem_nhdsWithin
-/
lemma eventuallyle (z : Complex) (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hd : DiffContOnCl Complex f (verticalStrip 0 1)) (hz : z in verticalStrip 0 1) :
    (fun _ : Real => ‖f z‖) <=ᶠ[𝓝[>] 0]
    (fun ε => ‖((ε + sSupNormIm f 0) ^ (1 - z) * (ε + sSupNormIm f 1) ^ z : Complex)‖) := by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using
    norm_le_interpStrip_of_mem_verticalClosedStrip_eps f ε hε z hB hd
      (mem_of_mem_of_subset hz (preimage_mono Ioo_subset_Icc_self))

/--
lemma `norm_le_interpStrip_of_mem_verticalStrip_zero` / 引理 `norm_le_interpStrip_of_mem_verticalStrip_zero`

English:
lemma norm_le_interpStrip_of_mem_verticalStrip_zero
  statement: (z : Complex)
  proof: by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · simp only [tendsto_const_nhds_iff]
  -- Proof that we can let epsilon tend to zero.
  · rw [interpStrip_eq_of_mem_verticalStrip _ _ hz]
    convert! ContinuousWithinAt.tendsto _ using 2
    · simp only [ofReal_zero, zero_add]
    · simp_rw [← ofReal_add]
      have : forall x in Ioi 0, (x + sSupNormIm f 0) ^ (1 - z.re) * (x + sSupNormIm f 1) ^ z.re
          = ‖((x + sSupNormIm f 0 : Real) ^ (1 - z) * (x + sSupNormIm f 1 : Real) ^ z : Complex)‖ := by
              intro x hx
              simp only [norm_mul]
              repeat rw [norm_cpow_eq_rpow_re_of_nonneg (le_of_lt (sSupNormIm_eps_pos f hx _)) _]
              · simp only [sub_re, one_re]
              · simpa using (ne_comm.mpr (ne_of_lt hz.1))
              · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))
      apply tendsto_nhdsWithin_congr this _
      simp only [zero_add]
      rw [norm_mul]; rw [norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]; rw [norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]
      · apply Tendsto.mul
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 0)]
            exact Tendsto.add_const (sSupNormIm f 0) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.2]
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 1)]
            exact Tendsto.add_const (sSupNormIm f 1) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [le_of_lt hz.1]
      · simpa using (ne_comm.mpr (ne_of_lt hz.1))
      · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))

中文:
引理 norm_le_interpStrip_of_mem_verticalStrip_zero
  结论: (z : 复形)
  证明: by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · simp only [tendsto_const_nhds_iff]
  -- Proof that we can let epsilon tend to zero.
  · rw [interpStrip_eq_of_mem_verticalStrip _ _ hz]
    convert! ContinuousWithinAt.tendsto _ using 2
    · simp only [ofReal_zero, zero_add]
    · simp_rw [← ofReal_add]
      have : forall x in Ioi 0, (x + sSupNormIm f 0) ^ (1 - z.re) * (x + sSupNormIm f 1) ^ z.re
          = ‖((x + sSupNormIm f 0 : Real) ^ (1 - z) * (x + sSupNormIm f 1 : Real) ^ z : Complex)‖ := by
              intro x hx
              simp only [norm_mul]
              repeat rw [norm_cpow_eq_rpow_re_of_nonneg (le_of_lt (sSupNormIm_eps_pos f hx _)) _]
              · simp only [sub_re, one_re]
              · simpa using (ne_comm.mpr (ne_of_lt hz.1))
              · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))
      apply tendsto_nhdsWithin_congr this _
      simp only [zero_add]
      rw [norm_mul]; rw [norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]; rw [norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]
      · apply Tendsto.mul
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 0)]
            exact Tendsto.add_const (sSupNormIm f 0) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.2]
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 1)]
            exact Tendsto.add_const (sSupNormIm f 1) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [le_of_lt hz.1]
      · simpa using (ne_comm.mpr (ne_of_lt hz.1))
      · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))

Depends on / 依赖: eventuallyle, tendsto_const_nhds_iff, tendsto_le_of_eventuallyLE
-/
lemma norm_le_interpStrip_of_mem_verticalStrip_zero (z : Complex)
    (hd : DiffContOnCl Complex f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) (hz : z in verticalStrip 0 1) :
    ‖f z‖ <= ‖interpStrip f z‖ := by
  apply tendsto_le_of_eventuallyLE _ _ (eventuallyle f z hB hd hz)
  · simp only [tendsto_const_nhds_iff]
  -- Proof that we can let epsilon tend to zero.
  · rw [interpStrip_eq_of_mem_verticalStrip _ _ hz]
    convert! ContinuousWithinAt.tendsto _ using 2
    · simp only [ofReal_zero, zero_add]
    · simp_rw [← ofReal_add]
      have : forall x in Ioi 0, (x + sSupNormIm f 0) ^ (1 - z.re) * (x + sSupNormIm f 1) ^ z.re
          = ‖((x + sSupNormIm f 0 : Real) ^ (1 - z) * (x + sSupNormIm f 1 : Real) ^ z : Complex)‖ := by
              intro x hx
              simp only [norm_mul]
              repeat rw [norm_cpow_eq_rpow_re_of_nonneg (le_of_lt (sSupNormIm_eps_pos f hx _)) _]
              · simp only [sub_re, one_re]
              · simpa using (ne_comm.mpr (ne_of_lt hz.1))
              · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))
      apply tendsto_nhdsWithin_congr this _
      simp only [zero_add]
      rw [norm_mul]; rw [norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]; rw [norm_cpow_eq_rpow_re_of_nonneg (sSupNormIm_nonneg _ _) _]
      · apply Tendsto.mul
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 0)]
            exact Tendsto.add_const (sSupNormIm f 0) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [sub_nonneg, le_of_lt hz.2]
        · apply Tendsto.rpow_const
          · nth_rw 2 [← zero_add (sSupNormIm f 1)]
            exact Tendsto.add_const (sSupNormIm f 1) (tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto continuous_id' _))
          · right; simp only [le_of_lt hz.1]
      · simpa using (ne_comm.mpr (ne_of_lt hz.1))
      · simpa [sub_eq_zero] using (ne_comm.mpr (ne_of_lt hz.2))

/--
lemma `norm_le_interpStrip_of_mem_verticalClosedStrip₀₁` / 引理 `norm_le_interpStrip_of_mem_verticalClosedStrip₀₁`

English:
lemma norm_le_interpStrip_of_mem_verticalClosedStrip₀₁
  statement: (f : Complex -> E) {z : Complex}
  proof: by
  apply le_on_closure (fun w hw => norm_le_interpStrip_of_mem_verticalStrip_zero f w hd hB hw)
    (Continuous.comp_continuousOn' continuous_norm hd.2)
    (Continuous.comp_continuousOn' continuous_norm (diffContOnCl_interpStrip f).2)
  rwa [verticalClosedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz

中文:
引理 norm_le_interpStrip_of_mem_verticalClosedStrip₀₁
  结论: (f : 复形 -> E) {z : 复形}
  证明: by
  apply le_on_closure (fun w hw => norm_le_interpStrip_of_mem_verticalStrip_zero f w hd hB hw)
    (Continuous.comp_continuousOn' continuous_norm hd.2)
    (Continuous.comp_continuousOn' continuous_norm (diffContOnCl_interpStrip f).2)
  rwa [verticalClosedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz

Depends on / 依赖: Continuous, Continuous.comp_continuousOn, closure_Ioo, closure_preimage_re, comp_continuousOn, continuous_norm, diffContOnCl_interpStrip, le_on_closure, norm_le_interpStrip_of_mem_verticalStrip_zero, verticalClosedStrip, zero_ne_one
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (f : Complex -> E) {z : Complex}
    (hz : z in verticalClosedStrip 0 1) (hd : DiffContOnCl Complex f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1)) :
    ‖f z‖ <= ‖interpStrip f z‖ := by
  apply le_on_closure (fun w hw => norm_le_interpStrip_of_mem_verticalStrip_zero f w hd hB hw)
    (Continuous.comp_continuousOn' continuous_norm hd.2)
    (Continuous.comp_continuousOn' continuous_norm (diffContOnCl_interpStrip f).2)
  rwa [verticalClosedStrip, ← closure_Ioo zero_ne_one, ← closure_preimage_re] at hz

/--
lemma `norm_le_interp_of_mem_verticalClosedStrip₀₁'` / 引理 `norm_le_interp_of_mem_verticalClosedStrip₀₁'`

English:
lemma norm_le_interp_of_mem_verticalClosedStrip₀₁'
  statement: (f : Complex -> E) {z : Complex} {a b : Real}
  proof: by
  have : ‖interpStrip f z‖ <= sSupNormIm f 0 ^ (1 - z.re) * sSupNormIm f 1 ^ z.re := by
    by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    · rw [interpStrip_eq_of_zero f z h, norm_zero, mul_nonneg_iff]
      left
      exact ⟨Real.rpow_nonneg (sSupNormIm_nonneg f _) _,
        Real.rpow_nonneg (sSupNormIm_nonneg f _) _ ⟩
    · rcases h with ⟨h0, h1⟩
      rw [ne_comm] at h0 h1
      simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
      simp only [norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h0).mp (sSupNormIm_nonneg f _)) _]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h1).mp (sSupNormIm_nonneg f _)) _]
      simp only [sub_re, one_re, le_refl]
  apply (norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ f hz hd hB).trans (this.trans _)
  apply mul_le_mul_of_nonneg _ _ (Real.rpow_nonneg (sSupNormIm_nonneg f _) _)
  · apply (Real.rpow_nonneg _ _)
    specialize hb 1
    simp only [mem_preimage, one_re, mem_singleton_iff, forall_true_left] at hb
    exact (norm_nonneg _).trans hb
  · gcongr
    · exact sSupNormIm_nonneg f _
    · exact sub_nonneg.mpr hz.2
    rw [sSupNormIm]
    apply csSup_le _
    · simpa [comp_apply, mem_image, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂] using ha
    · use ‖(f 0)‖, 0
      simp
  · apply Real.rpow_le_rpow (sSupNormIm_nonneg f _) _ hz.1
    · rw [sSupNormIm]
      apply csSup_le _
      · simpa [comp_apply, mem_image, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] using hb
      · use ‖(f 1)‖, 1
        simp only [mem_preimage, one_re, mem_singleton_iff, comp_apply,
          and_self]

中文:
引理 norm_le_interp_of_mem_verticalClosedStrip₀₁'
  结论: (f : 复形 -> E) {z : 复形} {a b : 实数}
  证明: by
  have : ‖interpStrip f z‖ <= sSupNormIm f 0 ^ (1 - z.re) * sSupNormIm f 1 ^ z.re := by
    by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    · rw [interpStrip_eq_of_zero f z h, norm_zero, mul_nonneg_iff]
      left
      exact ⟨Real.rpow_nonneg (sSupNormIm_nonneg f _) _,
        Real.rpow_nonneg (sSupNormIm_nonneg f _) _ ⟩
    · rcases h with ⟨h0, h1⟩
      rw [ne_comm] at h0 h1
      simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
      simp only [norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h0).mp (sSupNormIm_nonneg f _)) _]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h1).mp (sSupNormIm_nonneg f _)) _]
      simp only [sub_re, one_re, le_refl]
  apply (norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ f hz hd hB).trans (this.trans _)
  apply mul_le_mul_of_nonneg _ _ (Real.rpow_nonneg (sSupNormIm_nonneg f _) _)
  · apply (Real.rpow_nonneg _ _)
    specialize hb 1
    simp only [mem_preimage, one_re, mem_singleton_iff, forall_true_left] at hb
    exact (norm_nonneg _).trans hb
  · gcongr
    · exact sSupNormIm_nonneg f _
    · exact sub_nonneg.mpr hz.2
    rw [sSupNormIm]
    apply csSup_le _
    · simpa [comp_apply, mem_image, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂] using ha
    · use ‖(f 0)‖, 0
      simp
  · apply Real.rpow_le_rpow (sSupNormIm_nonneg f _) _ hz.1
    · rw [sSupNormIm]
      apply csSup_le _
      · simpa [comp_apply, mem_image, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] using hb
      · use ‖(f 1)‖, 1
        simp only [mem_preimage, one_re, mem_singleton_iff, comp_apply,
          and_self]

Depends on / 依赖: Real.rpow_nonneg, interpStrip, interpStrip_eq_of_pos, interpStrip_eq_of_zero, lt_of_le_of_ne, mul_nonneg_iff, ne_comm, norm_mul, norm_zero, rpow_nonneg, sSupNormIm, sSupNormIm_nonneg, simp_rw, z.re
-/
lemma norm_le_interp_of_mem_verticalClosedStrip₀₁' (f : Complex -> E) {z : Complex} {a b : Real}
    (hz : z in verticalClosedStrip 0 1) (hd : DiffContOnCl Complex f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (ha : forall z in re ⁻¹' {0}, ‖f z‖ <= a) (hb : forall z in re ⁻¹' {1}, ‖f z‖ <= b) :
    ‖f z‖ <= a ^ (1 - z.re) * b ^ z.re := by
  have : ‖interpStrip f z‖ <= sSupNormIm f 0 ^ (1 - z.re) * sSupNormIm f 1 ^ z.re := by
    by_cases! h : sSupNormIm f 0 = 0 ∨ sSupNormIm f 1 = 0
    · rw [interpStrip_eq_of_zero f z h, norm_zero, mul_nonneg_iff]
      left
      exact ⟨Real.rpow_nonneg (sSupNormIm_nonneg f _) _,
        Real.rpow_nonneg (sSupNormIm_nonneg f _) _ ⟩
    · rcases h with ⟨h0, h1⟩
      rw [ne_comm] at h0 h1
      simp_rw [interpStrip_eq_of_pos f _ (lt_of_le_of_ne (sSupNormIm_nonneg f 0) h0)
        (lt_of_le_of_ne (sSupNormIm_nonneg f 1) h1)]
      simp only [norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h0).mp (sSupNormIm_nonneg f _)) _]
      rw [norm_cpow_eq_rpow_re_of_pos ((Ne.le_iff_lt h1).mp (sSupNormIm_nonneg f _)) _]
      simp only [sub_re, one_re, le_refl]
  apply (norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ f hz hd hB).trans (this.trans _)
  apply mul_le_mul_of_nonneg _ _ (Real.rpow_nonneg (sSupNormIm_nonneg f _) _)
  · apply (Real.rpow_nonneg _ _)
    specialize hb 1
    simp only [mem_preimage, one_re, mem_singleton_iff, forall_true_left] at hb
    exact (norm_nonneg _).trans hb
  · gcongr
    · exact sSupNormIm_nonneg f _
    · exact sub_nonneg.mpr hz.2
    rw [sSupNormIm]
    apply csSup_le _
    · simpa [comp_apply, mem_image, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂] using ha
    · use ‖(f 0)‖, 0
      simp
  · apply Real.rpow_le_rpow (sSupNormIm_nonneg f _) _ hz.1
    · rw [sSupNormIm]
      apply csSup_le _
      · simpa [comp_apply, mem_image, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] using hb
      · use ‖(f 1)‖, 1
        simp only [mem_preimage, one_re, mem_singleton_iff, comp_apply,
          and_self]

/--
lemma `scale_id_mem_verticalStrip_of_mem_verticalStrip` / 引理 `scale_id_mem_verticalStrip_of_mem_verticalStrip`

English:
lemma scale_id_mem_verticalStrip_of_mem_verticalStrip
  statement: {l u : Real} (hul : l < u) {z : Complex}
  proof: by
  simp only [verticalStrip, mem_preimage, mem_Ioo] at hz
  simp only [verticalStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im, ofReal_im,
    sub_self, mul_zero, sub_zero, mem_Ioo, lt_add_iff_pos_right]
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [hz₁, mul_pos_iff_of_pos_left, sub_pos, hul, true_and]
  rw [add_comm]; rw [← sub_lt_sub_iff_right l]; rw [add_sub_assoc]; rw [sub_self]; rw [add_zero]
  nth_rewrite 2 [← one_mul (u - l)]
  gcongr

中文:
引理 scale_id_mem_verticalStrip_of_mem_verticalStrip
  结论: {l u : 实数} (hul : l < u) {z : 复形}
  证明: by
  simp only [verticalStrip, mem_preimage, mem_Ioo] at hz
  simp only [verticalStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im, ofReal_im,
    sub_self, mul_zero, sub_zero, mem_Ioo, lt_add_iff_pos_right]
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [hz₁, mul_pos_iff_of_pos_left, sub_pos, hul, true_and]
  rw [add_comm]; rw [← sub_lt_sub_iff_right l]; rw [add_sub_assoc]; rw [sub_self]; rw [add_zero]
  nth_rewrite 2 [← one_mul (u - l)]
  gcongr

Depends on / 依赖: add_comm, add_re, add_sub_assoc, add_zero, lt_add_iff_pos_right, mem_Ioo, mem_preimage, mul_pos_iff_of_pos_left, mul_re, mul_zero, nth_rewrite, ofReal_im, ofReal_re, one_mul, sub_im, sub_lt_sub_iff_right, sub_pos, sub_re, sub_self, sub_zero
-/
lemma scale_id_mem_verticalStrip_of_mem_verticalStrip {l u : Real} (hul : l < u) {z : Complex}
    (hz : z in verticalStrip 0 1) : l + z * (u - l) in verticalStrip l u := by
  simp only [verticalStrip, mem_preimage, mem_Ioo] at hz
  simp only [verticalStrip, mem_preimage, add_re, ofReal_re, mul_re, sub_re, sub_im, ofReal_im,
    sub_self, mul_zero, sub_zero, mem_Ioo, lt_add_iff_pos_right]
  obtain ⟨hz₁, hz₂⟩ := hz
  simp only [hz₁, mul_pos_iff_of_pos_left, sub_pos, hul, true_and]
  rw [add_comm]; rw [← sub_lt_sub_iff_right l]; rw [add_sub_assoc]; rw [sub_self]; rw [add_zero]
  nth_rewrite 2 [← one_mul (u - l)]
  gcongr

/--
lemma `mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip` / 引理 `mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip`

English:
lemma mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip
  statement: {z : Complex} {l u : Real} (hul : l < u)
  proof: by
  simp only [verticalClosedStrip, Complex.div_re, mem_preimage, sub_re, mem_Icc,
    sub_nonneg, tsub_le_iff_right, ofReal_re, ofReal_im, sub_im, sub_self, mul_zero, zero_div,
    add_zero]
  simp only [verticalClosedStrip] at hz
  norm_cast
  simp_rw [Complex.normSq_ofReal, mul_div_assoc, div_mul_eq_div_div_swap,
    div_self (by linarith : u - l != 0), ← div_eq_mul_one_div]
  constructor
  · gcongr
    exact hz.1
  · rw [← sub_le_sub_iff_right (l / (u - l)), add_sub_assoc, sub_self, add_zero, div_sub_div_same,
      div_le_one (by simp [hul]), sub_le_sub_iff_right l]
    exact hz.2

中文:
引理 mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip
  结论: {z : 复形} {l u : 实数} (hul : l < u)
  证明: by
  simp only [verticalClosedStrip, Complex.div_re, mem_preimage, sub_re, mem_Icc,
    sub_nonneg, tsub_le_iff_right, ofReal_re, ofReal_im, sub_im, sub_self, mul_zero, zero_div,
    add_zero]
  simp only [verticalClosedStrip] at hz
  norm_cast
  simp_rw [Complex.normSq_ofReal, mul_div_assoc, div_mul_eq_div_div_swap,
    div_self (by linarith : u - l != 0), ← div_eq_mul_one_div]
  constructor
  · gcongr
    exact hz.1
  · rw [← sub_le_sub_iff_right (l / (u - l)), add_sub_assoc, sub_self, add_zero, div_sub_div_same,
      div_le_one (by simp [hul]), sub_le_sub_iff_right l]
    exact hz.2

Depends on / 依赖: Complex.div_re, Complex.normSq_ofReal, add_sub_assoc, add_zero, div_eq_mul_one_div, div_le_on, div_mul_eq_div_div_swap, div_re, div_self, div_sub_div_same, mem_Icc, mem_preimage, mul_div_assoc, mul_zero, normSq_ofReal, ofReal_im, ofReal_re, simp_rw, sub_im, sub_le_sub_iff_right
-/
lemma mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip {z : Complex} {l u : Real} (hul : l < u)
    (hz : z in verticalClosedStrip l u) : z / (u - l) - l / (u - l) in verticalClosedStrip 0 1 := by
  simp only [verticalClosedStrip, Complex.div_re, mem_preimage, sub_re, mem_Icc,
    sub_nonneg, tsub_le_iff_right, ofReal_re, ofReal_im, sub_im, sub_self, mul_zero, zero_div,
    add_zero]
  simp only [verticalClosedStrip] at hz
  norm_cast
  simp_rw [Complex.normSq_ofReal, mul_div_assoc, div_mul_eq_div_div_swap,
    div_self (by linarith : u - l != 0), ← div_eq_mul_one_div]
  constructor
  · gcongr
    exact hz.1
  · rw [← sub_le_sub_iff_right (l / (u - l)), add_sub_assoc, sub_self, add_zero, div_sub_div_same,
      div_le_one (by simp [hul]), sub_le_sub_iff_right l]
    exact hz.2

/--
lemma `scale_diffContOnCl` / 引理 `scale_diffContOnCl`

English:
lemma scale_diffContOnCl
  statement: {f : Complex -> E} {l u : Real} (hul : l < u)
  proof: by
  unfold scale
  apply DiffContOnCl.comp (s := verticalStrip l u) hd
  · apply DiffContOnCl.const_add
    apply DiffContOnCl.smul_const
    exact Differentiable.diffContOnCl differentiable_id
  · rw [MapsTo]
    intro z hz
    exact scale_id_mem_verticalStrip_of_mem_verticalStrip hul hz

中文:
引理 scale_diffContOnCl
  结论: {f : 复形 -> E} {l u : 实数} (hul : l < u)
  证明: by
  unfold scale
  apply DiffContOnCl.comp (s := verticalStrip l u) hd
  · apply DiffContOnCl.const_add
    apply DiffContOnCl.smul_const
    exact Differentiable.diffContOnCl differentiable_id
  · rw [MapsTo]
    intro z hz
    exact scale_id_mem_verticalStrip_of_mem_verticalStrip hul hz

Depends on / 依赖: DiffContOnCl, DiffContOnCl.comp, DiffContOnCl.const_add, DiffContOnCl.smul_const, Differentiable, Differentiable.diffContOnCl, MapsTo, const_add, diffContOnCl, differentiable_id, scale_id_mem_verticalStrip_of_mem_verticalStrip, smul_const, verticalStrip
-/
lemma scale_diffContOnCl {f : Complex -> E} {l u : Real} (hul : l < u)
    (hd : DiffContOnCl Complex f (verticalStrip l u)) :
    DiffContOnCl Complex (scale f l u) (verticalStrip 0 1) := by
  unfold scale
  apply DiffContOnCl.comp (s := verticalStrip l u) hd
  · apply DiffContOnCl.const_add
    apply DiffContOnCl.smul_const
    exact Differentiable.diffContOnCl differentiable_id
  · rw [MapsTo]
    intro z hz
    exact scale_id_mem_verticalStrip_of_mem_verticalStrip hul hz

/--
lemma `fun_arg_eq` / 引理 `fun_arg_eq`

English:
lemma fun_arg_eq
  given: {l u : Real} (hul : l < u) (z : Complex)
  proof: by
  rw [sub_mul]; rw [div_mul_comm]; rw [div_self (by norm_cast; linarith)]; rw [div_mul_comm]; rw [div_self (by norm_cast; linarith)]
  simp

中文:
引理 fun_arg_eq
  条件: {l u : 实数} (hul : l < u) (z : 复形)
  证明: by
  rw [sub_mul]; rw [div_mul_comm]; rw [div_self (by norm_cast; linarith)]; rw [div_mul_comm]; rw [div_self (by norm_cast; linarith)]
  simp
-/
private lemma fun_arg_eq {l u : Real} (hul : l < u) (z : Complex) :
    (↑l + (z / (↑u - ↑l) - ↑l / (↑u - ↑l)) * (↑u - ↑l)) = z := by
  rw [sub_mul]; rw [div_mul_comm]; rw [div_self (by norm_cast; linarith)]; rw [div_mul_comm]; rw [div_self (by norm_cast; linarith)]
  simp

/--
lemma `bound_exp_eq` / 引理 `bound_exp_eq`

English:
lemma bound_exp_eq
  given: {l u : Real} (hul : l < u) (z : Complex)
  proof: by
  norm_cast
  rw [Complex.div_re]; rw [Complex.normSq_ofReal]; rw [Complex.ofReal_re]; rw [Complex.ofReal_im]; rw [mul_div_assoc]; rw [div_mul_eq_div_div_swap]; rw [div_self (by norm_cast; linarith)]; rw [← div_eq_mul_one_div]
  simp only [mul_zero, zero_div, add_zero]
  rw [← div_sub_div_same]

中文:
引理 bound_exp_eq
  条件: {l u : 实数} (hul : l < u) (z : 复形)
  证明: by
  norm_cast
  rw [Complex.div_re]; rw [Complex.normSq_ofReal]; rw [Complex.ofReal_re]; rw [Complex.ofReal_im]; rw [mul_div_assoc]; rw [div_mul_eq_div_div_swap]; rw [div_self (by norm_cast; linarith)]; rw [← div_eq_mul_one_div]
  simp only [mul_zero, zero_div, add_zero]
  rw [← div_sub_div_same]
-/
private lemma bound_exp_eq {l u : Real} (hul : l < u) (z : Complex) :
    (z / (↑u - ↑l)).re - ((l : Complex) / (↑u - ↑l)).re = (z.re - l) / (u - l) := by
  norm_cast
  rw [Complex.div_re]; rw [Complex.normSq_ofReal]; rw [Complex.ofReal_re]; rw [Complex.ofReal_im]; rw [mul_div_assoc]; rw [div_mul_eq_div_div_swap]; rw [div_self (by norm_cast; linarith)]; rw [← div_eq_mul_one_div]
  simp only [mul_zero, zero_div, add_zero]
  rw [← div_sub_div_same]

/--
lemma `norm_le_interpStrip_of_mem_verticalClosedStrip` / 引理 `norm_le_interpStrip_of_mem_verticalClosedStrip`

English:
lemma norm_le_interpStrip_of_mem_verticalClosedStrip
  statement: {l u : Real} (hul : l < u)
  proof: by
  have hgoal := norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz)
    (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
  simp only [scale, smul_eq_mul] at hgoal
  rw [fun_arg_eq hul]; rw [div_sub_div_same]; rw [interpStrip_scale f hul z] at hgoal
  exact hgoal

中文:
引理 norm_le_interpStrip_of_mem_verticalClosedStrip
  结论: {l u : 实数} (hul : l < u)
  证明: by
  have hgoal := norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz)
    (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
  simp only [scale, smul_eq_mul] at hgoal
  rw [fun_arg_eq hul]; rw [div_sub_div_same]; rw [interpStrip_scale f hul z] at hgoal
  exact hgoal

Depends on / 依赖: div_sub_div_same, fun_arg_eq, interpStrip_scale, mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip, scale_bddAbove, scale_diffContOnCl, smul_eq_mul
-/
lemma norm_le_interpStrip_of_mem_verticalClosedStrip {l u : Real} (hul : l < u)
    {f : Complex -> E} {z : Complex}
    (hz : z in verticalClosedStrip l u) (hd : DiffContOnCl Complex f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u)) :
    ‖f z‖ <= ‖interpStrip' f l u z‖ := by
  have hgoal := norm_le_interpStrip_of_mem_verticalClosedStrip₀₁ (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz)
    (scale_diffContOnCl hul hd) (scale_bddAbove hul hB)
  simp only [scale, smul_eq_mul] at hgoal
  rw [fun_arg_eq hul]; rw [div_sub_div_same]; rw [interpStrip_scale f hul z] at hgoal
  exact hgoal

/--
lemma `norm_le_interp_of_mem_verticalClosedStrip'` / 引理 `norm_le_interp_of_mem_verticalClosedStrip'`

English:
lemma norm_le_interp_of_mem_verticalClosedStrip'
  statement: {f : Complex -> E} {z : Complex} {a b l u : Real}
  proof: by
  have hgoal := norm_le_interp_of_mem_verticalClosedStrip₀₁' (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz) (scale_diffContOnCl hul hd)
    (scale_bddAbove hul hB) (scale_bound_left ha) (scale_bound_right hb)
  simp only [scale, smul_eq_mul, sub_re] at hgoal
  rw [fun_arg_eq hul]; rw [bound_exp_eq hul] at hgoal
  exact hgoal

中文:
引理 norm_le_interp_of_mem_verticalClosedStrip'
  结论: {f : 复形 -> E} {z : 复形} {a b l u : 实数}
  证明: by
  have hgoal := norm_le_interp_of_mem_verticalClosedStrip₀₁' (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz) (scale_diffContOnCl hul hd)
    (scale_bddAbove hul hB) (scale_bound_left ha) (scale_bound_right hb)
  simp only [scale, smul_eq_mul, sub_re] at hgoal
  rw [fun_arg_eq hul]; rw [bound_exp_eq hul] at hgoal
  exact hgoal

Depends on / 依赖: bound_exp_eq, fun_arg_eq, mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip, scale_bddAbove, scale_bound_left, scale_bound_right, scale_diffContOnCl, smul_eq_mul, sub_re
-/
lemma norm_le_interp_of_mem_verticalClosedStrip' {f : Complex -> E} {z : Complex} {a b l u : Real}
    (hul : l < u) (hz : z in verticalClosedStrip l u) (hd : DiffContOnCl Complex f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u))
    (ha : forall z in re ⁻¹' {l}, ‖f z‖ <= a) (hb : forall z in re ⁻¹' {u}, ‖f z‖ <= b) :
    ‖f z‖ <= a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) := by
  have hgoal := norm_le_interp_of_mem_verticalClosedStrip₀₁' (scale f l u)
    (mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip hul hz) (scale_diffContOnCl hul hd)
    (scale_bddAbove hul hB) (scale_bound_left ha) (scale_bound_right hb)
  simp only [scale, smul_eq_mul, sub_re] at hgoal
  rw [fun_arg_eq hul]; rw [bound_exp_eq hul] at hgoal
  exact hgoal

end HadamardThreeLines
end Complex
