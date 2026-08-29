/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of Shannon q-ary entropy and binary entropy functions

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1 - p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

More generally, the q-ary entropy function is the Shannon entropy of the random variable
with possible outcomes `{1, ..., q}`, where outcome `1` has probability `1 - p`
and all other outcomes are equally likely.

`qaryEntropy (q : ℕ) (p : ℝ) := p * log (q - 1) - p * log p - (1 - p) * log (1 - p)`

This file assumes that entropy is measured in Nats, hence the use of natural logarithms.
Most lemmas are also valid using a logarithm in a different base.

## Main declarations

* `Real.binEntropy`: the binary entropy function
* `Real.qaryEntropy`: the `q`-ary entropy function

## Main results

The functions are also defined outside the interval `Icc 0 1` due to `log x = log |x|`.

* They are continuous everywhere (`binEntropy_continuous` and `qaryEntropy_continuous`).
* They are differentiable everywhere except at points `0` or `1`
  (`hasDerivAt_binEntropy` and `hasDerivAt_qaryEntropy`).
  In addition, due to junk values, `deriv binEntropy p = log (1 - p) - log p`
  holds everywhere (`deriv_binEntropy`).
* they are strictly increasing on `Icc 0 (1 - 1/q))`
  (`qaryEntropy_strictMonoOn`, `binEntropy_strictMonoOn`)
  and strictly decreasing on `Icc (1 - 1/q) 1`
  (`binEntropy_strictAntiOn` and `qaryEntropy_strictAntiOn`).
* they are strictly concave on `Icc 0 1`
  (`strictConcaveOn_qaryEntropy` and `strictConcave_binEntropy`).

## Tags

entropy, Shannon, binary, nit, nepit
-/

public section

namespace Real
variable {q : Nat} {p : Real}

/-! ### Binary entropy -/

/--
Definition of `binEntropy` / `binEntropy` 的定义

English:
definition binEntropy
  signature: (p : Real)
  body: p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹

中文:
定义 binEntropy
  签名: (p : 实数)
  定义体: p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹
-/
@[pp_nodot] noncomputable def binEntropy (p : Real) : Real := p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹

/--
lemma `binEntropy_zero` / 引理 `binEntropy_zero`

English:
lemma binEntropy_zero
  statement: binEntropy 0 = 0
  proof: by simp [binEntropy]

中文:
引理 binEntropy_zero
  结论: binEntropy 0 = 0
  证明: by simp [binEntropy]
-/
@[simp] lemma binEntropy_zero : binEntropy 0 = 0 := by simp [binEntropy]

/--
lemma `binEntropy_one` / 引理 `binEntropy_one`

English:
lemma binEntropy_one
  statement: binEntropy 1 = 0
  proof: by simp [binEntropy]

中文:
引理 binEntropy_one
  结论: binEntropy 1 = 0
  证明: by simp [binEntropy]
-/
@[simp] lemma binEntropy_one : binEntropy 1 = 0 := by simp [binEntropy]

/--
lemma `binEntropy_two_inv` / 引理 `binEntropy_two_inv`

English:
lemma binEntropy_two_inv
  statement: binEntropy 2⁻¹ = log 2
  proof: by norm_num [binEntropy]; simp; ring

中文:
引理 binEntropy_two_inv
  结论: binEntropy 2⁻¹ = log 2
  证明: by norm_num [binEntropy]; simp; ring
-/
@[simp] lemma binEntropy_two_inv : binEntropy 2⁻¹ = log 2 := by norm_num [binEntropy]; simp; ring

/--
lemma `binEntropy_eq_negMulLog_add_negMulLog_one_sub` / 引理 `binEntropy_eq_negMulLog_add_negMulLog_one_sub`

English:
lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub
  given: (p : Real)
  proof: by simp [binEntropy, negMulLog, ← neg_mul]

中文:
引理 binEntropy_eq_negMulLog_add_negMulLog_one_sub
  条件: (p : 实数)
  证明: by simp [binEntropy, negMulLog, ← neg_mul]

Depends on / 依赖: binEntropy, negMulLog, neg_mul
-/
lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub (p : Real) :
    binEntropy p = negMulLog p + negMulLog (1 - p) := by simp [binEntropy, negMulLog, ← neg_mul]

/--
lemma `binEntropy_eq_negMulLog_add_negMulLog_one_sub'` / 引理 `binEntropy_eq_negMulLog_add_negMulLog_one_sub'`

English:
lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub'
  proof: funext binEntropy_eq_negMulLog_add_negMulLog_one_sub

中文:
引理 binEntropy_eq_negMulLog_add_negMulLog_one_sub'
  证明: funext binEntropy_eq_negMulLog_add_negMulLog_one_sub

Depends on / 依赖: HasStrongEpiMonoFactorisations, binEntropy_eq_negMulLog_add_negMulLog_one_sub
-/
lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub' :
    binEntropy = fun p => negMulLog p + negMulLog (1 - p) :=
  funext binEntropy_eq_negMulLog_add_negMulLog_one_sub

/--
lemma `binEntropy_one_sub` / 引理 `binEntropy_one_sub`

English:
lemma binEntropy_one_sub
  given: (p : Real)
  statement: binEntropy (1 - p) = binEntropy p
  proof: by
  simp [binEntropy, add_comm]

中文:
引理 binEntropy_one_sub
  条件: (p : 实数)
  结论: binEntropy (1 - p) = binEntropy p
  证明: by
  simp [binEntropy, add_comm]
-/
@[simp] lemma binEntropy_one_sub (p : Real) : binEntropy (1 - p) = binEntropy p := by
  simp [binEntropy, add_comm]

/--
lemma `binEntropy_two_inv_add` / 引理 `binEntropy_two_inv_add`

English:
lemma binEntropy_two_inv_add
  given: (p : Real)
  statement: binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p)
  proof: by
  rw [← binEntropy_one_sub]; ring_nf

中文:
引理 binEntropy_two_inv_add
  条件: (p : 实数)
  结论: binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p)
  证明: by
  rw [← binEntropy_one_sub]; ring_nf

Depends on / 依赖: binEntropy_one_sub, ring_nf
-/
lemma binEntropy_two_inv_add (p : Real) : binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p) := by
  rw [← binEntropy_one_sub]; ring_nf

/--
lemma `binEntropy_pos` / 引理 `binEntropy_pos`

English:
lemma binEntropy_pos
  given: (hp₀ : 0 < p) (hp₁ : p < 1)
  statement: 0 < binEntropy p
  proof: by
  unfold binEntropy
  have : 0 < 1 - p := sub_pos.2 hp₁
have : 0 < log p⁻¹ := log_pos (one_lt_inv₀ hp₀).2 hp₁
have : 0 < log (1 - p)⁻¹ := log_pos (one_lt_inv₀ ‹_›).2 (sub_lt_self _ hp₀)
  positivity

中文:
引理 binEntropy_pos
  条件: (hp₀ : 0 < p) (hp₁ : p < 1)
  结论: 0 < binEntropy p
  证明: by
  unfold binEntropy
  have : 0 < 1 - p := sub_pos.2 hp₁
have : 0 < log p⁻¹ := log_pos (one_lt_inv₀ hp₀).2 hp₁
have : 0 < log (1 - p)⁻¹ := log_pos (one_lt_inv₀ ‹_›).2 (sub_lt_self _ hp₀)
  positivity

Depends on / 依赖: binEntropy, log_pos, sub_lt_self, sub_pos
-/
lemma binEntropy_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < binEntropy p := by
  unfold binEntropy
  have : 0 < 1 - p := sub_pos.2 hp₁
have : 0 < log p⁻¹ := log_pos (one_lt_inv₀ hp₀).2 hp₁
have : 0 < log (1 - p)⁻¹ := log_pos (one_lt_inv₀ ‹_›).2 (sub_lt_self _ hp₀)
  positivity

/--
lemma `binEntropy_nonneg` / 引理 `binEntropy_nonneg`

English:
lemma binEntropy_nonneg
  given: (hp₀ : 0 <= p) (hp₁ : p <= 1)
  statement: 0 <= binEntropy p
  proof: by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  exact (binEntropy_pos hp₀ hp₁).le

中文:
引理 binEntropy_nonneg
  条件: (hp₀ : 0 <= p) (hp₁ : p <= 1)
  结论: 0 <= binEntropy p
  证明: by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  exact (binEntropy_pos hp₀ hp₁).le

Depends on / 依赖: Category, Category.assoc, IsImage, IsImage.isoExt_hom, IsImage.lift_, Limits, Limits.image, Limits.image.fac, binEntropy_pos, cancel_mono, coimageStrongEpiMonoFactorisation_m, cokernel, eq_or_lt, isoExt_hom
-/
lemma binEntropy_nonneg (hp₀ : 0 <= p) (hp₁ : p <= 1) : 0 <= binEntropy p := by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  exact (binEntropy_pos hp₀ hp₁).le

/--
lemma `binEntropy_neg_of_neg` / 引理 `binEntropy_neg_of_neg`

English:
lemma binEntropy_neg_of_neg
  given: (hp : p < 0)
  statement: binEntropy p < 0
  proof: by
  rw [binEntropy]; rw [log_inv]; rw [log_inv]
  suffices -p * log p < (1 - p) * log (1 - p) by linarith
  by_cases hp' : p < -1
  · have : log p < log (1 - p) := by
      rw [← log_neg_eq_log]
      exact log_lt_log (Left.neg_pos_iff.mpr hp) (by linarith)
    nlinarith [log_pos_of_lt_neg_one hp']
  · have : -p * log p <= 0 := by
      wlog h : -1 < p
      · simp only [show p = -1 by linarith, log_neg_eq_log, log_one, le_refl, mul_zero]
      · nlinarith [log_neg_of_lt_zero hp h]
    nlinarith [(log_pos (by linarith) : 0 < log (1 - p))]

中文:
引理 binEntropy_neg_of_neg
  条件: (hp : p < 0)
  结论: binEntropy p < 0
  证明: by
  rw [binEntropy]; rw [log_inv]; rw [log_inv]
  suffices -p * log p < (1 - p) * log (1 - p) by linarith
  by_cases hp' : p < -1
  · have : log p < log (1 - p) := by
      rw [← log_neg_eq_log]
      exact log_lt_log (Left.neg_pos_iff.mpr hp) (by linarith)
    nlinarith [log_pos_of_lt_neg_one hp']
  · have : -p * log p <= 0 := by
      wlog h : -1 < p
      · simp only [show p = -1 by linarith, log_neg_eq_log, log_one, le_refl, mul_zero]
      · nlinarith [log_neg_of_lt_zero hp h]
    nlinarith [(log_pos (by linarith) : 0 < log (1 - p))]

Depends on / 依赖: Left.neg_pos_iff.mpr, binEntropy, le_refl, log_inv, log_lt_log, log_neg_eq_log, log_neg_of_lt_zero, log_one, log_pos, log_pos_of_lt_neg_one, mul_zero, neg_pos_iff
-/
lemma binEntropy_neg_of_neg (hp : p < 0) : binEntropy p < 0 := by
  rw [binEntropy]; rw [log_inv]; rw [log_inv]
  suffices -p * log p < (1 - p) * log (1 - p) by linarith
  by_cases hp' : p < -1
  · have : log p < log (1 - p) := by
      rw [← log_neg_eq_log]
      exact log_lt_log (Left.neg_pos_iff.mpr hp) (by linarith)
    nlinarith [log_pos_of_lt_neg_one hp']
  · have : -p * log p <= 0 := by
      wlog h : -1 < p
      · simp only [show p = -1 by linarith, log_neg_eq_log, log_one, le_refl, mul_zero]
      · nlinarith [log_neg_of_lt_zero hp h]
    nlinarith [(log_pos (by linarith) : 0 < log (1 - p))]

/--
lemma `binEntropy_nonpos_of_nonpos` / 引理 `binEntropy_nonpos_of_nonpos`

English:
lemma binEntropy_nonpos_of_nonpos
  given: (hp : p <= 0)
  statement: binEntropy p <= 0
  proof: by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  · exact (binEntropy_neg_of_neg hp).le

中文:
引理 binEntropy_nonpos_of_nonpos
  条件: (hp : p <= 0)
  结论: binEntropy p <= 0
  证明: by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  · exact (binEntropy_neg_of_neg hp).le

Depends on / 依赖: binEntropy_neg_of_neg, eq_or_lt, hp.eq_or_lt
-/
lemma binEntropy_nonpos_of_nonpos (hp : p <= 0) : binEntropy p <= 0 := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  · exact (binEntropy_neg_of_neg hp).le

/--
lemma `binEntropy_neg_of_one_lt` / 引理 `binEntropy_neg_of_one_lt`

English:
lemma binEntropy_neg_of_one_lt
  given: (hp : 1 < p)
  statement: binEntropy p < 0
  proof: by
  rw [← binEntropy_one_sub]; exact binEntropy_neg_of_neg (sub_neg.2 hp)

中文:
引理 binEntropy_neg_of_one_lt
  条件: (hp : 1 < p)
  结论: binEntropy p < 0
  证明: by
  rw [← binEntropy_one_sub]; exact binEntropy_neg_of_neg (sub_neg.2 hp)

Depends on / 依赖: binEntropy_neg_of_neg, binEntropy_one_sub, sub_neg
-/
lemma binEntropy_neg_of_one_lt (hp : 1 < p) : binEntropy p < 0 := by
  rw [← binEntropy_one_sub]; exact binEntropy_neg_of_neg (sub_neg.2 hp)

/--
lemma `binEntropy_nonpos_of_one_le` / 引理 `binEntropy_nonpos_of_one_le`

English:
lemma binEntropy_nonpos_of_one_le
  given: (hp : 1 <= p)
  statement: binEntropy p <= 0
  proof: by
  rw [← binEntropy_one_sub]; exact binEntropy_nonpos_of_nonpos (sub_nonpos.2 hp)

中文:
引理 binEntropy_nonpos_of_one_le
  条件: (hp : 1 <= p)
  结论: binEntropy p <= 0
  证明: by
  rw [← binEntropy_one_sub]; exact binEntropy_nonpos_of_nonpos (sub_nonpos.2 hp)

Depends on / 依赖: binEntropy_nonpos_of_nonpos, binEntropy_one_sub, sub_nonpos
-/
lemma binEntropy_nonpos_of_one_le (hp : 1 <= p) : binEntropy p <= 0 := by
  rw [← binEntropy_one_sub]; exact binEntropy_nonpos_of_nonpos (sub_nonpos.2 hp)

/--
lemma `binEntropy_eq_zero` / 引理 `binEntropy_eq_zero`

English:
lemma binEntropy_eq_zero
  statement: binEntropy p = 0 ↔ p = 0 ∨ p = 1
  proof: by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  contrapose! h
  obtain hp₀ | hp₀ := h.1.lt_or_gt
  · exact (binEntropy_neg_of_neg hp₀).ne
  obtain hp₁ | hp₁ := h.2.lt_or_gt.symm
  · exact (binEntropy_neg_of_one_lt hp₁).ne
  · exact (binEntropy_pos hp₀ hp₁).ne'

中文:
引理 binEntropy_eq_zero
  结论: binEntropy p = 0 ↔ p = 0 ∨ p = 1
  证明: by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  contrapose! h
  obtain hp₀ | hp₀ := h.1.lt_or_gt
  · exact (binEntropy_neg_of_neg hp₀).ne
  obtain hp₁ | hp₁ := h.2.lt_or_gt.symm
  · exact (binEntropy_neg_of_one_lt hp₁).ne
  · exact (binEntropy_pos hp₀ hp₁).ne'

Depends on / 依赖: binEntropy_neg_of_neg, binEntropy_neg_of_one_lt, binEntropy_pos, contrapose, lt_or_gt, lt_or_gt.symm
-/
lemma binEntropy_eq_zero : binEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  contrapose! h
  obtain hp₀ | hp₀ := h.1.lt_or_gt
  · exact (binEntropy_neg_of_neg hp₀).ne
  obtain hp₁ | hp₁ := h.2.lt_or_gt.symm
  · exact (binEntropy_neg_of_one_lt hp₁).ne
  · exact (binEntropy_pos hp₀ hp₁).ne'

/--
lemma `binEntropy_lt_log_two` / 引理 `binEntropy_lt_log_two`

English:
lemma binEntropy_lt_log_two
  statement: binEntropy p < log 2 ↔ p != 2⁻¹
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro h rfl
    simp at h
  wlog hp : p < 2⁻¹
  · have hp : 1 - p < 2⁻¹ := by
      rw [sub_lt_comm]; norm_num at *; linarith +splitNe
    rw [← binEntropy_one_sub]
    exact this hp.ne hp
  obtain hp₀ | hp₀ := le_or_gt p 0
· exact (binEntropy_nonpos_of_nonpos hp₀).trans_lt log_pos by simp
have hp₁ : 0 < 1 - p := sub_pos.2 hp.trans by norm_num
  calc
  _ < log (p * p⁻¹ + (1 - p) * (1 - p)⁻¹) :=
    strictConcaveOn_log_Ioi.2 (inv_pos.2 hp₀) (inv_pos.2 hp₁)
      (by simpa [eq_sub_iff_add_eq, ← two_mul, mul_comm, mul_eq_one_iff_eq_inv₀]) hp₀ hp₁ (by simp)
  _ = log 2 := by rw [mul_inv_cancel₀, mul_inv_cancel₀, one_add_one_eq_two] <;> positivity

中文:
引理 binEntropy_lt_log_two
  结论: binEntropy p < log 2 ↔ p != 2⁻¹
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro h rfl
    simp at h
  wlog hp : p < 2⁻¹
  · have hp : 1 - p < 2⁻¹ := by
      rw [sub_lt_comm]; norm_num at *; linarith +splitNe
    rw [← binEntropy_one_sub]
    exact this hp.ne hp
  obtain hp₀ | hp₀ := le_or_gt p 0
· exact (binEntropy_nonpos_of_nonpos hp₀).trans_lt log_pos by simp
have hp₁ : 0 < 1 - p := sub_pos.2 hp.trans by norm_num
  calc
  _ < log (p * p⁻¹ + (1 - p) * (1 - p)⁻¹) :=
    strictConcaveOn_log_Ioi.2 (inv_pos.2 hp₀) (inv_pos.2 hp₁)
      (by simpa [eq_sub_iff_add_eq, ← two_mul, mul_comm, mul_eq_one_iff_eq_inv₀]) hp₀ hp₁ (by simp)
  _ = log 2 := by rw [mul_inv_cancel₀, mul_inv_cancel₀, one_add_one_eq_two] <;> positivity

Depends on / 依赖: binEntropy_nonpos_of_nonpos, binEntropy_one_sub, eq_sub_iff_add_eq, hp.ne, hp.trans, inv_pos, le_or_gt, log_pos, splitNe, strictConcaveOn_log_Ioi, sub_lt_comm, sub_pos, trans_lt, two_mul
-/
lemma binEntropy_lt_log_two : binEntropy p < log 2 ↔ p != 2⁻¹ := by
  refine ⟨?_, fun h => ?_⟩
  · rintro h rfl
    simp at h
  wlog hp : p < 2⁻¹
  · have hp : 1 - p < 2⁻¹ := by
      rw [sub_lt_comm]; norm_num at *; linarith +splitNe
    rw [← binEntropy_one_sub]
    exact this hp.ne hp
  obtain hp₀ | hp₀ := le_or_gt p 0
· exact (binEntropy_nonpos_of_nonpos hp₀).trans_lt log_pos by simp
have hp₁ : 0 < 1 - p := sub_pos.2 hp.trans by norm_num
  calc
  _ < log (p * p⁻¹ + (1 - p) * (1 - p)⁻¹) :=
    strictConcaveOn_log_Ioi.2 (inv_pos.2 hp₀) (inv_pos.2 hp₁)
      (by simpa [eq_sub_iff_add_eq, ← two_mul, mul_comm, mul_eq_one_iff_eq_inv₀]) hp₀ hp₁ (by simp)
  _ = log 2 := by rw [mul_inv_cancel₀, mul_inv_cancel₀, one_add_one_eq_two] <;> positivity

/--
lemma `binEntropy_le_log_two` / 引理 `binEntropy_le_log_two`

English:
lemma binEntropy_le_log_two
  statement: binEntropy p <= log 2
  proof: by
  obtain rfl | hp := eq_or_ne p 2⁻¹
  · simp
  · exact (binEntropy_lt_log_two.2 hp).le

中文:
引理 binEntropy_le_log_two
  结论: binEntropy p <= log 2
  证明: by
  obtain rfl | hp := eq_or_ne p 2⁻¹
  · simp
  · exact (binEntropy_lt_log_two.2 hp).le

Depends on / 依赖: binEntropy_lt_log_two, eq_or_ne
-/
lemma binEntropy_le_log_two : binEntropy p <= log 2 := by
  obtain rfl | hp := eq_or_ne p 2⁻¹
  · simp
  · exact (binEntropy_lt_log_two.2 hp).le

/--
lemma `binEntropy_eq_log_two` / 引理 `binEntropy_eq_log_two`

English:
lemma binEntropy_eq_log_two
  statement: binEntropy p = log 2 ↔ p = 2⁻¹
  proof: by
  rw [← binEntropy_le_log_two.not_lt_iff_eq]; rw [binEntropy_lt_log_two]; rw [not_ne_iff]

中文:
引理 binEntropy_eq_log_two
  结论: binEntropy p = log 2 ↔ p = 2⁻¹
  证明: by
  rw [← binEntropy_le_log_two.not_lt_iff_eq]; rw [binEntropy_lt_log_two]; rw [not_ne_iff]

Depends on / 依赖: binEntropy_le_log_two, binEntropy_le_log_two.not_lt_iff_eq, binEntropy_lt_log_two, not_lt_iff_eq, not_ne_iff
-/
lemma binEntropy_eq_log_two : binEntropy p = log 2 ↔ p = 2⁻¹ := by
  rw [← binEntropy_le_log_two.not_lt_iff_eq]; rw [binEntropy_lt_log_two]; rw [not_ne_iff]

/--
lemma `binEntropy_continuous` / 引理 `binEntropy_continuous`

English:
lemma binEntropy_continuous
  statement: Continuous binEntropy
  proof: by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; fun_prop

中文:
引理 binEntropy_continuous
  结论: 连续 binEntropy
  证明: by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; fun_prop
-/
@[fun_prop] lemma binEntropy_continuous : Continuous binEntropy := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; fun_prop

/--
lemma `differentiableAt_binEntropy` / 引理 `differentiableAt_binEntropy`

English:
lemma differentiableAt_binEntropy
  given: (hp₀ : p != 0) (hp₁ : p != 1)
  proof: by
  rw [ne_comm]; rw [← sub_ne_zero] at hp₁
  unfold binEntropy
  simp only [log_inv, mul_neg]
  fun_prop

中文:
引理 differentiableAt_binEntropy
  条件: (hp₀ : p != 0) (hp₁ : p != 1)
  证明: by
  rw [ne_comm]; rw [← sub_ne_zero] at hp₁
  unfold binEntropy
  simp only [log_inv, mul_neg]
  fun_prop
-/
@[fun_prop] lemma differentiableAt_binEntropy (hp₀ : p != 0) (hp₁ : p != 1) :
    DifferentiableAt Real binEntropy p := by
  rw [ne_comm]; rw [← sub_ne_zero] at hp₁
  unfold binEntropy
  simp only [log_inv, mul_neg]
  fun_prop

/--
lemma `differentiableAt_binEntropy_iff_ne_zero_one` / 引理 `differentiableAt_binEntropy_iff_ne_zero_one`

English:
lemma differentiableAt_binEntropy_iff_ne_zero_one
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => differentiableAt_binEntropy h.1 h.2⟩
    <;> rintro rfl <;> unfold binEntropy at h
  · rw [DifferentiableAt.fun_add_iff_left] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)
  · rw [DifferentiableAt.fun_add_iff_right, differentiableAt_iff_comp_const_sub (b := 1)] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)

中文:
引理 differentiableAt_binEntropy_iff_ne_zero_one
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => differentiableAt_binEntropy h.1 h.2⟩
    <;> rintro rfl <;> unfold binEntropy at h
  · rw [DifferentiableAt.fun_add_iff_left] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)
  · rw [DifferentiableAt.fun_add_iff_right, differentiableAt_iff_comp_const_sub (b := 1)] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fun_add_iff_left, DifferentiableAt.fun_add_iff_right, binEntropy, differentiableAt_binEntropy, differentiableAt_iff_comp_const_sub, differentiableAt_negMulLog_iff, fun_add_iff_left, fun_add_iff_right, fun_prop, log_inv, mul_neg, negMulLog_def, neg_mul
-/
lemma differentiableAt_binEntropy_iff_ne_zero_one :
    DifferentiableAt Real binEntropy p ↔ p != 0 ∧ p != 1 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => differentiableAt_binEntropy h.1 h.2⟩
    <;> rintro rfl <;> unfold binEntropy at h
  · rw [DifferentiableAt.fun_add_iff_left] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)
  · rw [DifferentiableAt.fun_add_iff_right, differentiableAt_iff_comp_const_sub (b := 1)] at h
    · simp [log_inv, mul_neg, ← neg_mul, ← negMulLog_def, differentiableAt_negMulLog_iff] at h
    · fun_prop (disch := simp)

/--
lemma `deriv_binEntropy` / 引理 `deriv_binEntropy`

English:
lemma deriv_binEntropy
  given: (p : Real)
  statement: deriv binEntropy p = log (1 - p) - log p
  proof: by
  by_cases hp : p != 0 ∧ p != 1
  · obtain ⟨hp₀, hp₁⟩ := hp
    rw [ne_comm]; rw [← sub_ne_zero] at hp₁
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; rw [deriv_fun_add]; rw [deriv_comp_const_sub]; rw [deriv_negMulLog hp₀]; rw [deriv_negMulLog hp₁]
    · ring
    all_goals fun_prop
  -- pathological case where `deriv = 0` since `binEntropy` is not differentiable there
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_binEntropy_iff_ne_zero_one.not.2 hp)]
    push +distrib Not at hp
    obtain rfl | rfl := hp <;> simp

中文:
引理 deriv_binEntropy
  条件: (p : 实数)
  结论: deriv binEntropy p = log (1 - p) - log p
  证明: by
  by_cases hp : p != 0 ∧ p != 1
  · obtain ⟨hp₀, hp₁⟩ := hp
    rw [ne_comm]; rw [← sub_ne_zero] at hp₁
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; rw [deriv_fun_add]; rw [deriv_comp_const_sub]; rw [deriv_negMulLog hp₀]; rw [deriv_negMulLog hp₁]
    · ring
    all_goals fun_prop
  -- pathological case where `deriv = 0` since `binEntropy` is not differentiable there
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_binEntropy_iff_ne_zero_one.not.2 hp)]
    push +distrib Not at hp
    obtain rfl | rfl := hp <;> simp

Depends on / 依赖: all_goals, binEntropy_eq_negMulLog_add_negMulLog_one_sub, deriv_comp_const_sub, deriv_fun_add, deriv_negMulLog, fun_prop, ne_comm, sub_ne_zero
-/
lemma deriv_binEntropy (p : Real) : deriv binEntropy p = log (1 - p) - log p := by
  by_cases hp : p != 0 ∧ p != 1
  · obtain ⟨hp₀, hp₁⟩ := hp
    rw [ne_comm]; rw [← sub_ne_zero] at hp₁
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; rw [deriv_fun_add]; rw [deriv_comp_const_sub]; rw [deriv_negMulLog hp₀]; rw [deriv_negMulLog hp₁]
    · ring
    all_goals fun_prop
  -- pathological case where `deriv = 0` since `binEntropy` is not differentiable there
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_binEntropy_iff_ne_zero_one.not.2 hp)]
    push +distrib Not at hp
    obtain rfl | rfl := hp <;> simp

/-! ### `q`-ary entropy -/

/--
Definition of `qaryEntropy` / `qaryEntropy` 的定义

English:
definition qaryEntropy
  signature: (q : Nat) (p : Real)
  body: p * log (q - 1 : Int) + binEntropy p

中文:
定义 qaryEntropy
  签名: (q : 自然数) (p : 实数)
  定义体: p * log (q - 1 : Int) + binEntropy p
-/
@[pp_nodot] noncomputable def qaryEntropy (q : Nat) (p : Real) : Real := p * log (q - 1 : Int) + binEntropy p

/--
lemma `qaryEntropy_zero` / 引理 `qaryEntropy_zero`

English:
lemma qaryEntropy_zero
  given: (q : Nat)
  statement: qaryEntropy q 0 = 0
  proof: by simp [qaryEntropy]

中文:
引理 qaryEntropy_zero
  条件: (q : 自然数)
  结论: qaryEntropy q 0 = 0
  证明: by simp [qaryEntropy]
-/
@[simp] lemma qaryEntropy_zero (q : Nat) : qaryEntropy q 0 = 0 := by simp [qaryEntropy]
/--
lemma `qaryEntropy_one` / 引理 `qaryEntropy_one`

English:
lemma qaryEntropy_one
  given: (q : Nat)
  statement: qaryEntropy q 1 = log (q - 1 : Int)
  proof: by simp [qaryEntropy]

中文:
引理 qaryEntropy_one
  条件: (q : 自然数)
  结论: qaryEntropy q 1 = log (q - 1 : 整数)
  证明: by simp [qaryEntropy]
-/
@[simp] lemma qaryEntropy_one (q : Nat) : qaryEntropy q 1 = log (q - 1 : Int) := by simp [qaryEntropy]
/--
lemma `qaryEntropy_two` / 引理 `qaryEntropy_two`

English:
lemma qaryEntropy_two
  statement: qaryEntropy 2 = binEntropy
  proof: by ext; simp [qaryEntropy]

中文:
引理 qaryEntropy_two
  结论: qaryEntropy 2 = binEntropy
  证明: by ext; simp [qaryEntropy]

Depends on / 依赖: HasEqualizers, hasEqualizers
-/
@[simp] lemma qaryEntropy_two : qaryEntropy 2 = binEntropy := by ext; simp [qaryEntropy]

/--
lemma `qaryEntropy_pos` / 引理 `qaryEntropy_pos`

English:
lemma qaryEntropy_pos
  given: (hp₀ : 0 < p) (hp₁ : p < 1)
  statement: 0 < qaryEntropy q p
  proof: by
  unfold qaryEntropy
  positivity [binEntropy_pos hp₀ hp₁]

中文:
引理 qaryEntropy_pos
  条件: (hp₀ : 0 < p) (hp₁ : p < 1)
  结论: 0 < qaryEntropy q p
  证明: by
  unfold qaryEntropy
  positivity [binEntropy_pos hp₀ hp₁]

Depends on / 依赖: HasPullbacks, binEntropy_pos, hasPullbacks, qaryEntropy
-/
lemma qaryEntropy_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  positivity [binEntropy_pos hp₀ hp₁]

/--
lemma `qaryEntropy_nonneg` / 引理 `qaryEntropy_nonneg`

English:
lemma qaryEntropy_nonneg
  given: (hp₀ : 0 <= p) (hp₁ : p <= 1)
  statement: 0 <= qaryEntropy q p
  proof: by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simpa [qaryEntropy, -Int.cast_sub] using log_intCast_nonneg _
  exact (qaryEntropy_pos hp₀ hp₁).le

中文:
引理 qaryEntropy_nonneg
  条件: (hp₀ : 0 <= p) (hp₁ : p <= 1)
  结论: 0 <= qaryEntropy q p
  证明: by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simpa [qaryEntropy, -Int.cast_sub] using log_intCast_nonneg _
  exact (qaryEntropy_pos hp₀ hp₁).le

Depends on / 依赖: HasCoequalizers, Int.cast_sub, cast_sub, eq_or_lt, hasCoequalizers, log_intCast_nonneg, qaryEntropy, qaryEntropy_pos
-/
lemma qaryEntropy_nonneg (hp₀ : 0 <= p) (hp₁ : p <= 1) : 0 <= qaryEntropy q p := by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simpa [qaryEntropy, -Int.cast_sub] using log_intCast_nonneg _
  exact (qaryEntropy_pos hp₀ hp₁).le

/--
lemma `qaryEntropy_neg_of_neg` / 引理 `qaryEntropy_neg_of_neg`

English:
lemma qaryEntropy_neg_of_neg
  given: (hp : p < 0)
  statement: qaryEntropy q p < 0
  proof: add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg hp.le (log_intCast_nonneg _))
    (binEntropy_neg_of_neg hp)

中文:
引理 qaryEntropy_neg_of_neg
  条件: (hp : p < 0)
  结论: qaryEntropy q p < 0
  证明: add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg hp.le (log_intCast_nonneg _))
    (binEntropy_neg_of_neg hp)

Depends on / 依赖: HasPushouts, add_neg_of_nonpos_of_neg, binEntropy_neg_of_neg, hasPushouts, hp.le, log_intCast_nonneg, mul_nonpos_of_nonpos_of_nonneg
-/
lemma qaryEntropy_neg_of_neg (hp : p < 0) : qaryEntropy q p < 0 :=
  add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg hp.le (log_intCast_nonneg _))
    (binEntropy_neg_of_neg hp)

/--
lemma `qaryEntropy_nonpos_of_nonpos` / 引理 `qaryEntropy_nonpos_of_nonpos`

English:
lemma qaryEntropy_nonpos_of_nonpos
  given: (hp : p <= 0)
  statement: qaryEntropy q p <= 0
  proof: add_nonpos (mul_nonpos_of_nonpos_of_nonneg hp (log_intCast_nonneg _))
    (binEntropy_nonpos_of_nonpos hp)

中文:
引理 qaryEntropy_nonpos_of_nonpos
  条件: (hp : p <= 0)
  结论: qaryEntropy q p <= 0
  证明: add_nonpos (mul_nonpos_of_nonpos_of_nonneg hp (log_intCast_nonneg _))
    (binEntropy_nonpos_of_nonpos hp)

Depends on / 依赖: HasFiniteLimits, add_nonpos, binEntropy_nonpos_of_nonpos, hasFiniteLimits, log_intCast_nonneg, mul_nonpos_of_nonpos_of_nonneg
-/
lemma qaryEntropy_nonpos_of_nonpos (hp : p <= 0) : qaryEntropy q p <= 0 :=
  add_nonpos (mul_nonpos_of_nonpos_of_nonneg hp (log_intCast_nonneg _))
    (binEntropy_nonpos_of_nonpos hp)

/--
lemma `qaryEntropy_continuous` / 引理 `qaryEntropy_continuous`

English:
lemma qaryEntropy_continuous
  statement: Continuous (qaryEntropy q)
  proof: by
  unfold qaryEntropy; fun_prop

中文:
引理 qaryEntropy_continuous
  结论: 连续 (qaryEntropy q)
  证明: by
  unfold qaryEntropy; fun_prop

Depends on / 依赖: HasFiniteColimits, hasFiniteColimits
-/
@[fun_prop] lemma qaryEntropy_continuous : Continuous (qaryEntropy q) := by
  unfold qaryEntropy; fun_prop

/--
lemma `differentiableAt_qaryEntropy` / 引理 `differentiableAt_qaryEntropy`

English:
lemma differentiableAt_qaryEntropy
  given: (hp₀ : p != 0) (hp₁ : p != 1)
  proof: by unfold qaryEntropy; fun_prop

中文:
引理 differentiableAt_qaryEntropy
  条件: (hp₀ : p != 0) (hp₁ : p != 1)
  证明: by unfold qaryEntropy; fun_prop
-/
@[fun_prop] lemma differentiableAt_qaryEntropy (hp₀ : p != 0) (hp₁ : p != 1) :
    DifferentiableAt Real (qaryEntropy q) p := by unfold qaryEntropy; fun_prop

/--
lemma `deriv_qaryEntropy` / 引理 `deriv_qaryEntropy`

English:
lemma deriv_qaryEntropy
  given: (hp₀ : p != 0) (hp₁ : p != 1)
  proof: by
  unfold qaryEntropy
  rw [deriv_fun_add]
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, differentiableAt_fun_id,
      deriv_mul_const, deriv_id'', one_mul, deriv_binEntropy, add_sub_assoc]
  all_goals fun_prop

中文:
引理 deriv_qaryEntropy
  条件: (hp₀ : p != 0) (hp₁ : p != 1)
  证明: by
  unfold qaryEntropy
  rw [deriv_fun_add]
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, differentiableAt_fun_id,
      deriv_mul_const, deriv_id'', one_mul, deriv_binEntropy, add_sub_assoc]
  all_goals fun_prop

Depends on / 依赖: Int.cast_natCast, Int.cast_one, Int.cast_sub, add_sub_assoc, all_goals, cast_natCast, cast_one, cast_sub, deriv_binEntropy, deriv_fun_add, deriv_id, deriv_mul_const, differentiableAt_fun_id, fun_prop, one_mul, qaryEntropy
-/
lemma deriv_qaryEntropy (hp₀ : p != 0) (hp₁ : p != 1) :
    deriv (qaryEntropy q) p = log (q - 1) + log (1 - p) - log p := by
  unfold qaryEntropy
  rw [deriv_fun_add]
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, differentiableAt_fun_id,
      deriv_mul_const, deriv_id'', one_mul, deriv_binEntropy, add_sub_assoc]
  all_goals fun_prop

/--
lemma `hasDerivAt_binEntropy` / 引理 `hasDerivAt_binEntropy`

English:
lemma hasDerivAt_binEntropy
  given: (hp₀ : p != 0) (hp₁ : p != 1)
  proof: deriv_binEntropy _ ▸ (differentiableAt_binEntropy hp₀ hp₁).hasDerivAt

中文:
引理 hasDerivAt_binEntropy
  条件: (hp₀ : p != 0) (hp₁ : p != 1)
  证明: deriv_binEntropy _ ▸ (differentiableAt_binEntropy hp₀ hp₁).hasDerivAt

Depends on / 依赖: deriv_binEntropy, differentiableAt_binEntropy, hasDerivAt
-/
lemma hasDerivAt_binEntropy (hp₀ : p != 0) (hp₁ : p != 1) :
    HasDerivAt binEntropy (log (1 - p) - log p) p :=
  deriv_binEntropy _ ▸ (differentiableAt_binEntropy hp₀ hp₁).hasDerivAt

/--
lemma `hasDerivAt_qaryEntropy` / 引理 `hasDerivAt_qaryEntropy`

English:
lemma hasDerivAt_qaryEntropy
  given: (hp₀ : p != 0) (hp₁ : p != 1)
  proof: deriv_qaryEntropy hp₀ hp₁ ▸ (differentiableAt_qaryEntropy hp₀ hp₁).hasDerivAt

中文:
引理 hasDerivAt_qaryEntropy
  条件: (hp₀ : p != 0) (hp₁ : p != 1)
  证明: deriv_qaryEntropy hp₀ hp₁ ▸ (differentiableAt_qaryEntropy hp₀ hp₁).hasDerivAt

Depends on / 依赖: deriv_qaryEntropy, differentiableAt_qaryEntropy, hasDerivAt
-/
lemma hasDerivAt_qaryEntropy (hp₀ : p != 0) (hp₁ : p != 1) :
    HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - p) - log p) p :=
  deriv_qaryEntropy hp₀ hp₁ ▸ (differentiableAt_qaryEntropy hp₀ hp₁).hasDerivAt

open Filter Topology Set

/--
lemma `tendsto_log_one_sub_sub_log_nhdsGT_atAtop` / 引理 `tendsto_log_one_sub_sub_log_nhdsGT_atAtop`

English:
lemma tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  proof: by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1 / 2) : Real)
  · have h₁ : (0 : Real) < 1 / 2 := by simp
    filter_upwards [Ioc_mem_nhdsGT h₁] with p hx
    gcongr
    linarith [hx.2]
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsGT_zero

中文:
引理 tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  证明: by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1 / 2) : Real)
  · have h₁ : (0 : Real) < 1 / 2 := by simp
    filter_upwards [Ioc_mem_nhdsGT h₁] with p hx
    gcongr
    linarith [hx.2]
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsGT_zero
-/
private lemma tendsto_log_one_sub_sub_log_nhdsGT_atAtop :
    Tendsto (fun p => log (1 - p) - log p) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1 / 2) : Real)
  · have h₁ : (0 : Real) < 1 / 2 := by simp
    filter_upwards [Ioc_mem_nhdsGT h₁] with p hx
    gcongr
    linarith [hx.2]
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsGT_zero

/--
lemma `tendsto_log_one_sub_sub_log_nhdsLT_one_atBot` / 引理 `tendsto_log_one_sub_sub_log_nhdsLT_one_atBot`

English:
lemma tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  proof: by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsGT_zero
    apply Tendsto.comp (f := (1 - ·)) (g := log) this
    have contF : Continuous ((1 : Real) - ·) := continuous_sub_left 1
    have : MapsTo ((1 : Real) - ·) (Iio 1) (Ioi 0) := by
      intro p hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert! ContinuousWithinAt.tendsto_nhdsWithin (x := (1 : Real)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : Real) - (2 : Real)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsLT h₁] with p hx
    gcongr
    exact hx.1

中文:
引理 tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  证明: by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsGT_zero
    apply Tendsto.comp (f := (1 - ·)) (g := log) this
    have contF : Continuous ((1 : Real) - ·) := continuous_sub_left 1
    have : MapsTo ((1 : Real) - ·) (Iio 1) (Ioi 0) := by
      intro p hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert! ContinuousWithinAt.tendsto_nhdsWithin (x := (1 : Real)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : Real) - (2 : Real)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsLT h₁] with p hx
    gcongr
    exact hx.1
-/
private lemma tendsto_log_one_sub_sub_log_nhdsLT_one_atBot :
    Tendsto (fun p => log (1 - p) - log p) (𝓝[<] 1) atBot := by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsGT_zero
    apply Tendsto.comp (f := (1 - ·)) (g := log) this
    have contF : Continuous ((1 : Real) - ·) := continuous_sub_left 1
    have : MapsTo ((1 : Real) - ·) (Iio 1) (Ioi 0) := by
      intro p hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert! ContinuousWithinAt.tendsto_nhdsWithin (x := (1 : Real)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : Real) - (2 : Real)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsLT h₁] with p hx
    gcongr
    exact hx.1

/--
lemma `not_continuousAt_deriv_qaryEntropy_one` / 引理 `not_continuousAt_deriv_qaryEntropy_one`

English:
lemma not_continuousAt_deriv_qaryEntropy_one
  proof: by
  have tendstoBot : Tendsto (fun p => log (q - 1) + log (1 - p) - log p) (𝓝[<] 1) atBot := by
    have : (fun p => log (q - 1) + log (1 - p) - log p)
      = (fun p => log (q - 1) + (log (1 - p) - log p)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoBot) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atBot_iff, not_isBot, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsLT (show 1 - 2⁻¹ < (1 : Real) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith [show (1 : Real) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := Real)]

中文:
引理 not_continuousAt_deriv_qaryEntropy_one
  证明: by
  have tendstoBot : Tendsto (fun p => log (q - 1) + log (1 - p) - log p) (𝓝[<] 1) atBot := by
    have : (fun p => log (q - 1) + log (1 - p) - log p)
      = (fun p => log (q - 1) + (log (1 - p) - log p)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoBot) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atBot_iff, not_isBot, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsLT (show 1 - 2⁻¹ < (1 : Real) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith [show (1 : Real) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := Real)]

Depends on / 依赖: Filter, Filter.Tendsto.congr, Ioo_mem_nhdsLT, Tendsto, disjoint_nhds_atBot_iff, filter_upwards, nhdsWithin_le_nhds, not_continuousAt_of_tendsto, not_false_eq_true, not_isBot, tendstoBot, tendsto_atBot_add_const_left, tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
-/
lemma not_continuousAt_deriv_qaryEntropy_one :
    ¬ContinuousAt (deriv (qaryEntropy q)) 1 := by
  have tendstoBot : Tendsto (fun p => log (q - 1) + log (1 - p) - log p) (𝓝[<] 1) atBot := by
    have : (fun p => log (q - 1) + log (1 - p) - log p)
      = (fun p => log (q - 1) + (log (1 - p) - log p)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoBot) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atBot_iff, not_isBot, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsLT (show 1 - 2⁻¹ < (1 : Real) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith [show (1 : Real) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := Real)]

/--
lemma `not_continuousAt_deriv_qaryEntropy_zero` / 引理 `not_continuousAt_deriv_qaryEntropy_zero`

English:
lemma not_continuousAt_deriv_qaryEntropy_zero
  proof: by
  have tendstoTop : Tendsto (fun p => log (q - 1) + log (1 - p) - log p) (𝓝[>] 0) atTop := by
    have : (fun p => log (q - 1) + log (1 - p) - log p)
        = (fun p => log (q - 1) + (log (1 - p) - log p)) := by ext; ring
    rw [this]
    exact tendsto_atTop_add_const_left _ _ tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoTop) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atTop_iff, not_isTop, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := Real)]

中文:
引理 not_continuousAt_deriv_qaryEntropy_zero
  证明: by
  have tendstoTop : Tendsto (fun p => log (q - 1) + log (1 - p) - log p) (𝓝[>] 0) atTop := by
    have : (fun p => log (q - 1) + log (1 - p) - log p)
        = (fun p => log (q - 1) + (log (1 - p) - log p)) := by ext; ring
    rw [this]
    exact tendsto_atTop_add_const_left _ _ tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoTop) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atTop_iff, not_isTop, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := Real)]

Depends on / 依赖: Filter, Filter.Tendsto.congr, Ioo_mem_nhdsGT, Tendsto, disjoint_nhds_atTop_iff, filter_upwards, nhdsWithin_le_nhds, not_continuousAt_of_tendsto, not_false_eq_true, not_isTop, tendstoTop, tendsto_atTop_add_const_left, tendsto_log_one_sub_sub_log_nhdsGT_atAtop
-/
lemma not_continuousAt_deriv_qaryEntropy_zero :
    ¬ContinuousAt (deriv (qaryEntropy q)) 0 := by
  have tendstoTop : Tendsto (fun p => log (q - 1) + log (1 - p) - log p) (𝓝[>] 0) atTop := by
    have : (fun p => log (q - 1) + log (1 - p) - log p)
        = (fun p => log (q - 1) + (log (1 - p) - log p)) := by ext; ring
    rw [this]
    exact tendsto_atTop_add_const_left _ _ tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoTop) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atTop_iff, not_isTop, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := Real)]

/--
lemma `deriv2_qaryEntropy` / 引理 `deriv2_qaryEntropy`

English:
lemma deriv2_qaryEntropy
  proof: by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : p != 0 ∧ p != 1 -- normal case
  · obtain ⟨xne0, xne1⟩ := is_x_where_nondiff
    suffices forallᶠ y in (𝓝 p),
        deriv (fun p => (qaryEntropy q) p) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_fun_sub ?_ (differentiableAt_log xne0)]
      · rw [deriv.log differentiableAt_fun_id xne0]
        simp only [deriv_id'', one_div]
        · have {q : Real} (p : Real) : DifferentiableAt Real (fun p => q - p) p := by fun_prop
          simp [field, sub_ne_zero_of_ne xne1.symm, this]
          ring
      · apply DifferentiableAt.add
        · simp only [differentiableAt_const]
        exact DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr xne1.symm)
    filter_upwards [eventually_ne_nhds xne0, eventually_ne_nhds xne1]
      with y xne0 h2 using deriv_qaryEntropy xne0 h2
  -- Pathological case where we use junk value (because function not differentiable)
  · have : p = 0 ∨ p = 1 := Decidable.or_iff_not_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    · simp_all only [ne_eq, not_and, Decidable.not_not]
      cases this <;>
        simp_all only [mul_zero, one_ne_zero, zero_ne_one, sub_zero, mul_one, div_zero, sub_self]
    · intro h
      have contAt := h.continuousAt
      cases this <;>
        simp_all [not_continuousAt_deriv_qaryEntropy_zero, not_continuousAt_deriv_qaryEntropy_one]

中文:
引理 deriv2_qaryEntropy
  证明: by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : p != 0 ∧ p != 1 -- normal case
  · obtain ⟨xne0, xne1⟩ := is_x_where_nondiff
    suffices forallᶠ y in (𝓝 p),
        deriv (fun p => (qaryEntropy q) p) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_fun_sub ?_ (differentiableAt_log xne0)]
      · rw [deriv.log differentiableAt_fun_id xne0]
        simp only [deriv_id'', one_div]
        · have {q : Real} (p : Real) : DifferentiableAt Real (fun p => q - p) p := by fun_prop
          simp [field, sub_ne_zero_of_ne xne1.symm, this]
          ring
      · apply DifferentiableAt.add
        · simp only [differentiableAt_const]
        exact DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr xne1.symm)
    filter_upwards [eventually_ne_nhds xne0, eventually_ne_nhds xne1]
      with y xne0 h2 using deriv_qaryEntropy xne0 h2
  -- Pathological case where we use junk value (because function not differentiable)
  · have : p = 0 ∨ p = 1 := Decidable.or_iff_not_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    · simp_all only [ne_eq, not_and, Decidable.not_not]
      cases this <;>
        simp_all only [mul_zero, one_ne_zero, zero_ne_one, sub_zero, mul_one, div_zero, sub_self]
    · intro h
      have contAt := h.continuousAt
      cases this <;>
        simp_all [not_continuousAt_deriv_qaryEntropy_zero, not_continuousAt_deriv_qaryEntropy_one]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.deriv_eq, Function, Function.comp_apply, Function.id_comp, Function.iterate_succ, Function.iterate_zero, comp_apply, deriv.log, deriv_eq, deriv_fun_sub, deriv_id, differentiableAt_fun_id, differentiableAt_log, id_comp, is_x_where_nondiff, iterate_succ, iterate_zero, normal
-/
lemma deriv2_qaryEntropy :
    deriv^[2] (qaryEntropy q) p = -1 / (p * (1 - p)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases is_x_where_nondiff : p != 0 ∧ p != 1 -- normal case
  · obtain ⟨xne0, xne1⟩ := is_x_where_nondiff
    suffices forallᶠ y in (𝓝 p),
        deriv (fun p => (qaryEntropy q) p) y = log (q - 1) + log (1 - y) - log y by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_fun_sub ?_ (differentiableAt_log xne0)]
      · rw [deriv.log differentiableAt_fun_id xne0]
        simp only [deriv_id'', one_div]
        · have {q : Real} (p : Real) : DifferentiableAt Real (fun p => q - p) p := by fun_prop
          simp [field, sub_ne_zero_of_ne xne1.symm, this]
          ring
      · apply DifferentiableAt.add
        · simp only [differentiableAt_const]
        exact DifferentiableAt.log (by fun_prop) (sub_ne_zero.mpr xne1.symm)
    filter_upwards [eventually_ne_nhds xne0, eventually_ne_nhds xne1]
      with y xne0 h2 using deriv_qaryEntropy xne0 h2
  -- Pathological case where we use junk value (because function not differentiable)
  · have : p = 0 ∨ p = 1 := Decidable.or_iff_not_not_and_not.mpr is_x_where_nondiff
    rw [deriv_zero_of_not_differentiableAt]
    · simp_all only [ne_eq, not_and, Decidable.not_not]
      cases this <;>
        simp_all only [mul_zero, one_ne_zero, zero_ne_one, sub_zero, mul_one, div_zero, sub_self]
    · intro h
      have contAt := h.continuousAt
      cases this <;>
        simp_all [not_continuousAt_deriv_qaryEntropy_zero, not_continuousAt_deriv_qaryEntropy_one]

/--
lemma `deriv2_binEntropy` / 引理 `deriv2_binEntropy`

English:
lemma deriv2_binEntropy
  statement: deriv^[2] binEntropy p = -1 / (p * (1 - p))
  proof: qaryEntropy_two ▸ deriv2_qaryEntropy

中文:
引理 deriv2_binEntropy
  结论: deriv^[2] binEntropy p = -1 / (p * (1 - p))
  证明: qaryEntropy_two ▸ deriv2_qaryEntropy

Depends on / 依赖: deriv2_qaryEntropy, qaryEntropy_two
-/
lemma deriv2_binEntropy : deriv^[2] binEntropy p = -1 / (p * (1 - p)) :=
  qaryEntropy_two ▸ deriv2_qaryEntropy

/-! ### Strict monotonicity of entropy -/

/--
lemma `qaryEntropy_strictMonoOn` / 引理 `qaryEntropy_strictMonoOn`

English:
lemma qaryEntropy_strictMonoOn
  given: (qLe2 : 2 <= q)
  proof: by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1 / (q : Real))) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 <= (q : Real) := Nat.ofNat_le_cast.mpr qLe2
    have zero_le_qinv : 0 < (q : Real)⁻¹ := by positivity
    have : 0 < 1 - p := by
      simp only [sub_pos]
      have p_lt_1_minus_qinv : p < 1 - (q : Real)⁻¹ := by
        simp_all only [inv_pos, interior_Icc, mem_Ioo, one_div]
      linarith
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp only [sub_pos, gt_iff_lt]
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr hp.1)
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left, show 0 < (q : Real) - 1 by linarith]
      · have qpos : 0 < (q : Real) := by positivity
        have : q * p < q - 1 := by
          convert! mul_lt_mul_of_pos_left hp.2 qpos using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : p < 1)).symm

中文:
引理 qaryEntropy_strictMonoOn
  条件: (qLe2 : 2 <= q)
  证明: by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1 / (q : Real))) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 <= (q : Real) := Nat.ofNat_le_cast.mpr qLe2
    have zero_le_qinv : 0 < (q : Real)⁻¹ := by positivity
    have : 0 < 1 - p := by
      simp only [sub_pos]
      have p_lt_1_minus_qinv : p < 1 - (q : Real)⁻¹ := by
        simp_all only [inv_pos, interior_Icc, mem_Ioo, one_div]
      linarith
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp only [sub_pos, gt_iff_lt]
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr hp.1)
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left, show 0 < (q : Real) - 1 by linarith]
      · have qpos : 0 < (q : Real) := by positivity
        have : q * p < q - 1 := by
          convert! mul_lt_mul_of_pos_left hp.2 qpos using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : p < 1)).symm

Depends on / 依赖: Nat.ofNat_le_cast.mpr, continuousOn, convex_Icc, deriv_qa, interior_Icc, inv_pos, mem_Ioo, ofNat_le_cast, one_div, p_lt_1_minus_qinv, qaryEntropy_continuous, qaryEntropy_continuous.continuousOn, strictMonoOn_of_deriv_pos, sub_pos, zero_le_qinv
-/
lemma qaryEntropy_strictMonoOn (qLe2 : 2 <= q) :
    StrictMonoOn (qaryEntropy q) (Icc 0 (1 - 1 / q)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1 / (q : Real))) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 <= (q : Real) := Nat.ofNat_le_cast.mpr qLe2
    have zero_le_qinv : 0 < (q : Real)⁻¹ := by positivity
    have : 0 < 1 - p := by
      simp only [sub_pos]
      have p_lt_1_minus_qinv : p < 1 - (q : Real)⁻¹ := by
        simp_all only [inv_pos, interior_Icc, mem_Ioo, one_div]
      linarith
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp only [sub_pos, gt_iff_lt]
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr hp.1)
      · simp_all only [mem_Ioi, mul_pos_iff_of_pos_left, show 0 < (q : Real) - 1 by linarith]
      · have qpos : 0 < (q : Real) := by positivity
        have : q * p < q - 1 := by
          convert! mul_lt_mul_of_pos_left hp.2 qpos using 1
          simp only [mul_sub, mul_one, isUnit_iff_ne_zero, ne_eq, ne_of_gt qpos, not_false_eq_true,
            IsUnit.mul_inv_cancel]
        linarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp this : p < 1)).symm

/--
lemma `qaryEntropy_strictAntiOn` / 引理 `qaryEntropy_strictAntiOn`

English:
lemma qaryEntropy_strictAntiOn
  given: (qLe2 : 2 <= q)
  proof: by
  intro p1 hp1 p2 hp2 p1le2
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 - 1 / (q : Real)) 1) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 <= (q : Real) := Nat.ofNat_le_cast.mpr qLe2
    have qinv_lt_1 : (q : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have zero_lt_1_sub_p : 0 < 1 - p := by simp_all only [sub_pos, interior_Icc, mem_Ioo]
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp only [sub_neg, gt_iff_lt]
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr (show 0 < (↑q - 1) * (1 - p) by nlinarith))
      · simp_all only [mem_Ioi]
        linarith
      · have qpos : 0 < (q : Real) := by positivity
        ring_nf
        have : (q : Real) - 1 < p * q := by
          have h1 := mul_lt_mul_of_pos_right hp.1 qpos
          have h2 : (1 - (q : Real)⁻¹) * ↑q = q - 1 := by calc (1 - (q : Real)⁻¹) * ↑q
            _ = q - (q : Real)⁻¹ * (q : Real) := by ring
            _ = q - 1 := by simp [qpos.ne']
          rwa [h2] at h1
        nlinarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp zero_lt_1_sub_p : p < 1)).symm

中文:
引理 qaryEntropy_strictAntiOn
  条件: (qLe2 : 2 <= q)
  证明: by
  intro p1 hp1 p2 hp2 p1le2
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 - 1 / (q : Real)) 1) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 <= (q : Real) := Nat.ofNat_le_cast.mpr qLe2
    have qinv_lt_1 : (q : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have zero_lt_1_sub_p : 0 < 1 - p := by simp_all only [sub_pos, interior_Icc, mem_Ioo]
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp only [sub_neg, gt_iff_lt]
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr (show 0 < (↑q - 1) * (1 - p) by nlinarith))
      · simp_all only [mem_Ioi]
        linarith
      · have qpos : 0 < (q : Real) := by positivity
        ring_nf
        have : (q : Real) - 1 < p * q := by
          have h1 := mul_lt_mul_of_pos_right hp.1 qpos
          have h2 : (1 - (q : Real)⁻¹) * ↑q = q - 1 := by calc (1 - (q : Real)⁻¹) * ↑q
            _ = q - (q : Real)⁻¹ * (q : Real) := by ring
            _ = q - 1 := by simp [qpos.ne']
          rwa [h2] at h1
        nlinarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp zero_lt_1_sub_p : p < 1)).symm

Depends on / 依赖: Nat.ofNat_le_cast.mpr, continuousOn, convex_Icc, deriv_qaryEntropy, gt_iff_l, interior_Icc, mem_Ioo, ofNat_le_cast, one_div, qaryEntropy_continuous, qaryEntropy_continuous.continuousOn, qinv_lt_1, strictAntiOn_of_deriv_neg, sub_neg, sub_pos, zero_lt_1_sub_p
-/
lemma qaryEntropy_strictAntiOn (qLe2 : 2 <= q) :
    StrictAntiOn (qaryEntropy q) (Icc (1 - 1 / q) 1) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 - 1 / (q : Real)) 1) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have : 2 <= (q : Real) := Nat.ofNat_le_cast.mpr qLe2
    have qinv_lt_1 : (q : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have zero_lt_1_sub_p : 0 < 1 - p := by simp_all only [sub_pos, interior_Icc, mem_Ioo]
    simp only [one_div, interior_Icc, mem_Ioo] at hp
    rw [deriv_qaryEntropy (by linarith)]
    · simp only [sub_neg, gt_iff_lt]
      rw [← log_mul (by linarith) (by linarith)]
      apply Real.strictMonoOn_log (mem_Ioi.mpr (show 0 < (↑q - 1) * (1 - p) by nlinarith))
      · simp_all only [mem_Ioi]
        linarith
      · have qpos : 0 < (q : Real) := by positivity
        ring_nf
        have : (q : Real) - 1 < p * q := by
          have h1 := mul_lt_mul_of_pos_right hp.1 qpos
          have h2 : (1 - (q : Real)⁻¹) * ↑q = q - 1 := by calc (1 - (q : Real)⁻¹) * ↑q
            _ = q - (q : Real)⁻¹ * (q : Real) := by ring
            _ = q - 1 := by simp [qpos.ne']
          rwa [h2] at h1
        nlinarith
    exact (ne_of_gt (lt_add_neg_iff_lt.mp zero_lt_1_sub_p : p < 1)).symm

/--
lemma `binEntropy_strictMonoOn` / 引理 `binEntropy_strictMonoOn`

English:
lemma binEntropy_strictMonoOn
  statement: StrictMonoOn binEntropy (Icc 0 2⁻¹)
  proof: by
  rw [show Icc (0 : Real) 2⁻¹ = Icc 0 (1 - 1 / 2) by norm_num]; rw [← qaryEntropy_two]
  exact qaryEntropy_strictMonoOn (by rfl)

中文:
引理 binEntropy_strictMonoOn
  结论: StrictMonoOn binEntropy (闭区间 0 2⁻¹)
  证明: by
  rw [show Icc (0 : Real) 2⁻¹ = Icc 0 (1 - 1 / 2) by norm_num]; rw [← qaryEntropy_two]
  exact qaryEntropy_strictMonoOn (by rfl)

Depends on / 依赖: qaryEntropy_strictMonoOn, qaryEntropy_two
-/
lemma binEntropy_strictMonoOn : StrictMonoOn binEntropy (Icc 0 2⁻¹) := by
  rw [show Icc (0 : Real) 2⁻¹ = Icc 0 (1 - 1 / 2) by norm_num]; rw [← qaryEntropy_two]
  exact qaryEntropy_strictMonoOn (by rfl)

/--
lemma `binEntropy_strictAntiOn` / 引理 `binEntropy_strictAntiOn`

English:
lemma binEntropy_strictAntiOn
  statement: StrictAntiOn binEntropy (Icc 2⁻¹ 1)
  proof: by
  rw [show (Icc (2⁻¹ : Real) 1) = Icc (1 / 2) 1 by norm_num]; rw [← qaryEntropy_two]
  convert! qaryEntropy_strictAntiOn (by rfl) using 1
  norm_num

中文:
引理 binEntropy_strictAntiOn
  结论: StrictAntiOn binEntropy (闭区间 2⁻¹ 1)
  证明: by
  rw [show (Icc (2⁻¹ : Real) 1) = Icc (1 / 2) 1 by norm_num]; rw [← qaryEntropy_two]
  convert! qaryEntropy_strictAntiOn (by rfl) using 1
  norm_num

Depends on / 依赖: convert, qaryEntropy_strictAntiOn, qaryEntropy_two
-/
lemma binEntropy_strictAntiOn : StrictAntiOn binEntropy (Icc 2⁻¹ 1) := by
  rw [show (Icc (2⁻¹ : Real) 1) = Icc (1 / 2) 1 by norm_num]; rw [← qaryEntropy_two]
  convert! qaryEntropy_strictAntiOn (by rfl) using 1
  norm_num


/--
lemma `strictConcaveOn_qaryEntropy` / 引理 `strictConcaveOn_qaryEntropy`

English:
lemma strictConcaveOn_qaryEntropy
  statement: StrictConcaveOn Real (Icc 0 1) (qaryEntropy q)
  proof: by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro p hp
  rw [deriv2_qaryEntropy]
  · simp_all only [interior_Icc, mem_Ioo]
    apply div_neg_of_neg_of_pos
    · norm_num [show 0 < log 2 by positivity]
    · simp_all only [mul_pos_iff_of_pos_left, sub_pos]

中文:
引理 strictConcaveOn_qaryEntropy
  结论: StrictConcaveOn 实数 (闭区间 0 1) (qaryEntropy q)
  证明: by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro p hp
  rw [deriv2_qaryEntropy]
  · simp_all only [interior_Icc, mem_Ioo]
    apply div_neg_of_neg_of_pos
    · norm_num [show 0 < log 2 by positivity]
    · simp_all only [mul_pos_iff_of_pos_left, sub_pos]

Depends on / 依赖: continuousOn, convex_Icc, deriv2_qaryEntropy, div_neg_of_neg_of_pos, interior_Icc, mem_Ioo, mul_pos_iff_of_pos_left, qaryEntropy_continuous, qaryEntropy_continuous.continuousOn, strictConcaveOn_of_deriv2_neg, sub_pos
-/
lemma strictConcaveOn_qaryEntropy : StrictConcaveOn Real (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro p hp
  rw [deriv2_qaryEntropy]
  · simp_all only [interior_Icc, mem_Ioo]
    apply div_neg_of_neg_of_pos
    · norm_num [show 0 < log 2 by positivity]
    · simp_all only [mul_pos_iff_of_pos_left, sub_pos]

/--
lemma `strictConcave_binEntropy` / 引理 `strictConcave_binEntropy`

English:
lemma strictConcave_binEntropy
  statement: StrictConcaveOn Real (Icc 0 1) binEntropy
  proof: qaryEntropy_two ▸ strictConcaveOn_qaryEntropy

中文:
引理 strictConcave_binEntropy
  结论: StrictConcaveOn 实数 (闭区间 0 1) binEntropy
  证明: qaryEntropy_two ▸ strictConcaveOn_qaryEntropy

Depends on / 依赖: qaryEntropy_two, strictConcaveOn_qaryEntropy
-/
lemma strictConcave_binEntropy : StrictConcaveOn Real (Icc 0 1) binEntropy :=
  qaryEntropy_two ▸ strictConcaveOn_qaryEntropy

end Real
