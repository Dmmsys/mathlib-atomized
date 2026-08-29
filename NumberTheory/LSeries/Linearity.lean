/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Linearity of the L-series of `f` as a function of `f`

We show that the `LSeries` of `f : ℕ → ℂ` is a linear function of `f` (assuming convergence
of both L-series when adding two functions).
-/

public section

/-!
### Addition
-/

open LSeries

/--
lemma `LSeries.term_add` / 引理 `LSeries.term_add`

English:
lemma LSeries.term_add
  given: (f g : Nat -> Complex) (s : Complex)
  statement: term (f + g) s = term f s + term g s
  proof: by
  ext ⟨- | n⟩ <;>
  simp [add_div]

中文:
引理 LSeries.term_add
  条件: (f g : 自然数 -> 复形) (s : 复形)
  结论: term (f + g) s = term f s + term g s
  证明: by
  ext ⟨- | n⟩ <;>
  simp [add_div]

Depends on / 依赖: add_div
-/
lemma LSeries.term_add (f g : Nat -> Complex) (s : Complex) : term (f + g) s = term f s + term g s := by
  ext ⟨- | n⟩ <;>
  simp [add_div]

/--
lemma `LSeries.term_add_apply` / 引理 `LSeries.term_add_apply`

English:
lemma LSeries.term_add_apply
  given: (f g : Nat -> Complex) (s : Complex) (n : Nat)
  proof: by
  simp [term_add]

中文:
引理 LSeries.term_add_apply
  条件: (f g : 自然数 -> 复形) (s : 复形) (n : 自然数)
  证明: by
  simp [term_add]

Depends on / 依赖: term_add
-/
lemma LSeries.term_add_apply (f g : Nat -> Complex) (s : Complex) (n : Nat) :
    term (f + g) s n = term f s n + term g s n := by
  simp [term_add]

/--
lemma `LSeriesHasSum.add` / 引理 `LSeriesHasSum.add`

English:
lemma LSeriesHasSum.add
  statement: {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHasSum f s a)
  proof: by
  simpa [LSeriesHasSum, term_add] using! HasSum.add hf hg

中文:
引理 LSeriesHasSum.add
  结论: {f g : 自然数 -> 复形} {s a b : 复形} (hf : LSeriesHasSum f s a)
  证明: by
  simpa [LSeriesHasSum, term_add] using! HasSum.add hf hg

Depends on / 依赖: HasSum, HasSum.add, LSeriesHasSum, term_add
-/
lemma LSeriesHasSum.add {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f + g) s (a + b) := by
  simpa [LSeriesHasSum, term_add] using! HasSum.add hf hg

/--
lemma `LSeriesSummable.add` / 引理 `LSeriesSummable.add`

English:
lemma LSeriesSummable.add
  statement: {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
  proof: by
  simpa [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]

中文:
引理 LSeriesSummable.add
  结论: {f g : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s)
  证明: by
  simpa [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]

Depends on / 依赖: LSeriesSummable, Summable, Summable.add, term_add_apply
-/
lemma LSeriesSummable.add {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f + g) s := by
  simpa [LSeriesSummable, ← term_add_apply] using Summable.add hf hg

@[simp]
/--
lemma `LSeries_add` / 引理 `LSeries_add`

English:
lemma LSeries_add
  given: {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s)
  proof: by
  simpa [LSeries, term_add] using hf.tsum_add hg

中文:
引理 LSeries_add
  条件: {f g : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s)
  证明: by
  simpa [LSeries, term_add] using hf.tsum_add hg

Depends on / 依赖: LSeries, hf.tsum_add, term_add, tsum_add
-/
lemma LSeries_add {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f + g) s = LSeries f s + LSeries g s := by
  simpa [LSeries, term_add] using hf.tsum_add hg


/--
lemma `LSeries.term_neg` / 引理 `LSeries.term_neg`

English:
lemma LSeries.term_neg
  given: (f : Nat -> Complex) (s : Complex)
  statement: term (-f) s = -term f s
  proof: by
  ext ⟨- | n⟩ <;>
  simp [neg_div]

中文:
引理 LSeries.term_neg
  条件: (f : 自然数 -> 复形) (s : 复形)
  结论: term (-f) s = -term f s
  证明: by
  ext ⟨- | n⟩ <;>
  simp [neg_div]

Depends on / 依赖: neg_div
-/
lemma LSeries.term_neg (f : Nat -> Complex) (s : Complex) : term (-f) s = -term f s := by
  ext ⟨- | n⟩ <;>
  simp [neg_div]

/--
lemma `LSeries.term_neg_apply` / 引理 `LSeries.term_neg_apply`

English:
lemma LSeries.term_neg_apply
  given: (f : Nat -> Complex) (s : Complex) (n : Nat)
  statement: term (-f) s n = -term f s n
  proof: by
  simp [term_neg]

中文:
引理 LSeries.term_neg_apply
  条件: (f : 自然数 -> 复形) (s : 复形) (n : 自然数)
  结论: term (-f) s n = -term f s n
  证明: by
  simp [term_neg]

Depends on / 依赖: term_neg
-/
lemma LSeries.term_neg_apply (f : Nat -> Complex) (s : Complex) (n : Nat) : term (-f) s n = -term f s n := by
  simp [term_neg]

/--
lemma `LSeriesHasSum.neg` / 引理 `LSeriesHasSum.neg`

English:
lemma LSeriesHasSum.neg
  given: {f : Nat -> Complex} {s a : Complex} (hf : LSeriesHasSum f s a)
  proof: by
  simpa [LSeriesHasSum, term_neg] using! HasSum.neg hf

中文:
引理 LSeriesHasSum.neg
  条件: {f : 自然数 -> 复形} {s a : 复形} (hf : LSeriesHasSum f s a)
  证明: by
  simpa [LSeriesHasSum, term_neg] using! HasSum.neg hf

Depends on / 依赖: HasSum, HasSum.neg, LSeriesHasSum, term_neg
-/
lemma LSeriesHasSum.neg {f : Nat -> Complex} {s a : Complex} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (-f) s (-a) := by
  simpa [LSeriesHasSum, term_neg] using! HasSum.neg hf

/--
lemma `LSeriesSummable.neg` / 引理 `LSeriesSummable.neg`

English:
lemma LSeriesSummable.neg
  given: {f : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
  proof: by
  simpa [LSeriesSummable, term_neg] using! Summable.neg hf

@[simp]

中文:
引理 LSeriesSummable.neg
  条件: {f : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s)
  证明: by
  simpa [LSeriesSummable, term_neg] using! Summable.neg hf

@[simp]

Depends on / 依赖: LSeriesSummable, Summable, Summable.neg, term_neg
-/
lemma LSeriesSummable.neg {f : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s) :
    LSeriesSummable (-f) s := by
  simpa [LSeriesSummable, term_neg] using! Summable.neg hf

@[simp]
/--
lemma `LSeriesSummable.neg_iff` / 引理 `LSeriesSummable.neg_iff`

English:
lemma LSeriesSummable.neg_iff
  given: {f : Nat -> Complex} {s : Complex}
  proof: ⟨fun H => neg_neg f ▸ H.neg, .neg⟩

@[simp]

中文:
引理 LSeriesSummable.neg_iff
  条件: {f : 自然数 -> 复形} {s : 复形}
  证明: ⟨fun H => neg_neg f ▸ H.neg, .neg⟩

@[simp]

Depends on / 依赖: H.neg, neg_neg
-/
lemma LSeriesSummable.neg_iff {f : Nat -> Complex} {s : Complex} :
    LSeriesSummable (-f) s ↔ LSeriesSummable f s :=
  ⟨fun H => neg_neg f ▸ H.neg, .neg⟩

@[simp]
/--
lemma `LSeries_neg` / 引理 `LSeries_neg`

English:
lemma LSeries_neg
  given: (f : Nat -> Complex) (s : Complex)
  statement: LSeries (-f) s = -LSeries f s
  proof: by
  simp [LSeries, term_neg_apply, tsum_neg]

中文:
引理 LSeries_neg
  条件: (f : 自然数 -> 复形) (s : 复形)
  结论: LSeries (-f) s = -LSeries f s
  证明: by
  simp [LSeries, term_neg_apply, tsum_neg]

Depends on / 依赖: LSeries, term_neg_apply, tsum_neg
-/
lemma LSeries_neg (f : Nat -> Complex) (s : Complex) : LSeries (-f) s = -LSeries f s := by
  simp [LSeries, term_neg_apply, tsum_neg]


/--
lemma `LSeries.term_sub` / 引理 `LSeries.term_sub`

English:
lemma LSeries.term_sub
  given: (f g : Nat -> Complex) (s : Complex)
  statement: term (f - g) s = term f s - term g s
  proof: by
  simp_rw [sub_eq_add_neg, term_add, term_neg]

中文:
引理 LSeries.term_sub
  条件: (f g : 自然数 -> 复形) (s : 复形)
  结论: term (f - g) s = term f s - term g s
  证明: by
  simp_rw [sub_eq_add_neg, term_add, term_neg]

Depends on / 依赖: simp_rw, sub_eq_add_neg, term_add, term_neg
-/
lemma LSeries.term_sub (f g : Nat -> Complex) (s : Complex) : term (f - g) s = term f s - term g s := by
  simp_rw [sub_eq_add_neg, term_add, term_neg]

/--
lemma `LSeries.term_sub_apply` / 引理 `LSeries.term_sub_apply`

English:
lemma LSeries.term_sub_apply
  given: (f g : Nat -> Complex) (s : Complex) (n : Nat)
  proof: by
  rw [term_sub]; rw [Pi.sub_apply]

中文:
引理 LSeries.term_sub_apply
  条件: (f g : 自然数 -> 复形) (s : 复形) (n : 自然数)
  证明: by
  rw [term_sub]; rw [Pi.sub_apply]

Depends on / 依赖: Pi.sub_apply, sub_apply, term_sub
-/
lemma LSeries.term_sub_apply (f g : Nat -> Complex) (s : Complex) (n : Nat) :
    term (f - g) s n = term f s n - term g s n := by
  rw [term_sub]; rw [Pi.sub_apply]

/--
lemma `LSeriesHasSum.sub` / 引理 `LSeriesHasSum.sub`

English:
lemma LSeriesHasSum.sub
  statement: {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHasSum f s a)
  proof: by
  simpa [LSeriesHasSum, term_sub] using! HasSum.sub hf hg

中文:
引理 LSeriesHasSum.sub
  结论: {f g : 自然数 -> 复形} {s a b : 复形} (hf : LSeriesHasSum f s a)
  证明: by
  simpa [LSeriesHasSum, term_sub] using! HasSum.sub hf hg

Depends on / 依赖: HasSum, HasSum.sub, LSeriesHasSum, term_sub
-/
lemma LSeriesHasSum.sub {f g : Nat -> Complex} {s a b : Complex} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f - g) s (a - b) := by
  simpa [LSeriesHasSum, term_sub] using! HasSum.sub hf hg

/--
lemma `LSeriesSummable.sub` / 引理 `LSeriesSummable.sub`

English:
lemma LSeriesSummable.sub
  statement: {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
  proof: by
  simpa [LSeriesSummable, ← term_sub_apply] using Summable.sub hf hg

@[simp]

中文:
引理 LSeriesSummable.sub
  结论: {f g : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s)
  证明: by
  simpa [LSeriesSummable, ← term_sub_apply] using Summable.sub hf hg

@[simp]

Depends on / 依赖: LSeriesSummable, Summable, Summable.sub, term_sub_apply
-/
lemma LSeriesSummable.sub {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f - g) s := by
  simpa [LSeriesSummable, ← term_sub_apply] using Summable.sub hf hg

@[simp]
/--
lemma `LSeries_sub` / 引理 `LSeries_sub`

English:
lemma LSeries_sub
  given: {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s)
  proof: by
  simpa [LSeries, term_sub] using hf.tsum_sub hg

中文:
引理 LSeries_sub
  条件: {f g : 自然数 -> 复形} {s : 复形} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s)
  证明: by
  simpa [LSeries, term_sub] using hf.tsum_sub hg

Depends on / 依赖: LSeries, hf.tsum_sub, term_sub, tsum_sub
-/
lemma LSeries_sub {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (f - g) s = LSeries f s - LSeries g s := by
  simpa [LSeries, term_sub] using hf.tsum_sub hg


/--
lemma `LSeries.term_smul` / 引理 `LSeries.term_smul`

English:
lemma LSeries.term_smul
  given: (f : Nat -> Complex) (c s : Complex)
  statement: term (c • f) s = c • term f s
  proof: by
  ext ⟨- | n⟩ <;>
  simp [mul_div_assoc]

中文:
引理 LSeries.term_smul
  条件: (f : 自然数 -> 复形) (c s : 复形)
  结论: term (c • f) s = c • term f s
  证明: by
  ext ⟨- | n⟩ <;>
  simp [mul_div_assoc]

Depends on / 依赖: mul_div_assoc
-/
lemma LSeries.term_smul (f : Nat -> Complex) (c s : Complex) : term (c • f) s = c • term f s := by
  ext ⟨- | n⟩ <;>
  simp [mul_div_assoc]

/--
lemma `LSeries.term_smul_apply` / 引理 `LSeries.term_smul_apply`

English:
lemma LSeries.term_smul_apply
  given: (f : Nat -> Complex) (c s : Complex) (n : Nat)
  proof: by
  simp [term_smul]

中文:
引理 LSeries.term_smul_apply
  条件: (f : 自然数 -> 复形) (c s : 复形) (n : 自然数)
  证明: by
  simp [term_smul]

Depends on / 依赖: term_smul
-/
lemma LSeries.term_smul_apply (f : Nat -> Complex) (c s : Complex) (n : Nat) :
    term (c • f) s n = c * term f s n := by
  simp [term_smul]

/--
lemma `LSeriesHasSum.smul` / 引理 `LSeriesHasSum.smul`

English:
lemma LSeriesHasSum.smul
  given: {f : Nat -> Complex} (c : Complex) {s a : Complex} (hf : LSeriesHasSum f s a)
  proof: by
  simpa [LSeriesHasSum, term_smul] using! hf.const_smul c

中文:
引理 LSeriesHasSum.smul
  条件: {f : 自然数 -> 复形} (c : 复形) {s a : 复形} (hf : LSeriesHasSum f s a)
  证明: by
  simpa [LSeriesHasSum, term_smul] using! hf.const_smul c

Depends on / 依赖: LSeriesHasSum, const_smul, hf.const_smul, term_smul
-/
lemma LSeriesHasSum.smul {f : Nat -> Complex} (c : Complex) {s a : Complex} (hf : LSeriesHasSum f s a) :
    LSeriesHasSum (c • f) s (c * a) := by
  simpa [LSeriesHasSum, term_smul] using! hf.const_smul c

/--
lemma `LSeriesSummable.smul` / 引理 `LSeriesSummable.smul`

English:
lemma LSeriesSummable.smul
  given: {f : Nat -> Complex} (c : Complex) {s : Complex} (hf : LSeriesSummable f s)
  proof: by
  simpa [LSeriesSummable, term_smul] using! hf.const_smul c

中文:
引理 LSeriesSummable.smul
  条件: {f : 自然数 -> 复形} (c : 复形) {s : 复形} (hf : LSeriesSummable f s)
  证明: by
  simpa [LSeriesSummable, term_smul] using! hf.const_smul c

Depends on / 依赖: LSeriesSummable, const_smul, hf.const_smul, term_smul
-/
lemma LSeriesSummable.smul {f : Nat -> Complex} (c : Complex) {s : Complex} (hf : LSeriesSummable f s) :
    LSeriesSummable (c • f) s := by
  simpa [LSeriesSummable, term_smul] using! hf.const_smul c

/--
lemma `LSeriesSummable.of_smul` / 引理 `LSeriesSummable.of_smul`

English:
lemma LSeriesSummable.of_smul
  given: {f : Nat -> Complex} {c s : Complex} (hc : c != 0) (hf : LSeriesSummable (c • f) s)
  proof: by
  simpa [hc] using hf.smul (c⁻¹)

中文:
引理 LSeriesSummable.of_smul
  条件: {f : 自然数 -> 复形} {c s : 复形} (hc : c != 0) (hf : LSeriesSummable (c • f) s)
  证明: by
  simpa [hc] using hf.smul (c⁻¹)

Depends on / 依赖: hf.smul
-/
lemma LSeriesSummable.of_smul {f : Nat -> Complex} {c s : Complex} (hc : c != 0) (hf : LSeriesSummable (c • f) s) :
    LSeriesSummable f s := by
  simpa [hc] using hf.smul (c⁻¹)

/--
lemma `LSeriesSummable.smul_iff` / 引理 `LSeriesSummable.smul_iff`

English:
lemma LSeriesSummable.smul_iff
  given: {f : Nat -> Complex} {c s : Complex} (hc : c != 0)
  proof: ⟨of_smul hc, smul c⟩

@[simp]

中文:
引理 LSeriesSummable.smul_iff
  条件: {f : 自然数 -> 复形} {c s : 复形} (hc : c != 0)
  证明: ⟨of_smul hc, smul c⟩

@[simp]

Depends on / 依赖: of_smul
-/
lemma LSeriesSummable.smul_iff {f : Nat -> Complex} {c s : Complex} (hc : c != 0) :
    LSeriesSummable (c • f) s ↔ LSeriesSummable f s :=
  ⟨of_smul hc, smul c⟩

@[simp]
/--
lemma `LSeries_smul` / 引理 `LSeries_smul`

English:
lemma LSeries_smul
  given: (f : Nat -> Complex) (c s : Complex)
  statement: LSeries (c • f) s = c * LSeries f s
  proof: by
  simp [LSeries, term_smul_apply, tsum_mul_left]

中文:
引理 LSeries_smul
  条件: (f : 自然数 -> 复形) (c s : 复形)
  结论: LSeries (c • f) s = c * LSeries f s
  证明: by
  simp [LSeries, term_smul_apply, tsum_mul_left]

Depends on / 依赖: LSeries, term_smul_apply, tsum_mul_left
-/
lemma LSeries_smul (f : Nat -> Complex) (c s : Complex) : LSeries (c • f) s = c * LSeries f s := by
  simp [LSeries, term_smul_apply, tsum_mul_left]

/-!
### Sums
-/

section sum

variable {ι : Type*} (f : ι -> Nat -> Complex) (S : Finset ι) (s : Complex)

@[simp]
/--
lemma `LSeries.term_sum_apply` / 引理 `LSeries.term_sum_apply`

English:
lemma LSeries.term_sum_apply
  given: (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, Finset.sum_div]

中文:
引理 LSeries.term_sum_apply
  条件: (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, Finset.sum_div]

Depends on / 依赖: Finset, Finset.sum_div, eq_or_ne, sum_div
-/
lemma LSeries.term_sum_apply (n : Nat) :
    term (∑ i in S, f i) s n = ∑ i in S, term (f i) s n := by
  rcases eq_or_ne n 0 with hn | hn <;>
  simp [hn, Finset.sum_div]

/--
lemma `LSeries.term_sum` / 引理 `LSeries.term_sum`

English:
lemma LSeries.term_sum
  statement: term (∑ i in S, f i) s = ∑ i in S, term (f i) s
  proof: funext fun _ => by simp

中文:
引理 LSeries.term_sum
  结论: term (∑ i in S, f i) s = ∑ i in S, term (f i) s
  证明: funext fun _ => by simp
-/
lemma LSeries.term_sum : term (∑ i in S, f i) s = ∑ i in S, term (f i) s :=
  funext fun _ => by simp

variable {f S s}

/--
lemma `LSeriesHasSum.sum` / 引理 `LSeriesHasSum.sum`

English:
lemma LSeriesHasSum.sum
  given: {a : ι -> Complex} (hf : forall i in S, LSeriesHasSum (f i) s (a i))
  proof: by
  simpa [LSeriesHasSum, term_sum, Finset.sum_fn S fun i => term (f i) s] using hasSum_sum hf

中文:
引理 LSeriesHasSum.求和
  条件: {a : ι -> 复形} (hf : 对任意 i in S, LSeriesHasSum (f i) s (a i))
  证明: by
  simpa [LSeriesHasSum, term_sum, Finset.sum_fn S fun i => term (f i) s] using hasSum_sum hf

Depends on / 依赖: Finset, Finset.sum_fn, LSeriesHasSum, hasSum_sum, sum_fn, term_sum
-/
lemma LSeriesHasSum.sum {a : ι -> Complex} (hf : forall i in S, LSeriesHasSum (f i) s (a i)) :
    LSeriesHasSum (∑ i in S, f i) s (∑ i in S, a i) := by
  simpa [LSeriesHasSum, term_sum, Finset.sum_fn S fun i => term (f i) s] using hasSum_sum hf

/--
lemma `LSeriesSummable.sum` / 引理 `LSeriesSummable.sum`

English:
lemma LSeriesSummable.sum
  given: (hf : forall i in S, LSeriesSummable (f i) s)
  proof: by
  simpa [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]

中文:
引理 LSeriesSummable.求和
  条件: (hf : 对任意 i in S, LSeriesSummable (f i) s)
  证明: by
  simpa [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]

Depends on / 依赖: LSeriesSummable, summable_sum, term_sum_apply
-/
lemma LSeriesSummable.sum (hf : forall i in S, LSeriesSummable (f i) s) :
    LSeriesSummable (∑ i in S, f i) s := by
  simpa [LSeriesSummable, ← term_sum_apply] using summable_sum hf

@[simp]
/--
lemma `LSeries_sum` / 引理 `LSeries_sum`

English:
lemma LSeries_sum
  given: (hf : forall i in S, LSeriesSummable (f i) s)
  proof: by
  simpa [LSeries, term_sum] using Summable.tsum_finsetSum hf

中文:
引理 LSeries_sum
  条件: (hf : 对任意 i in S, LSeriesSummable (f i) s)
  证明: by
  simpa [LSeries, term_sum] using Summable.tsum_finsetSum hf

Depends on / 依赖: LSeries, Summable, Summable.tsum_finsetSum, term_sum, tsum_finsetSum
-/
lemma LSeries_sum (hf : forall i in S, LSeriesSummable (f i) s) :
    LSeries (∑ i in S, f i) s = ∑ i in S, LSeries (f i) s := by
  simpa [LSeries, term_sum] using Summable.tsum_finsetSum hf

end sum
