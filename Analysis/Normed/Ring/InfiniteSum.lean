/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Multiplying two infinite sums in a normed ring

In this file, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean` (e.g.
`tsum_mul_tsum`), but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `ι` and `ι'`, and then we specialize to
`ι = ι' = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
-/

public section


variable {R : Type*} {ι : Type*} {ι' : Type*} [NormedRing R]

open scoped Topology

open Finset Filter


/--
theorem `Summable.mul_of_nonneg` / 定理 `Summable.mul_of_nonneg`

English:
theorem Summable.mul_of_nonneg
  statement: {f : ι -> Real} {g : ι' -> Real} (hf : Summable f) (hg : Summable g)
  proof: (summable_prod_of_nonneg fun _ => mul_nonneg (hf' _) (hg' _)).2 ⟨fun x => hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩

中文:
定理 Summable.mul_of_nonneg
  结论: {f : ι -> 实数} {g : ι' -> 实数} (hf : Summable f) (hg : Summable g)
  证明: (summable_prod_of_nonneg fun _ => mul_nonneg (hf' _) (hg' _)).2 ⟨fun x => hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩

Depends on / 依赖: hf.mul_right, hg.mul_left, hg.tsum_mul_left, mul_left, mul_nonneg, mul_right, summable_prod_of_nonneg, tsum_mul_left
-/
theorem Summable.mul_of_nonneg {f : ι -> Real} {g : ι' -> Real} (hf : Summable f) (hg : Summable g)
    (hf' : 0 <= f) (hg' : 0 <= g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (summable_prod_of_nonneg fun _ => mul_nonneg (hf' _) (hg' _)).2 ⟨fun x => hg.mul_left (f x),
    by simpa only [hg.tsum_mul_left _] using hf.mul_right (∑' x, g x)⟩

/--
theorem `Summable.mul_norm` / 定理 `Summable.mul_norm`

English:
theorem Summable.mul_norm
  statement: {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖)
  proof: .of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x :)

中文:
定理 Summable.mul_norm
  结论: {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖)
  证明: .of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x :)

Depends on / 依赖: hf.mul_of_nonneg, mul_of_nonneg, norm_mul_le, norm_nonneg, of_nonneg_of_le
-/
theorem Summable.mul_norm {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' => ‖f x.1 * g x.2‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x :)

/--
theorem `summable_mul_of_summable_norm` / 定理 `summable_mul_of_summable_norm`

English:
theorem summable_mul_of_summable_norm
  statement: [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
  proof: (hf.mul_norm hg).of_norm

中文:
定理 summable_mul_of_summable_norm
  结论: [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
  证明: (hf.mul_norm hg).of_norm

Depends on / 依赖: hf.mul_norm, mul_norm, of_norm
-/
theorem summable_mul_of_summable_norm [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun x : ι × ι' => f x.1 * g x.2 :=
  (hf.mul_norm hg).of_norm

/--
theorem `summable_mul_of_summable_norm'` / 定理 `summable_mul_of_summable_norm'`

English:
theorem summable_mul_of_summable_norm'
  statement: {f : ι -> R} {g : ι' -> R}
  proof: by
  classical
  suffices HasSum (fun x : ι × ι' => f x.1 * g x.2) ((∑' i, f i) * (∑' j, g j)) from this.summable
  let s : Finset ι × Finset ι' -> Finset (ι × ι') := fun p => p.1 ×ˢ p.2
  apply hasSum_of_subseq_of_summable (hf.mul_norm hg) tendsto_finsetProd_atTop
  rw [← prod_atTop_atTop_eq]
  hav

中文:
定理 summable_mul_of_summable_norm'
  结论: {f : ι -> R} {g : ι' -> R}
  证明: by
  classical
  suffices HasSum (fun x : ι × ι' => f x.1 * g x.2) ((∑' i, f i) * (∑' j, g j)) from this.summable
  let s : Finset ι × Finset ι' -> Finset (ι × ι') := fun p => p.1 ×ˢ p.2
  apply hasSum_of_subseq_of_summable (hf.mul_norm hg) tendsto_finsetProd_atTop
  rw [← prod_atTop_atTop_eq]
  hav

Depends on / 依赖: Finset, HasSum, Tendsto, Tendsto.prodMap, classical, continuousAt, continuous_mul, convert, f.hasSum, g.hasSum, hasSum, hasSum_of_subseq_of_summable, hf.mul_norm, mul_norm, nhds_prod_eq, prodMap, prod_atTop_atTop_eq, sum_product, summable, tendsto
-/
theorem summable_mul_of_summable_norm' {f : ι -> R} {g : ι' -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    Summable fun x : ι × ι' => f x.1 * g x.2 := by
  classical
  suffices HasSum (fun x : ι × ι' => f x.1 * g x.2) ((∑' i, f i) * (∑' j, g j)) from this.summable
  let s : Finset ι × Finset ι' -> Finset (ι × ι') := fun p => p.1 ×ˢ p.2
  apply hasSum_of_subseq_of_summable (hf.mul_norm hg) tendsto_finsetProd_atTop
  rw [← prod_atTop_atTop_eq]
  have := Tendsto.prodMap h'f.hasSum h'g.hasSum
  rw [← nhds_prod_eq] at this
  convert!
    ((continuous_mul (M := R)).continuousAt (x := (∑' (i : ι), f i, ∑' (j : ι'), g j))).tendsto.comp
      this with
    p
  simp [sum_product, ← mul_sum, ← sum_mul]

/--
theorem `tsum_mul_tsum_of_summable_norm` / 定理 `tsum_mul_tsum_of_summable_norm`

English:
theorem tsum_mul_tsum_of_summable_norm
  statement: [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
  proof: hf.of_norm.tsum_mul_tsum hg.of_norm (summable_mul_of_summable_norm hf hg)

中文:
定理 tsum_mul_tsum_of_summable_norm
  结论: [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
  证明: hf.of_norm.tsum_mul_tsum hg.of_norm (summable_mul_of_summable_norm hf hg)

Depends on / 依赖: hf.of_norm.tsum_mul_tsum, hg.of_norm, of_norm, summable_mul_of_summable_norm, tsum_mul_tsum
-/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace R] {f : ι -> R} {g : ι' -> R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  hf.of_norm.tsum_mul_tsum hg.of_norm (summable_mul_of_summable_norm hf hg)

/--
theorem `tsum_mul_tsum_of_summable_norm'` / 定理 `tsum_mul_tsum_of_summable_norm'`

English:
theorem tsum_mul_tsum_of_summable_norm'
  statement: {f : ι -> R} {g : ι' -> R}
  proof: h'f.tsum_mul_tsum h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

中文:
定理 tsum_mul_tsum_of_summable_norm'
  结论: {f : ι -> R} {g : ι' -> R}
  证明: h'f.tsum_mul_tsum h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

Depends on / 依赖: f.tsum_mul_tsum, summable_mul_of_summable_norm, tsum_mul_tsum
-/
theorem tsum_mul_tsum_of_summable_norm' {f : ι -> R} {g : ι' -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  h'f.tsum_mul_tsum h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`Finset.range (n+1)` involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`. -/

section Nat

open Finset.Nat

/--
theorem `summable_norm_sum_mul_antidiagonal_of_summable_norm` / 定理 `summable_norm_sum_mul_antidiagonal_of_summable_norm`

English:
theorem summable_norm_sum_mul_antidiagonal_of_summable_norm
  statement: {f g : Nat -> R}
  proof: by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine this.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  calc
    ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ <= ∑ kl in antidiagonal n, ‖f 

中文:
定理 summable_norm_sum_mul_antidiagonal_of_summable_norm
  结论: {f g : 自然数 -> R}
  证明: by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine this.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  calc
    ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ <= ∑ kl in antidiagonal n, ‖f 

Depends on / 依赖: Summable, Summable.mul_of_nonneg, antidiagonal, mul_of_nonneg, norm_mul_le, norm_nonneg, norm_sum_le, of_nonneg_of_le, summable_sum_mul_antidiagonal_of_summable_mul, this.of_nonneg_of_le
-/
theorem summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun n => ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ := by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine this.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  calc
    ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ <= ∑ kl in antidiagonal n, ‖f kl.1 * g kl.2‖ :=
      norm_sum_le _ _
    _ <= ∑ kl in antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := by gcongr; apply norm_mul_le

/--
theorem `summable_sum_mul_antidiagonal_of_summable_norm'` / 定理 `summable_sum_mul_antidiagonal_of_summable_norm'`

English:
theorem summable_sum_mul_antidiagonal_of_summable_norm'
  statement: {f g : Nat -> R}
  proof: summable_sum_mul_antidiagonal_of_summable_mul (summable_mul_of_summable_norm' hf h'f hg h'g)

中文:
定理 summable_sum_mul_antidiagonal_of_summable_norm'
  结论: {f g : 自然数 -> R}
  证明: summable_sum_mul_antidiagonal_of_summable_mul (summable_mul_of_summable_norm' hf h'f hg h'g)

Depends on / 依赖: summable_mul_of_summable_norm, summable_sum_mul_antidiagonal_of_summable_mul
-/
theorem summable_sum_mul_antidiagonal_of_summable_norm' {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    Summable fun n => ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  summable_sum_mul_antidiagonal_of_summable_mul (summable_mul_of_summable_norm' hf h'f hg h'g)

/--
theorem `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` / 定理 `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`

English:
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
  statement: [CompleteSpace R] {f g : Nat -> R}
  proof: hf.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.of_norm (summable_mul_of_summable_norm hf hg)

中文:
定理 tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
  结论: [CompleteSpace R] {f g : 自然数 -> R}
  证明: hf.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.of_norm (summable_mul_of_summable_norm hf hg)

Depends on / 依赖: hf.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal, hg.of_norm, of_norm, summable_mul_of_summable_norm, tsum_mul_tsum_eq_tsum_sum_antidiagonal
-/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  hf.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg.of_norm (summable_mul_of_summable_norm hf hg)

/--
theorem `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'` / 定理 `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'`

English:
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'
  statement: {f g : Nat -> R}
  proof: h'f.tsum_mul_tsum_eq_tsum_sum_antidiagonal h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

中文:
定理 tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm'
  结论: {f g : 自然数 -> R}
  证明: h'f.tsum_mul_tsum_eq_tsum_sum_antidiagonal h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

Depends on / 依赖: f.tsum_mul_tsum_eq_tsum_sum_antidiagonal, summable_mul_of_summable_norm, tsum_mul_tsum_eq_tsum_sum_antidiagonal
-/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  h'f.tsum_mul_tsum_eq_tsum_sum_antidiagonal h'g (summable_mul_of_summable_norm' hf h'f hg h'g)

/--
theorem `summable_norm_sum_mul_range_of_summable_norm` / 定理 `summable_norm_sum_mul_range_of_summable_norm`

English:
theorem summable_norm_sum_mul_range_of_summable_norm
  statement: {f g : Nat -> R} (hf : Summable fun x => ‖f x‖)
  proof: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

中文:
定理 summable_norm_sum_mul_range_of_summable_norm
  结论: {f g : 自然数 -> R} (hf : Summable fun x => ‖f x‖)
  证明: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

Depends on / 依赖: simp_rw, sum_antidiagonal_eq_sum_range_succ, summable_norm_sum_mul_antidiagonal_of_summable_norm
-/
theorem summable_norm_sum_mul_range_of_summable_norm {f g : Nat -> R} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ k in range (n + 1), f k * g (n - k)‖ := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg

/--
theorem `summable_sum_mul_range_of_summable_norm'` / 定理 `summable_sum_mul_range_of_summable_norm'`

English:
theorem summable_sum_mul_range_of_summable_norm'
  statement: {f g : Nat -> R}
  proof: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_norm' hf h'f hg h'g

中文:
定理 summable_sum_mul_range_of_summable_norm'
  结论: {f g : 自然数 -> R}
  证明: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_norm' hf h'f hg h'g

Depends on / 依赖: simp_rw, sum_antidiagonal_eq_sum_range_succ, summable_sum_mul_antidiagonal_of_summable_norm
-/
theorem summable_sum_mul_range_of_summable_norm' {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    Summable fun n => ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_norm' hf h'f hg h'g

/--
theorem `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` / 定理 `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`

English:
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
  statement: [CompleteSpace R] {f g : Nat -> R}
  proof: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

中文:
定理 tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
  结论: [CompleteSpace R] {f g : 自然数 -> R}
  证明: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

Depends on / 依赖: simp_rw, sum_antidiagonal_eq_sum_range_succ, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
-/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace R] {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg

/--
theorem `hasSum_sum_range_mul_of_summable_norm` / 定理 `hasSum_sum_range_mul_of_summable_norm`

English:
theorem hasSum_sum_range_mul_of_summable_norm
  statement: [CompleteSpace R] {f g : Nat -> R}
  proof: by
  convert! (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm.hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg

中文:
定理 hasSum_sum_range_mul_of_summable_norm
  结论: [CompleteSpace R] {f g : 自然数 -> R}
  证明: by
  convert! (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm.hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg

Depends on / 依赖: convert, hasSum, of_norm, of_norm.hasSum, summable_norm_sum_mul_range_of_summable_norm, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
-/
theorem hasSum_sum_range_mul_of_summable_norm [CompleteSpace R] {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    HasSum (fun n => ∑ k in range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n) := by
  convert! (summable_norm_sum_mul_range_of_summable_norm hf hg).of_norm.hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg

/--
theorem `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'` / 定理 `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'`

English:
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'
  statement: {f g : Nat -> R}
  proof: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hf h'f hg h'g

中文:
定理 tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm'
  结论: {f g : 自然数 -> R}
  证明: by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hf h'f hg h'g

Depends on / 依赖: simp_rw, sum_antidiagonal_eq_sum_range_succ, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
-/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm' hf h'f hg h'g

/--
theorem `hasSum_sum_range_mul_of_summable_norm'` / 定理 `hasSum_sum_range_mul_of_summable_norm'`

English:
theorem hasSum_sum_range_mul_of_summable_norm'
  statement: {f g : Nat -> R}
  proof: by
  convert! (summable_sum_mul_range_of_summable_norm' hf h'f hg h'g).hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' hf h'f hg h'g

中文:
定理 hasSum_sum_range_mul_of_summable_norm'
  结论: {f g : 自然数 -> R}
  证明: by
  convert! (summable_sum_mul_range_of_summable_norm' hf h'f hg h'g).hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' hf h'f hg h'g

Depends on / 依赖: convert, hasSum, summable_sum_mul_range_of_summable_norm, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
-/
theorem hasSum_sum_range_mul_of_summable_norm' {f g : Nat -> R}
    (hf : Summable fun x => ‖f x‖) (h'f : Summable f)
    (hg : Summable fun x => ‖g x‖) (h'g : Summable g) :
    HasSum (fun n => ∑ k in range (n + 1), f k * g (n - k)) ((∑' n, f n) * ∑' n, g n) := by
  convert! (summable_sum_mul_range_of_summable_norm' hf h'f hg h'g).hasSum
  exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm' hf h'f hg h'g

end Nat

/--
lemma `summable_of_absolute_convergence_real` / 引理 `summable_of_absolute_convergence_real`

English:
lemma summable_of_absolute_convergence_real
  given: {f : Nat -> Real}

中文:
引理 summable_of_absolute_convergence_real
  条件: {f : 自然数 -> 实数}
-/
lemma summable_of_absolute_convergence_real {f : Nat -> Real} :
    (exists r, Tendsto (fun n => ∑ i in range n, |f i|) atTop (𝓝 r)) -> Summable f
  | ⟨r, hr⟩ => by
    refine .of_norm ⟨r, (hasSum_iff_tendsto_nat_of_nonneg ?_ _).2 ?_⟩
    · exact fun i => norm_nonneg _
    · simpa only using! hr
