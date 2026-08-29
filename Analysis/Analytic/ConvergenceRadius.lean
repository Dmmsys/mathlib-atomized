/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Radius of convergence of a power series

This file introduces the notion of the radius of convergence of a power series.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ℝ≥0∞` such that `‖p n‖ * r^n` grows subexponentially.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_isBigO`: if `‖p n‖ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.isLittleO_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`,
  `p.isLittleO_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `‖p n‖ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_isBigO`: if `r ≠ 0` and `‖p n‖ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partialSum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

@[expose] public section

noncomputable section

variable {𝕜 𝕜' E F G : Type*}

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise

namespace FormalMultilinearSeries

variable [Semiring 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]
variable [TopologicalSpace E] [TopologicalSpace F]
variable [ContinuousAdd E] [ContinuousAdd F]
variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  body: ∑' n : Nat, p n fun _ => x

中文:
定义 求和
  签名: (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  定义体: ∑' n : Nat, p n fun _ => x
-/
protected def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : Nat, p n fun _ => x

/--
theorem `sum_mem` / 定理 `sum_mem`

English:
theorem sum_mem
  statement: {S : Type*} {s : S} [SetLike S F] [AddSubmonoidClass S F]
  proof: tsum_mem h_closed h

中文:
定理 sum_mem
  结论: {S : 类型} {s : S} [集合状 S F] [加法子幺半群类 S F]
  证明: tsum_mem h_closed h

Depends on / 依赖: h_closed, tsum_mem
-/
theorem sum_mem {S : Type*} {s : S} [SetLike S F] [AddSubmonoidClass S F]
    (h_closed : IsClosed (s : Set F)) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (h : forall k, p k (fun _ : Fin k => x) in s) :
    p.sum x in s :=
  tsum_mem h_closed h

variable {𝕜' : Type} [DivisionSemiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F]
  [SMulCommClass 𝕜 𝕜' F]

/--
theorem `const_smul_sum_apply` / 定理 `const_smul_sum_apply`

English:
theorem const_smul_sum_apply
  given: [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) (z : E)
  proof: by
  unfold FormalMultilinearSeries.sum
  simp [tsum_const_smul'']

中文:
定理 const_smul_sum_apply
  条件: [T2空间 F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) (z : E)
  证明: by
  unfold FormalMultilinearSeries.sum
  simp [tsum_const_smul'']

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.sum, tsum_const_smul
-/
theorem const_smul_sum_apply [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) (z : E) :
    a • f.sum z = (a • f).sum z := by
  unfold FormalMultilinearSeries.sum
  simp [tsum_const_smul'']

/--
theorem `const_smul_sum` / 定理 `const_smul_sum`

English:
theorem const_smul_sum
  given: [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F)
  proof: by
  ext z
  apply const_smul_sum_apply

中文:
定理 const_smul_sum
  条件: [T2空间 F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F)
  证明: by
  ext z
  apply const_smul_sum_apply

Depends on / 依赖: const_smul_sum_apply
-/
theorem const_smul_sum [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) :
    a • f.sum = (a • f).sum := by
  ext z
  apply const_smul_sum_apply

/--
Definition of `partialSum` / `partialSum` 的定义

English:
definition partialSum
  signature: (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) (x : E)
  body: ∑ k in Finset.range n, p k fun _ : Fin k => x

中文:
定义 partialSum
  签名: (p : FormalMultilinearSeries 𝕜 E F) (n : 自然数) (x : E)
  定义体: ∑ k in Finset.range n, p k fun _ : Fin k => x

Depends on / 依赖: Finset, Finset.range
-/
def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) (x : E) : F :=
  ∑ k in Finset.range n, p k fun _ : Fin k => x

/--
theorem `partialSum_continuous` / 定理 `partialSum_continuous`

English:
theorem partialSum_continuous
  given: (p : FormalMultilinearSeries 𝕜 E F) (n : Nat)
  proof: by
  unfold partialSum
  fun_prop

中文:
定理 partialSum_continuous
  条件: (p : FormalMultilinearSeries 𝕜 E F) (n : 自然数)
  证明: by
  unfold partialSum
  fun_prop

Depends on / 依赖: fun_prop, partialSum
-/
theorem partialSum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) :
    Continuous (p.partialSum n) := by
  unfold partialSum
  fun_prop

end FormalMultilinearSeries

/-! ### The radius of a formal multilinear series -/

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}

/--
Definition of `radius` / `radius` 的定义

English:
definition radius
  signature: (p : FormalMultilinearSeries 𝕜 E F)
  body: ⨆ (r : Real>=0) (C : Real) (_ : forall n, ‖p n‖ * (r : Real) ^ n <= C), (r : Real>=0∞)

中文:
定义 radius
  签名: (p : FormalMultilinearSeries 𝕜 E F)
  定义体: ⨆ (r : Real>=0) (C : Real) (_ : forall n, ‖p n‖ * (r : Real) ^ n <= C), (r : Real>=0∞)
-/
def radius (p : FormalMultilinearSeries 𝕜 E F) : Real>=0∞ :=
  ⨆ (r : Real>=0) (C : Real) (_ : forall n, ‖p n‖ * (r : Real) ^ n <= C), (r : Real>=0∞)

/--
theorem `le_radius_of_bound` / 定理 `le_radius_of_bound`

English:
theorem le_radius_of_bound
  given: (C : Real) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C)
  proof: le_iSup_of_le r le_iSup_of_le C le_iSup (fun _ => (r : Real>=0∞)) h

中文:
定理 le_radius_of_bound
  条件: (C : 实数) {r : 实数>=0} (h : 对任意 n : 自然数, ‖p n‖ * (r : 实数) ^ n <= C)
  证明: le_iSup_of_le r le_iSup_of_le C le_iSup (fun _ => (r : Real>=0∞)) h

Depends on / 依赖: le_iSup, le_iSup_of_le
-/
theorem le_radius_of_bound (C : Real) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) :
    (r : Real>=0∞) <= p.radius :=
le_iSup_of_le r le_iSup_of_le C le_iSup (fun _ => (r : Real>=0∞)) h

/--
theorem `le_radius_of_bound_nnreal` / 定理 `le_radius_of_bound_nnreal`

English:
theorem le_radius_of_bound_nnreal
  given: (C : Real>=0) {r : Real>=0} (h : forall n : Nat, ‖p n‖₊ * r ^ n <= C)
  proof: p.le_radius_of_bound C fun n => mod_cast h n

中文:
定理 le_radius_of_bound_nnreal
  条件: (C : 实数>=0) {r : 实数>=0} (h : 对任意 n : 自然数, ‖p n‖₊ * r ^ n <= C)
  证明: p.le_radius_of_bound C fun n => mod_cast h n

Depends on / 依赖: le_radius_of_bound, mod_cast, p.le_radius_of_bound
-/
theorem le_radius_of_bound_nnreal (C : Real>=0) {r : Real>=0} (h : forall n : Nat, ‖p n‖₊ * r ^ n <= C) :
    (r : Real>=0∞) <= p.radius :=
  p.le_radius_of_bound C fun n => mod_cast h n

/--
theorem `le_radius_of_isBigO` / 定理 `le_radius_of_isBigO`

English:
theorem le_radius_of_isBigO
  given: (h : (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real))
  proof: Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)

中文:
定理 le_radius_of_isBigO
  条件: (h : (fun n => ‖p n‖ * (r : 实数) ^ n) =O[atTop] fun _ => (1 : 实数))
  证明: Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)

Depends on / 依赖: Exists, Exists.elim, isBigO_one_nat_atTop_iff, le_abs_self, le_radius_of_bound, p.le_radius_of_bound
-/
theorem le_radius_of_isBigO (h : (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) :
    ↑r <= p.radius :=
  Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)

/--
theorem `le_radius_of_eventually_le` / 定理 `le_radius_of_eventually_le`

English:
theorem le_radius_of_eventually_le
  given: (C) (h : forallᶠ n in atTop, ‖p n‖ * (r : Real) ^ n <= C)
  proof: p.le_radius_of_isBigO IsBigO.of_bound C h.mono fun n hn => by simpa

中文:
定理 le_radius_of_eventually_le
  条件: (C) (h : 对任意ᶠ n in atTop, ‖p n‖ * (r : 实数) ^ n <= C)
  证明: p.le_radius_of_isBigO IsBigO.of_bound C h.mono fun n hn => by simpa

Depends on / 依赖: IsBigO, IsBigO.of_bound, h.mono, le_radius_of_isBigO, of_bound, p.le_radius_of_isBigO
-/
theorem le_radius_of_eventually_le (C) (h : forallᶠ n in atTop, ‖p n‖ * (r : Real) ^ n <= C) :
    ↑r <= p.radius :=
p.le_radius_of_isBigO IsBigO.of_bound C h.mono fun n hn => by simpa

/--
theorem `le_radius_of_summable_nnnorm` / 定理 `le_radius_of_summable_nnnorm`

English:
theorem le_radius_of_summable_nnnorm
  given: (h : Summable fun n => ‖p n‖₊ * r ^ n)
  statement: ↑r <= p.radius
  proof: p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) fun _ => h.le_tsum' _

中文:
定理 le_radius_of_summable_nnnorm
  条件: (h : Summable fun n => ‖p n‖₊ * r ^ n)
  结论: ↑r <= p.radius
  证明: p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) fun _ => h.le_tsum' _

Depends on / 依赖: h.le_tsum, le_radius_of_bound_nnreal, le_tsum, p.le_radius_of_bound_nnreal
-/
theorem le_radius_of_summable_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r <= p.radius :=
  p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) fun _ => h.le_tsum' _

/--
theorem `le_radius_of_summable` / 定理 `le_radius_of_summable`

English:
theorem le_radius_of_summable
  given: (h : Summable fun n => ‖p n‖ * (r : Real) ^ n)
  statement: ↑r <= p.radius
  proof: p.le_radius_of_summable_nnnorm by
    simp only [← coe_nnnorm] at h
    exact mod_cast h

中文:
定理 le_radius_of_summable
  条件: (h : Summable fun n => ‖p n‖ * (r : 实数) ^ n)
  结论: ↑r <= p.radius
  证明: p.le_radius_of_summable_nnnorm by
    simp only [← coe_nnnorm] at h
    exact mod_cast h

Depends on / 依赖: coe_nnnorm, le_radius_of_summable_nnnorm, mod_cast, p.le_radius_of_summable_nnnorm
-/
theorem le_radius_of_summable (h : Summable fun n => ‖p n‖ * (r : Real) ^ n) : ↑r <= p.radius :=
p.le_radius_of_summable_nnnorm by
    simp only [← coe_nnnorm] at h
    exact mod_cast h

/--
theorem `radius_eq_top_of_forall_nnreal_isBigO` / 定理 `radius_eq_top_of_forall_nnreal_isBigO`

English:
theorem radius_eq_top_of_forall_nnreal_isBigO
  proof: ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)

中文:
定理 radius_eq_top_of_对任意_nnreal_isBigO
  证明: ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)

Depends on / 依赖: ENNReal, ENNReal.eq_top_of_forall_nnreal_le, eq_top_of_forall_nnreal_le, le_radius_of_isBigO, p.le_radius_of_isBigO
-/
theorem radius_eq_top_of_forall_nnreal_isBigO
    (h : forall r : Real>=0, (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)

/--
theorem `radius_eq_top_of_eventually_eq_zero` / 定理 `radius_eq_top_of_eventually_eq_zero`

English:
theorem radius_eq_top_of_eventually_eq_zero
  given: (h : forallᶠ n in atTop, p n = 0)
  statement: p.radius = ∞
  proof: p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl

中文:
定理 radius_eq_top_of_eventually_eq_zero
  条件: (h : 对任意ᶠ n in atTop, p n = 0)
  结论: p.radius = ∞
  证明: p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h.mono, isBigO_zero, p.radius_eq_top_of_forall_nnreal_isBigO, radius_eq_top_of_forall_nnreal_isBigO
-/
theorem radius_eq_top_of_eventually_eq_zero (h : forallᶠ n in atTop, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl

/--
theorem `radius_eq_top_of_forall_image_add_eq_zero` / 定理 `radius_eq_top_of_forall_image_add_eq_zero`

English:
theorem radius_eq_top_of_forall_image_add_eq_zero
  given: (n : Nat) (hn : forall m, p (m + n) = 0)
  proof: p.radius_eq_top_of_eventually_eq_zero
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp]

中文:
定理 radius_eq_top_of_对任意_image_add_eq_zero
  条件: (n : 自然数) (hn : 对任意 m, p (m + n) = 0)
  证明: p.radius_eq_top_of_eventually_eq_zero
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp]

Depends on / 依赖: mem_atTop_sets, p.radius_eq_top_of_eventually_eq_zero, radius_eq_top_of_eventually_eq_zero, tsub_add_cancel_of_le
-/
theorem radius_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m + n) = 0) :
    p.radius = ∞ :=
p.radius_eq_top_of_eventually_eq_zero
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp]
/--
theorem `constFormalMultilinearSeries_radius` / 定理 `constFormalMultilinearSeries_radius`

English:
theorem constFormalMultilinearSeries_radius
  given: {v : F}
  proof: (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])

中文:
定理 constFormalMultilinearSeries_radius
  条件: {v : F}
  证明: (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])

Depends on / 依赖: constFormalMultilinearSeries, radius_eq_top_of_forall_image_add_eq_zero
-/
theorem constFormalMultilinearSeries_radius {v : F} :
    (constFormalMultilinearSeries 𝕜 E v).radius = ⊤ :=
  (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])

/--
lemma `zero_radius` / 引理 `zero_radius`

English:
lemma zero_radius
  statement: (0 : FormalMultilinearSeries 𝕜 E F).radius = ∞
  proof: by
  rw [← constFormalMultilinearSeries_zero]
  exact constFormalMultilinearSeries_radius

中文:
引理 zero_radius
  结论: (0 : FormalMultilinearSeries 𝕜 E F).radius = ∞
  证明: by
  rw [← constFormalMultilinearSeries_zero]
  exact constFormalMultilinearSeries_radius
-/
@[simp] lemma zero_radius : (0 : FormalMultilinearSeries 𝕜 E F).radius = ∞ := by
  rw [← constFormalMultilinearSeries_zero]
  exact constFormalMultilinearSeries_radius

/--
theorem `isLittleO_of_lt_radius` / 定理 `isLittleO_of_lt_radius`

English:
theorem isLittleO_of_lt_radius
  given: (h : ↑r < p.radius)
  proof: by
  have := (TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 1 4
  rw [this]
  -- Porting note: was
  -- rw [(TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4]
  simp only [radius, lt_iSup_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [ENNReal.coe_lt_coe]

中文:
定理 isLittleO_of_lt_radius
  条件: (h : ↑r < p.radius)
  证明: by
  have := (TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 1 4
  rw [this]
  -- Porting note: was
  -- rw [(TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4]
  simp only [radius, lt_iSup_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [ENNReal.coe_lt_coe]

Depends on / 依赖: TFAE_exists_lt_isLittleO_pow
-/
theorem isLittleO_of_lt_radius (h : ↑r < p.radius) :
    exists a in Ioo (0 : Real) 1, (fun n => ‖p n‖ * (r : Real) ^ n) =o[atTop] (a ^ ·) := by
  have := (TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 1 4
  rw [this]
  -- Porting note: was
  -- rw [(TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4]
  simp only [radius, lt_iSup_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at rt
  have : 0 < (t : Real) := r.coe_nonneg.trans_lt rt
  rw [← div_lt_one this] at rt
  refine ⟨_, rt, C, Or.inr zero_lt_one, fun n => ?_⟩
  calc
    |‖p n‖ * (r : Real) ^ n| = ‖p n‖ * (t : Real) ^ n * (r / t : Real) ^ n := by
      simp [field, abs_mul, div_pow]
    _ <= C * (r / t : Real) ^ n := by gcongr; apply hC

/--
theorem `isLittleO_one_of_lt_radius` / 定理 `isLittleO_one_of_lt_radius`

English:
theorem isLittleO_one_of_lt_radius
  given: (h : ↑r < p.radius)
  proof: let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
hp.trans (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow

中文:
定理 isLittleO_one_of_lt_radius
  条件: (h : ↑r < p.radius)
  证明: let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
hp.trans (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow

Depends on / 依赖: hp.trans, isLittleO_of_lt_radius, isLittleO_pow_pow_of_lt_left, one_pow, p.isLittleO_of_lt_radius
-/
theorem isLittleO_one_of_lt_radius (h : ↑r < p.radius) :
    (fun n => ‖p n‖ * (r : Real) ^ n) =o[atTop] (fun _ => 1 : Nat -> Real) :=
  let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
hp.trans (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow

/--
theorem `norm_mul_pow_le_mul_pow_of_lt_radius` / 定理 `norm_mul_pow_le_mul_pow_of_lt_radius`

English:
theorem norm_mul_pow_le_mul_pow_of_lt_radius
  given: (h : ↑r < p.radius)
  proof: by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

中文:
定理 norm_mul_pow_le_mul_pow_of_lt_radius
  条件: (h : ↑r < p.radius)
  证明: by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

Depends on / 依赖: TFAE_exists_lt_isLittleO_pow, isLittleO_of_lt_radius, le_abs_self, p.isLittleO_of_lt_radius
-/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    exists a in Ioo (0 : Real) 1, exists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C * a ^ n := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

/--
theorem `lt_radius_of_isBigO` / 定理 `lt_radius_of_isBigO`

English:
theorem lt_radius_of_isBigO
  statement: (h₀ : r != 0) {a : Real} (ha : a in Ioo (-1 : Real) 1)
  proof: by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero]; rw [← NNReal.coe_pos] at h₀
  lift a to Real>=0 using ha.1.le
  have : (r : Real) < r / a := by
    simpa only [div_one] using (div

中文:
定理 lt_radius_of_isBigO
  结论: (h₀ : r != 0) {a : 实数} (ha : a in 开区间 (-1 : 实数) 1)
  证明: by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero]; rw [← NNReal.coe_pos] at h₀
  lift a to Real>=0 using ha.1.le
  have : (r : Real) < r / a := by
    simpa only [div_one] using (div

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, NNReal, NNReal.coe_div, NNReal.coe_pos, TFAE_exists_lt_isLittleO_pow, coe_div, coe_lt_coe, coe_pos, div_lt_div_iff_of_pos_left, div_one, div_pow, le_radius_of_bound, mul_div_ass, p.le_radius_of_bound, pos_iff_ne_zero, this.mp, this.trans_le, trans_le, zero_lt_one
-/
theorem lt_radius_of_isBigO (h₀ : r != 0) {a : Real} (ha : a in Ioo (-1 : Real) 1)
    (hp : (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] (a ^ ·)) : ↑r < p.radius := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : Real) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero]; rw [← NNReal.coe_pos] at h₀
  lift a to Real>=0 using ha.1.le
  have : (r : Real) < r / a := by
    simpa only [div_one] using (div_lt_div_iff_of_pos_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast at this
  rw [← ENNReal.coe_lt_coe] at this
  refine this.trans_le (p.le_radius_of_bound C fun n => ?_)
  rw [NNReal.coe_div]; rw [div_pow]; rw [← mul_div_assoc]; rw [div_le_iff₀ (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)

/--
theorem `norm_mul_pow_le_of_lt_radius` / 定理 `norm_mul_pow_le_of_lt_radius`

English:
theorem norm_mul_pow_le_of_lt_radius
  statement: (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}
  proof: let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
⟨C, hC, fun n => (h n).trans mul_le_of_le_one_right hC.lt.le (pow_le_one₀ ha.1.le ha.2.le)⟩

中文:
定理 norm_mul_pow_le_of_lt_radius
  结论: (p : FormalMultilinearSeries 𝕜 E F) {r : 实数>=0}
  证明: let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
⟨C, hC, fun n => (h n).trans mul_le_of_le_one_right hC.lt.le (pow_le_one₀ ha.1.le ha.2.le)⟩

Depends on / 依赖: hC.lt.le, mul_le_of_le_one_right, norm_mul_pow_le_mul_pow_of_lt_radius, p.norm_mul_pow_le_mul_pow_of_lt_radius
-/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}
    (h : (r : Real>=0∞) < p.radius) : exists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C :=
  let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
⟨C, hC, fun n => (h n).trans mul_le_of_le_one_right hC.lt.le (pow_le_one₀ ha.1.le ha.2.le)⟩

/--
theorem `norm_le_div_pow_of_pos_of_lt_radius` / 定理 `norm_le_div_pow_of_pos_of_lt_radius`

English:
theorem norm_le_div_pow_of_pos_of_lt_radius
  statement: (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}
  proof: let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff₀ (pow_pos h0 _)) (hp n)⟩

中文:
定理 norm_le_div_pow_of_pos_of_lt_radius
  结论: (p : FormalMultilinearSeries 𝕜 E F) {r : 实数>=0}
  证明: let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff₀ (pow_pos h0 _)) (hp n)⟩

Depends on / 依赖: Iff.mpr, norm_mul_pow_le_of_lt_radius, p.norm_mul_pow_le_of_lt_radius, pow_pos
-/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}
    (h0 : 0 < r) (h : (r : Real>=0∞) < p.radius) : exists C > 0, forall n, ‖p n‖ <= C / (r : Real) ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff₀ (pow_pos h0 _)) (hp n)⟩

/--
theorem `nnnorm_mul_pow_le_of_lt_radius` / 定理 `nnnorm_mul_pow_le_of_lt_radius`

English:
theorem nnnorm_mul_pow_le_of_lt_radius
  statement: (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}
  proof: let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, mod_cast hp⟩

中文:
定理 nnnorm_mul_pow_le_of_lt_radius
  结论: (p : FormalMultilinearSeries 𝕜 E F) {r : 实数>=0}
  证明: let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, mod_cast hp⟩

Depends on / 依赖: hC.lt.le, mod_cast, norm_mul_pow_le_of_lt_radius, p.norm_mul_pow_le_of_lt_radius
-/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0}
    (h : (r : Real>=0∞) < p.radius) : exists C > 0, forall n, ‖p n‖₊ * r ^ n <= C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, mod_cast hp⟩

/--
theorem `le_radius_of_tendsto` / 定理 `le_radius_of_tendsto`

English:
theorem le_radius_of_tendsto
  statement: (p : FormalMultilinearSeries 𝕜 E F) {l : Real}
  proof: p.le_radius_of_isBigO (h.isBigO_one _)

中文:
定理 le_radius_of_tendsto
  结论: (p : FormalMultilinearSeries 𝕜 E F) {l : 实数}
  证明: p.le_radius_of_isBigO (h.isBigO_one _)

Depends on / 依赖: h.isBigO_one, isBigO_one, le_radius_of_isBigO, p.le_radius_of_isBigO
-/
theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : Real}
    (h : Tendsto (fun n => ‖p n‖ * (r : Real) ^ n) atTop (𝓝 l)) : ↑r <= p.radius :=
  p.le_radius_of_isBigO (h.isBigO_one _)

/--
theorem `le_radius_of_summable_norm` / 定理 `le_radius_of_summable_norm`

English:
theorem le_radius_of_summable_norm
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: p.le_radius_of_tendsto hs.tendsto_atTop_zero

中文:
定理 le_radius_of_summable_norm
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: p.le_radius_of_tendsto hs.tendsto_atTop_zero

Depends on / 依赖: hs.tendsto_atTop_zero, le_radius_of_tendsto, p.le_radius_of_tendsto, tendsto_atTop_zero
-/
theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : Summable fun n => ‖p n‖ * (r : Real) ^ n) : ↑r <= p.radius :=
  p.le_radius_of_tendsto hs.tendsto_atTop_zero

/--
theorem `not_summable_norm_of_radius_lt_nnnorm` / 定理 `not_summable_norm_of_radius_lt_nnnorm`

English:
theorem not_summable_norm_of_radius_lt_nnnorm
  statement: (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  proof: fun hs => not_le_of_gt h (p.le_radius_of_summable_norm hs)

中文:
定理 not_summable_norm_of_radius_lt_nnnorm
  结论: (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  证明: fun hs => not_le_of_gt h (p.le_radius_of_summable_norm hs)

Depends on / 依赖: le_radius_of_summable_norm, not_le_of_gt, p.le_radius_of_summable_norm
-/
theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (h : p.radius < ‖x‖₊) : ¬Summable fun n => ‖p n‖ * ‖x‖ ^ n :=
  fun hs => not_le_of_gt h (p.le_radius_of_summable_norm hs)

/--
theorem `summable_norm_mul_pow` / 定理 `summable_norm_mul_pow`

English:
theorem summable_norm_mul_pow
  given: (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius)
  proof: by
  obtain ⟨a, ha : a in Ioo (0 : Real) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact .of_nonneg_of_le (fun _ => by positivity)
    hp ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)

中文:
定理 summable_norm_mul_pow
  条件: (p : FormalMultilinearSeries 𝕜 E F) {r : 实数>=0} (h : ↑r < p.radius)
  证明: by
  obtain ⟨a, ha : a in Ioo (0 : Real) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact .of_nonneg_of_le (fun _ => by positivity)
    hp ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)

Depends on / 依赖: mul_left, norm_mul_pow_le_mul_pow_of_lt_radius, of_nonneg_of_le, p.norm_mul_pow_le_mul_pow_of_lt_radius, summable_geometric_of_lt_one
-/
theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) :
    Summable fun n : Nat => ‖p n‖ * (r : Real) ^ n := by
  obtain ⟨a, ha : a in Ioo (0 : Real) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact .of_nonneg_of_le (fun _ => by positivity)
    hp ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)

/--
theorem `summable_norm_apply` / 定理 `summable_norm_apply`

English:
theorem summable_norm_apply
  statement: (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  proof: by
  rw [mem_eball_zero_iff] at hx
  refine .of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ((p n).le_opNorm _).trans_eq ?_) (p.summable_norm_mul_pow hx)
  simp

中文:
定理 summable_norm_apply
  结论: (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  证明: by
  rw [mem_eball_zero_iff] at hx
  refine .of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ((p n).le_opNorm _).trans_eq ?_) (p.summable_norm_mul_pow hx)
  simp

Depends on / 依赖: le_opNorm, mem_eball_zero_iff, norm_nonneg, of_nonneg_of_le, p.summable_norm_mul_pow, summable_norm_mul_pow, trans_eq
-/
theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x in Metric.eball (0 : E) p.radius) : Summable fun n : Nat => ‖p n fun _ => x‖ := by
  rw [mem_eball_zero_iff] at hx
  refine .of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ((p n).le_opNorm _).trans_eq ?_) (p.summable_norm_mul_pow hx)
  simp

/--
theorem `summable_nnnorm_mul_pow` / 定理 `summable_nnnorm_mul_pow`

English:
theorem summable_nnnorm_mul_pow
  given: (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius)
  proof: by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

中文:
定理 summable_nnnorm_mul_pow
  条件: (p : FormalMultilinearSeries 𝕜 E F) {r : 实数>=0} (h : ↑r < p.radius)
  证明: by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

Depends on / 依赖: NNReal, NNReal.summable_coe, p.summable_norm_mul_pow, summable_coe, summable_norm_mul_pow
-/
theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) :
    Summable fun n : Nat => ‖p n‖₊ * r ^ n := by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

/--
theorem `summable` / 定理 `summable`

English:
theorem summable
  statement: [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  proof: (p.summable_norm_apply hx).of_norm

中文:
定理 summable
  结论: [完备空间 F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  证明: (p.summable_norm_apply hx).of_norm
-/
protected theorem summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x in Metric.eball (0 : E) p.radius) : Summable fun n : Nat => p n fun _ => x :=
  (p.summable_norm_apply hx).of_norm

/--
theorem `radius_eq_top_of_summable_norm` / 定理 `radius_eq_top_of_summable_norm`

English:
theorem radius_eq_top_of_summable_norm
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

中文:
定理 radius_eq_top_of_summable_norm
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

Depends on / 依赖: ENNReal, ENNReal.eq_top_of_forall_nnreal_le, eq_top_of_forall_nnreal_le, le_radius_of_summable_norm, p.le_radius_of_summable_norm
-/
theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : forall r : Real>=0, Summable fun n => ‖p n‖ * (r : Real) ^ n) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

/--
theorem `radius_eq_top_iff_summable_norm` / 定理 `radius_eq_top_iff_summable_norm`

English:
theorem radius_eq_top_iff_summable_norm
  given: (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  constructor
  · intro h r
    obtain ⟨a, ha : a in Ioo (0 : Real) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius
      (show (r : Real>=0∞) < p.radius from h.symm ▸ ENNReal.coe_lt_top)
    refine .of_norm_bounded
      (g := fun n => (C : Real) * a ^ n) ((summable_geometric_of_l

中文:
定理 radius_eq_top_iff_summable_norm
  条件: (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  constructor
  · intro h r
    obtain ⟨a, ha : a in Ioo (0 : Real) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius
      (show (r : Real>=0∞) < p.radius from h.symm ▸ ENNReal.coe_lt_top)
    refine .of_norm_bounded
      (g := fun n => (C : Real) * a ^ n) ((summable_geometric_of_l

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, Real.norm_of_nonneg, coe_lt_top, h.symm, mul_left, norm_mul_pow_le_mul_pow_of_lt_radius, norm_of_nonneg, of_norm_bounded, p.norm_mul_pow_le_mul_pow_of_lt_radius, p.radius, p.radius_eq_top_of_summable_norm, radius, radius_eq_top_of_summable_norm, specialize, summable_geometric_of_lt_one
-/
theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ forall r : Real>=0, Summable fun n => ‖p n‖ * (r : Real) ^ n := by
  constructor
  · intro h r
    obtain ⟨a, ha : a in Ioo (0 : Real) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius
      (show (r : Real>=0∞) < p.radius from h.symm ▸ ENNReal.coe_lt_top)
    refine .of_norm_bounded
      (g := fun n => (C : Real) * a ^ n) ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)
      fun n => ?_
    specialize hp n
    rwa [Real.norm_of_nonneg (by positivity)]
  · exact p.radius_eq_top_of_summable_norm

/--
theorem `le_mul_pow_of_radius_pos` / 定理 `le_mul_pow_of_radius_pos`

English:
theorem le_mul_pow_of_radius_pos
  given: (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius)
  proof: by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : Real) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => ?_⟩
  rw [inv_pow]; rw [← div_

中文:
定理 le_mul_pow_of_radius_pos
  条件: (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius)
  证明: by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : Real) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => ?_⟩
  rw [inv_pow]; rw [← div_

Depends on / 依赖: ENNReal, ENNReal.coe_pos, ENNReal.lt_iff_exists_nnreal_btwn, coe_pos, div_eq_mul_inv, inv_pos, inv_pow, lt_iff_exists_nnreal_btwn, norm_le_div_pow_of_pos_of_lt_radius
-/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    exists (C r : _) (_ : 0 < C) (_ : 0 < r), forall n, ‖p n‖ <= C * r ^ n := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : Real) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => ?_⟩
  rw [inv_pow]; rw [← div_eq_mul_inv]
  exact hCp n

/--
lemma `radius_le_of_le` / 引理 `radius_le_of_le`

English:
lemma radius_le_of_le
  statement: {𝕜' E' F' : Type*}
  proof: by
  apply le_of_forall_nnreal_lt (fun r hr => ?_)
  rcases norm_mul_pow_le_of_lt_radius _ hr with ⟨C, -, hC⟩
  apply le_radius_of_bound _ C (fun n => ?_)
  apply le_trans _ (hC n)
  gcongr
  exact h n

中文:
引理 radius_le_of_le
  结论: {𝕜' E' F' : 类型}
  证明: by
  apply le_of_forall_nnreal_lt (fun r hr => ?_)
  rcases norm_mul_pow_le_of_lt_radius _ hr with ⟨C, -, hC⟩
  apply le_radius_of_bound _ C (fun n => ?_)
  apply le_trans _ (hC n)
  gcongr
  exact h n

Depends on / 依赖: le_of_forall_nnreal_lt, le_radius_of_bound, le_trans, norm_mul_pow_le_of_lt_radius
-/
lemma radius_le_of_le {𝕜' E' F' : Type*}
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜' E' F'}
    (h : forall n, ‖p n‖ <= ‖q n‖) : q.radius <= p.radius := by
  apply le_of_forall_nnreal_lt (fun r hr => ?_)
  rcases norm_mul_pow_le_of_lt_radius _ hr with ⟨C, -, hC⟩
  apply le_radius_of_bound _ C (fun n => ?_)
  apply le_trans _ (hC n)
  gcongr
  exact h n

/--
theorem `min_radius_le_radius_add` / 定理 `min_radius_le_radius_add`

English:
theorem min_radius_le_radius_add
  given: (p q : FormalMultilinearSeries 𝕜 E F)
  proof: by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
  rw [← add_mul]; rw [norm_mul]; rw [norm_mu

中文:
定理 min_radius_le_radius_add
  条件: (p q : FormalMultilinearSeries 𝕜 E F)
  证明: by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
  rw [← add_mul]; rw [norm_mul]; rw [norm_mu

Depends on / 依赖: ENNReal, ENNReal.le_of_forall_nnreal_lt, add_mul, isBigO, isBigO_of_le, isLittleO_one_of_lt_radius, le_abs_self, le_of_forall_nnreal_lt, le_radius_of_isBigO, lt_min_iff, norm_add_le, norm_mul, norm_norm, p.isLittleO_one_of_lt_radius, q.isLittleO_one_of_lt_radius
-/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) :
    min p.radius q.radius <= (p + q).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
  rw [← add_mul]; rw [norm_mul]; rw [norm_mul]; rw [norm_norm]
  gcongr
  exact (norm_add_le _ _).trans (le_abs_self _)

@[simp]
/--
theorem `radius_neg` / 定理 `radius_neg`

English:
theorem radius_neg
  given: (p : FormalMultilinearSeries 𝕜 E F)
  statement: (-p).radius = p.radius
  proof: by
  simp only [radius, neg_apply, norm_neg]

中文:
定理 radius_neg
  条件: (p : FormalMultilinearSeries 𝕜 E F)
  结论: (-p).radius = p.radius
  证明: by
  simp only [radius, neg_apply, norm_neg]

Depends on / 依赖: neg_apply, norm_neg, radius
-/
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp only [radius, neg_apply, norm_neg]

/--
theorem `radius_le_smul` / 定理 `radius_le_smul`

English:
theorem radius_le_smul
  statement: {p : FormalMultilinearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜']
  proof: by
  simp only [radius, smul_apply]
  refine iSup_mono fun r => iSup_mono' fun C => ⟨‖c‖ * C, iSup_mono' fun h => ?_⟩
  simp only [le_refl, exists_prop, and_true]
  intro n
  grw [norm_smul_le, mul_assoc, h]

中文:
定理 radius_le_smul
  结论: {p : FormalMultilinearSeries 𝕜 E F} {𝕜' : 类型} {c : 𝕜'} [赋范环 𝕜']
  证明: by
  simp only [radius, smul_apply]
  refine iSup_mono fun r => iSup_mono' fun C => ⟨‖c‖ * C, iSup_mono' fun h => ?_⟩
  simp only [le_refl, exists_prop, and_true]
  intro n
  grw [norm_smul_le, mul_assoc, h]

Depends on / 依赖: and_true, exists_prop, iSup_mono, le_refl, mul_assoc, norm_smul_le, radius, smul_apply
-/
theorem radius_le_smul {p : FormalMultilinearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [IsBoundedSMul 𝕜' F] :
    p.radius <= (c • p).radius := by
  simp only [radius, smul_apply]
  refine iSup_mono fun r => iSup_mono' fun C => ⟨‖c‖ * C, iSup_mono' fun h => ?_⟩
  simp only [le_refl, exists_prop, and_true]
  intro n
  grw [norm_smul_le, mul_assoc, h]

/--
theorem `radius_smul_eq` / 定理 `radius_smul_eq`

English:
theorem radius_smul_eq
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  apply eq_of_le_of_ge _ radius_le_smul
  exact radius_le_smul.trans_eq (congr_arg _ <| inv_smul_smul₀ hc p)

中文:
定理 radius_smul_eq
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  apply eq_of_le_of_ge _ radius_le_smul
  exact radius_le_smul.trans_eq (congr_arg _ <| inv_smul_smul₀ hc p)

Depends on / 依赖: congr_arg, eq_of_le_of_ge, radius_le_smul, radius_le_smul.trans_eq, trans_eq
-/
theorem radius_smul_eq (p : FormalMultilinearSeries 𝕜 E F)
    {𝕜' : Type*} {c : 𝕜'} [NormedDivisionRing 𝕜'] [Module 𝕜' F] [NormSMulClass 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (hc : c != 0) :
    (c • p).radius = p.radius := by
  apply eq_of_le_of_ge _ radius_le_smul
  exact radius_le_smul.trans_eq (congr_arg _ <| inv_smul_smul₀ hc p)

/--
lemma `norm_compContinuousLinearMap_le` / 引理 `norm_compContinuousLinearMap_le`

English:
lemma norm_compContinuousLinearMap_le
  given: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : Nat)
  proof: by
  simp only [compContinuousLinearMap]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp

中文:
引理 norm_compContinuousLinearMap_le
  条件: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : 自然数)
  证明: by
  simp only [compContinuousLinearMap]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_compContinuousLinearMap_le, compContinuousLinearMap, le_trans, norm_compContinuousLinearMap_le
-/
lemma norm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : Nat) :
    ‖p.compContinuousLinearMap u n‖ <= ‖p n‖ * ‖u‖ ^ n := by
  simp only [compContinuousLinearMap]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp

/--
lemma `enorm_compContinuousLinearMap_le` / 引理 `enorm_compContinuousLinearMap_le`

English:
lemma enorm_compContinuousLinearMap_le
  statement: (p : FormalMultilinearSeries 𝕜 F G)
  proof: by
  rw [← ofReal_norm]; rw [← ofReal_norm]; rw [← ofReal_norm]; rw [← ENNReal.ofReal_pow (by simp)]; rw [← ENNReal.ofReal_mul (by simp)]
  gcongr
  apply norm_compContinuousLinearMap_le

中文:
引理 enorm_compContinuousLinearMap_le
  结论: (p : FormalMultilinearSeries 𝕜 F G)
  证明: by
  rw [← ofReal_norm]; rw [← ofReal_norm]; rw [← ofReal_norm]; rw [← ENNReal.ofReal_pow (by simp)]; rw [← ENNReal.ofReal_mul (by simp)]
  gcongr
  apply norm_compContinuousLinearMap_le

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, ENNReal.ofReal_pow, norm_compContinuousLinearMap_le, ofReal_mul, ofReal_norm, ofReal_pow
-/
lemma enorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G)
    (u : E ->L[𝕜] F) (n : Nat) : ‖p.compContinuousLinearMap u n‖ₑ <= ‖p n‖ₑ * ‖u‖ₑ ^ n := by
  rw [← ofReal_norm]; rw [← ofReal_norm]; rw [← ofReal_norm]; rw [← ENNReal.ofReal_pow (by simp)]; rw [← ENNReal.ofReal_mul (by simp)]
  gcongr
  apply norm_compContinuousLinearMap_le

/--
lemma `nnnorm_compContinuousLinearMap_le` / 引理 `nnnorm_compContinuousLinearMap_le`

English:
lemma nnnorm_compContinuousLinearMap_le
  statement: (p : FormalMultilinearSeries 𝕜 F G)
  proof: norm_compContinuousLinearMap_le p u n

中文:
引理 nnnorm_compContinuousLinearMap_le
  结论: (p : FormalMultilinearSeries 𝕜 F G)
  证明: norm_compContinuousLinearMap_le p u n

Depends on / 依赖: norm_compContinuousLinearMap_le
-/
lemma nnnorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G)
    (u : E ->L[𝕜] F) (n : Nat) : ‖p.compContinuousLinearMap u n‖₊ <= ‖p n‖₊ * ‖u‖₊ ^ n :=
  norm_compContinuousLinearMap_le p u n

/--
theorem `div_le_radius_compContinuousLinearMap` / 定理 `div_le_radius_compContinuousLinearMap`

English:
theorem div_le_radius_compContinuousLinearMap
  given: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F)
  proof: by
  obtain (rfl | h_zero) := eq_zero_or_nnnorm_pos u
  · simp
  rw [ENNReal.div_le_iff (by simpa using h_zero) (by simp)]
  refine le_of_forall_nnreal_lt fun r hr => ?_
  rw [← ENNReal.div_le_iff (by simpa using h_zero) (by simp)]; rw [enorm_eq_nnnorm]; rw [← coe_div h_zero.ne']
  obtain ⟨C, hC_pos

中文:
定理 div_le_radius_compContinuousLinearMap
  条件: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F)
  证明: by
  obtain (rfl | h_zero) := eq_zero_or_nnnorm_pos u
  · simp
  rw [ENNReal.div_le_iff (by simpa using h_zero) (by simp)]
  refine le_of_forall_nnreal_lt fun r hr => ?_
  rw [← ENNReal.div_le_iff (by simpa using h_zero) (by simp)]; rw [enorm_eq_nnnorm]; rw [← coe_div h_zero.ne']
  obtain ⟨C, hC_pos

Depends on / 依赖: ENNReal, ENNReal.div_le_iff, coe_div, compContinuousLinearMap, div_le_iff, enorm_eq_nnnorm, eq_zero_or_nnnorm_pos, hC_pos, h_zero, h_zero.ne, le_of_forall_nnreal_lt, le_radius_of_bound, nnnorm_compConti, norm_mul_pow_le_of_lt_radius, p.compContinuousLinearMap, p.norm_mul_pow_le_of_lt_radius
-/
theorem div_le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) :
    p.radius / ‖u‖ₑ <= (p.compContinuousLinearMap u).radius := by
  obtain (rfl | h_zero) := eq_zero_or_nnnorm_pos u
  · simp
  rw [ENNReal.div_le_iff (by simpa using h_zero) (by simp)]
  refine le_of_forall_nnreal_lt fun r hr => ?_
  rw [← ENNReal.div_le_iff (by simpa using h_zero) (by simp)]; rw [enorm_eq_nnnorm]; rw [← coe_div h_zero.ne']
  obtain ⟨C, hC_pos, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  refine le_radius_of_bound _ C fun n => ?_
  calc
    ‖p.compContinuousLinearMap u n‖ * ↑(r / ‖u‖₊) ^ n <= ‖p n‖ * ‖u‖ ^ n * ↑(r / ‖u‖₊) ^ n := by
      gcongr
      exact nnnorm_compContinuousLinearMap_le p u n
    _ = ‖p n‖ * r ^ n := by
      simp only [NNReal.coe_div, coe_nnnorm, div_pow, mul_assoc]
      rw [mul_div_cancel₀]
      rw [← NNReal.coe_pos] at h_zero
      positivity
    _ <= C := hC n

/--
theorem `le_radius_compContinuousLinearMap` / 定理 `le_radius_compContinuousLinearMap`

English:
theorem le_radius_compContinuousLinearMap
  given: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->ₗᵢ[𝕜] F)
  proof: by
  obtain (h | h) := subsingleton_or_nontrivial E
  · simp [Subsingleton.elim u.toContinuousLinearMap 0]
  · simpa [u.norm_toContinuousLinearMap]
      using div_le_radius_compContinuousLinearMap p u.toContinuousLinearMap

中文:
定理 le_radius_compContinuousLinearMap
  条件: (p : FormalMultilinearSeries 𝕜 F G) (u : E ->ₗᵢ[𝕜] F)
  证明: by
  obtain (h | h) := subsingleton_or_nontrivial E
  · simp [Subsingleton.elim u.toContinuousLinearMap 0]
  · simpa [u.norm_toContinuousLinearMap]
      using div_le_radius_compContinuousLinearMap p u.toContinuousLinearMap

Depends on / 依赖: Subsingleton, Subsingleton.elim, div_le_radius_compContinuousLinearMap, norm_toContinuousLinearMap, subsingleton_or_nontrivial, toContinuousLinearMap, u.norm_toContinuousLinearMap, u.toContinuousLinearMap
-/
theorem le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->ₗᵢ[𝕜] F) :
    p.radius <= (p.compContinuousLinearMap u.toContinuousLinearMap).radius := by
  obtain (h | h) := subsingleton_or_nontrivial E
  · simp [Subsingleton.elim u.toContinuousLinearMap 0]
  · simpa [u.norm_toContinuousLinearMap]
      using div_le_radius_compContinuousLinearMap p u.toContinuousLinearMap

/--
theorem `radius_compContinuousLinearMap_le` / 定理 `radius_compContinuousLinearMap_le`

English:
theorem radius_compContinuousLinearMap_le
  statement: [Nontrivial F]
  proof: by
  have := (p.compContinuousLinearMap u.toContinuousLinearMap).div_le_radius_compContinuousLinearMap
    u.symm.toContinuousLinearMap
  simp only [compContinuousLinearMap_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
    compContinuousLinearMap_id] at this
  rwa [ENNReal.div_le_iff' (by simpa [DF

中文:
定理 radius_compContinuousLinearMap_le
  结论: [非平凡 F]
  证明: by
  have := (p.compContinuousLinearMap u.toContinuousLinearMap).div_le_radius_compContinuousLinearMap
    u.symm.toContinuousLinearMap
  simp only [compContinuousLinearMap_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
    compContinuousLinearMap_id] at this
  rwa [ENNReal.div_le_iff' (by simpa [DF

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_comp_coe_symm, DFunLike, DFunLike.ext_iff, ENNReal, ENNReal.div_le_iff, coe_comp_coe_symm, compContinuousLinearMap, compContinuousLinearMap_comp, compContinuousLinearMap_id, div_le_iff, div_le_radius_compContinuousLinearMap, exists_ne, ext_iff, p.compContinuousLinearMap, toContinuousLinearMap, u.symm.toContinuousLinearMap, u.toContinuousLinearMap
-/
theorem radius_compContinuousLinearMap_le [Nontrivial F]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃L[𝕜] F) :
    (p.compContinuousLinearMap u.toContinuousLinearMap).radius <=
    ‖u.symm.toContinuousLinearMap‖ₑ * p.radius := by
  have := (p.compContinuousLinearMap u.toContinuousLinearMap).div_le_radius_compContinuousLinearMap
    u.symm.toContinuousLinearMap
  simp only [compContinuousLinearMap_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
    compContinuousLinearMap_id] at this
  rwa [ENNReal.div_le_iff' (by simpa [DFunLike.ext_iff] using exists_ne 0) (by simp)] at this

@[simp]
/--
theorem `radius_compContinuousLinearMap_linearIsometryEquiv_eq` / 定理 `radius_compContinuousLinearMap_linearIsometryEquiv_eq`

English:
theorem radius_compContinuousLinearMap_linearIsometryEquiv_eq
  statement: [Nontrivial E]
  proof: by
refine le_antisymm ?_ le_radius_compContinuousLinearMap _ _
  have _ : Nontrivial F := u.symm.toEquiv.nontrivial
  convert! radius_compContinuousLinearMap_le p u.toContinuousLinearEquiv
  have : u.toContinuousLinearEquiv.symm.toContinuousLinearMap =
    u.symm.toLinearIsometry.toContinuousLinearM

中文:
定理 radius_compContinuousLinearMap_linearIsometryEquiv_eq
  结论: [非平凡 E]
  证明: by
refine le_antisymm ?_ le_radius_compContinuousLinearMap _ _
  have _ : Nontrivial F := u.symm.toEquiv.nontrivial
  convert! radius_compContinuousLinearMap_le p u.toContinuousLinearEquiv
  have : u.toContinuousLinearEquiv.symm.toContinuousLinearMap =
    u.symm.toLinearIsometry.toContinuousLinearM

Depends on / 依赖: Nontrivial, convert, le_antisymm, le_radius_compContinuousLinearMap, nontrivial, radius_compContinuousLinearMap_le, toContinuousLinearEquiv, toContinuousLinearMap, toEquiv, toLinearIsometry, u.symm.toEquiv.nontrivial, u.symm.toLinearIsometry.toContinuousLinearMap, u.toContinuousLinearEquiv, u.toContinuousLinearEquiv.symm.toContinuousLinearMap
-/
theorem radius_compContinuousLinearMap_linearIsometryEquiv_eq [Nontrivial E]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃ₗᵢ[𝕜] F) :
    (p.compContinuousLinearMap u.toLinearIsometry.toContinuousLinearMap).radius = p.radius := by
refine le_antisymm ?_ le_radius_compContinuousLinearMap _ _
  have _ : Nontrivial F := u.symm.toEquiv.nontrivial
  convert! radius_compContinuousLinearMap_le p u.toContinuousLinearEquiv
  have : u.toContinuousLinearEquiv.symm.toContinuousLinearMap =
    u.symm.toLinearIsometry.toContinuousLinearMap := rfl
  simp [this]

/--
theorem `radius_compContinuousLinearMap_eq` / 定理 `radius_compContinuousLinearMap_eq`

English:
theorem radius_compContinuousLinearMap_eq
  statement: [Nontrivial E]
  proof: let v : E ≃ₗᵢ[𝕜] F :=
    { LinearEquiv.ofBijective u.toLinearMap ⟨hu_iso.injective, hu_surj⟩ with
      norm_map' := hu_iso.norm_map_of_map_zero (map_zero u) }
  radius_compContinuousLinearMap_linearIsometryEquiv_eq p v

@[simp]

中文:
定理 radius_compContinuousLinearMap_eq
  结论: [非平凡 E]
  证明: let v : E ≃ₗᵢ[𝕜] F :=
    { LinearEquiv.ofBijective u.toLinearMap ⟨hu_iso.injective, hu_surj⟩ with
      norm_map' := hu_iso.norm_map_of_map_zero (map_zero u) }
  radius_compContinuousLinearMap_linearIsometryEquiv_eq p v

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, hu_iso, hu_iso.injective, hu_iso.norm_map_of_map_zero, hu_surj, injective, map_zero, norm_map, norm_map_of_map_zero, ofBijective, radius_compContinuousLinearMap_linearIsometryEquiv_eq, toLinearMap, u.toLinearMap
-/
theorem radius_compContinuousLinearMap_eq [Nontrivial E]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (hu_iso : Isometry u)
    (hu_surj : Function.Surjective u) :
    (p.compContinuousLinearMap u).radius = p.radius :=
  let v : E ≃ₗᵢ[𝕜] F :=
    { LinearEquiv.ofBijective u.toLinearMap ⟨hu_iso.injective, hu_surj⟩ with
      norm_map' := hu_iso.norm_map_of_map_zero (map_zero u) }
  radius_compContinuousLinearMap_linearIsometryEquiv_eq p v

@[simp]
/--
theorem `radius_compNeg` / 定理 `radius_compNeg`

English:
theorem radius_compNeg
  given: [Nontrivial E] (p : FormalMultilinearSeries 𝕜 E F)
  proof: radius_compContinuousLinearMap_linearIsometryEquiv_eq _ (.neg 𝕜)

@[simp]

中文:
定理 radius_compNeg
  条件: [非平凡 E] (p : FormalMultilinearSeries 𝕜 E F)
  证明: radius_compContinuousLinearMap_linearIsometryEquiv_eq _ (.neg 𝕜)

@[simp]

Depends on / 依赖: radius_compContinuousLinearMap_linearIsometryEquiv_eq
-/
theorem radius_compNeg [Nontrivial E] (p : FormalMultilinearSeries 𝕜 E F) :
    (p.compContinuousLinearMap (-(.id _ _))).radius = p.radius :=
  radius_compContinuousLinearMap_linearIsometryEquiv_eq _ (.neg 𝕜)

@[simp]
/--
theorem `radius_shift` / 定理 `radius_shift`

English:
theorem radius_shift
  given: (p : FormalMultilinearSeries 𝕜 E F)
  statement: p.shift.radius = p.radius
  proof: by
  simp only [radius, shift, Nat.succ_eq_add_one, ContinuousMultilinearMap.curryRight_norm]
  congr
  ext r
  apply eq_of_le_of_ge
  · apply iSup_mono'
    intro C
    use ‖p 0‖ ⊔ (C * r)
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    rc

中文:
定理 radius_shift
  条件: (p : FormalMultilinearSeries 𝕜 E F)
  结论: p.shift.radius = p.radius
  证明: by
  simp only [radius, shift, Nat.succ_eq_add_one, ContinuousMultilinearMap.curryRight_norm]
  congr
  ext r
  apply eq_of_le_of_ge
  · apply iSup_mono'
    intro C
    use ‖p 0‖ ⊔ (C * r)
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    rc

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryRight_norm, Nat.succ_eq_add_one, and_true, curryRight_norm, eq_of_le_of_ge, eq_zero_or_pos, exists_prop, iSup_mono, le_refl, le_sup_iff, mul_assoc, pow_succ, radius, succ_eq_add_one
-/
theorem radius_shift (p : FormalMultilinearSeries 𝕜 E F) : p.shift.radius = p.radius := by
  simp only [radius, shift, Nat.succ_eq_add_one, ContinuousMultilinearMap.curryRight_norm]
  congr
  ext r
  apply eq_of_le_of_ge
  · apply iSup_mono'
    intro C
    use ‖p 0‖ ⊔ (C * r)
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    rcases n with - | m
    · simp
    right
    rw [pow_succ]; rw [← mul_assoc]
    gcongr; apply h
  · apply iSup_mono'
    intro C
    use ‖p 1‖ ⊔ C / r
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    cases eq_zero_or_pos r with
    | inl hr =>
      rw [hr]
      cases n <;> simp
    | inr hr =>
      right
      rw [← NNReal.coe_pos] at hr
      specialize h (n + 1)
      rw [le_div_iff₀ hr]
      rwa [pow_succ, ← mul_assoc] at h

@[simp]
/--
theorem `radius_unshift` / 定理 `radius_unshift`

English:
theorem radius_unshift
  given: (p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F)
  proof: by
  rw [← radius_shift]; rw [unshift_shift]

中文:
定理 radius_unshift
  条件: (p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F)
  证明: by
  rw [← radius_shift]; rw [unshift_shift]

Depends on / 依赖: radius_shift, unshift_shift
-/
theorem radius_unshift (p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F) :
    (p.unshift z).radius = p.radius := by
  rw [← radius_shift]; rw [unshift_shift]

/--
theorem `hasSum` / 定理 `hasSum`

English:
theorem hasSum
  statement: [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  proof: (p.summable hx).hasSum

中文:
定理 hasSum
  结论: [完备空间 F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  证明: (p.summable hx).hasSum
-/
protected theorem hasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x in Metric.eball (0 : E) p.radius) : HasSum (fun n : Nat => p n fun _ => x) (p.sum x) :=
  (p.summable hx).hasSum

/--
theorem `radius_le_radius_continuousLinearMap_comp` / 定理 `radius_le_radius_continuousLinearMap_comp`

English:
theorem radius_le_radius_continuousLinearMap_comp
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ ?_) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (Eventually.of_forall fun n

中文:
定理 radius_le_radius_continuousLinearMap_comp
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ ?_) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (Eventually.of_forall fun n

Depends on / 依赖: ENNReal, ENNReal.le_of_forall_nnreal_lt, Eventually, Eventually.of_forall, IsBigO, IsBigO.mul, IsBigO.trans_isLittleO, IsBigOWith, IsBigOWith.isBigO, IsBigOWith.of_bound, f.norm_compContinuousMultilinearMap_le, isBigO, isBigO_refl, isLittleO_one_of_lt_radius, le_of_forall_nnreal_lt, le_radius_of_isBigO, norm_compContinuousMultilinearMap_le, norm_norm, of_bound, of_forall
-/
theorem radius_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E F)
    (f : F ->L[𝕜] G) : p.radius <= (f.compFormalMultilinearSeries p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ ?_) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (Eventually.of_forall fun n => ?_)
  simpa only [norm_norm] using! f.norm_compContinuousMultilinearMap_le (p n)

end FormalMultilinearSeries
