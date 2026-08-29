/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Summability of logarithms

We give conditions under which the logarithms of a summable sequence are summable. We also use this
to relate summability of `f` to multipliability of `1 + f`.

-/

public section

variable {ι : Type*}

open Filter Topology NNReal SummationFilter

namespace Complex
variable {f : ι -> Complex} {a : Complex}

/--
lemma `hasProd_of_hasSum_log` / 引理 `hasProd_of_hasSum_log`

English:
lemma hasProd_of_hasSum_log
  given: (hfn : forall i, f i != 0) (hf : HasSum (fun i => log (f i)) a)
  proof: hf.cexp.congr (by simp [exp_log, hfn])

中文:
引理 hasProd_of_hasSum_log
  条件: (hfn : 对任意 i, f i != 0) (hf : HasSum (fun i => log (f i)) a)
  证明: hf.cexp.congr (by simp [exp_log, hfn])

Depends on / 依赖: exp_log, hf.cexp.congr
-/
lemma hasProd_of_hasSum_log (hfn : forall i, f i != 0) (hf : HasSum (fun i => log (f i)) a) :
    HasProd f (exp a) :=
  hf.cexp.congr (by simp [exp_log, hfn])

/--
lemma `multipliable_of_summable_log` / 引理 `multipliable_of_summable_log`

English:
lemma multipliable_of_summable_log
  given: (hf : Summable fun i => log (f i))
  proof: by
  by_cases! hfn : exists n, f n = 0
  · exact multipliable_of_exists_eq_zero hfn
  · exact ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

中文:
引理 multipliable_of_summable_log
  条件: (hf : Summable fun i => log (f i))
  证明: by
  by_cases! hfn : exists n, f n = 0
  · exact multipliable_of_exists_eq_zero hfn
  · exact ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

Depends on / 依赖: hasProd_of_hasSum_log, hasSum, hf.hasSum, multipliable_of_exists_eq_zero
-/
lemma multipliable_of_summable_log (hf : Summable fun i => log (f i)) :
    Multipliable f := by
  by_cases! hfn : exists n, f n = 0
  · exact multipliable_of_exists_eq_zero hfn
  · exact ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/--
lemma `cexp_tsum_eq_tprod` / 引理 `cexp_tsum_eq_tprod`

English:
lemma cexp_tsum_eq_tprod
  given: (hfn : forall i, f i != 0) (hf : Summable fun i => log (f i))
  proof: (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

中文:
引理 cexp_tsum_eq_tprod
  条件: (hfn : 对任意 i, f i != 0) (hf : Summable fun i => log (f i))
  证明: (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

Depends on / 依赖: hasProd_of_hasSum_log, hasSum, hf.hasSum, tprod_eq, tprod_eq.symm
-/
lemma cexp_tsum_eq_tprod (hfn : forall i, f i != 0) (hf : Summable fun i => log (f i)) :
    cexp (∑' i, log (f i)) = ∏' i, f i :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

/--
lemma `summable_log_one_add_of_summable` / 引理 `summable_log_one_add_of_summable`

English:
lemma summable_log_one_add_of_summable
  given: {f : ι -> Complex} (hf : Summable f)
  proof: by
  apply (hf.norm.mul_left (3 / 2)).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    using norm_log_one_add_half_le_self hi

中文:
引理 summable_log_one_add_of_summable
  条件: {f : ι -> 复形} (hf : Summable f)
  证明: by
  apply (hf.norm.mul_left (3 / 2)).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    using norm_log_one_add_half_le_self hi

Depends on / 依赖: eventually_le_const, filter_upwards, hf.norm.mul_left, hf.norm.tendsto_cofinite_zero.eventually_le_const, mul_left, norm_log_one_add_half_le_self, of_norm_bounded_eventually, one_half_pos, tendsto_cofinite_zero
-/
lemma summable_log_one_add_of_summable {f : ι -> Complex} (hf : Summable f) :
    Summable (fun i => log (1 + f i)) := by
  apply (hf.norm.mul_left (3 / 2)).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    using norm_log_one_add_half_le_self hi

/--
lemma `multipliable_one_add_of_summable` / 引理 `multipliable_one_add_of_summable`

English:
lemma multipliable_one_add_of_summable
  given: (hf : Summable f)
  proof: multipliable_of_summable_log (summable_log_one_add_of_summable hf)

中文:
引理 multipliable_one_add_of_summable
  条件: (hf : Summable f)
  证明: multipliable_of_summable_log (summable_log_one_add_of_summable hf)
-/
protected lemma multipliable_one_add_of_summable (hf : Summable f) :
    Multipliable (fun i => 1 + f i) :=
  multipliable_of_summable_log (summable_log_one_add_of_summable hf)

end Complex

namespace Real
variable {f : ι -> Real} {a : Real}

/--
lemma `hasProd_of_hasSum_log` / 引理 `hasProd_of_hasSum_log`

English:
lemma hasProd_of_hasSum_log
  given: (hfn : forall i, 0 < f i) (hf : HasSum (fun i => log (f i)) a)
  proof: hf.rexp.congr (by simp [exp_log, hfn])

中文:
引理 hasProd_of_hasSum_log
  条件: (hfn : 对任意 i, 0 < f i) (hf : HasSum (fun i => log (f i)) a)
  证明: hf.rexp.congr (by simp [exp_log, hfn])

Depends on / 依赖: exp_log, hf.rexp.congr
-/
lemma hasProd_of_hasSum_log (hfn : forall i, 0 < f i) (hf : HasSum (fun i => log (f i)) a) :
    HasProd f (rexp a) :=
  hf.rexp.congr (by simp [exp_log, hfn])

/--
lemma `multipliable_of_summable_log` / 引理 `multipliable_of_summable_log`

English:
lemma multipliable_of_summable_log
  given: (hfn : forall i, 0 < f i) (hf : Summable fun i => log (f i))
  proof: ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

中文:
引理 multipliable_of_summable_log
  条件: (hfn : 对任意 i, 0 < f i) (hf : Summable fun i => log (f i))
  证明: ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

Depends on / 依赖: hasProd_of_hasSum_log, hasSum, hf.hasSum
-/
lemma multipliable_of_summable_log (hfn : forall i, 0 < f i) (hf : Summable fun i => log (f i)) :
    Multipliable f :=
  ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/--
lemma `multipliable_of_summable_log'` / 引理 `multipliable_of_summable_log'`

English:
lemma multipliable_of_summable_log'
  statement: (hfn : forallᶠ i in cofinite, 0 < f i)
  proof: by
  have : Summable fun i => log (if 0 < f i then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i => if 0 < f i then f i else 1 := by
    refine multipliable_of_summable_log (fun i => ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite₀ (fun i => ?_) ?_
  · split_ifs with h <;> simp [h, ne_of_gt]
  · filter_upwards [hfn] with i hi using by simp [hi]

中文:
引理 multipliable_of_summable_log'
  结论: (hfn : 对任意ᶠ i in cofinite, 0 < f i)
  证明: by
  have : Summable fun i => log (if 0 < f i then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i => if 0 < f i then f i else 1 := by
    refine multipliable_of_summable_log (fun i => ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite₀ (fun i => ?_) ?_
  · split_ifs with h <;> simp [h, ne_of_gt]
  · filter_upwards [hfn] with i hi using by simp [hi]

Depends on / 依赖: Multipliable, Summable, congr_cofinite, filter_upwards, hf.congr_cofinite, multipliable_of_summable_log, ne_of_gt, split_ifs, this.congr_cofinite
-/
lemma multipliable_of_summable_log' (hfn : forallᶠ i in cofinite, 0 < f i)
    (hf : Summable fun i => log (f i)) : Multipliable f := by
  have : Summable fun i => log (if 0 < f i then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i => if 0 < f i then f i else 1 := by
    refine multipliable_of_summable_log (fun i => ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite₀ (fun i => ?_) ?_
  · split_ifs with h <;> simp [h, ne_of_gt]
  · filter_upwards [hfn] with i hi using by simp [hi]

/--
lemma `rexp_tsum_eq_tprod` / 引理 `rexp_tsum_eq_tprod`

English:
lemma rexp_tsum_eq_tprod
  given: (hfn : forall i, 0 < f i) (hf : Summable fun i => log (f i))
  proof: (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

中文:
引理 rexp_tsum_eq_tprod
  条件: (hfn : 对任意 i, 0 < f i) (hf : Summable fun i => log (f i))
  证明: (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

Depends on / 依赖: hasProd_of_hasSum_log, hasSum, hf.hasSum, tprod_eq, tprod_eq.symm
-/
lemma rexp_tsum_eq_tprod (hfn : forall i, 0 < f i) (hf : Summable fun i => log (f i)) :
    rexp (∑' i, log (f i)) = ∏' i, f i :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

open Complex in
/--
lemma `summable_log_one_add_of_summable` / 引理 `summable_log_one_add_of_summable`

English:
lemma summable_log_one_add_of_summable
  given: (hf : Summable f)
  proof: by
  rw [← summable_ofReal]
  apply (Complex.summable_log_one_add_of_summable (summable_ofReal.mpr hf)).congr_cofinite
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_le neg_one_lt_zero] with i hi
  rw [ofReal_log]; rw [ofReal_add]; rw [ofReal_one]
  linarith

中文:
引理 summable_log_one_add_of_summable
  条件: (hf : Summable f)
  证明: by
  rw [← summable_ofReal]
  apply (Complex.summable_log_one_add_of_summable (summable_ofReal.mpr hf)).congr_cofinite
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_le neg_one_lt_zero] with i hi
  rw [ofReal_log]; rw [ofReal_add]; rw [ofReal_one]
  linarith

Depends on / 依赖: Complex.summable_log_one_add_of_summable, congr_cofinite, eventually_const_le, filter_upwards, hf.tendsto_cofinite_zero.eventually_const_le, neg_one_lt_zero, ofReal_add, ofReal_log, ofReal_one, summable_log_one_add_of_summable, summable_ofReal, summable_ofReal.mpr, tendsto_cofinite_zero
-/
lemma summable_log_one_add_of_summable (hf : Summable f) :
    Summable (fun i => log (1 + f i)) := by
  rw [← summable_ofReal]
  apply (Complex.summable_log_one_add_of_summable (summable_ofReal.mpr hf)).congr_cofinite
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_le neg_one_lt_zero] with i hi
  rw [ofReal_log]; rw [ofReal_add]; rw [ofReal_one]
  linarith

/--
lemma `multipliable_one_add_of_summable` / 引理 `multipliable_one_add_of_summable`

English:
lemma multipliable_one_add_of_summable
  given: (hf : Summable f)
  proof: by
  refine multipliable_of_summable_log' ?_ (summable_log_one_add_of_summable hf)
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_lt neg_one_lt_zero] with i hi
  linarith

中文:
引理 multipliable_one_add_of_summable
  条件: (hf : Summable f)
  证明: by
  refine multipliable_of_summable_log' ?_ (summable_log_one_add_of_summable hf)
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_lt neg_one_lt_zero] with i hi
  linarith
-/
protected lemma multipliable_one_add_of_summable (hf : Summable f) :
    Multipliable (fun i => 1 + f i) := by
  refine multipliable_of_summable_log' ?_ (summable_log_one_add_of_summable hf)
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_lt neg_one_lt_zero] with i hi
  linarith

end Real

/--
lemma `summable_finsetProd_of_summable_nonneg` / 引理 `summable_finsetProd_of_summable_nonneg`

English:
lemma summable_finsetProd_of_summable_nonneg
  statement: {f : ι -> Real} (hf : forall i, 0 <= f i)
  proof: by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' i, f i))
    (fun s => Finset.prod_nonneg fun i _ => hf i) fun T => ?_
  calc ∑ s in T, ∏ i in s, f i
      <= ∑ s in (T.biUnion id).powerset, ∏ i in s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.mpr
          (Finset.subset_biUnion_of_mem id hs)) (fun s _ _ => Finset.prod_nonneg fun i _ => hf i)
    _ = ∏ i in T.biUnion id, (1 + f i) := (Finset.prod_one_add _).symm
    _ <= Real.exp (∑ i in T.biUnion id, f i) := Real.prod_one_add_le_exp_sum _ hf
    _ <= Real.exp (∑' i, f i) :=
        Real.exp_le_exp.mpr (hfs.sum_le_tsum _ fun _ _ => hf _)

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_nonneg := summable_finsetProd_of_summable_nonneg

中文:
引理 summable_finsetProd_of_summable_nonneg
  结论: {f : ι -> 实数} (hf : 对任意 i, 0 <= f i)
  证明: by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' i, f i))
    (fun s => Finset.prod_nonneg fun i _ => hf i) fun T => ?_
  calc ∑ s in T, ∏ i in s, f i
      <= ∑ s in (T.biUnion id).powerset, ∏ i in s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.mpr
          (Finset.subset_biUnion_of_mem id hs)) (fun s _ _ => Finset.prod_nonneg fun i _ => hf i)
    _ = ∏ i in T.biUnion id, (1 + f i) := (Finset.prod_one_add _).symm
    _ <= Real.exp (∑ i in T.biUnion id, f i) := Real.prod_one_add_le_exp_sum _ hf
    _ <= Real.exp (∑' i, f i) :=
        Real.exp_le_exp.mpr (hfs.sum_le_tsum _ fun _ _ => hf _)

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_nonneg := summable_finsetProd_of_summable_nonneg

Depends on / 依赖: Finset, Finset.mem_powerset.mpr, Finset.prod_nonneg, Finset.prod_one_add, Finset.subset_biUnion_of_mem, Finset.sum_le_sum_of_subset_of_nonneg, Real.exp, Real.prod_one_add_le, T.biUnion, biUnion, classical, mem_powerset, powerset, prod_nonneg, prod_one_add, prod_one_add_le, subset_biUnion_of_mem, sum_le_sum_of_subset_of_nonneg, summable_of_sum_le
-/
lemma summable_finsetProd_of_summable_nonneg {f : ι -> Real} (hf : forall i, 0 <= f i)
    (hfs : Summable f) : Summable (fun s : Finset ι => ∏ i in s, f i) := by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' i, f i))
    (fun s => Finset.prod_nonneg fun i _ => hf i) fun T => ?_
  calc ∑ s in T, ∏ i in s, f i
      <= ∑ s in (T.biUnion id).powerset, ∏ i in s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.mpr
          (Finset.subset_biUnion_of_mem id hs)) (fun s _ _ => Finset.prod_nonneg fun i _ => hf i)
    _ = ∏ i in T.biUnion id, (1 + f i) := (Finset.prod_one_add _).symm
    _ <= Real.exp (∑ i in T.biUnion id, f i) := Real.prod_one_add_le_exp_sum _ hf
    _ <= Real.exp (∑' i, f i) :=
        Real.exp_le_exp.mpr (hfs.sum_le_tsum _ fun _ _ => hf _)

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_nonneg := summable_finsetProd_of_summable_nonneg

section NormedRing

/--
lemma `Multipliable.eventually_bounded_finsetProd` / 引理 `Multipliable.eventually_bounded_finsetProd`

English:
lemma Multipliable.eventually_bounded_finsetProd
  given: {v : ι -> Real} (hv : Multipliable v)
  proof: by
  obtain ⟨r₁, hr₁⟩ := exists_gt (max 0 <| ∏' i, v i)
  rw [max_lt_iff] at hr₁
  have := hv.hasProd.eventually_le_const hr₁.2
  rw [unconditional]; rw [eventually_atTop] at this
  exact ⟨r₁, hr₁.1, this⟩

@[deprecated (since := "2026-04-08")]
alias Multipliable.eventually_bounded_finset_prod := Multipliable.eventually_bounded_finsetProd

中文:
引理 Multipliable.eventually_bounded_finsetProd
  条件: {v : ι -> 实数} (hv : Multipliable v)
  证明: by
  obtain ⟨r₁, hr₁⟩ := exists_gt (max 0 <| ∏' i, v i)
  rw [max_lt_iff] at hr₁
  have := hv.hasProd.eventually_le_const hr₁.2
  rw [unconditional]; rw [eventually_atTop] at this
  exact ⟨r₁, hr₁.1, this⟩

@[deprecated (since := "2026-04-08")]
alias Multipliable.eventually_bounded_finset_prod := Multipliable.eventually_bounded_finsetProd

Depends on / 依赖: eventually_atTop, eventually_le_const, exists_gt, hasProd, hv.hasProd.eventually_le_const, max_lt_iff, unconditional
-/
lemma Multipliable.eventually_bounded_finsetProd {v : ι -> Real} (hv : Multipliable v) :
    exists r₁ > 0, exists s₁, forall t, s₁ subseteq t -> ∏ i in t, v i <= r₁ := by
  obtain ⟨r₁, hr₁⟩ := exists_gt (max 0 <| ∏' i, v i)
  rw [max_lt_iff] at hr₁
  have := hv.hasProd.eventually_le_const hr₁.2
  rw [unconditional]; rw [eventually_atTop] at this
  exact ⟨r₁, hr₁.1, this⟩

@[deprecated (since := "2026-04-08")]
alias Multipliable.eventually_bounded_finset_prod := Multipliable.eventually_bounded_finsetProd

variable {R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι -> R}

/--
lemma `multipliable_norm_one_add_of_summable_norm` / 引理 `multipliable_norm_one_add_of_summable_norm`

English:
lemma multipliable_norm_one_add_of_summable_norm
  given: (hf : Summable fun i => ‖f i‖)
  proof: by
  conv => enter [1, i]; rw [← sub_add_cancel ‖1 + f i‖ 1, add_comm]
refine Real.multipliable_one_add_of_summable hf.of_norm_bounded (fun i => ?_)
  simpa using abs_norm_sub_norm_le (1 + f i) 1

中文:
引理 multipliable_norm_one_add_of_summable_norm
  条件: (hf : Summable fun i => ‖f i‖)
  证明: by
  conv => enter [1, i]; rw [← sub_add_cancel ‖1 + f i‖ 1, add_comm]
refine Real.multipliable_one_add_of_summable hf.of_norm_bounded (fun i => ?_)
  simpa using abs_norm_sub_norm_le (1 + f i) 1

Depends on / 依赖: Real.multipliable_one_add_of_summable, abs_norm_sub_norm_le, add_comm, hf.of_norm_bounded, multipliable_one_add_of_summable, of_norm_bounded, sub_add_cancel
-/
lemma multipliable_norm_one_add_of_summable_norm (hf : Summable fun i => ‖f i‖) :
    Multipliable fun i => ‖1 + f i‖ := by
  conv => enter [1, i]; rw [← sub_add_cancel ‖1 + f i‖ 1, add_comm]
refine Real.multipliable_one_add_of_summable hf.of_norm_bounded (fun i => ?_)
  simpa using abs_norm_sub_norm_le (1 + f i) 1

/--
lemma `Finset.norm_prod_one_add_sub_one_le` / 引理 `Finset.norm_prod_one_add_sub_one_le`

English:
lemma Finset.norm_prod_one_add_sub_one_le
  given: (t : Finset ι) (f : ι -> R)
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx IH =>
    rw [Finset.prod_insert hx]; rw [Finset.sum_insert hx]; rw [Real.exp_add]; rw [show (1 + f x) * ∏ i in t]; rw [(1 + f i) - 1 =
        (∏ i in t]; rw [(1 + f i) - 1) + f x * ∏ x in t]; rw [(1 + f x) by ring]
    refine (norm_add_le_of_le IH (norm_mul_le _ _)).trans ?_
    generalize h : Real.exp (∑ i in t, ‖f i‖) = A at ⊢ IH
    rw [sub_add_eq_add_sub]; rw [sub_le_sub_iff_right]
    transitivity A + ‖f x‖ * A
    · grw [norm_le_norm_sub_add (∏ x in t, (1 + f x)) 1, IH, norm_one, sub_add_cancel]
    rw [← one_add_mul]; rw [add_comm]
    exact mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (h ▸ Real.exp_nonneg _)

中文:
引理 有限集.norm_prod_one_add_sub_one_le
  条件: (t : 有限集 ι) (f : ι -> R)
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx IH =>
    rw [Finset.prod_insert hx]; rw [Finset.sum_insert hx]; rw [Real.exp_add]; rw [show (1 + f x) * ∏ i in t]; rw [(1 + f i) - 1 =
        (∏ i in t]; rw [(1 + f i) - 1) + f x * ∏ x in t]; rw [(1 + f x) by ring]
    refine (norm_add_le_of_le IH (norm_mul_le _ _)).trans ?_
    generalize h : Real.exp (∑ i in t, ‖f i‖) = A at ⊢ IH
    rw [sub_add_eq_add_sub]; rw [sub_le_sub_iff_right]
    transitivity A + ‖f x‖ * A
    · grw [norm_le_norm_sub_add (∏ x in t, (1 + f x)) 1, IH, norm_one, sub_add_cancel]
    rw [← one_add_mul]; rw [add_comm]
    exact mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (h ▸ Real.exp_nonneg _)

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_insert, Finset.sum_insert, Real.exp, Real.exp_add, classical, exp_add, generalize, induction_on, insert, norm_add_le_of_le, norm_le_nor, norm_mul_le, prod_insert, sub_add_eq_add_sub, sub_le_sub_iff_right, sum_insert, transitivity
-/
lemma Finset.norm_prod_one_add_sub_one_le (t : Finset ι) (f : ι -> R) :
    ‖∏ i in t, (1 + f i) - 1‖ <= Real.exp (∑ i in t, ‖f i‖) - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx IH =>
    rw [Finset.prod_insert hx]; rw [Finset.sum_insert hx]; rw [Real.exp_add]; rw [show (1 + f x) * ∏ i in t]; rw [(1 + f i) - 1 =
        (∏ i in t]; rw [(1 + f i) - 1) + f x * ∏ x in t]; rw [(1 + f x) by ring]
    refine (norm_add_le_of_le IH (norm_mul_le _ _)).trans ?_
    generalize h : Real.exp (∑ i in t, ‖f i‖) = A at ⊢ IH
    rw [sub_add_eq_add_sub]; rw [sub_le_sub_iff_right]
    transitivity A + ‖f x‖ * A
    · grw [norm_le_norm_sub_add (∏ x in t, (1 + f x)) 1, IH, norm_one, sub_add_cancel]
    rw [← one_add_mul]; rw [add_comm]
    exact mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (h ▸ Real.exp_nonneg _)

/--
lemma `prod_vanishing_of_summable_norm` / 引理 `prod_vanishing_of_summable_norm`

English:
lemma prod_vanishing_of_summable_norm
  given: (hf : Summable fun i => ‖f i‖) {ε : Real} (hε : 0 < ε)
  proof: by
  suffices exists s, forall t, Disjoint t s -> Real.exp (∑ i in t, ‖f i‖) - 1 < ε from
    this.imp fun s hs t ht => (t.norm_prod_one_add_sub_one_le _).trans_lt (hs t ht)
  suffices {x | Real.exp x - 1 < ε} in 𝓝 0 from hf.vanishing this
  let f (x) := Real.exp x - 1
  have : Set.Iio ε in nhds (f 0) := by simpa [f] using Iio_mem_nhds hε
  exact ContinuousAt.preimage_mem_nhds (by fun_prop) this

中文:
引理 prod_vanishing_of_summable_norm
  条件: (hf : Summable fun i => ‖f i‖) {ε : 实数} (hε : 0 < ε)
  证明: by
  suffices exists s, forall t, Disjoint t s -> Real.exp (∑ i in t, ‖f i‖) - 1 < ε from
    this.imp fun s hs t ht => (t.norm_prod_one_add_sub_one_le _).trans_lt (hs t ht)
  suffices {x | Real.exp x - 1 < ε} in 𝓝 0 from hf.vanishing this
  let f (x) := Real.exp x - 1
  have : Set.Iio ε in nhds (f 0) := by simpa [f] using Iio_mem_nhds hε
  exact ContinuousAt.preimage_mem_nhds (by fun_prop) this

Depends on / 依赖: ContinuousAt, ContinuousAt.preimage_mem_nhds, Disjoint, Iio_mem_nhds, Real.exp, Set.Iio, fun_prop, hf.vanishing, norm_prod_one_add_sub_one_le, preimage_mem_nhds, t.norm_prod_one_add_sub_one_le, this.imp, trans_lt, vanishing
-/
lemma prod_vanishing_of_summable_norm (hf : Summable fun i => ‖f i‖) {ε : Real} (hε : 0 < ε) :
    exists s₂, forall t, Disjoint t s₂ -> ‖∏ i in t, (1 + f i) - 1‖ < ε := by
  suffices exists s, forall t, Disjoint t s -> Real.exp (∑ i in t, ‖f i‖) - 1 < ε from
    this.imp fun s hs t ht => (t.norm_prod_one_add_sub_one_le _).trans_lt (hs t ht)
  suffices {x | Real.exp x - 1 < ε} in 𝓝 0 from hf.vanishing this
  let f (x) := Real.exp x - 1
  have : Set.Iio ε in nhds (f 0) := by simpa [f] using Iio_mem_nhds hε
  exact ContinuousAt.preimage_mem_nhds (by fun_prop) this

open Finset in
/--
lemma `multipliable_one_add_of_summable` / 引理 `multipliable_one_add_of_summable`

English:
lemma multipliable_one_add_of_summable
  statement: [CompleteSpace R]
  proof: by
  classical
refine CompleteSpace.complete Metric.cauchy_iff.mpr ⟨by infer_instance, fun ε hε => ?_⟩
  obtain ⟨r₁, hr₁, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hf).eventually_bounded_finsetProd
  obtain ⟨s₂, hs₂⟩ := prod_vanishing_of_summable_norm hf (show 0 < ε / (2 * r₁) by positivity)
  simp only [unconditional, Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
  let s := s₁ union s₂
  -- The idea here is that if `s` is a large enough finset, then the product over `s` is bounded
  -- by some `r`, and the product over finsets disjoint from `s` is within `ε / (2 * r)` of 1.
  -- From this it follows that the products over any two finsets containing `s` are within `ε` of
  -- each other.
  -- Here `s₁ ⊆ s` guarantees that the product over `s` is bounded, and `s₂ ⊆ s` guarantees that
  -- the product over terms not in `s` is small.
  refine ⟨Metric.ball (∏ i in s, (1 + f i)) (ε / 2), ⟨s, fun b hb => ?_⟩, ?_⟩
  · rw [← union_sdiff_of_subset hb, prod_union sdiff_disjoint.symm,
      Metric.mem_ball, dist_eq_norm_sub, ← mul_sub_one,
      show ε / 2 = r₁ * (ε / (2 * r₁)) by field]
    apply (norm_mul_le _ _).trans_lt
    refine lt_of_le_of_lt (b := r₁ * ‖∏ x in b \ s, (1 + f x) - 1‖) ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (Finset.norm_prod_le _ _).trans (hs₁ _ subset_union_left)
    · refine mul_lt_mul_of_pos_left (hs₂ _ ?_) hr₁
      simp [s, sdiff_union_distrib, disjoint_iff_inter_eq_empty]
  · intro x hx y hy
    exact (dist_triangle_right _ _ (∏ i in s, (1 + f i))).trans_lt (add_halves ε ▸ add_lt_add hx hy)

中文:
引理 multipliable_one_add_of_summable
  结论: [完备空间 R]
  证明: by
  classical
refine CompleteSpace.complete Metric.cauchy_iff.mpr ⟨by infer_instance, fun ε hε => ?_⟩
  obtain ⟨r₁, hr₁, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hf).eventually_bounded_finsetProd
  obtain ⟨s₂, hs₂⟩ := prod_vanishing_of_summable_norm hf (show 0 < ε / (2 * r₁) by positivity)
  simp only [unconditional, Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
  let s := s₁ union s₂
  -- The idea here is that if `s` is a large enough finset, then the product over `s` is bounded
  -- by some `r`, and the product over finsets disjoint from `s` is within `ε / (2 * r)` of 1.
  -- From this it follows that the products over any two finsets containing `s` are within `ε` of
  -- each other.
  -- Here `s₁ ⊆ s` guarantees that the product over `s` is bounded, and `s₂ ⊆ s` guarantees that
  -- the product over terms not in `s` is small.
  refine ⟨Metric.ball (∏ i in s, (1 + f i)) (ε / 2), ⟨s, fun b hb => ?_⟩, ?_⟩
  · rw [← union_sdiff_of_subset hb, prod_union sdiff_disjoint.symm,
      Metric.mem_ball, dist_eq_norm_sub, ← mul_sub_one,
      show ε / 2 = r₁ * (ε / (2 * r₁)) by field]
    apply (norm_mul_le _ _).trans_lt
    refine lt_of_le_of_lt (b := r₁ * ‖∏ x in b \ s, (1 + f x) - 1‖) ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (Finset.norm_prod_le _ _).trans (hs₁ _ subset_union_left)
    · refine mul_lt_mul_of_pos_left (hs₂ _ ?_) hr₁
      simp [s, sdiff_union_distrib, disjoint_iff_inter_eq_empty]
  · intro x hx y hy
    exact (dist_triangle_right _ _ (∏ i in s, (1 + f i))).trans_lt (add_halves ε ▸ add_lt_add hx hy)

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, Filter, Filter.mem_map, Metric, Metric.cauchy_iff.mpr, Set.mem_preimage, cauchy_iff, classical, complete, eventually_bounded_finsetProd, infer_instance, mem_atTop_sets, mem_map, mem_preimage, multipliable_norm_one_add_of_summable_norm, prod_vanishing_of_summable_norm, unconditional
-/
lemma multipliable_one_add_of_summable [CompleteSpace R]
    (hf : Summable fun i => ‖f i‖) : Multipliable fun i => (1 + f i) := by
  classical
refine CompleteSpace.complete Metric.cauchy_iff.mpr ⟨by infer_instance, fun ε hε => ?_⟩
  obtain ⟨r₁, hr₁, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hf).eventually_bounded_finsetProd
  obtain ⟨s₂, hs₂⟩ := prod_vanishing_of_summable_norm hf (show 0 < ε / (2 * r₁) by positivity)
  simp only [unconditional, Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
  let s := s₁ union s₂
  -- The idea here is that if `s` is a large enough finset, then the product over `s` is bounded
  -- by some `r`, and the product over finsets disjoint from `s` is within `ε / (2 * r)` of 1.
  -- From this it follows that the products over any two finsets containing `s` are within `ε` of
  -- each other.
  -- Here `s₁ ⊆ s` guarantees that the product over `s` is bounded, and `s₂ ⊆ s` guarantees that
  -- the product over terms not in `s` is small.
  refine ⟨Metric.ball (∏ i in s, (1 + f i)) (ε / 2), ⟨s, fun b hb => ?_⟩, ?_⟩
  · rw [← union_sdiff_of_subset hb, prod_union sdiff_disjoint.symm,
      Metric.mem_ball, dist_eq_norm_sub, ← mul_sub_one,
      show ε / 2 = r₁ * (ε / (2 * r₁)) by field]
    apply (norm_mul_le _ _).trans_lt
    refine lt_of_le_of_lt (b := r₁ * ‖∏ x in b \ s, (1 + f x) - 1‖) ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (Finset.norm_prod_le _ _).trans (hs₁ _ subset_union_left)
    · refine mul_lt_mul_of_pos_left (hs₂ _ ?_) hr₁
      simp [s, sdiff_union_distrib, disjoint_iff_inter_eq_empty]
  · intro x hx y hy
    exact (dist_triangle_right _ _ (∏ i in s, (1 + f i))).trans_lt (add_halves ε ▸ add_lt_add hx hy)

/--
lemma `summable_finsetProd_of_summable_norm` / 引理 `summable_finsetProd_of_summable_norm`

English:
lemma summable_finsetProd_of_summable_norm
  given: [CompleteSpace R] (hf : Summable (fun i => ‖f i‖))
  proof: (summable_finsetProd_of_summable_nonneg (fun _ => norm_nonneg _) hf).of_norm_bounded
    fun _ => Finset.norm_prod_le _ _

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_norm := summable_finsetProd_of_summable_norm

中文:
引理 summable_finsetProd_of_summable_norm
  条件: [完备空间 R] (hf : Summable (fun i => ‖f i‖))
  证明: (summable_finsetProd_of_summable_nonneg (fun _ => norm_nonneg _) hf).of_norm_bounded
    fun _ => Finset.norm_prod_le _ _

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_norm := summable_finsetProd_of_summable_norm

Depends on / 依赖: Finset, Finset.norm_prod_le, getRightAdjoint, norm_nonneg, norm_prod_le, of_norm_bounded, summable_finsetProd_of_summable_nonneg
-/
lemma summable_finsetProd_of_summable_norm [CompleteSpace R] (hf : Summable (fun i => ‖f i‖)) :
    Summable (fun s => ∏ i in s, f i) :=
  (summable_finsetProd_of_summable_nonneg (fun _ => norm_nonneg _) hf).of_norm_bounded
    fun _ => Finset.norm_prod_le _ _

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_norm := summable_finsetProd_of_summable_norm

/--
lemma `Summable.summable_log_norm_one_add` / 引理 `Summable.summable_log_norm_one_add`

English:
lemma Summable.summable_log_norm_one_add
  given: (hu : Summable fun n => ‖f n‖)
  proof: by
  suffices Summable (‖1 + f ·‖ - 1) from
    (Real.summable_log_one_add_of_summable this).congr (by simp)
  refine .of_norm (hu.of_nonneg_of_le (fun i => by positivity) fun i => ?_)
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · simpa using norm_add_le (1 + f i) (-f i)
  · simpa [add_comm] using norm_add_le (f i) 1

中文:
引理 Summable.summable_log_norm_one_add
  条件: (hu : Summable fun n => ‖f n‖)
  证明: by
  suffices Summable (‖1 + f ·‖ - 1) from
    (Real.summable_log_one_add_of_summable this).congr (by simp)
  refine .of_norm (hu.of_nonneg_of_le (fun i => by positivity) fun i => ?_)
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · simpa using norm_add_le (1 + f i) (-f i)
  · simpa [add_comm] using norm_add_le (f i) 1

Depends on / 依赖: Real.norm_eq_abs, Real.summable_log_one_add_of_summable, Summable, abs_le, add_comm, hu.of_nonneg_of_le, norm_add_le, norm_eq_abs, of_nonneg_of_le, of_norm, summable_log_one_add_of_summable
-/
lemma Summable.summable_log_norm_one_add (hu : Summable fun n => ‖f n‖) :
    Summable fun i => Real.log ‖1 + f i‖ := by
  suffices Summable (‖1 + f ·‖ - 1) from
    (Real.summable_log_one_add_of_summable this).congr (by simp)
  refine .of_norm (hu.of_nonneg_of_le (fun i => by positivity) fun i => ?_)
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · simpa using norm_add_le (1 + f i) (-f i)
  · simpa [add_comm] using norm_add_le (f i) 1

/--
lemma `tprod_one_add_ne_zero_of_summable` / 引理 `tprod_one_add_ne_zero_of_summable`

English:
lemma tprod_one_add_ne_zero_of_summable
  statement: [CompleteSpace R] [NormMulClass R]
  proof: by
  rw [← norm_ne_zero_iff]; rw [Multipliable.norm_tprod]
  · rw [← Real.rexp_tsum_eq_tprod (fun i => norm_pos_iff.mpr <| hf i) hu.summable_log_norm_one_add]
    apply Real.exp_ne_zero
  · exact multipliable_one_add_of_summable hu

中文:
引理 tprod_one_add_ne_zero_of_summable
  结论: [完备空间 R] [NormMul类 R]
  证明: by
  rw [← norm_ne_zero_iff]; rw [Multipliable.norm_tprod]
  · rw [← Real.rexp_tsum_eq_tprod (fun i => norm_pos_iff.mpr <| hf i) hu.summable_log_norm_one_add]
    apply Real.exp_ne_zero
  · exact multipliable_one_add_of_summable hu

Depends on / 依赖: Multipliable, Multipliable.norm_tprod, Real.exp_ne_zero, Real.rexp_tsum_eq_tprod, exp_ne_zero, hu.summable_log_norm_one_add, multipliable_one_add_of_summable, norm_ne_zero_iff, norm_pos_iff, norm_pos_iff.mpr, norm_tprod, rexp_tsum_eq_tprod, summable_log_norm_one_add
-/
lemma tprod_one_add_ne_zero_of_summable [CompleteSpace R] [NormMulClass R]
    (hf : forall i, 1 + f i != 0)
    (hu : Summable (‖f ·‖)) : ∏' i : ι, (1 + f i) != 0 := by
  rw [← norm_ne_zero_iff]; rw [Multipliable.norm_tprod]
  · rw [← Real.rexp_tsum_eq_tprod (fun i => norm_pos_iff.mpr <| hf i) hu.summable_log_norm_one_add]
    apply Real.exp_ne_zero
  · exact multipliable_one_add_of_summable hu

end NormedRing
