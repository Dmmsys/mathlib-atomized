/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# Uniform convergence of products of functions

We gather some results about the uniform convergence of infinite products, in particular those of
the form `∏' i, (1 + f i x)` for a sequence `f` of complex-valued functions.
-/

public section

open Filter Function Complex Finset Topology

variable {α ι : Type*} {s : Set α} {K : Set α} {u : ι -> Real}

section Complex

variable {f : ι -> α -> Complex}

/--
lemma `TendstoUniformlyOn.comp_cexp` / 引理 `TendstoUniformlyOn.comp_cexp`

English:
lemma TendstoUniformlyOn.comp_cexp
  statement: {p : Filter ι} {g : α -> Complex}
  proof: by
obtain ⟨v, hv⟩ : exists v, forall x in K, (g x).re <= v := hg.imp by simp [mem_upperBounds]
  have : forallᶠ i in p, forall x in K, (f i x).re <= v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  exact

中文:
引理 TendstoUniformlyOn.comp_cexp
  结论: {p : 滤子 ι} {g : α -> 复形}
  证明: by
obtain ⟨v, hv⟩ : exists v, forall x in K, (g x).re <= v := hg.imp by simp [mem_upperBounds]
  have : forallᶠ i in p, forall x in K, (f i x).re <= v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  exact

Depends on / 依赖: UniformContinuousOn, UniformContinuousOn.cexp, comp_tendstoUniformlyOn_eventually, eventually_forall_le, hf.re.eventually_forall_le, hg.imp, lt_add_one, mem_upperBounds
-/
lemma TendstoUniformlyOn.comp_cexp {p : Filter ι} {g : α -> Complex}
    (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x => (g x).re) '' K) :
    TendstoUniformlyOn (cexp ∘ f ·) (cexp ∘ g) p K := by
obtain ⟨v, hv⟩ : exists v, forall x in K, (g x).re <= v := hg.imp by simp [mem_upperBounds]
  have : forallᶠ i in p, forall x in K, (f i x).re <= v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  exact fun x hx => (hv x hx).trans (lt_add_one v).le

/--
lemma `Summable.hasSumUniformlyOn_log_one_add` / 引理 `Summable.hasSumUniformlyOn_log_one_add`

English:
lemma Summable.hasSumUniformlyOn_log_one_add
  statement: (hu : Summable u)
  proof: by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn]
apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hi' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hi').trans

中文:
引理 Summable.hasSumUniformlyOn_log_one_add
  结论: (hu : Summable u)
  证明: by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn]
apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hi' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hi').trans

Depends on / 依赖: eventually_le_const, filter_upwards, hasSumUniformlyOn_iff_tendstoUniformlyOn, hu.mul_left, hu.tendsto_cofinite_zero.eventually_le_const, mul_left, norm_log_one_add_half_le_self, one_half_pos, tendstoUniformlyOn_tsum_of_cofinite_eventually, tendsto_cofinite_zero
-/
lemma Summable.hasSumUniformlyOn_log_one_add (hu : Summable u)
    (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) :
    HasSumUniformlyOn (fun i x => log (1 + f i x)) (fun x => ∑' i, log (1 + f i x)) K := by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn]
apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hi' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hi').trans (by simpa using hi x hx)

/--
lemma `Summable.tendstoUniformlyOn_tsum_nat_log_one_add` / 引理 `Summable.tendstoUniformlyOn_tsum_nat_log_one_add`

English:
lemma Summable.tendstoUniformlyOn_tsum_nat_log_one_add
  statement: {f : Nat -> α -> Complex} {u : Nat -> Real}
  proof: by
  rw [← Nat.cofinite_eq_atTop] at h
  exact (hu.hasSumUniformlyOn_log_one_add h).tendstoUniformlyOn_finsetRange

中文:
引理 Summable.tendstoUniformlyOn_tsum_nat_log_one_add
  结论: {f : 自然数 -> α -> 复形} {u : 自然数 -> 实数}
  证明: by
  rw [← Nat.cofinite_eq_atTop] at h
  exact (hu.hasSumUniformlyOn_log_one_add h).tendstoUniformlyOn_finsetRange

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, hasSumUniformlyOn_log_one_add, hu.hasSumUniformlyOn_log_one_add, tendstoUniformlyOn_finsetRange
-/
lemma Summable.tendstoUniformlyOn_tsum_nat_log_one_add {f : Nat -> α -> Complex} {u : Nat -> Real}
    (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n x‖ <= u n) :
    TendstoUniformlyOn (fun n x => ∑ m in Finset.range n, log (1 + f m x))
    (fun x => ∑' n, log (1 + f n x)) atTop K := by
  rw [← Nat.cofinite_eq_atTop] at h
  exact (hu.hasSumUniformlyOn_log_one_add h).tendstoUniformlyOn_finsetRange

/--
lemma `hasProdUniformlyOn_of_clog` / 引理 `hasProdUniformlyOn_of_clog`

English:
lemma hasProdUniformlyOn_of_clog
  statement: (hf : SummableUniformlyOn (fun i x => log (f i x)) s)
  proof: by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  obtain ⟨r, hr⟩ := hf.exists
  suffices H : TendstoUniformlyOn (fun s x => ∏ i in s, f i x) (cexp ∘ r) atTop s by
    refine H.congr_right (hr.tsum_eqOn.comp_left.symm.trans ?_)
    exact fun x hx => (cexp_tsum_eq_tprod (hfn x hx) (hf.summa

中文:
引理 hasProdUniformlyOn_of_clog
  结论: (hf : SummableUniformlyOn (fun i x => log (f i x)) s)
  证明: by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  obtain ⟨r, hr⟩ := hf.exists
  suffices H : TendstoUniformlyOn (fun s x => ∏ i in s, f i x) (cexp ∘ r) atTop s by
    refine H.congr_right (hr.tsum_eqOn.comp_left.symm.trans ?_)
    exact fun x hx => (cexp_tsum_eq_tprod (hfn x hx) (hf.summa

Depends on / 依赖: H.congr_right, TendstoUniformlyOn, cexp_tsum_eq_tprod, comp_cexp, comp_left, congr_right, contextual, exp_log, exp_sum, filter_upwards, hasProdUniformlyOn_iff_tendstoUniformlyOn, hf.exists, hf.summable, hr.tendstoUniformlyOn.comp_cexp, hr.tsum_eqOn, hr.tsum_eqOn.comp_left.symm.trans, summable, tendstoUniformlyOn, tsum_eqOn
-/
lemma hasProdUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x => log (f i x)) s)
    (hfn : forall x in s, forall i, f i x != 0)
    (hg : BddAbove <| (fun x => (∑' i, log (f i x)).re) '' s) :
    HasProdUniformlyOn f (fun x => ∏' i, f i x) s := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  obtain ⟨r, hr⟩ := hf.exists
  suffices H : TendstoUniformlyOn (fun s x => ∏ i in s, f i x) (cexp ∘ r) atTop s by
    refine H.congr_right (hr.tsum_eqOn.comp_left.symm.trans ?_)
    exact fun x hx => (cexp_tsum_eq_tprod (hfn x hx) (hf.summable hx))
  refine (hr.tendstoUniformlyOn.comp_cexp ?_).congr ?_
  · simpa +contextual [← hr.tsum_eqOn _] using hg
  · filter_upwards with s i hi using by simp [exp_sum, fun y => exp_log (hfn i hi y)]

/--
lemma `multipliableUniformlyOn_of_clog` / 引理 `multipliableUniformlyOn_of_clog`

English:
lemma multipliableUniformlyOn_of_clog
  statement: (hf : SummableUniformlyOn (fun i x => log (f i x)) s)
  proof: ⟨_, hasProdUniformlyOn_of_clog hf hfn hg⟩

中文:
引理 multipliableUniformlyOn_of_clog
  结论: (hf : SummableUniformlyOn (fun i x => log (f i x)) s)
  证明: ⟨_, hasProdUniformlyOn_of_clog hf hfn hg⟩

Depends on / 依赖: hasProdUniformlyOn_of_clog
-/
lemma multipliableUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x => log (f i x)) s)
    (hfn : forall x in s, forall i, f i x != 0)
    (hg : BddAbove <| (fun x => (∑' i, log (f i x)).re) '' s) :
    MultipliableUniformlyOn f s :=
  ⟨_, hasProdUniformlyOn_of_clog hf hfn hg⟩

end Complex

namespace Summable

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [TopologicalSpace α]
  {f : ι -> α -> R}

/--
lemma `hasProdUniformlyOn_one_add` / 引理 `hasProdUniformlyOn_one_add`

English:
lemma hasProdUniformlyOn_one_add
  statement: (hK : IsCompact K) (hu : Summable u)
  proof: by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  by_cases hKe : K = ∅
  · simp [TendstoUniformly, hKe]
  · have hCK : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hne : Nonempty K := by rwa [Set.nonempty_coe_sort, Set.n

中文:
引理 hasProdUniformlyOn_one_add
  结论: (hK : 是紧集 K) (hu : Summable u)
  证明: by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  by_cases hKe : K = ∅
  · simp [TendstoUniformly, hKe]
  · have hCK : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hne : Nonempty K := by rwa [Set.nonempty_coe_sort, Set.n

Depends on / 依赖: CompactSpace, ContinuousMap, ContinuousMap.norm_le_of_nonempty, Nonempty, Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, TendstoUniformly, cofinite, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, filter_upwar, hasProdUniformlyOn_iff_tendstoUniformlyOn, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, nonempty_coe_sort, nonempty_iff_ne_empty, norm_le_of_nonempty, tendstoUniformlyOn_iff_tendstoUniformly_comp_coe
-/
lemma hasProdUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, ContinuousOn (f i) K) :
    HasProdUniformlyOn (fun i x => 1 + f i x) (fun x => ∏' i, (1 + f i x)) K := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  by_cases hKe : K = ∅
  · simp [TendstoUniformly, hKe]
  · have hCK : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hne : Nonempty K := by rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty]
    let f' i : C(K, R) := ⟨_, continuousOn_iff_continuous_domRestrict.mp (hcts i)⟩
    have hf'_bd : forallᶠ i in cofinite, ‖f' i‖ <= u i := by
      simp only [ContinuousMap.norm_le_of_nonempty]
      filter_upwards [h] with i hi using fun x => hi x x.2
    have hM : Multipliable fun i => 1 + f' i :=
      multipliable_one_add_of_summable (hu.of_norm_bounded_eventually (by simpa using hf'_bd))
    convert! ContinuousMap.tendsto_iff_tendstoUniformly.mp hM.hasProd
    · simp [f']
    · exact funext fun k => ContinuousMap.tprod_apply hM k

/--
lemma `multipliableUniformlyOn_one_add` / 引理 `multipliableUniformlyOn_one_add`

English:
lemma multipliableUniformlyOn_one_add
  statement: (hK : IsCompact K) (hu : Summable u)
  proof: ⟨_, hasProdUniformlyOn_one_add hK hu h hcts⟩

中文:
引理 multipliableUniformlyOn_one_add
  结论: (hK : 是紧集 K) (hu : Summable u)
  证明: ⟨_, hasProdUniformlyOn_one_add hK hu h hcts⟩

Depends on / 依赖: hasProdUniformlyOn_one_add
-/
lemma multipliableUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, ContinuousOn (f i) K) :
    MultipliableUniformlyOn (fun i x => 1 + f i x) K :=
  ⟨_, hasProdUniformlyOn_one_add hK hu h hcts⟩

/--
lemma `hasProdUniformlyOn_nat_one_add` / 引理 `hasProdUniformlyOn_nat_one_add`

English:
lemma hasProdUniformlyOn_nat_one_add
  statement: {f : Nat -> α -> R} (hK : IsCompact K) {u : Nat -> Real}
  proof: hasProdUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

中文:
引理 hasProdUniformlyOn_nat_one_add
  结论: {f : 自然数 -> α -> R} (hK : 是紧集 K) {u : 自然数 -> 实数}
  证明: hasProdUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, hasProdUniformlyOn_one_add
-/
lemma hasProdUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsCompact K) {u : Nat -> Real}
    (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n x‖ <= u n)
    (hcts : forall n, ContinuousOn (f n) K) :
    HasProdUniformlyOn (fun n x => 1 + f n x) (fun x => ∏' i, (1 + f i x)) K :=
  hasProdUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

/--
lemma `multipliableUniformlyOn_nat_one_add` / 引理 `multipliableUniformlyOn_nat_one_add`

English:
lemma multipliableUniformlyOn_nat_one_add
  statement: {f : Nat -> α -> R} (hK : IsCompact K)
  proof: ⟨_, hasProdUniformlyOn_nat_one_add hK hu h hcts⟩

中文:
引理 multipliableUniformlyOn_nat_one_add
  结论: {f : 自然数 -> α -> R} (hK : 是紧集 K)
  证明: ⟨_, hasProdUniformlyOn_nat_one_add hK hu h hcts⟩

Depends on / 依赖: hasProdUniformlyOn_nat_one_add
-/
lemma multipliableUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsCompact K)
    {u : Nat -> Real} (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n x‖ <= u n)
    (hcts : forall n, ContinuousOn (f n) K) :
    MultipliableUniformlyOn (fun n x => 1 + f n x) K :=
  ⟨_, hasProdUniformlyOn_nat_one_add hK hu h hcts⟩

section LocallyCompactSpace

variable [LocallyCompactSpace α]

/--
lemma `hasProdLocallyUniformlyOn_one_add` / 引理 `hasProdLocallyUniformlyOn_one_add`

English:
lemma hasProdLocallyUniformlyOn_one_add
  statement: (hK : IsOpen K) (hu : Summable u)
  proof: by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC => hasProdUniformlyOn_one_add hC hu ?_ fun i => (hcts i).mono hS
  filter_upwards [h] with i hi a ha using hi a (hS ha)

中文:
引理 hasProdLocallyUniformlyOn_one_add
  结论: (hK : 是开集 K) (hu : Summable u)
  证明: by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC => hasProdUniformlyOn_one_add hC hu ?_ fun i => (hcts i).mono hS
  filter_upwards [h] with i hi a ha using hi a (hS ha)

Depends on / 依赖: filter_upwards, hasProdLocallyUniformlyOn_of_forall_compact, hasProdUniformlyOn_one_add
-/
lemma hasProdLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u)
    (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, ContinuousOn (f i) K) :
    HasProdLocallyUniformlyOn (fun i x => 1 + f i x) (fun x => ∏' i, (1 + f i x)) K := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC => hasProdUniformlyOn_one_add hC hu ?_ fun i => (hcts i).mono hS
  filter_upwards [h] with i hi a ha using hi a (hS ha)

/--
lemma `multipliableLocallyUniformlyOn_one_add` / 引理 `multipliableLocallyUniformlyOn_one_add`

English:
lemma multipliableLocallyUniformlyOn_one_add
  statement: (hK : IsOpen K) (hu : Summable u)
  proof: ⟨_, hasProdLocallyUniformlyOn_one_add hK hu h hcts⟩

中文:
引理 multipliableLocallyUniformlyOn_one_add
  结论: (hK : 是开集 K) (hu : Summable u)
  证明: ⟨_, hasProdLocallyUniformlyOn_one_add hK hu h hcts⟩

Depends on / 依赖: hasProdLocallyUniformlyOn_one_add
-/
lemma multipliableLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u)
    (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, ContinuousOn (f i) K) :
    MultipliableLocallyUniformlyOn (fun i x => 1 + f i x) K :=
  ⟨_, hasProdLocallyUniformlyOn_one_add hK hu h hcts⟩

/--
lemma `hasProdLocallyUniformlyOn_nat_one_add` / 引理 `hasProdLocallyUniformlyOn_nat_one_add`

English:
lemma hasProdLocallyUniformlyOn_nat_one_add
  statement: {f : Nat -> α -> R} (hK : IsOpen K) {u : Nat -> Real}
  proof: hasProdLocallyUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

中文:
引理 hasProdLocallyUniformlyOn_nat_one_add
  结论: {f : 自然数 -> α -> R} (hK : 是开集 K) {u : 自然数 -> 实数}
  证明: hasProdLocallyUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, hasProdLocallyUniformlyOn_one_add
-/
lemma hasProdLocallyUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsOpen K) {u : Nat -> Real}
    (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n x‖ <= u n)
    (hcts : forall n, ContinuousOn (f n) K) :
    HasProdLocallyUniformlyOn (fun n x => 1 + f n x) (fun x => ∏' i, (1 + f i x)) K :=
  hasProdLocallyUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

/--
lemma `multipliableLocallyUniformlyOn_nat_one_add` / 引理 `multipliableLocallyUniformlyOn_nat_one_add`

English:
lemma multipliableLocallyUniformlyOn_nat_one_add
  statement: {f : Nat -> α -> R} (hK : IsOpen K) {u : Nat -> Real}
  proof: ⟨_, hasProdLocallyUniformlyOn_nat_one_add hK hu h hcts⟩

中文:
引理 multipliableLocallyUniformlyOn_nat_one_add
  结论: {f : 自然数 -> α -> R} (hK : 是开集 K) {u : 自然数 -> 实数}
  证明: ⟨_, hasProdLocallyUniformlyOn_nat_one_add hK hu h hcts⟩

Depends on / 依赖: hasProdLocallyUniformlyOn_nat_one_add
-/
lemma multipliableLocallyUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsOpen K) {u : Nat -> Real}
    (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n x‖ <= u n)
    (hcts : forall n, ContinuousOn (f n) K) :
    MultipliableLocallyUniformlyOn (fun n x => 1 + f n x) K :=
  ⟨_, hasProdLocallyUniformlyOn_nat_one_add hK hu h hcts⟩

end LocallyCompactSpace

end Summable
