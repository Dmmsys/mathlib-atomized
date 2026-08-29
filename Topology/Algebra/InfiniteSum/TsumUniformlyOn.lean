/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of sum of functions

We prove some `HasSumUniformlyOn` versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions we also prove an `iteratedDerivWithin`
version.

-/

public section

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

section UniformlyOn

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α -> Real}

/--
theorem `HasSumUniformlyOn.of_norm_le_summable` / 定理 `HasSumUniformlyOn.of_norm_le_summable`

English:
theorem HasSumUniformlyOn.of_norm_le_summable
  statement: {f : α -> β -> F} (hu : Summable u) {s : Set β}
  proof: by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

中文:
定理 HasSumUniformlyOn.of_norm_le_summable
  结论: {f : α -> β -> F} (hu : Summable u) {s : 集合 β}
  证明: by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

Depends on / 依赖: hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum
-/
theorem HasSumUniformlyOn.of_norm_le_summable {f : α -> β -> F} (hu : Summable u) {s : Set β}
    (hfu : forall n x, x in s -> ‖f n x‖ <= u n) : HasSumUniformlyOn f (fun x => ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

/--
theorem `HasSumUniformlyOn.of_norm_le_summable_eventually` / 定理 `HasSumUniformlyOn.of_norm_le_summable_eventually`

English:
theorem HasSumUniformlyOn.of_norm_le_summable_eventually
  statement: {ι : Type*} {f : ι -> β -> F} {u : ι -> Real}
  proof: by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

中文:
定理 HasSumUniformlyOn.of_norm_le_summable_eventually
  结论: {ι : 类型} {f : ι -> β -> F} {u : ι -> 实数}
  证明: by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

Depends on / 依赖: hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum_of_cofinite_eventually
-/
theorem HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real}
    (hu : Summable u) {s : Set β} (hfu : forallᶠ n in cofinite, forall x in s, ‖f n x‖ <= u n) :
    HasSumUniformlyOn f (fun x => ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

/--
lemma `SummableLocallyUniformlyOn.of_locally_bounded_eventually` / 引理 `SummableLocallyUniformlyOn.of_locally_bounded_eventually`

English:
lemma SummableLocallyUniformlyOn.of_locally_bounded_eventually
  statement: [TopologicalSpace β]
  proof: by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x => ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]; rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

中文:
引理 SummableLocallyUniformlyOn.of_locally_bounded_eventually
  结论: [拓扑空间 β]
  证明: by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x => ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]; rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

Depends on / 依赖: HasSumLocallyUniformlyOn, HasSumLocallyUniformlyOn.summableLocallyUniformlyOn, hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, summableLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact, tendstoUniformlyOn_tsum_of_cofinite_eventually
-/
lemma SummableLocallyUniformlyOn.of_locally_bounded_eventually [TopologicalSpace β]
    [LocallyCompactSpace β] {f : α -> β -> F} {s : Set β} (hs : IsOpen s)
    (hu : forall K subseteq s, IsCompact K -> exists u : α -> Real, Summable u ∧
    forallᶠ n in cofinite, forall k in K, ‖f n k‖ <= u n) : SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x => ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]; rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

/--
lemma `SummableLocallyUniformlyOn_of_locally_bounded` / 引理 `SummableLocallyUniformlyOn_of_locally_bounded`

English:
lemma SummableLocallyUniformlyOn_of_locally_bounded
  statement: [TopologicalSpace β] [LocallyCompactSpace β]
  proof: by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

中文:
引理 SummableLocallyUniformlyOn_of_locally_bounded
  结论: [拓扑空间 β] [局部紧空间 β]
  证明: by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

Depends on / 依赖: SummableLocallyUniformlyOn, SummableLocallyUniformlyOn.of_locally_bounded_eventually, filter_upwards, of_locally_bounded_eventually
-/
lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α -> β -> F} {s : Set β} (hs : IsOpen s)
    (hu : forall K subseteq s, IsCompact K -> exists u : α -> Real, Summable u ∧ forall n, forall k in K, ‖f n k‖ <= u n) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

end UniformlyOn

variable {ι 𝕜 F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set 𝕜}

/--
theorem `derivWithin_tsum` / 定理 `derivWithin_tsum`

English:
theorem derivWithin_tsum
  statement: {f : ι -> 𝕜 -> F} (hs : IsOpen s) {x : 𝕜} (hx : x in s)
  proof: by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy => (hf y hy).hasSum) hx
    (f' := fun n : Finset ι => fun a => ∑ i in n, derivWithin (fun z => f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb => (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq => ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

中文:
定理 derivWithin_tsum
  结论: {f : ι -> 𝕜 -> F} (hs : 是开集 s) {x : 𝕜} (hx : x in s)
  证明: by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy => (hf y hy).hasSum) hx
    (f' := fun n : Finset ι => fun a => ∑ i in n, derivWithin (fun z => f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb => (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq => ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

Depends on / 依赖: Finset, HasDerivAt, HasDerivAt.fun_sum, HasDerivAt.hasDerivWithinAt, HasDerivWithinAt, HasDerivWithinAt.derivWithin, congr_right, derivWithin, differ, filter_upwards, fun_sum, hasDerivAt_of_tendstoLocallyUniformlyOn, hasDerivWithinAt, hasSum, hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp, hg.tsum_eqOn, hs.uniqueDiffWithinAt, tsum_eqOn, uniqueDiffWithinAt
-/
theorem derivWithin_tsum {f : ι -> 𝕜 -> F} (hs : IsOpen s) {x : 𝕜} (hx : x in s)
    (hf : forall y in s, Summable fun n => f n y)
    (h : SummableLocallyUniformlyOn (fun n => (derivWithin (fun z => f n z) s)) s)
    (hf2 : forall n r, r in s -> DifferentiableAt 𝕜 (f n) r) :
    derivWithin (fun z => ∑' n, f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy => (hf y hy).hasSum) hx
    (f' := fun n : Finset ι => fun a => ∑ i in n, derivWithin (fun z => f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb => (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq => ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

/--
theorem `iteratedDerivWithin_tsum` / 定理 `iteratedDerivWithin_tsum`

English:
theorem iteratedDerivWithin_tsum
  statement: {f : ι -> 𝕜 -> F} (m : Nat) (hs : IsOpen s)
  proof: by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _ _ (fun n r hr => hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht => hm ht (fun k hk1 hkm => h k hk1 (by lia))
          (fun k r e hr he => hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm => h k hk1 (by lia))
          (fun k r e hr he => hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ => by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht => by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))

中文:
定理 iteratedDerivWithin_tsum
  结论: {f : ι -> 𝕜 -> F} (m : 自然数) (hs : 是开集 s)
  证明: by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _ _ (fun n r hr => hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht => hm ht (fun k hk1 hkm => h k hk1 (by lia))
          (fun k r e hr he => hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm => h k hk1 (by lia))
          (fun k r e hr he => hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ => by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht => by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))

Depends on / 依赖: derivWithin_congr, derivWithin_tsum, generalizing, iteratedDerivWithin_succ, simp_rw, summable
-/
theorem iteratedDerivWithin_tsum {f : ι -> 𝕜 -> F} (m : Nat) (hs : IsOpen s)
    {x : 𝕜} (hx : x in s) (hsum : forall t in s, Summable (fun n : ι => f n t))
    (h : forall k, 1 <= k -> k <= m -> SummableLocallyUniformlyOn
      (fun n => (iteratedDerivWithin k (fun z => f n z) s)) s)
    (hf2 : forall n k r, k <= m -> r in s ->
      DifferentiableAt 𝕜 (iteratedDerivWithin k (fun z => f n z) s) r) :
    iteratedDerivWithin m (fun z => ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _ _ (fun n r hr => hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht => hm ht (fun k hk1 hkm => h k hk1 (by lia))
          (fun k r e hr he => hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm => h k hk1 (by lia))
          (fun k r e hr he => hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ => by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht => by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))
