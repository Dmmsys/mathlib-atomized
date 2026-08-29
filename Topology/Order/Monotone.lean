/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Tactic.Order
public import Mathlib.Topology.Order.IsLUB

/-!
# Monotone functions on an order topology

This file contains lemmas about limits and continuity for monotone / antitone functions on
linearly-ordered sets (with the order topology). For example, we prove that a monotone function
has left and right limits at any point (`Monotone.tendsto_nhdsLT`, `Monotone.tendsto_nhdsGT`).

-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section LinearOrder

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [LinearOrder β]
  {s : Set α} {x : α} {f : α -> β}

/--
lemma `MonotoneOn.insert_of_continuousWithinAt` / 引理 `MonotoneOn.insert_of_continuousWithinAt`

English:
lemma MonotoneOn.insert_of_continuousWithinAt
  statement: [TopologicalSpace β] [OrderClosedTopology β]
  proof: by
  have : (𝓝[s] x).NeBot := hx
  apply monotoneOn_insert_iff.2 ⟨fun b hb hbx => ?_, fun b hb hxb => ?_, hf⟩
  · rcases hbx.eq_or_lt with rfl | hbx
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply ge_of_tendsto h'x
    have : s inter Ioi b in 𝓝[s] x := inter_mem_nhdsWithin _ (Ioi_mem_nhds hbx)
    filter_upwards [this] with y hy using hf hb hy.1 (le_of_lt hy.2)
  · rcases hxb.eq_or_lt with rfl | hxb
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply le_of_tendsto h'x
    have : s inter Iio b in 𝓝[s] x := inter_mem_nhdsWithin _ (Iio_mem_nhds hxb)
    filter_upwards [this] with y hy
    exact hf hy.1 hb (le_of_lt hy.2)

中文:
引理 MonotoneOn.insert_of_continuousWithinAt
  结论: [拓扑空间 β] [OrderClosed拓扑 β]
  证明: by
  have : (𝓝[s] x).NeBot := hx
  apply monotoneOn_insert_iff.2 ⟨fun b hb hbx => ?_, fun b hb hxb => ?_, hf⟩
  · rcases hbx.eq_or_lt with rfl | hbx
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply ge_of_tendsto h'x
    have : s inter Ioi b in 𝓝[s] x := inter_mem_nhdsWithin _ (Ioi_mem_nhds hbx)
    filter_upwards [this] with y hy using hf hb hy.1 (le_of_lt hy.2)
  · rcases hxb.eq_or_lt with rfl | hxb
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply le_of_tendsto h'x
    have : s inter Iio b in 𝓝[s] x := inter_mem_nhdsWithin _ (Iio_mem_nhds hxb)
    filter_upwards [this] with y hy
    exact hf hy.1 hb (le_of_lt hy.2)

Depends on / 依赖: ContinuousWithinAt, Ioi_mem_nhds, eq_or_lt, filter_upwards, ge_of_tendsto, hbx.eq_or_lt, hxb.eq_or_lt, inter_mem_nhdsWithin, le_of_lt, le_of_tendsto, le_rfl, monotoneOn_insert_iff
-/
lemma MonotoneOn.insert_of_continuousWithinAt [TopologicalSpace β] [OrderClosedTopology β]
    (hf : MonotoneOn f s) (hx : ClusterPt x (𝓟 s)) (h'x : ContinuousWithinAt f s x) :
    MonotoneOn f (insert x s) := by
  have : (𝓝[s] x).NeBot := hx
  apply monotoneOn_insert_iff.2 ⟨fun b hb hbx => ?_, fun b hb hxb => ?_, hf⟩
  · rcases hbx.eq_or_lt with rfl | hbx
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply ge_of_tendsto h'x
    have : s inter Ioi b in 𝓝[s] x := inter_mem_nhdsWithin _ (Ioi_mem_nhds hbx)
    filter_upwards [this] with y hy using hf hb hy.1 (le_of_lt hy.2)
  · rcases hxb.eq_or_lt with rfl | hxb
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply le_of_tendsto h'x
    have : s inter Iio b in 𝓝[s] x := inter_mem_nhdsWithin _ (Iio_mem_nhds hxb)
    filter_upwards [this] with y hy
    exact hf hy.1 hb (le_of_lt hy.2)

/--
lemma `MonotoneOn.countable_setOfPred_two_preimages` / 引理 `MonotoneOn.countable_setOfPred_two_preimages`

English:
lemma MonotoneOn.countable_setOfPred_two_preimages
  statement: [SecondCountableTopology α]
  proof: by
  nontriviality α
  let t := {c | exists x, exists y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c}
  have : forall c in t, exists x, exists y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c := fun c hc => hc
  choose! x y hxs hys hxy hfx hfy using this
  let u := x '' t
  suffices H : Set.Countable (x '' t) by
    have : Set.InjOn x t := by
      intro c hc d hd hcd
      have : f (x c) = f (x d) := by simp [hcd]
      rwa [hfx _ hc, hfx _ hd] at this
    exact countable_of_injective_of_countable_image this H
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := fun a => y (f a)); swap
  · rintro a ⟨c, hc, rfl⟩
    rw [hfx _ hc]
    exact hxy _ hc
  simp only [PairwiseDisjoint, Set.Pairwise, mem_image, onFun, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro c hc d hd hcd
  wlog H : c < d generalizing c d with h
  · apply (h d hd c hc hcd.symm ?_).symm
    have : c != d := fun h => hcd (congrArg x h)
    order
  simp only [disjoint_iff_forall_ne, mem_Ioo, ne_eq, and_imp]
  rintro a xca ayc b xda ayd rfl
  rw [hfx _ hc] at ayc
  have : x d <= y c := (xda.trans ayc).le
  have : f (x d) <= f (y c) := hf (hxs _ hd) (hys _ hc) this
  rw [hfx _ hd]; rw [hfy _ hc] at this
  exact not_le.2 H this

@[deprecated (since := "2026-07-09")] alias MonotoneOn.countable_setOf_two_preimages :=
  MonotoneOn.countable_setOfPred_two_preimages

中文:
引理 MonotoneOn.countable_setOfPred_two_preimages
  结论: [第二可数拓扑 α]
  证明: by
  nontriviality α
  let t := {c | exists x, exists y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c}
  have : forall c in t, exists x, exists y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c := fun c hc => hc
  choose! x y hxs hys hxy hfx hfy using this
  let u := x '' t
  suffices H : Set.Countable (x '' t) by
    have : Set.InjOn x t := by
      intro c hc d hd hcd
      have : f (x c) = f (x d) := by simp [hcd]
      rwa [hfx _ hc, hfx _ hd] at this
    exact countable_of_injective_of_countable_image this H
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := fun a => y (f a)); swap
  · rintro a ⟨c, hc, rfl⟩
    rw [hfx _ hc]
    exact hxy _ hc
  simp only [PairwiseDisjoint, Set.Pairwise, mem_image, onFun, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro c hc d hd hcd
  wlog H : c < d generalizing c d with h
  · apply (h d hd c hc hcd.symm ?_).symm
    have : c != d := fun h => hcd (congrArg x h)
    order
  simp only [disjoint_iff_forall_ne, mem_Ioo, ne_eq, and_imp]
  rintro a xca ayc b xda ayd rfl
  rw [hfx _ hc] at ayc
  have : x d <= y c := (xda.trans ayc).le
  have : f (x d) <= f (y c) := hf (hxs _ hd) (hys _ hc) this
  rw [hfx _ hd]; rw [hfy _ hc] at this
  exact not_le.2 H this

@[deprecated (since := "2026-07-09")] alias MonotoneOn.countable_setOf_two_preimages :=
  MonotoneOn.countable_setOfPred_two_preimages

Depends on / 依赖: Countable, PairwiseDisjo, Set.Countable, Set.InjOn, Set.PairwiseDisjo, countable_of_injective_of_countable_image, nontriviality
-/
lemma MonotoneOn.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : MonotoneOn f s) :
    Set.Countable {c | exists x y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c} := by
  nontriviality α
  let t := {c | exists x, exists y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c}
  have : forall c in t, exists x, exists y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c := fun c hc => hc
  choose! x y hxs hys hxy hfx hfy using this
  let u := x '' t
  suffices H : Set.Countable (x '' t) by
    have : Set.InjOn x t := by
      intro c hc d hd hcd
      have : f (x c) = f (x d) := by simp [hcd]
      rwa [hfx _ hc, hfx _ hd] at this
    exact countable_of_injective_of_countable_image this H
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := fun a => y (f a)); swap
  · rintro a ⟨c, hc, rfl⟩
    rw [hfx _ hc]
    exact hxy _ hc
  simp only [PairwiseDisjoint, Set.Pairwise, mem_image, onFun, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro c hc d hd hcd
  wlog H : c < d generalizing c d with h
  · apply (h d hd c hc hcd.symm ?_).symm
    have : c != d := fun h => hcd (congrArg x h)
    order
  simp only [disjoint_iff_forall_ne, mem_Ioo, ne_eq, and_imp]
  rintro a xca ayc b xda ayd rfl
  rw [hfx _ hc] at ayc
  have : x d <= y c := (xda.trans ayc).le
  have : f (x d) <= f (y c) := hf (hxs _ hd) (hys _ hc) this
  rw [hfx _ hd]; rw [hfy _ hc] at this
  exact not_le.2 H this

@[deprecated (since := "2026-07-09")] alias MonotoneOn.countable_setOf_two_preimages :=
  MonotoneOn.countable_setOfPred_two_preimages

/--
lemma `Monotone.countable_setOfPred_two_preimages` / 引理 `Monotone.countable_setOfPred_two_preimages`

English:
lemma Monotone.countable_setOfPred_two_preimages
  statement: [SecondCountableTopology α]
  proof: by
  rw [← monotoneOn_univ] at hf
  simpa using hf.countable_setOfPred_two_preimages

@[deprecated (since := "2026-07-09")] alias Monotone.countable_setOf_two_preimages :=
  Monotone.countable_setOfPred_two_preimages

中文:
引理 递增.countable_setOfPred_two_preimages
  结论: [第二可数拓扑 α]
  证明: by
  rw [← monotoneOn_univ] at hf
  simpa using hf.countable_setOfPred_two_preimages

@[deprecated (since := "2026-07-09")] alias Monotone.countable_setOf_two_preimages :=
  Monotone.countable_setOfPred_two_preimages

Depends on / 依赖: countable_setOfPred_two_preimages, hf.countable_setOfPred_two_preimages, monotoneOn_univ
-/
lemma Monotone.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : Monotone f) :
    Set.Countable {c | exists x y, x < y ∧ f x = c ∧ f y = c} := by
  rw [← monotoneOn_univ] at hf
  simpa using hf.countable_setOfPred_two_preimages

@[deprecated (since := "2026-07-09")] alias Monotone.countable_setOf_two_preimages :=
  Monotone.countable_setOfPred_two_preimages

/--
lemma `AntitoneOn.countable_setOfPred_two_preimages` / 引理 `AntitoneOn.countable_setOfPred_two_preimages`

English:
lemma AntitoneOn.countable_setOfPred_two_preimages
  statement: [SecondCountableTopology α]
  proof: (MonotoneOn.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias AntitoneOn.countable_setOf_two_preimages :=
  AntitoneOn.countable_setOfPred_two_preimages

中文:
引理 AntitoneOn.countable_setOfPred_two_preimages
  结论: [第二可数拓扑 α]
  证明: (MonotoneOn.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias AntitoneOn.countable_setOf_two_preimages :=
  AntitoneOn.countable_setOfPred_two_preimages

Depends on / 依赖: MonotoneOn, MonotoneOn.countable_setOfPred_two_preimages, countable_setOfPred_two_preimages, dual_right, hf.dual_right
-/
lemma AntitoneOn.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : AntitoneOn f s) :
    Set.Countable {c | exists x y, x in s ∧ y in s ∧ x < y ∧ f x = c ∧ f y = c} :=
  (MonotoneOn.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias AntitoneOn.countable_setOf_two_preimages :=
  AntitoneOn.countable_setOfPred_two_preimages

/--
lemma `Antitone.countable_setOfPred_two_preimages` / 引理 `Antitone.countable_setOfPred_two_preimages`

English:
lemma Antitone.countable_setOfPred_two_preimages
  statement: [SecondCountableTopology α]
  proof: (Monotone.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias Antitone.countable_setOf_two_preimages :=
  Antitone.countable_setOfPred_two_preimages

中文:
引理 递减.countable_setOfPred_two_preimages
  结论: [第二可数拓扑 α]
  证明: (Monotone.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias Antitone.countable_setOf_two_preimages :=
  Antitone.countable_setOfPred_two_preimages

Depends on / 依赖: Monotone, Monotone.countable_setOfPred_two_preimages, countable_setOfPred_two_preimages, dual_right, hf.dual_right
-/
lemma Antitone.countable_setOfPred_two_preimages [SecondCountableTopology α]
    (hf : Antitone f) :
    Set.Countable {c | exists x y, x < y ∧ f x = c ∧ f y = c} :=
  (Monotone.countable_setOfPred_two_preimages hf.dual_right :)

@[deprecated (since := "2026-07-09")] alias Antitone.countable_setOf_two_preimages :=
  Antitone.countable_setOfPred_two_preimages

section Continuity

variable [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β]

/--
theorem `MonotoneOn.countable_not_continuousWithinAt_Ioi` / 定理 `MonotoneOn.countable_not_continuousWithinAt_Ioi`

English:
theorem MonotoneOn.countable_not_continuousWithinAt_Ioi
  given: (hf : MonotoneOn f s)
  proof: by
  apply (countable_image_lt_image_Ioi_within s f).mono
  rintro x ⟨xs, hx : ¬ContinuousWithinAt f (s inter Ioi x) x⟩
  dsimp only [mem_ofPred_eq]
  contrapose! hx
  refine tendsto_order.2 ⟨fun m hm => ?_, fun u hu => ?_⟩
  · filter_upwards [@self_mem_nhdsWithin _ _ x (s inter Ioi x)] with y hy
    exact hm.trans_le (hf xs hy.1 (le_of_lt hy.2))
  rcases hx xs u hu with ⟨v, vs, xv, fvu⟩
  have : s inter Ioo x v in 𝓝[s inter Ioi x] x := by simp [nhdsWithin_inter, mem_inf_of_left,
    self_mem_nhdsWithin, mem_inf_of_right, Ioo_mem_nhdsGT xv]
  filter_upwards [this] with y hy
  exact (hf hy.1 vs hy.2.2.le).trans_lt fvu

中文:
定理 MonotoneOn.countable_not_continuousWithinAt_Ioi
  条件: (hf : MonotoneOn f s)
  证明: by
  apply (countable_image_lt_image_Ioi_within s f).mono
  rintro x ⟨xs, hx : ¬ContinuousWithinAt f (s inter Ioi x) x⟩
  dsimp only [mem_ofPred_eq]
  contrapose! hx
  refine tendsto_order.2 ⟨fun m hm => ?_, fun u hu => ?_⟩
  · filter_upwards [@self_mem_nhdsWithin _ _ x (s inter Ioi x)] with y hy
    exact hm.trans_le (hf xs hy.1 (le_of_lt hy.2))
  rcases hx xs u hu with ⟨v, vs, xv, fvu⟩
  have : s inter Ioo x v in 𝓝[s inter Ioi x] x := by simp [nhdsWithin_inter, mem_inf_of_left,
    self_mem_nhdsWithin, mem_inf_of_right, Ioo_mem_nhdsGT xv]
  filter_upwards [this] with y hy
  exact (hf hy.1 vs hy.2.2.le).trans_lt fvu

Depends on / 依赖: ContinuousWithinAt, contrapose, countable_image_lt_image_Ioi_within, filter_upwards, hm.trans_le, le_of_lt, mem_inf_of_left, mem_inf_of_rig, mem_ofPred_eq, nhdsWithin_inter, self_mem_nhdsWithin, tendsto_order, trans_le
-/
theorem MonotoneOn.countable_not_continuousWithinAt_Ioi (hf : MonotoneOn f s) :
    Set.Countable {x in s | ¬ContinuousWithinAt f (s inter Ioi x) x} := by
  apply (countable_image_lt_image_Ioi_within s f).mono
  rintro x ⟨xs, hx : ¬ContinuousWithinAt f (s inter Ioi x) x⟩
  dsimp only [mem_ofPred_eq]
  contrapose! hx
  refine tendsto_order.2 ⟨fun m hm => ?_, fun u hu => ?_⟩
  · filter_upwards [@self_mem_nhdsWithin _ _ x (s inter Ioi x)] with y hy
    exact hm.trans_le (hf xs hy.1 (le_of_lt hy.2))
  rcases hx xs u hu with ⟨v, vs, xv, fvu⟩
  have : s inter Ioo x v in 𝓝[s inter Ioi x] x := by simp [nhdsWithin_inter, mem_inf_of_left,
    self_mem_nhdsWithin, mem_inf_of_right, Ioo_mem_nhdsGT xv]
  filter_upwards [this] with y hy
  exact (hf hy.1 vs hy.2.2.le).trans_lt fvu

/--
theorem `MonotoneOn.countable_not_continuousWithinAt_Iio` / 定理 `MonotoneOn.countable_not_continuousWithinAt_Iio`

English:
theorem MonotoneOn.countable_not_continuousWithinAt_Iio
  given: (hf : MonotoneOn f s)
  proof: hf.dual.countable_not_continuousWithinAt_Ioi

中文:
定理 MonotoneOn.countable_not_continuousWithinAt_Iio
  条件: (hf : MonotoneOn f s)
  证明: hf.dual.countable_not_continuousWithinAt_Ioi

Depends on / 依赖: countable_not_continuousWithinAt_Ioi, hf.dual.countable_not_continuousWithinAt_Ioi
-/
theorem MonotoneOn.countable_not_continuousWithinAt_Iio (hf : MonotoneOn f s) :
    Set.Countable {x in s | ¬ContinuousWithinAt f (s inter Iio x) x} :=
  hf.dual.countable_not_continuousWithinAt_Ioi

/--
theorem `MonotoneOn.countable_not_continuousWithinAt` / 定理 `MonotoneOn.countable_not_continuousWithinAt`

English:
theorem MonotoneOn.countable_not_continuousWithinAt
  given: (hf : MonotoneOn f s)
  proof: by
  apply (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
  refine compl_subset_compl.1 ?_
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_not] at hx h'x ⊢
  intro xs
  exact continuousWithinAt_iff_continuous_left'_right'.2 ⟨h'x xs, hx xs⟩

中文:
定理 MonotoneOn.countable_not_continuousWithinAt
  条件: (hf : MonotoneOn f s)
  证明: by
  apply (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
  refine compl_subset_compl.1 ?_
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_not] at hx h'x ⊢
  intro xs
  exact continuousWithinAt_iff_continuous_left'_right'.2 ⟨h'x xs, hx xs⟩

Depends on / 依赖: _right, compl_subset_compl, compl_union, continuousWithinAt_iff_continuous_left, countable_not_continuousWithinAt_Iio, countable_not_continuousWithinAt_Ioi, hf.countable_not_continuousWithinAt_Iio, hf.countable_not_continuousWithinAt_Ioi.union, mem_compl_iff, mem_ofPred_eq, not_and, not_not
-/
theorem MonotoneOn.countable_not_continuousWithinAt (hf : MonotoneOn f s) :
    Set.Countable {x in s | ¬ContinuousWithinAt f s x} := by
  apply (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
  refine compl_subset_compl.1 ?_
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_not] at hx h'x ⊢
  intro xs
  exact continuousWithinAt_iff_continuous_left'_right'.2 ⟨h'x xs, hx xs⟩

/--
theorem `Monotone.countable_not_continuousAt` / 定理 `Monotone.countable_not_continuousAt`

English:
theorem Monotone.countable_not_continuousAt
  given: (hf : Monotone f)
  proof: by
  simpa [continuousWithinAt_univ] using (hf.monotoneOn univ).countable_not_continuousWithinAt

中文:
定理 递增.countable_not_continuousAt
  条件: (hf : 递增 f)
  证明: by
  simpa [continuousWithinAt_univ] using (hf.monotoneOn univ).countable_not_continuousWithinAt

Depends on / 依赖: continuousWithinAt_univ, countable_not_continuousWithinAt, hf.monotoneOn, monotoneOn
-/
theorem Monotone.countable_not_continuousAt (hf : Monotone f) :
    Set.Countable {x | ¬ContinuousAt f x} := by
  simpa [continuousWithinAt_univ] using (hf.monotoneOn univ).countable_not_continuousWithinAt

/--
theorem `_root_.AntitoneOn.countable_not_continuousWithinAt` / 定理 `_root_.AntitoneOn.countable_not_continuousWithinAt`

English:
theorem _root_.AntitoneOn.countable_not_continuousWithinAt
  proof: hf.dual_right.countable_not_continuousWithinAt

中文:
定理 _root_.AntitoneOn.countable_not_continuousWithinAt
  证明: hf.dual_right.countable_not_continuousWithinAt

Depends on / 依赖: countable_not_continuousWithinAt, dual_right, hf.dual_right.countable_not_continuousWithinAt
-/
theorem _root_.AntitoneOn.countable_not_continuousWithinAt
    {s : Set α} (hf : AntitoneOn f s) :
    Set.Countable {x in s | ¬ContinuousWithinAt f s x} :=
  hf.dual_right.countable_not_continuousWithinAt

/--
theorem `Antitone.countable_not_continuousAt` / 定理 `Antitone.countable_not_continuousAt`

English:
theorem Antitone.countable_not_continuousAt
  given: (hf : Antitone f)
  proof: hf.dual_right.countable_not_continuousAt

中文:
定理 递减.countable_not_continuousAt
  条件: (hf : 递减 f)
  证明: hf.dual_right.countable_not_continuousAt

Depends on / 依赖: countable_not_continuousAt, dual_right, hf.dual_right.countable_not_continuousAt
-/
theorem Antitone.countable_not_continuousAt (hf : Antitone f) :
    Set.Countable {x | ¬ContinuousAt f x} :=
  hf.dual_right.countable_not_continuousAt

end Continuity

section OrdContinuous

variable [TopologicalSpace β] [OrderTopology β]

/-- A monotone left-continuous function is left-continuous in the order-theoretic sense. -/
@[to_dual
/-- A monotone right-continuous function is right-continuous in the order-theoretic sense. -/
]
/--
theorem `Monotone.leftOrdContinuous` / 定理 `Monotone.leftOrdContinuous`

English:
theorem Monotone.leftOrdContinuous
  statement: (hf : Monotone f)
  proof: fun s x hs hx => IsLUB.isLUB_of_tendsto (hf.monotoneOn s) hx hs ((cont x).mono hx.1)

中文:
定理 递增.leftOrdContinuous
  结论: (hf : 递增 f)
  证明: fun s x hs hx => IsLUB.isLUB_of_tendsto (hf.monotoneOn s) hx hs ((cont x).mono hx.1)

Depends on / 依赖: IsLUB.isLUB_of_tendsto, hf.monotoneOn, isLUB_of_tendsto, monotoneOn
-/
theorem Monotone.leftOrdContinuous (hf : Monotone f)
    (cont : forall x, ContinuousWithinAt f (Iic x) x) : LeftOrdContinuous f :=
  fun s x hs hx => IsLUB.isLUB_of_tendsto (hf.monotoneOn s) hx hs ((cont x).mono hx.1)

/-- A monotone continuous function is left-continuous in the order-theoretic sense. -/
@[to_dual
/-- A monotone continuous function is right-continuous in the order-theoretic sense. -/
]
/--
theorem `Continuous.leftOrdContinuous` / 定理 `Continuous.leftOrdContinuous`

English:
theorem Continuous.leftOrdContinuous
  given: (cont : Continuous f) (hf : Monotone f)
  proof: hf.leftOrdContinuous fun _ => cont.continuousWithinAt

中文:
定理 连续.leftOrdContinuous
  条件: (cont : 连续 f) (hf : 递增 f)
  证明: hf.leftOrdContinuous fun _ => cont.continuousWithinAt

Depends on / 依赖: cont.continuousWithinAt, continuousWithinAt, hf.leftOrdContinuous, leftOrdContinuous
-/
theorem Continuous.leftOrdContinuous (cont : Continuous f) (hf : Monotone f) :
    LeftOrdContinuous f :=
  hf.leftOrdContinuous fun _ => cont.continuousWithinAt

end OrdContinuous

end LinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]

/--
theorem `MonotoneOn.map_csSup_of_continuousWithinAt` / 定理 `MonotoneOn.map_csSup_of_continuousWithinAt`

English:
theorem MonotoneOn.map_csSup_of_continuousWithinAt
  statement: {f : α -> β} {A : Set α}
  proof: --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
.symm ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto Mf A_nonemp <|
    Cf.mono_left fun ⦃_⦄ a => a).csSup_eq (A_nonemp.image f)

中文:
定理 MonotoneOn.map_csSup_of_continuousWithinAt
  结论: {f : α -> β} {A : 集合 α}
  证明: --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
.symm ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto Mf A_nonemp <|
    Cf.mono_left fun ⦃_⦄ a => a).csSup_eq (A_nonemp.image f)

Depends on / 依赖: bddDefault
-/
theorem MonotoneOn.map_csSup_of_continuousWithinAt {f : α -> β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sSup A))
    (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sSup (f '' A) :=
  --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
.symm ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto Mf A_nonemp <|
    Cf.mono_left fun ⦃_⦄ a => a).csSup_eq (A_nonemp.image f)

/--
theorem `Monotone.map_csSup_of_continuousAt` / 定理 `Monotone.map_csSup_of_continuousAt`

English:
theorem Monotone.map_csSup_of_continuousAt
  statement: {f : α -> β} {A : Set α}
  proof: MonotoneOn.map_csSup_of_continuousWithinAt Cf.continuousWithinAt
    (Mf.monotoneOn _) A_nonemp A_bdd

中文:
定理 递增.map_csSup_of_continuousAt
  结论: {f : α -> β} {A : 集合 α}
  证明: MonotoneOn.map_csSup_of_continuousWithinAt Cf.continuousWithinAt
    (Mf.monotoneOn _) A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Cf.continuousWithinAt, Mf.monotoneOn, MonotoneOn, MonotoneOn.map_csSup_of_continuousWithinAt, bddDefault, continuousWithinAt, map_csSup_of_continuousWithinAt, monotoneOn
-/
theorem Monotone.map_csSup_of_continuousAt {f : α -> β} {A : Set α}
    (Cf : ContinuousAt f (sSup A)) (Mf : Monotone f) (A_nonemp : A.Nonempty)
    (A_bdd : BddAbove A := by bddDefault) : f (sSup A) = sSup (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt Cf.continuousWithinAt
    (Mf.monotoneOn _) A_nonemp A_bdd

/--
theorem `Monotone.map_ciSup_of_continuousAt` / 定理 `Monotone.map_ciSup_of_continuousAt`

English:
theorem Monotone.map_ciSup_of_continuousAt
  statement: {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
  proof: by
  rw [iSup]; rw [Monotone.map_csSup_of_continuousAt Cf Mf (range_nonempty g) bdd]; rw [← range_comp]; rw [iSup]; rw [comp_def]

中文:
定理 递增.map_ciSup_of_continuousAt
  结论: {ι : 类型层*} [非空 ι] {f : α -> β} {g : ι -> α}
  证明: by
  rw [iSup]; rw [Monotone.map_csSup_of_continuousAt Cf Mf (range_nonempty g) bdd]; rw [← range_comp]; rw [iSup]; rw [comp_def]

Depends on / 依赖: Monotone, Monotone.map_csSup_of_continuousAt, bddDefault, comp_def, map_csSup_of_continuousAt, range_comp, range_nonempty
-/
theorem Monotone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup]; rw [Monotone.map_csSup_of_continuousAt Cf Mf (range_nonempty g) bdd]; rw [← range_comp]; rw [iSup]; rw [comp_def]

/--
theorem `MonotoneOn.map_csInf_of_continuousWithinAt` / 定理 `MonotoneOn.map_csInf_of_continuousWithinAt`

English:
theorem MonotoneOn.map_csInf_of_continuousWithinAt
  statement: {f : α -> β} {A : Set α}
  proof: MonotoneOn.map_csSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

中文:
定理 MonotoneOn.map_csInf_of_continuousWithinAt
  结论: {f : α -> β} {A : 集合 α}
  证明: MonotoneOn.map_csSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Mf.dual, MonotoneOn, MonotoneOn.map_csSup_of_continuousWithinAt, bddDefault, map_csSup_of_continuousWithinAt
-/
theorem MonotoneOn.map_csInf_of_continuousWithinAt {f : α -> β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sInf A))
    (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

/--
theorem `Monotone.map_csInf_of_continuousAt` / 定理 `Monotone.map_csInf_of_continuousAt`

English:
theorem Monotone.map_csInf_of_continuousAt
  statement: {f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A))
  proof: Monotone.map_csSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

中文:
定理 递增.map_csInf_of_continuousAt
  结论: {f : α -> β} {A : 集合 α} (Cf : ContinuousAt f (sInf A))
  证明: Monotone.map_csSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Mf.dual, Monotone, Monotone.map_csSup_of_continuousAt, bddDefault, map_csSup_of_continuousAt
-/
theorem Monotone.map_csInf_of_continuousAt {f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  Monotone.map_csSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

/--
theorem `Monotone.map_ciInf_of_continuousAt` / 定理 `Monotone.map_ciInf_of_continuousAt`

English:
theorem Monotone.map_ciInf_of_continuousAt
  statement: {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
  proof: by
  rw [iInf]; rw [Monotone.map_csInf_of_continuousAt Cf Mf (range_nonempty g) bdd]; rw [← range_comp]; rw [iInf]; rw [comp_def]

中文:
定理 递增.map_ciInf_of_continuousAt
  结论: {ι : 类型层*} [非空 ι] {f : α -> β} {g : ι -> α}
  证明: by
  rw [iInf]; rw [Monotone.map_csInf_of_continuousAt Cf Mf (range_nonempty g) bdd]; rw [← range_comp]; rw [iInf]; rw [comp_def]

Depends on / 依赖: Monotone, Monotone.map_csInf_of_continuousAt, bddDefault, comp_def, map_csInf_of_continuousAt, range_comp, range_nonempty
-/
theorem Monotone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [iInf]; rw [Monotone.map_csInf_of_continuousAt Cf Mf (range_nonempty g) bdd]; rw [← range_comp]; rw [iInf]; rw [comp_def]

/--
theorem `AntitoneOn.map_csInf_of_continuousWithinAt` / 定理 `AntitoneOn.map_csInf_of_continuousWithinAt`

English:
theorem AntitoneOn.map_csInf_of_continuousWithinAt
  statement: {f : α -> β} {A : Set α}
  proof: MonotoneOn.map_csInf_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

中文:
定理 AntitoneOn.map_csInf_of_continuousWithinAt
  结论: {f : α -> β} {A : 集合 α}
  证明: MonotoneOn.map_csInf_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Af.dual_right, MonotoneOn, MonotoneOn.map_csInf_of_continuousWithinAt, bddDefault, dual_right, map_csInf_of_continuousWithinAt
-/
theorem AntitoneOn.map_csInf_of_continuousWithinAt {f : α -> β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sInf A))
    (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  MonotoneOn.map_csInf_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/--
theorem `Antitone.map_csInf_of_continuousAt` / 定理 `Antitone.map_csInf_of_continuousAt`

English:
theorem Antitone.map_csInf_of_continuousAt
  statement: {f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A))
  proof: Monotone.map_csInf_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

中文:
定理 递减.map_csInf_of_continuousAt
  结论: {f : α -> β} {A : 集合 α} (Cf : ContinuousAt f (sInf A))
  证明: Monotone.map_csInf_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Af.dual_right, Monotone, Monotone.map_csInf_of_continuousAt, bddDefault, dual_right, map_csInf_of_continuousAt
-/
theorem Antitone.map_csInf_of_continuousAt {f : α -> β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  Monotone.map_csInf_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/--
theorem `Antitone.map_ciInf_of_continuousAt` / 定理 `Antitone.map_ciInf_of_continuousAt`

English:
theorem Antitone.map_ciInf_of_continuousAt
  statement: {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
  proof: by
  rw [iInf]; rw [Antitone.map_csInf_of_continuousAt Cf Af (range_nonempty g) bdd]; rw [← range_comp]; rw [iSup]; rw [comp_def]

中文:
定理 递减.map_ciInf_of_continuousAt
  结论: {ι : 类型层*} [非空 ι] {f : α -> β} {g : ι -> α}
  证明: by
  rw [iInf]; rw [Antitone.map_csInf_of_continuousAt Cf Af (range_nonempty g) bdd]; rw [← range_comp]; rw [iSup]; rw [comp_def]

Depends on / 依赖: Antitone, Antitone.map_csInf_of_continuousAt, bddDefault, comp_def, map_csInf_of_continuousAt, range_comp, range_nonempty
-/
theorem Antitone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨆ i, f (g i) := by
  rw [iInf]; rw [Antitone.map_csInf_of_continuousAt Cf Af (range_nonempty g) bdd]; rw [← range_comp]; rw [iSup]; rw [comp_def]

/--
theorem `AntitoneOn.map_csSup_of_continuousWithinAt` / 定理 `AntitoneOn.map_csSup_of_continuousWithinAt`

English:
theorem AntitoneOn.map_csSup_of_continuousWithinAt
  statement: {f : α -> β} {A : Set α}
  proof: MonotoneOn.map_csSup_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

中文:
定理 AntitoneOn.map_csSup_of_continuousWithinAt
  结论: {f : α -> β} {A : 集合 α}
  证明: MonotoneOn.map_csSup_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Af.dual_right, MonotoneOn, MonotoneOn.map_csSup_of_continuousWithinAt, bddDefault, dual_right, map_csSup_of_continuousWithinAt
-/
theorem AntitoneOn.map_csSup_of_continuousWithinAt {f : α -> β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sSup A))
    (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/--
theorem `Antitone.map_csSup_of_continuousAt` / 定理 `Antitone.map_csSup_of_continuousAt`

English:
theorem Antitone.map_csSup_of_continuousAt
  statement: {f : α -> β} {A : Set α} (Cf : ContinuousAt f (sSup A))
  proof: Monotone.map_csSup_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

中文:
定理 递减.map_csSup_of_continuousAt
  结论: {f : α -> β} {A : 集合 α} (Cf : ContinuousAt f (sSup A))
  证明: Monotone.map_csSup_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

Depends on / 依赖: A_bdd, A_nonemp, Af.dual_right, Monotone, Monotone.map_csSup_of_continuousAt, bddDefault, dual_right, map_csSup_of_continuousAt
-/
theorem Antitone.map_csSup_of_continuousAt {f : α -> β} {A : Set α} (Cf : ContinuousAt f (sSup A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  Monotone.map_csSup_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/--
theorem `Antitone.map_ciSup_of_continuousAt` / 定理 `Antitone.map_ciSup_of_continuousAt`

English:
theorem Antitone.map_ciSup_of_continuousAt
  statement: {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
  proof: by
  rw [iSup]; rw [Antitone.map_csSup_of_continuousAt Cf Af (range_nonempty g) bdd]; rw [← range_comp]; rw [iInf]; rw [comp_def]

中文:
定理 递减.map_ciSup_of_continuousAt
  结论: {ι : 类型层*} [非空 ι] {f : α -> β} {g : ι -> α}
  证明: by
  rw [iSup]; rw [Antitone.map_csSup_of_continuousAt Cf Af (range_nonempty g) bdd]; rw [← range_comp]; rw [iInf]; rw [comp_def]

Depends on / 依赖: Antitone, Antitone.map_csSup_of_continuousAt, bddDefault, comp_def, map_csSup_of_continuousAt, range_comp, range_nonempty
-/
theorem Antitone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨅ i, f (g i) := by
  rw [iSup]; rw [Antitone.map_csSup_of_continuousAt Cf Af (range_nonempty g) bdd]; rw [← range_comp]; rw [iInf]; rw [comp_def]

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [CompleteLinearOrder β]
  [TopologicalSpace β] [OrderClosedTopology β]

/--
theorem `sSup_mem_closure` / 定理 `sSup_mem_closure`

English:
theorem sSup_mem_closure
  given: {s : Set α} (hs : s.Nonempty)
  statement: sSup s in closure s
  proof: (isLUB_sSup s).mem_closure hs

中文:
定理 sSup_mem_closure
  条件: {s : 集合 α} (hs : s.非空)
  结论: sSup s in closure s
  证明: (isLUB_sSup s).mem_closure hs

Depends on / 依赖: isLUB_sSup, mem_closure
-/
theorem sSup_mem_closure {s : Set α} (hs : s.Nonempty) : sSup s in closure s :=
  (isLUB_sSup s).mem_closure hs

/--
theorem `sInf_mem_closure` / 定理 `sInf_mem_closure`

English:
theorem sInf_mem_closure
  given: {s : Set α} (hs : s.Nonempty)
  statement: sInf s in closure s
  proof: (isGLB_sInf s).mem_closure hs

中文:
定理 sInf_mem_closure
  条件: {s : 集合 α} (hs : s.非空)
  结论: sInf s in closure s
  证明: (isGLB_sInf s).mem_closure hs

Depends on / 依赖: isGLB_sInf, mem_closure
-/
theorem sInf_mem_closure {s : Set α} (hs : s.Nonempty) : sInf s in closure s :=
  (isGLB_sInf s).mem_closure hs

/--
theorem `IsClosed.sSup_mem` / 定理 `IsClosed.sSup_mem`

English:
theorem IsClosed.sSup_mem
  given: {s : Set α} (hs : s.Nonempty) (hc : IsClosed s)
  statement: sSup s in s
  proof: (isLUB_sSup s).mem_of_isClosed hs hc

中文:
定理 是闭集.sSup_mem
  条件: {s : 集合 α} (hs : s.非空) (hc : 是闭集 s)
  结论: sSup s in s
  证明: (isLUB_sSup s).mem_of_isClosed hs hc

Depends on / 依赖: isLUB_sSup, mem_of_isClosed
-/
theorem IsClosed.sSup_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sSup s in s :=
  (isLUB_sSup s).mem_of_isClosed hs hc

/--
theorem `IsClosed.sInf_mem` / 定理 `IsClosed.sInf_mem`

English:
theorem IsClosed.sInf_mem
  given: {s : Set α} (hs : s.Nonempty) (hc : IsClosed s)
  statement: sInf s in s
  proof: (isGLB_sInf s).mem_of_isClosed hs hc

中文:
定理 是闭集.sInf_mem
  条件: {s : 集合 α} (hs : s.非空) (hc : 是闭集 s)
  结论: sInf s in s
  证明: (isGLB_sInf s).mem_of_isClosed hs hc

Depends on / 依赖: isGLB_sInf, mem_of_isClosed
-/
theorem IsClosed.sInf_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sInf s in s :=
  (isGLB_sInf s).mem_of_isClosed hs hc

/--
theorem `MonotoneOn.map_sSup_of_continuousWithinAt` / 定理 `MonotoneOn.map_sSup_of_continuousWithinAt`

English:
theorem MonotoneOn.map_sSup_of_continuousWithinAt
  statement: {f : α -> β} {s : Set α}
  proof: by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Mf.map_csSup_of_continuousWithinAt Cf h

中文:
定理 MonotoneOn.map_sSup_of_continuousWithinAt
  结论: {f : α -> β} {s : 集合 α}
  证明: by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Mf.map_csSup_of_continuousWithinAt Cf h

Depends on / 依赖: Mf.map_csSup_of_continuousWithinAt, eq_empty_or_nonempty, map_csSup_of_continuousWithinAt, s.eq_empty_or_nonempty
-/
theorem MonotoneOn.map_sSup_of_continuousWithinAt {f : α -> β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sSup s))
    (Mf : MonotoneOn f s) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Mf.map_csSup_of_continuousWithinAt Cf h

/--
theorem `Monotone.map_sSup_of_continuousAt` / 定理 `Monotone.map_sSup_of_continuousAt`

English:
theorem Monotone.map_sSup_of_continuousAt
  statement: {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s))
  proof: MonotoneOn.map_sSup_of_continuousWithinAt Cf.continuousWithinAt (Mf.monotoneOn _) fbot

中文:
定理 递增.map_sSup_of_continuousAt
  结论: {f : α -> β} {s : 集合 α} (Cf : ContinuousAt f (sSup s))
  证明: MonotoneOn.map_sSup_of_continuousWithinAt Cf.continuousWithinAt (Mf.monotoneOn _) fbot

Depends on / 依赖: Cf.continuousWithinAt, Mf.monotoneOn, MonotoneOn, MonotoneOn.map_sSup_of_continuousWithinAt, continuousWithinAt, map_sSup_of_continuousWithinAt, monotoneOn
-/
theorem Monotone.map_sSup_of_continuousAt {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Mf : Monotone f) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt Cf.continuousWithinAt (Mf.monotoneOn _) fbot

/--
theorem `Monotone.map_iSup_of_continuousAt` / 定理 `Monotone.map_iSup_of_continuousAt`

English:
theorem Monotone.map_iSup_of_continuousAt
  statement: {ι : Sort*} {f : α -> β} {g : ι -> α}
  proof: by
  rw [iSup]; rw [Mf.map_sSup_of_continuousAt Cf fbot]; rw [← range_comp]; rw [iSup]; rw [comp_def]

中文:
定理 递增.map_iSup_of_continuousAt
  结论: {ι : 类型层*} {f : α -> β} {g : ι -> α}
  证明: by
  rw [iSup]; rw [Mf.map_sSup_of_continuousAt Cf fbot]; rw [← range_comp]; rw [iSup]; rw [comp_def]

Depends on / 依赖: Mf.map_sSup_of_continuousAt, comp_def, map_sSup_of_continuousAt, range_comp
-/
theorem Monotone.map_iSup_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f) (fbot : f ⊥ = ⊥) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup]; rw [Mf.map_sSup_of_continuousAt Cf fbot]; rw [← range_comp]; rw [iSup]; rw [comp_def]

/--
theorem `MonotoneOn.map_sInf_of_continuousWithinAt` / 定理 `MonotoneOn.map_sInf_of_continuousWithinAt`

English:
theorem MonotoneOn.map_sInf_of_continuousWithinAt
  statement: {f : α -> β} {s : Set α}
  proof: MonotoneOn.map_sSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

中文:
定理 MonotoneOn.map_sInf_of_continuousWithinAt
  结论: {f : α -> β} {s : 集合 α}
  证明: MonotoneOn.map_sSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

Depends on / 依赖: Mf.dual, MonotoneOn, MonotoneOn.map_sSup_of_continuousWithinAt, map_sSup_of_continuousWithinAt
-/
theorem MonotoneOn.map_sInf_of_continuousWithinAt {f : α -> β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sInf s)) (Mf : MonotoneOn f s) (ftop : f ⊤ = ⊤) :
    f (sInf s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/--
theorem `Monotone.map_sInf_of_continuousAt` / 定理 `Monotone.map_sInf_of_continuousAt`

English:
theorem Monotone.map_sInf_of_continuousAt
  statement: {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sInf s))
  proof: Monotone.map_sSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

中文:
定理 递增.map_sInf_of_continuousAt
  结论: {f : α -> β} {s : 集合 α} (Cf : ContinuousAt f (sInf s))
  证明: Monotone.map_sSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

Depends on / 依赖: Mf.dual, Monotone, Monotone.map_sSup_of_continuousAt, map_sSup_of_continuousAt
-/
theorem Monotone.map_sInf_of_continuousAt {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (sInf s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/--
theorem `Monotone.map_iInf_of_continuousAt` / 定理 `Monotone.map_iInf_of_continuousAt`

English:
theorem Monotone.map_iInf_of_continuousAt
  statement: {ι : Sort*} {f : α -> β} {g : ι -> α}
  proof: Monotone.map_iSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

中文:
定理 递增.map_iInf_of_continuousAt
  结论: {ι : 类型层*} {f : α -> β} {g : ι -> α}
  证明: Monotone.map_iSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

Depends on / 依赖: Mf.dual, Monotone, Monotone.map_iSup_of_continuousAt, map_iSup_of_continuousAt
-/
theorem Monotone.map_iInf_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (iInf g) = iInf (f ∘ g) :=
  Monotone.map_iSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/--
theorem `AntitoneOn.map_sSup_of_continuousWithinAt` / 定理 `AntitoneOn.map_sSup_of_continuousWithinAt`

English:
theorem AntitoneOn.map_sSup_of_continuousWithinAt
  statement: {f : α -> β} {s : Set α}
  proof: MonotoneOn.map_sSup_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sSup s) from Cf) Af fbot

中文:
定理 AntitoneOn.map_sSup_of_continuousWithinAt
  结论: {f : α -> β} {s : 集合 α}
  证明: MonotoneOn.map_sSup_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sSup s) from Cf) Af fbot

Depends on / 依赖: ContinuousWithinAt, MonotoneOn, MonotoneOn.map_sSup_of_continuousWithinAt, OrderDual, OrderDual.toDual, map_sSup_of_continuousWithinAt, toDual
-/
theorem AntitoneOn.map_sSup_of_continuousWithinAt {f : α -> β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sSup s)) (Af : AntitoneOn f s) (fbot : f ⊥ = ⊤) :
    f (sSup s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sSup s) from Cf) Af fbot

/--
theorem `Antitone.map_sSup_of_continuousAt` / 定理 `Antitone.map_sSup_of_continuousAt`

English:
theorem Antitone.map_sSup_of_continuousAt
  statement: {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s))
  proof: Monotone.map_sSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    fbot

中文:
定理 递减.map_sSup_of_continuousAt
  结论: {f : α -> β} {s : 集合 α} (Cf : ContinuousAt f (sSup s))
  证明: Monotone.map_sSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    fbot

Depends on / 依赖: ContinuousAt, Monotone, Monotone.map_sSup_of_continuousAt, OrderDual, OrderDual.toDual, map_sSup_of_continuousAt, toDual
-/
theorem Antitone.map_sSup_of_continuousAt {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Af : Antitone f) (fbot : f ⊥ = ⊤) : f (sSup s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    fbot

/--
theorem `Antitone.map_iSup_of_continuousAt` / 定理 `Antitone.map_iSup_of_continuousAt`

English:
theorem Antitone.map_iSup_of_continuousAt
  statement: {ι : Sort*} {f : α -> β} {g : ι -> α}
  proof: Monotone.map_iSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iSup g) from Cf) Af
    fbot

中文:
定理 递减.map_iSup_of_continuousAt
  结论: {ι : 类型层*} {f : α -> β} {g : ι -> α}
  证明: Monotone.map_iSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iSup g) from Cf) Af
    fbot

Depends on / 依赖: ContinuousAt, Monotone, Monotone.map_iSup_of_continuousAt, OrderDual, OrderDual.toDual, map_iSup_of_continuousAt, toDual
-/
theorem Antitone.map_iSup_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f) (fbot : f ⊥ = ⊤) :
    f (⨆ i, g i) = ⨅ i, f (g i) :=
  Monotone.map_iSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iSup g) from Cf) Af
    fbot

/--
theorem `AntitoneOn.map_sInf_of_continuousWithinAt` / 定理 `AntitoneOn.map_sInf_of_continuousWithinAt`

English:
theorem AntitoneOn.map_sInf_of_continuousWithinAt
  statement: {f : α -> β} {s : Set α}
  proof: MonotoneOn.map_sInf_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sInf s) from Cf) Af ftop

中文:
定理 AntitoneOn.map_sInf_of_continuousWithinAt
  结论: {f : α -> β} {s : 集合 α}
  证明: MonotoneOn.map_sInf_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sInf s) from Cf) Af ftop

Depends on / 依赖: ContinuousWithinAt, MonotoneOn, MonotoneOn.map_sInf_of_continuousWithinAt, OrderDual, OrderDual.toDual, map_sInf_of_continuousWithinAt, toDual
-/
theorem AntitoneOn.map_sInf_of_continuousWithinAt {f : α -> β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sInf s)) (Af : AntitoneOn f s) (ftop : f ⊤ = ⊥) :
    f (sInf s) = sSup (f '' s) :=
  MonotoneOn.map_sInf_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sInf s) from Cf) Af ftop

/--
theorem `Antitone.map_sInf_of_continuousAt` / 定理 `Antitone.map_sInf_of_continuousAt`

English:
theorem Antitone.map_sInf_of_continuousAt
  statement: {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sInf s))
  proof: Monotone.map_sInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ftop

中文:
定理 递减.map_sInf_of_continuousAt
  结论: {f : α -> β} {s : 集合 α} (Cf : ContinuousAt f (sInf s))
  证明: Monotone.map_sInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ftop

Depends on / 依赖: ContinuousAt, Monotone, Monotone.map_sInf_of_continuousAt, OrderDual, OrderDual.toDual, map_sInf_of_continuousAt, toDual
-/
theorem Antitone.map_sInf_of_continuousAt {f : α -> β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (sInf s) = sSup (f '' s) :=
  Monotone.map_sInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ftop

/--
theorem `Antitone.map_iInf_of_continuousAt` / 定理 `Antitone.map_iInf_of_continuousAt`

English:
theorem Antitone.map_iInf_of_continuousAt
  statement: {ι : Sort*} {f : α -> β} {g : ι -> α}
  proof: Monotone.map_iInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iInf g) from Cf) Af
    ftop

中文:
定理 递减.map_iInf_of_continuousAt
  结论: {ι : 类型层*} {f : α -> β} {g : ι -> α}
  证明: Monotone.map_iInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iInf g) from Cf) Af
    ftop

Depends on / 依赖: ContinuousAt, Monotone, Monotone.map_iInf_of_continuousAt, OrderDual, OrderDual.toDual, map_iInf_of_continuousAt, toDual
-/
theorem Antitone.map_iInf_of_continuousAt {ι : Sort*} {f : α -> β} {g : ι -> α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (iInf g) = iSup (f ∘ g) :=
  Monotone.map_iInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iInf g) from Cf) Af
    ftop

end CompleteLinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/--
theorem `csSup_mem_closure` / 定理 `csSup_mem_closure`

English:
theorem csSup_mem_closure
  given: {s : Set α} (hs : s.Nonempty) (B : BddAbove s)
  statement: sSup s in closure s
  proof: (isLUB_csSup hs B).mem_closure hs

中文:
定理 csSup_mem_closure
  条件: {s : 集合 α} (hs : s.非空) (B : BddAbove s)
  结论: sSup s in closure s
  证明: (isLUB_csSup hs B).mem_closure hs

Depends on / 依赖: isLUB_csSup, mem_closure
-/
theorem csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddAbove s) : sSup s in closure s :=
  (isLUB_csSup hs B).mem_closure hs

/--
theorem `csInf_mem_closure` / 定理 `csInf_mem_closure`

English:
theorem csInf_mem_closure
  given: {s : Set α} (hs : s.Nonempty) (B : BddBelow s)
  statement: sInf s in closure s
  proof: (isGLB_csInf hs B).mem_closure hs

中文:
定理 csInf_mem_closure
  条件: {s : 集合 α} (hs : s.非空) (B : BddBelow s)
  结论: sInf s in closure s
  证明: (isGLB_csInf hs B).mem_closure hs

Depends on / 依赖: isGLB_csInf, mem_closure
-/
theorem csInf_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddBelow s) : sInf s in closure s :=
  (isGLB_csInf hs B).mem_closure hs

/--
theorem `IsClosed.csSup_mem` / 定理 `IsClosed.csSup_mem`

English:
theorem IsClosed.csSup_mem
  given: {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s)
  proof: (isLUB_csSup hs B).mem_of_isClosed hs hc

中文:
定理 是闭集.csSup_mem
  条件: {s : 集合 α} (hc : 是闭集 s) (hs : s.非空) (B : BddAbove s)
  证明: (isLUB_csSup hs B).mem_of_isClosed hs hc

Depends on / 依赖: isLUB_csSup, mem_of_isClosed
-/
theorem IsClosed.csSup_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    sSup s in s :=
  (isLUB_csSup hs B).mem_of_isClosed hs hc

/--
theorem `IsClosed.csInf_mem` / 定理 `IsClosed.csInf_mem`

English:
theorem IsClosed.csInf_mem
  given: {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s)
  proof: (isGLB_csInf hs B).mem_of_isClosed hs hc

中文:
定理 是闭集.csInf_mem
  条件: {s : 集合 α} (hc : 是闭集 s) (hs : s.非空) (B : BddBelow s)
  证明: (isGLB_csInf hs B).mem_of_isClosed hs hc

Depends on / 依赖: isGLB_csInf, mem_of_isClosed
-/
theorem IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    sInf s in s :=
  (isGLB_csInf hs B).mem_of_isClosed hs hc

/--
theorem `IsClosed.isLeast_csInf` / 定理 `IsClosed.isLeast_csInf`

English:
theorem IsClosed.isLeast_csInf
  given: {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s)
  proof: ⟨hc.csInf_mem hs B, (isGLB_csInf hs B).1⟩

中文:
定理 是闭集.isLeast_csInf
  条件: {s : 集合 α} (hc : 是闭集 s) (hs : s.非空) (B : BddBelow s)
  证明: ⟨hc.csInf_mem hs B, (isGLB_csInf hs B).1⟩

Depends on / 依赖: csInf_mem, hc.csInf_mem, isGLB_csInf
-/
theorem IsClosed.isLeast_csInf {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    IsLeast s (sInf s) :=
  ⟨hc.csInf_mem hs B, (isGLB_csInf hs B).1⟩

/--
theorem `IsClosed.isGreatest_csSup` / 定理 `IsClosed.isGreatest_csSup`

English:
theorem IsClosed.isGreatest_csSup
  given: {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s)
  proof: IsClosed.isLeast_csInf (α := αᵒᵈ) hc hs B

中文:
定理 是闭集.isGreatest_csSup
  条件: {s : 集合 α} (hc : 是闭集 s) (hs : s.非空) (B : BddAbove s)
  证明: IsClosed.isLeast_csInf (α := αᵒᵈ) hc hs B

Depends on / 依赖: IsClosed, IsClosed.isLeast_csInf, isLeast_csInf
-/
theorem IsClosed.isGreatest_csSup {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    IsGreatest s (sSup s) :=
  IsClosed.isLeast_csInf (α := αᵒᵈ) hc hs B

/--
lemma `MonotoneOn.tendsto_nhdsWithin_Ioo_left` / 引理 `MonotoneOn.tendsto_nhdsWithin_Ioo_left`

English:
lemma MonotoneOn.tendsto_nhdsWithin_Ioo_left
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α]
  proof: by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : exists a : α, a in Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with w hw
exact lz.trans_le Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  · rcases h_nonempty with ⟨_, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsLT (hy.trans hx)] with w hw
    exact (le_csSup h_bdd (mem_image_of_mem _ hw)).trans_lt hm

中文:
引理 MonotoneOn.tendsto_nhdsWithin_Ioo_left
  结论: {α β : 类型} [线性序 α] [拓扑空间 α]
  证明: by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : exists a : α, a in Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with w hw
exact lz.trans_le Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  · rcases h_nonempty with ⟨_, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsLT (hy.trans hx)] with w hw
    exact (le_csSup h_bdd (mem_image_of_mem _ hw)).trans_lt hm

Depends on / 依赖: Ioo_mem_nhdsLT, exists_exists_and_eq_and, exists_lt_of_lt_csSup, exists_prop, filter_upwards, h_bdd, h_nonempty, h_nonempty.image, hy.trans, le_csSup, lz.trans_le, mem_image, mem_image_of_mem, tendsto_order, trans_le, yz.trans_le
-/
lemma MonotoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α -> β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Mf : MonotoneOn f (Ioo y x))
    (h_bdd : BddAbove (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Ioo y x))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : exists a : α, a in Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with w hw
exact lz.trans_le Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  · rcases h_nonempty with ⟨_, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsLT (hy.trans hx)] with w hw
    exact (le_csSup h_bdd (mem_image_of_mem _ hw)).trans_lt hm

/--
lemma `MonotoneOn.tendsto_nhdsWithin_Ioo_right` / 引理 `MonotoneOn.tendsto_nhdsWithin_Ioo_right`

English:
lemma MonotoneOn.tendsto_nhdsWithin_Ioo_right
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α]
  proof: by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · rcases h_nonempty with ⟨p, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsGT (hy.trans hx)] with w hw
exact hl.trans_le csInf_le h_bdd (mem_image_of_mem _ hw)
  · obtain ⟨z, ⟨xz, zy⟩, zm⟩ : exists a : α, a in Ioo x y ∧ f a < m := by
      simpa [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h_nonempty.image _) hm
    filter_upwards [Ioo_mem_nhdsGT xz] with w hw
    exact (Mf ⟨hw.1, hw.2.trans zy⟩ ⟨xz, zy⟩ hw.2.le).trans_lt zm

中文:
引理 MonotoneOn.tendsto_nhdsWithin_Ioo_right
  结论: {α β : 类型} [线性序 α] [拓扑空间 α]
  证明: by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · rcases h_nonempty with ⟨p, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsGT (hy.trans hx)] with w hw
exact hl.trans_le csInf_le h_bdd (mem_image_of_mem _ hw)
  · obtain ⟨z, ⟨xz, zy⟩, zm⟩ : exists a : α, a in Ioo x y ∧ f a < m := by
      simpa [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h_nonempty.image _) hm
    filter_upwards [Ioo_mem_nhdsGT xz] with w hw
    exact (Mf ⟨hw.1, hw.2.trans zy⟩ ⟨xz, zy⟩ hw.2.le).trans_lt zm

Depends on / 依赖: Ioo_mem_nhdsGT, csInf_le, exists_exists_and_eq_and, exists_lt_of_csInf_lt, exists_prop, filter_upwards, h_bdd, h_nonempty, h_nonempty.image, hl.trans_le, hy.trans, mem_image, mem_image_of_mem, tendsto_order, trans_le, trans_lt
-/
lemma MonotoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α -> β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Mf : MonotoneOn f (Ioo x y))
    (h_bdd : BddBelow (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioo x y))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · rcases h_nonempty with ⟨p, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsGT (hy.trans hx)] with w hw
exact hl.trans_le csInf_le h_bdd (mem_image_of_mem _ hw)
  · obtain ⟨z, ⟨xz, zy⟩, zm⟩ : exists a : α, a in Ioo x y ∧ f a < m := by
      simpa [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h_nonempty.image _) hm
    filter_upwards [Ioo_mem_nhdsGT xz] with w hw
    exact (Mf ⟨hw.1, hw.2.trans zy⟩ ⟨xz, zy⟩ hw.2.le).trans_lt zm

/--
lemma `MonotoneOn.tendsto_nhdsLT` / 引理 `MonotoneOn.tendsto_nhdsLT`

English:
lemma MonotoneOn.tendsto_nhdsLT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : exists a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using!
        exists_lt_of_lt_csSup (h.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with y hy using lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)

中文:
引理 MonotoneOn.tendsto_nhdsLT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : exists a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using!
        exists_lt_of_lt_csSup (h.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with y hy using lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)

Depends on / 依赖: Ioo_mem_nhdsLT, eq_empty_or_nonempty, exists_exists_and_eq_and, exists_lt_of_lt_csSup, exists_prop, filter_upwards, h.image, h_bdd, le_csSup, lt_of_le_of_lt, lz.trans_le, mem_image, mem_image_of_mem, mem_of_superset, self_mem_nhdsWithin, tendsto_order, trans_le
-/
lemma MonotoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β} {x : α}
    (Mf : MonotoneOn f (Iio x)) (h_bdd : BddAbove (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : exists a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using!
        exists_lt_of_lt_csSup (h.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with y hy using lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)

/--
lemma `MonotoneOn.tendsto_nhdsGT` / 引理 `MonotoneOn.tendsto_nhdsGT`

English:
lemma MonotoneOn.tendsto_nhdsGT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: MonotoneOn.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual h_bdd

中文:
引理 MonotoneOn.tendsto_nhdsGT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: MonotoneOn.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual h_bdd

Depends on / 依赖: Mf.dual, MonotoneOn, MonotoneOn.tendsto_nhdsLT, h_bdd, tendsto_nhdsLT
-/
lemma MonotoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β} {x : α}
    (Mf : MonotoneOn f (Ioi x)) (h_bdd : BddBelow (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  MonotoneOn.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual h_bdd

/--
theorem `Monotone.tendsto_nhdsLT` / 定理 `Monotone.tendsto_nhdsLT`

English:
theorem Monotone.tendsto_nhdsLT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: MonotoneOn.tendsto_nhdsLT (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)

中文:
定理 递增.tendsto_nhdsLT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: MonotoneOn.tendsto_nhdsLT (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)

Depends on / 依赖: Mf.map_bddAbove, Mf.monotoneOn, MonotoneOn, MonotoneOn.tendsto_nhdsLT, bddAbove_Iio, map_bddAbove, monotoneOn, tendsto_nhdsLT
-/
theorem Monotone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β}
    (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsLT (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)

/--
theorem `Monotone.tendsto_nhdsGT` / 定理 `Monotone.tendsto_nhdsGT`

English:
theorem Monotone.tendsto_nhdsGT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: Monotone.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x

中文:
定理 递增.tendsto_nhdsGT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: Monotone.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x

Depends on / 依赖: Mf.dual, Monotone, Monotone.tendsto_nhdsLT, tendsto_nhdsLT
-/
theorem Monotone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β}
    (Mf : Monotone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  Monotone.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x

/--
lemma `AntitoneOn.tendsto_nhdsWithin_Ioo_left` / 引理 `AntitoneOn.tendsto_nhdsWithin_Ioo_left`

English:
lemma AntitoneOn.tendsto_nhdsWithin_Ioo_left
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α]
  proof: MonotoneOn.tendsto_nhdsWithin_Ioo_left h_nonempty Af.dual_right h_bdd

中文:
引理 AntitoneOn.tendsto_nhdsWithin_Ioo_left
  结论: {α β : 类型} [线性序 α] [拓扑空间 α]
  证明: MonotoneOn.tendsto_nhdsWithin_Ioo_left h_nonempty Af.dual_right h_bdd

Depends on / 依赖: Af.dual_right, MonotoneOn, MonotoneOn.tendsto_nhdsWithin_Ioo_left, dual_right, h_bdd, h_nonempty, tendsto_nhdsWithin_Ioo_left
-/
lemma AntitoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α -> β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Af : AntitoneOn f (Ioo y x))
    (h_bdd : BddBelow (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Ioo y x))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_left h_nonempty Af.dual_right h_bdd

/--
lemma `AntitoneOn.tendsto_nhdsWithin_Ioo_right` / 引理 `AntitoneOn.tendsto_nhdsWithin_Ioo_right`

English:
lemma AntitoneOn.tendsto_nhdsWithin_Ioo_right
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α]
  proof: MonotoneOn.tendsto_nhdsWithin_Ioo_right h_nonempty Af.dual_right h_bdd

中文:
引理 AntitoneOn.tendsto_nhdsWithin_Ioo_right
  结论: {α β : 类型} [线性序 α] [拓扑空间 α]
  证明: MonotoneOn.tendsto_nhdsWithin_Ioo_right h_nonempty Af.dual_right h_bdd

Depends on / 依赖: Af.dual_right, MonotoneOn, MonotoneOn.tendsto_nhdsWithin_Ioo_right, dual_right, h_bdd, h_nonempty, tendsto_nhdsWithin_Ioo_right
-/
lemma AntitoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α -> β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Af : AntitoneOn f (Ioo x y))
    (h_bdd : BddAbove (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioo x y))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_right h_nonempty Af.dual_right h_bdd

/--
lemma `AntitoneOn.tendsto_nhdsLT` / 引理 `AntitoneOn.tendsto_nhdsLT`

English:
lemma AntitoneOn.tendsto_nhdsLT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: MonotoneOn.tendsto_nhdsLT Af.dual_right h_bdd

中文:
引理 AntitoneOn.tendsto_nhdsLT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: MonotoneOn.tendsto_nhdsLT Af.dual_right h_bdd

Depends on / 依赖: Af.dual_right, MonotoneOn, MonotoneOn.tendsto_nhdsLT, dual_right, h_bdd, tendsto_nhdsLT
-/
lemma AntitoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β} {x : α}
    (Af : AntitoneOn f (Iio x)) (h_bdd : BddBelow (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsLT Af.dual_right h_bdd

/--
lemma `AntitoneOn.tendsto_nhdsGT` / 引理 `AntitoneOn.tendsto_nhdsGT`

English:
lemma AntitoneOn.tendsto_nhdsGT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: MonotoneOn.tendsto_nhdsGT Af.dual_right h_bdd

中文:
引理 AntitoneOn.tendsto_nhdsGT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: MonotoneOn.tendsto_nhdsGT Af.dual_right h_bdd

Depends on / 依赖: Af.dual_right, MonotoneOn, MonotoneOn.tendsto_nhdsGT, dual_right, h_bdd, tendsto_nhdsGT
-/
lemma AntitoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β} {x : α}
    (Af : AntitoneOn f (Ioi x)) (h_bdd : BddAbove (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x))) :=
  MonotoneOn.tendsto_nhdsGT Af.dual_right h_bdd

/--
theorem `Antitone.tendsto_nhdsLT` / 定理 `Antitone.tendsto_nhdsLT`

English:
theorem Antitone.tendsto_nhdsLT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: Monotone.tendsto_nhdsLT Af.dual_right x

中文:
定理 递减.tendsto_nhdsLT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: Monotone.tendsto_nhdsLT Af.dual_right x

Depends on / 依赖: Af.dual_right, Monotone, Monotone.tendsto_nhdsLT, dual_right, tendsto_nhdsLT
-/
theorem Antitone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β}
    (Af : Antitone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) :=
  Monotone.tendsto_nhdsLT Af.dual_right x

/--
theorem `Antitone.tendsto_nhdsGT` / 定理 `Antitone.tendsto_nhdsGT`

English:
theorem Antitone.tendsto_nhdsGT
  statement: {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  proof: Monotone.tendsto_nhdsGT Af.dual_right x

中文:
定理 递减.tendsto_nhdsGT
  结论: {α β : 类型} [线性序 α] [拓扑空间 α] [Order拓扑 α]
  证明: Monotone.tendsto_nhdsGT Af.dual_right x

Depends on / 依赖: Af.dual_right, Monotone, Monotone.tendsto_nhdsGT, dual_right, tendsto_nhdsGT
-/
theorem Antitone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α -> β}
    (Af : Antitone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x))) :=
  Monotone.tendsto_nhdsGT Af.dual_right x

end ConditionallyCompleteLinearOrder
