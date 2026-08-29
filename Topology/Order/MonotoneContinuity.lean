/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Continuity of monotone functions

In this file we prove the following fact: if `f` is a monotone function on a neighborhood of `a`
and the image of this neighborhood is a neighborhood of `f a`, then `f` is continuous at `a`, see
`continuousWithinAt_of_monotoneOn_of_image_mem_nhds`, as well as several similar facts.

We also prove that an `OrderIso` is continuous.

## Tags

continuous, monotone
-/

public section


open Set Filter

open Topology

section LinearOrder

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [LinearOrder β] [TopologicalSpace β] [OrderTopology β]

/--
theorem `StrictMonoOn.continuousWithinAt_right_of_exists_between` / 定理 `StrictMonoOn.continuousWithinAt_right_of_exists_between`

English:
theorem StrictMonoOn.continuousWithinAt_right_of_exists_between
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: by
  have has : a in s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      ((h_mono.le_iff_le has hxs).2 hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩


中文:
定理 StrictMonoOn.continuousWithinAt_right_of_存在_between
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: by
  have has : a in s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      ((h_mono.le_iff_le has hxs).2 hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩


Depends on / 依赖: Ico_mem_nhdsGE, filter_upwards, h_mono, h_mono.le_iff_le, h_mono.lt_iff_lt, hb.trans_le, le_iff_le, lt_iff_lt, mem_of_mem_nhdsWithin, self_mem_Ici, self_mem_nhdsWithin, tendsto_order, trans_le
-/
theorem StrictMonoOn.continuousWithinAt_right_of_exists_between {f : α -> β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hfs : forall b > f a, exists c in s, f c in Ioc (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have has : a in s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      ((h_mono.le_iff_le has hxs).2 hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
    rw [h_mono.lt_iff_lt has hcs] at hac
    filter_upwards [hs, Ico_mem_nhdsGE hac]
    rintro x hx ⟨_, hxc⟩
    exact ((h_mono.lt_iff_lt hx hcs).2 hxc).trans_le hcb

/--
theorem `continuousWithinAt_right_of_monotoneOn_of_exists_between` / 定理 `continuousWithinAt_right_of_monotoneOn_of_exists_between`

English:
theorem continuousWithinAt_right_of_monotoneOn_of_exists_between
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: by
  have has : a in s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      (h_mono has hxs hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
have : a < c :

中文:
定理 continuousWithinAt_right_of_monotoneOn_of_存在_between
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: by
  have has : a in s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      (h_mono has hxs hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
have : a < c :

Depends on / 依赖: Ico_mem_nhdsGE, filter_upwards, h_mono, hac.not_ge, hb.trans_le, hxc.le, mem_of_mem_nhdsWithin, not_ge, not_le, self_mem_Ici, self_mem_nhdsWithin, tendsto_order, trans_le, trans_lt
-/
theorem continuousWithinAt_right_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s in 𝓝[>=] a) (hfs : forall b > f a, exists c in s, f c in Ioo (f a) b) :
    ContinuousWithinAt f (Ici a) a := by
  have has : a in s := mem_of_mem_nhdsWithin self_mem_Ici hs
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hs, @self_mem_nhdsWithin _ _ a (Ici a)] with _ hxs hxa using hb.trans_le
      (h_mono has hxs hxa)
  · rcases hfs b hb with ⟨c, hcs, hac, hcb⟩
have : a < c := not_le.1 fun h => hac.not_ge h_mono hcs has h
    filter_upwards [hs, Ico_mem_nhdsGE this]
    rintro x hx ⟨_, hxc⟩
    exact (h_mono hx hcs hxc.le).trans_lt hcb

/--
theorem `continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin` / 定理 `continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin`

English:
theorem continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
  statement: [DenselyOrdered β]
  proof: by
  refine continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono hs fun b hb => ?_
  rcases (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
  rcases exists_between hab' with ⟨c', hc'⟩
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') isOpen

中文:
定理 continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
  结论: [稠密序 β]
  证明: by
  refine continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono hs fun b hb => ?_
  rcases (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
  rcases exists_between hab' with ⟨c', hc'⟩
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') isOpen

Depends on / 依赖: continuousWithinAt_right_of_monotoneOn_of_exists_between, exists_between, h_mono, isOpen_Ioo, mem_closure_iff, mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset, trans_le
-/
theorem continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α -> β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝[>=] a)
    (hfs : closure (f '' s) in 𝓝[>=] f a) : ContinuousWithinAt f (Ici a) a := by
  refine continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono hs fun b hb => ?_
  rcases (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩
  rcases exists_between hab' with ⟨c', hc'⟩
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') isOpen_Ioo hc' with
    ⟨_, hc, ⟨c, hcs, rfl⟩⟩
  exact ⟨c, hcs, hc.1, hc.2.trans_le hbb'⟩

/--
theorem `continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin` / 定理 `continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin`

English:
theorem continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin
  statement: [DenselyOrdered β]
  proof: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    mem_of_superset hfs subset_closure

中文:
定理 continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin
  结论: [稠密序 β]
  证明: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    mem_of_superset hfs subset_closure

Depends on / 依赖: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin, h_mono, mem_of_superset, subset_closure
-/
theorem continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α -> β} {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝[>=] a)
    (hfs : f '' s in 𝓝[>=] f a) : ContinuousWithinAt f (Ici a) a :=
continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    mem_of_superset hfs subset_closure

/--
theorem `StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin` / 定理 `StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin`

English:
theorem StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
  statement: [DenselyOrdered β]
  proof: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
    (fun _ hx _ hy => (h_mono.le_iff_le hx hy).2) hs hfs

中文:
定理 StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
  结论: [稠密序 β]
  证明: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
    (fun _ hx _ hy => (h_mono.le_iff_le hx hy).2) hs hfs

Depends on / 依赖: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin, h_mono, h_mono.le_iff_le, le_iff_le
-/
theorem StrictMonoOn.continuousWithinAt_right_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[>=] a)
    (hfs : closure (f '' s) in 𝓝[>=] f a) : ContinuousWithinAt f (Ici a) a :=
  continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin
    (fun _ hx _ hy => (h_mono.le_iff_le hx hy).2) hs hfs

/--
theorem `StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin` / 定理 `StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin`

English:
theorem StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin
  statement: [DenselyOrdered β] {f : α -> β}
  proof: h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs
    (mem_of_superset hfs subset_closure)

中文:
定理 StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin
  结论: [稠密序 β] {f : α -> β}
  证明: h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs
    (mem_of_superset hfs subset_closure)

Depends on / 依赖: continuousWithinAt_right_of_closure_image_mem_nhdsWithin, h_mono, h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin, mem_of_superset, subset_closure
-/
theorem StrictMonoOn.continuousWithinAt_right_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α -> β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hfs : f '' s in 𝓝[>=] f a) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs
    (mem_of_superset hfs subset_closure)

/--
theorem `StrictMonoOn.continuousWithinAt_right_of_surjOn` / 定理 `StrictMonoOn.continuousWithinAt_right_of_surjOn`

English:
theorem StrictMonoOn.continuousWithinAt_right_of_surjOn
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: h_mono.continuousWithinAt_right_of_exists_between hs fun _ hb =>
    let ⟨c, hcs, hcb⟩ := hfs hb
    ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

中文:
定理 StrictMonoOn.continuousWithinAt_right_of_surjOn
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: h_mono.continuousWithinAt_right_of_exists_between hs fun _ hb =>
    let ⟨c, hcs, hcb⟩ := hfs hb
    ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

Depends on / 依赖: continuousWithinAt_right_of_exists_between, h_mono, h_mono.continuousWithinAt_right_of_exists_between, hcb.le, hcb.symm
-/
theorem StrictMonoOn.continuousWithinAt_right_of_surjOn {f : α -> β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s in 𝓝[>=] a) (hfs : SurjOn f s (Ioi (f a))) :
    ContinuousWithinAt f (Ici a) a :=
  h_mono.continuousWithinAt_right_of_exists_between hs fun _ hb =>
    let ⟨c, hcs, hcb⟩ := hfs hb
    ⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

/--
theorem `StrictMonoOn.continuousWithinAt_left_of_exists_between` / 定理 `StrictMonoOn.continuousWithinAt_left_of_exists_between`

English:
theorem StrictMonoOn.continuousWithinAt_left_of_exists_between
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: h_mono.dual.continuousWithinAt_right_of_exists_between hs fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

中文:
定理 StrictMonoOn.continuousWithinAt_left_of_存在_between
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: h_mono.dual.continuousWithinAt_right_of_exists_between hs fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

Depends on / 依赖: continuousWithinAt_right_of_exists_between, h_mono, h_mono.dual.continuousWithinAt_right_of_exists_between
-/
theorem StrictMonoOn.continuousWithinAt_left_of_exists_between {f : α -> β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s in 𝓝[<=] a) (hfs : forall b < f a, exists c in s, f c in Ico b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_exists_between hs fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

/--
theorem `continuousWithinAt_left_of_monotoneOn_of_exists_between` / 定理 `continuousWithinAt_left_of_monotoneOn_of_exists_between`

English:
theorem continuousWithinAt_left_of_monotoneOn_of_exists_between
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: @continuousWithinAt_right_of_monotoneOn_of_exists_between αᵒᵈ βᵒᵈ _ _ _ _ _ _ f s a hf.dual hs
    fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

中文:
定理 continuousWithinAt_left_of_monotoneOn_of_存在_between
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: @continuousWithinAt_right_of_monotoneOn_of_exists_between αᵒᵈ βᵒᵈ _ _ _ _ _ _ f s a hf.dual hs
    fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

Depends on / 依赖: continuousWithinAt_right_of_monotoneOn_of_exists_between, hf.dual
-/
theorem continuousWithinAt_left_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α}
    (hf : MonotoneOn f s) (hs : s in 𝓝[<=] a) (hfs : forall b < f a, exists c in s, f c in Ioo b (f a)) :
    ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_exists_between αᵒᵈ βᵒᵈ _ _ _ _ _ _ f s a hf.dual hs
    fun b hb =>
    let ⟨c, hcs, hcb, hca⟩ := hfs b hb
    ⟨c, hcs, hca, hcb⟩

/--
theorem `continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin` / 定理 `continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin`

English:
theorem continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin
  statement: [DenselyOrdered β]
  proof: @continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ f s
    a hf.dual hs hfs

中文:
定理 continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin
  结论: [稠密序 β]
  证明: @continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ f s
    a hf.dual hs hfs

Depends on / 依赖: continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin, hf.dual
-/
theorem continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α -> β} {s : Set α} {a : α} (hf : MonotoneOn f s) (hs : s in 𝓝[<=] a)
    (hfs : closure (f '' s) in 𝓝[<=] f a) : ContinuousWithinAt f (Iic a) a :=
  @continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ f s
    a hf.dual hs hfs

/--
theorem `continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin` / 定理 `continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin`

English:
theorem continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin
  statement: [DenselyOrdered β] {f : α -> β}
  proof: continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    (mem_of_superset hfs subset_closure)

中文:
定理 continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin
  结论: [稠密序 β] {f : α -> β}
  证明: continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    (mem_of_superset hfs subset_closure)

Depends on / 依赖: continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin, h_mono, mem_of_superset, subset_closure
-/
theorem continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α -> β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝[<=] a) (hfs : f '' s in 𝓝[<=] f a) :
    ContinuousWithinAt f (Iic a) a :=
  continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono hs
    (mem_of_superset hfs subset_closure)

/--
theorem `StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin` / 定理 `StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin`

English:
theorem StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin
  statement: [DenselyOrdered β]
  proof: h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs hfs

中文:
定理 StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin
  结论: [稠密序 β]
  证明: h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs hfs

Depends on / 依赖: continuousWithinAt_right_of_closure_image_mem_nhdsWithin, h_mono, h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
-/
theorem StrictMonoOn.continuousWithinAt_left_of_closure_image_mem_nhdsWithin [DenselyOrdered β]
    {f : α -> β} {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[<=] a)
    (hfs : closure (f '' s) in 𝓝[<=] f a) : ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_closure_image_mem_nhdsWithin hs hfs

/--
theorem `StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin` / 定理 `StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin`

English:
theorem StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin
  statement: [DenselyOrdered β] {f : α -> β}
  proof: h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin hs hfs

中文:
定理 StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin
  结论: [稠密序 β] {f : α -> β}
  证明: h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin hs hfs

Depends on / 依赖: continuousWithinAt_right_of_image_mem_nhdsWithin, h_mono, h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin
-/
theorem StrictMonoOn.continuousWithinAt_left_of_image_mem_nhdsWithin [DenselyOrdered β] {f : α -> β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝[<=] a) (hfs : f '' s in 𝓝[<=] f a) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_image_mem_nhdsWithin hs hfs

/--
theorem `StrictMonoOn.continuousWithinAt_left_of_surjOn` / 定理 `StrictMonoOn.continuousWithinAt_left_of_surjOn`

English:
theorem StrictMonoOn.continuousWithinAt_left_of_surjOn
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: h_mono.dual.continuousWithinAt_right_of_surjOn hs hfs

中文:
定理 StrictMonoOn.continuousWithinAt_left_of_surjOn
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: h_mono.dual.continuousWithinAt_right_of_surjOn hs hfs

Depends on / 依赖: continuousWithinAt_right_of_surjOn, h_mono, h_mono.dual.continuousWithinAt_right_of_surjOn
-/
theorem StrictMonoOn.continuousWithinAt_left_of_surjOn {f : α -> β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s in 𝓝[<=] a) (hfs : SurjOn f s (Iio (f a))) :
    ContinuousWithinAt f (Iic a) a :=
  h_mono.dual.continuousWithinAt_right_of_surjOn hs hfs

/--
theorem `StrictMonoOn.continuousAt_of_exists_between` / 定理 `StrictMonoOn.continuousAt_of_exists_between`

English:
theorem StrictMonoOn.continuousAt_of_exists_between
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_l,
      h_mono.continuousWithinAt_right_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

中文:
定理 StrictMonoOn.continuousAt_of_存在_between
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_l,
      h_mono.continuousWithinAt_right_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

Depends on / 依赖: continuousAt_iff_continuous_left_right, continuousWithinAt_left_of_exists_between, continuousWithinAt_right_of_exists_between, h_mono, h_mono.continuousWithinAt_left_of_exists_between, h_mono.continuousWithinAt_right_of_exists_between, hfs_l, hfs_r, mem_nhdsWithin_of_mem_nhds
-/
theorem StrictMonoOn.continuousAt_of_exists_between {f : α -> β} {s : Set α} {a : α}
    (h_mono : StrictMonoOn f s) (hs : s in 𝓝 a) (hfs_l : forall b < f a, exists c in s, f c in Ico b (f a))
    (hfs_r : forall b > f a, exists c in s, f c in Ioc (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_l,
      h_mono.continuousWithinAt_right_of_exists_between (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

/--
theorem `StrictMonoOn.continuousAt_of_closure_image_mem_nhds` / 定理 `StrictMonoOn.continuousAt_of_closure_image_mem_nhds`

English:
theorem StrictMonoOn.continuousAt_of_closure_image_mem_nhds
  statement: [DenselyOrdered β] {f : α -> β}
  proof: continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hs)
        (mem_nhdsWithin_of_mem_nhds hfs),
      h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nh

中文:
定理 StrictMonoOn.continuousAt_of_closure_image_mem_nhds
  结论: [稠密序 β] {f : α -> β}
  证明: continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hs)
        (mem_nhdsWithin_of_mem_nhds hfs),
      h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nh

Depends on / 依赖: continuousAt_iff_continuous_left_right, continuousWithinAt_left_of_closure_image_mem_nhdsWithin, continuousWithinAt_right_of_closure_image_mem_nhdsWithin, h_mono, h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin, h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
-/
theorem StrictMonoOn.continuousAt_of_closure_image_mem_nhds [DenselyOrdered β] {f : α -> β}
    {s : Set α} {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝 a)
    (hfs : closure (f '' s) in 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨h_mono.continuousWithinAt_left_of_closure_image_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hs)
        (mem_nhdsWithin_of_mem_nhds hfs),
      h_mono.continuousWithinAt_right_of_closure_image_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩

/--
theorem `StrictMonoOn.continuousAt_of_image_mem_nhds` / 定理 `StrictMonoOn.continuousAt_of_image_mem_nhds`

English:
theorem StrictMonoOn.continuousAt_of_image_mem_nhds
  statement: [DenselyOrdered β] {f : α -> β} {s : Set α}
  proof: h_mono.continuousAt_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

中文:
定理 StrictMonoOn.continuousAt_of_image_mem_nhds
  结论: [稠密序 β] {f : α -> β} {s : 集合 α}
  证明: h_mono.continuousAt_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

Depends on / 依赖: continuousAt_of_closure_image_mem_nhds, h_mono, h_mono.continuousAt_of_closure_image_mem_nhds, mem_of_superset, subset_closure
-/
theorem StrictMonoOn.continuousAt_of_image_mem_nhds [DenselyOrdered β] {f : α -> β} {s : Set α}
    {a : α} (h_mono : StrictMonoOn f s) (hs : s in 𝓝 a) (hfs : f '' s in 𝓝 (f a)) :
    ContinuousAt f a :=
  h_mono.continuousAt_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

/--
theorem `continuousAt_of_monotoneOn_of_exists_between` / 定理 `continuousAt_of_monotoneOn_of_exists_between`

English:
theorem continuousAt_of_monotoneOn_of_exists_between
  statement: {f : α -> β} {s : Set α} {a : α}
  proof: continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_exists_between h_mono (mem_nhdsWithin_of_mem_nhds hs)
        hfs_l,
      continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono
        (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

中文:
定理 continuousAt_of_monotoneOn_of_存在_between
  结论: {f : α -> β} {s : 集合 α} {a : α}
  证明: continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_exists_between h_mono (mem_nhdsWithin_of_mem_nhds hs)
        hfs_l,
      continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono
        (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

Depends on / 依赖: continuousAt_iff_continuous_left_right, continuousWithinAt_left_of_monotoneOn_of_exists_between, continuousWithinAt_right_of_monotoneOn_of_exists_between, h_mono, hfs_l, hfs_r, mem_nhdsWithin_of_mem_nhds
-/
theorem continuousAt_of_monotoneOn_of_exists_between {f : α -> β} {s : Set α} {a : α}
    (h_mono : MonotoneOn f s) (hs : s in 𝓝 a) (hfs_l : forall b < f a, exists c in s, f c in Ioo b (f a))
    (hfs_r : forall b > f a, exists c in s, f c in Ioo (f a) b) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_exists_between h_mono (mem_nhdsWithin_of_mem_nhds hs)
        hfs_l,
      continuousWithinAt_right_of_monotoneOn_of_exists_between h_mono
        (mem_nhdsWithin_of_mem_nhds hs) hfs_r⟩

/--
theorem `continuousAt_of_monotoneOn_of_closure_image_mem_nhds` / 定理 `continuousAt_of_monotoneOn_of_closure_image_mem_nhds`

English:
theorem continuousAt_of_monotoneOn_of_closure_image_mem_nhds
  statement: [DenselyOrdered β] {f : α -> β}
  proof: continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs),
      continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWi

中文:
定理 continuousAt_of_monotoneOn_of_closure_image_mem_nhds
  结论: [稠密序 β] {f : α -> β}
  证明: continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs),
      continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWi

Depends on / 依赖: continuousAt_iff_continuous_left_right, continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin, continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin, h_mono, mem_nhdsWithin_of_mem_nhds
-/
theorem continuousAt_of_monotoneOn_of_closure_image_mem_nhds [DenselyOrdered β] {f : α -> β}
    {s : Set α} {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝 a)
    (hfs : closure (f '' s) in 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs),
      continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin h_mono
        (mem_nhdsWithin_of_mem_nhds hs) (mem_nhdsWithin_of_mem_nhds hfs)⟩

/--
theorem `continuousAt_of_monotoneOn_of_image_mem_nhds` / 定理 `continuousAt_of_monotoneOn_of_image_mem_nhds`

English:
theorem continuousAt_of_monotoneOn_of_image_mem_nhds
  statement: [DenselyOrdered β] {f : α -> β} {s : Set α}
  proof: continuousAt_of_monotoneOn_of_closure_image_mem_nhds h_mono hs
    (mem_of_superset hfs subset_closure)

中文:
定理 continuousAt_of_monotoneOn_of_image_mem_nhds
  结论: [稠密序 β] {f : α -> β} {s : 集合 α}
  证明: continuousAt_of_monotoneOn_of_closure_image_mem_nhds h_mono hs
    (mem_of_superset hfs subset_closure)

Depends on / 依赖: continuousAt_of_monotoneOn_of_closure_image_mem_nhds, h_mono, mem_of_superset, subset_closure
-/
theorem continuousAt_of_monotoneOn_of_image_mem_nhds [DenselyOrdered β] {f : α -> β} {s : Set α}
    {a : α} (h_mono : MonotoneOn f s) (hs : s in 𝓝 a) (hfs : f '' s in 𝓝 (f a)) : ContinuousAt f a :=
  continuousAt_of_monotoneOn_of_closure_image_mem_nhds h_mono hs
    (mem_of_superset hfs subset_closure)

/--
theorem `Monotone.continuous_of_denseRange` / 定理 `Monotone.continuous_of_denseRange`

English:
theorem Monotone.continuous_of_denseRange
  statement: [DenselyOrdered β] {f : α -> β} (h_mono : Monotone f)
  proof: continuous_iff_continuousAt.mpr fun a =>
    continuousAt_of_monotoneOn_of_closure_image_mem_nhds (fun _ _ _ _ hxy => h_mono hxy)
univ_mem
      by simp only [image_univ, h_dense.closure_eq, univ_mem]

中文:
定理 递增.continuous_of_denseRange
  结论: [稠密序 β] {f : α -> β} (h_mono : 递增 f)
  证明: continuous_iff_continuousAt.mpr fun a =>
    continuousAt_of_monotoneOn_of_closure_image_mem_nhds (fun _ _ _ _ hxy => h_mono hxy)
univ_mem
      by simp only [image_univ, h_dense.closure_eq, univ_mem]

Depends on / 依赖: closure_eq, continuousAt_of_monotoneOn_of_closure_image_mem_nhds, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, h_dense, h_dense.closure_eq, h_mono, image_univ, univ_mem
-/
theorem Monotone.continuous_of_denseRange [DenselyOrdered β] {f : α -> β} (h_mono : Monotone f)
    (h_dense : DenseRange f) : Continuous f :=
  continuous_iff_continuousAt.mpr fun a =>
    continuousAt_of_monotoneOn_of_closure_image_mem_nhds (fun _ _ _ _ hxy => h_mono hxy)
univ_mem
      by simp only [image_univ, h_dense.closure_eq, univ_mem]

/--
theorem `Monotone.continuous_of_surjective` / 定理 `Monotone.continuous_of_surjective`

English:
theorem Monotone.continuous_of_surjective
  statement: [DenselyOrdered β] {f : α -> β} (h_mono : Monotone f)
  proof: h_mono.continuous_of_denseRange h_surj.denseRange

中文:
定理 递增.continuous_of_surjective
  结论: [稠密序 β] {f : α -> β} (h_mono : 递增 f)
  证明: h_mono.continuous_of_denseRange h_surj.denseRange

Depends on / 依赖: continuous_of_denseRange, denseRange, h_mono, h_mono.continuous_of_denseRange, h_surj, h_surj.denseRange
-/
theorem Monotone.continuous_of_surjective [DenselyOrdered β] {f : α -> β} (h_mono : Monotone f)
    (h_surj : Function.Surjective f) : Continuous f :=
  h_mono.continuous_of_denseRange h_surj.denseRange

end LinearOrder

/-!
### Continuity of order isomorphisms

In this section we prove that an `OrderIso` is continuous, hence it is a `Homeomorph`. We prove
this for an `OrderIso` between to partial orders with order topology.
-/


namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [OrderTopology α] [OrderTopology β]

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (e : α ≃o β)
  statement: Continuous e
  proof: by
  rw [‹OrderTopology β›.topology_eq_generate_intervals]; rw [continuous_generateFrom_iff]
  rintro s ⟨a, rfl | rfl⟩
  · rw [e.preimage_Ioi]
    apply isOpen_lt'
  · rw [e.preimage_Iio]
    apply isOpen_gt'

中文:
定理 continuous
  条件: (e : α ≃o β)
  结论: 连续 e
  证明: by
  rw [‹OrderTopology β›.topology_eq_generate_intervals]; rw [continuous_generateFrom_iff]
  rintro s ⟨a, rfl | rfl⟩
  · rw [e.preimage_Ioi]
    apply isOpen_lt'
  · rw [e.preimage_Iio]
    apply isOpen_gt'
-/
protected theorem continuous (e : α ≃o β) : Continuous e := by
  rw [‹OrderTopology β›.topology_eq_generate_intervals]; rw [continuous_generateFrom_iff]
  rintro s ⟨a, rfl | rfl⟩
  · rw [e.preimage_Ioi]
    apply isOpen_lt'
  · rw [e.preimage_Iio]
    apply isOpen_gt'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomeomorphClass (α ≃o β) α β
  body: OrderIso.continuous
  inv_continuous e := e.symm.continuous

中文:
实例 :
  签名: 同胚类 (α ≃o β) α β
  定义体: OrderIso.continuous
  inv_continuous e := e.symm.continuous

Depends on / 依赖: OrderIso, OrderIso.continuous, continuous
-/
instance : HomeomorphClass (α ≃o β) α β where
  map_continuous := OrderIso.continuous
  inv_continuous e := e.symm.continuous

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
abbreviation toHomeomorph
  signature: (e : α ≃o β)
  body: HomeomorphClass.toHomeomorph e

中文:
缩写 toHomeomorph
  签名: (e : α ≃o β)
  定义体: HomeomorphClass.toHomeomorph e

Depends on / 依赖: HomeomorphClass, HomeomorphClass.toHomeomorph, toHomeomorph
-/
abbrev toHomeomorph (e : α ≃o β) : α ≃ₜ β :=
  HomeomorphClass.toHomeomorph e

/--
theorem `coe_toHomeomorph` / 定理 `coe_toHomeomorph`

English:
theorem coe_toHomeomorph
  given: (e : α ≃o β)
  statement: ⇑e.toHomeomorph = e
  proof: rfl --Simp can prove this too

@[simp]

中文:
定理 coe_toHomeomorph
  条件: (e : α ≃o β)
  结论: ⇑e.toHomeomorph = e
  证明: rfl --Simp can prove this too

@[simp]
-/
theorem coe_toHomeomorph (e : α ≃o β) : ⇑e.toHomeomorph = e :=
  rfl --Simp can prove this too

@[simp]
/--
theorem `coe_toHomeomorph_symm` / 定理 `coe_toHomeomorph_symm`

English:
theorem coe_toHomeomorph_symm
  given: (e : α ≃o β)
  statement: ⇑e.toHomeomorph.symm = e.symm
  proof: rfl

中文:
定理 coe_toHomeomorph_symm
  条件: (e : α ≃o β)
  结论: ⇑e.toHomeomorph.symm = e.symm
  证明: rfl
-/
theorem coe_toHomeomorph_symm (e : α ≃o β) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

end OrderIso
