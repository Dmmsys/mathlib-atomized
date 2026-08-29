/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Properties of LUB and GLB in an order topology
-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α γ : Type*}

section OrderTopology

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

/--
theorem `IsLUB.frequently_mem` / 定理 `IsLUB.frequently_mem`

English:
theorem IsLUB.frequently_mem
  given: {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
  proof: by
  rcases hs with ⟨a', ha'⟩
  intro h
  rcases (ha.1 ha').eq_or_lt with (rfl | ha'a)
  · exact h.self_of_nhdsWithin le_rfl ha'
  · rcases (mem_nhdsLE_iff_exists_Ioc_subset' ha'a).1 h with ⟨b, hba, hb⟩
    rcases ha.exists_between hba with ⟨b', hb's, hb'⟩
    exact hb hb' hb's

中文:
定理 IsLUB.frequently_mem
  条件: {a : α} {s : 集合 α} (ha : IsLUB s a) (hs : s.非空)
  证明: by
  rcases hs with ⟨a', ha'⟩
  intro h
  rcases (ha.1 ha').eq_or_lt with (rfl | ha'a)
  · exact h.self_of_nhdsWithin le_rfl ha'
  · rcases (mem_nhdsLE_iff_exists_Ioc_subset' ha'a).1 h with ⟨b, hba, hb⟩
    rcases ha.exists_between hba with ⟨b', hb's, hb'⟩
    exact hb hb' hb's

Depends on / 依赖: eq_or_lt, exists_between, h.self_of_nhdsWithin, ha.exists_between, le_rfl, mem_nhdsLE_iff_exists_Ioc_subset, self_of_nhdsWithin
-/
theorem IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    existsᶠ x in 𝓝[<=] a, x in s := by
  rcases hs with ⟨a', ha'⟩
  intro h
  rcases (ha.1 ha').eq_or_lt with (rfl | ha'a)
  · exact h.self_of_nhdsWithin le_rfl ha'
  · rcases (mem_nhdsLE_iff_exists_Ioc_subset' ha'a).1 h with ⟨b, hba, hb⟩
    rcases ha.exists_between hba with ⟨b', hb's, hb'⟩
    exact hb hb' hb's

/--
theorem `IsLUB.frequently_nhds_mem` / 定理 `IsLUB.frequently_nhds_mem`

English:
theorem IsLUB.frequently_nhds_mem
  given: {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
  proof: (ha.frequently_mem hs).filter_mono inf_le_left

中文:
定理 IsLUB.frequently_nhds_mem
  条件: {a : α} {s : 集合 α} (ha : IsLUB s a) (hs : s.非空)
  证明: (ha.frequently_mem hs).filter_mono inf_le_left

Depends on / 依赖: filter_mono, frequently_mem, ha.frequently_mem, inf_le_left
-/
theorem IsLUB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    existsᶠ x in 𝓝 a, x in s :=
  (ha.frequently_mem hs).filter_mono inf_le_left

/--
theorem `IsGLB.frequently_mem` / 定理 `IsGLB.frequently_mem`

English:
theorem IsGLB.frequently_mem
  given: {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
  proof: IsLUB.frequently_mem (α := αᵒᵈ) ha hs

中文:
定理 IsGLB.frequently_mem
  条件: {a : α} {s : 集合 α} (ha : IsGLB s a) (hs : s.非空)
  证明: IsLUB.frequently_mem (α := αᵒᵈ) ha hs

Depends on / 依赖: IsLUB.frequently_mem, frequently_mem
-/
theorem IsGLB.frequently_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    existsᶠ x in 𝓝[>=] a, x in s :=
  IsLUB.frequently_mem (α := αᵒᵈ) ha hs

/--
theorem `IsGLB.frequently_nhds_mem` / 定理 `IsGLB.frequently_nhds_mem`

English:
theorem IsGLB.frequently_nhds_mem
  given: {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
  proof: (ha.frequently_mem hs).filter_mono inf_le_left

中文:
定理 IsGLB.frequently_nhds_mem
  条件: {a : α} {s : 集合 α} (ha : IsGLB s a) (hs : s.非空)
  证明: (ha.frequently_mem hs).filter_mono inf_le_left

Depends on / 依赖: filter_mono, frequently_mem, ha.frequently_mem, inf_le_left
-/
theorem IsGLB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    existsᶠ x in 𝓝 a, x in s :=
  (ha.frequently_mem hs).filter_mono inf_le_left

/--
theorem `IsLUB.mem_closure` / 定理 `IsLUB.mem_closure`

English:
theorem IsLUB.mem_closure
  given: {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
  statement: a in closure s
  proof: (ha.frequently_nhds_mem hs).mem_closure

中文:
定理 IsLUB.mem_closure
  条件: {a : α} {s : 集合 α} (ha : IsLUB s a) (hs : s.非空)
  结论: a in closure s
  证明: (ha.frequently_nhds_mem hs).mem_closure

Depends on / 依赖: frequently_nhds_mem, ha.frequently_nhds_mem, mem_closure
-/
theorem IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) : a in closure s :=
  (ha.frequently_nhds_mem hs).mem_closure

/--
theorem `IsGLB.mem_closure` / 定理 `IsGLB.mem_closure`

English:
theorem IsGLB.mem_closure
  given: {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
  statement: a in closure s
  proof: (ha.frequently_nhds_mem hs).mem_closure

中文:
定理 IsGLB.mem_closure
  条件: {a : α} {s : 集合 α} (ha : IsGLB s a) (hs : s.非空)
  结论: a in closure s
  证明: (ha.frequently_nhds_mem hs).mem_closure

Depends on / 依赖: frequently_nhds_mem, ha.frequently_nhds_mem, mem_closure
-/
theorem IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) : a in closure s :=
  (ha.frequently_nhds_mem hs).mem_closure

/--
theorem `IsLUB.nhdsWithin_neBot` / 定理 `IsLUB.nhdsWithin_neBot`

English:
theorem IsLUB.nhdsWithin_neBot
  given: {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
  proof: mem_closure_iff_nhdsWithin_neBot.1 (ha.mem_closure hs)

中文:
定理 IsLUB.nhdsWithin_neBot
  条件: {a : α} {s : 集合 α} (ha : IsLUB s a) (hs : s.非空)
  证明: mem_closure_iff_nhdsWithin_neBot.1 (ha.mem_closure hs)

Depends on / 依赖: ha.mem_closure, mem_closure, mem_closure_iff_nhdsWithin_neBot
-/
theorem IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    NeBot (𝓝[s] a) :=
  mem_closure_iff_nhdsWithin_neBot.1 (ha.mem_closure hs)

/--
theorem `IsGLB.nhdsWithin_neBot` / 定理 `IsGLB.nhdsWithin_neBot`

English:
theorem IsGLB.nhdsWithin_neBot
  given: {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
  proof: IsLUB.nhdsWithin_neBot (α := αᵒᵈ) ha hs

中文:
定理 IsGLB.nhdsWithin_neBot
  条件: {a : α} {s : 集合 α} (ha : IsGLB s a) (hs : s.非空)
  证明: IsLUB.nhdsWithin_neBot (α := αᵒᵈ) ha hs

Depends on / 依赖: IsLUB.nhdsWithin_neBot, nhdsWithin_neBot
-/
theorem IsGLB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    NeBot (𝓝[s] a) :=
  IsLUB.nhdsWithin_neBot (α := αᵒᵈ) ha hs

/--
theorem `isLUB_of_mem_nhds` / 定理 `isLUB_of_mem_nhds`

English:
theorem isLUB_of_mem_nhds
  statement: {s : Set α} {a : α} {f : Filter α} (hsa : a in upperBounds s) (hsf : s in f)
  proof: ⟨hsa, fun b hb =>
    not_lt.1 fun hba =>
      have : s inter { a | b < a } in f ⊓ 𝓝 a := inter_mem_inf hsf (IsOpen.mem_nhds (isOpen_lt' _) hba)
      let ⟨_x, ⟨hxs, hxb⟩⟩ := Filter.nonempty_of_mem this
have : b < b := lt_of_lt_of_le hxb hb hxs
      lt_irrefl b this⟩

中文:
定理 isLUB_of_mem_nhds
  结论: {s : 集合 α} {a : α} {f : 滤子 α} (hsa : a in upperBounds s) (hsf : s in f)
  证明: ⟨hsa, fun b hb =>
    not_lt.1 fun hba =>
      have : s inter { a | b < a } in f ⊓ 𝓝 a := inter_mem_inf hsf (IsOpen.mem_nhds (isOpen_lt' _) hba)
      let ⟨_x, ⟨hxs, hxb⟩⟩ := Filter.nonempty_of_mem this
have : b < b := lt_of_lt_of_le hxb hb hxs
      lt_irrefl b this⟩

Depends on / 依赖: Filter, Filter.nonempty_of_mem, IsOpen, IsOpen.mem_nhds, inter_mem_inf, isOpen_lt, lt_irrefl, lt_of_lt_of_le, mem_nhds, nonempty_of_mem, not_lt
-/
theorem isLUB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a in upperBounds s) (hsf : s in f)
    [NeBot (f ⊓ 𝓝 a)] : IsLUB s a :=
  ⟨hsa, fun b hb =>
    not_lt.1 fun hba =>
      have : s inter { a | b < a } in f ⊓ 𝓝 a := inter_mem_inf hsf (IsOpen.mem_nhds (isOpen_lt' _) hba)
      let ⟨_x, ⟨hxs, hxb⟩⟩ := Filter.nonempty_of_mem this
have : b < b := lt_of_lt_of_le hxb hb hxs
      lt_irrefl b this⟩

/--
theorem `isLUB_of_mem_closure` / 定理 `isLUB_of_mem_closure`

English:
theorem isLUB_of_mem_closure
  given: {s : Set α} {a : α} (hsa : a in upperBounds s) (hsf : a in closure s)
  proof: by
  rw [mem_closure_iff_clusterPt]; rw [ClusterPt]; rw [inf_comm] at hsf
  exact isLUB_of_mem_nhds hsa (mem_principal_self s)

中文:
定理 isLUB_of_mem_closure
  条件: {s : 集合 α} {a : α} (hsa : a in upperBounds s) (hsf : a in closure s)
  证明: by
  rw [mem_closure_iff_clusterPt]; rw [ClusterPt]; rw [inf_comm] at hsf
  exact isLUB_of_mem_nhds hsa (mem_principal_self s)

Depends on / 依赖: ClusterPt, inf_comm, isLUB_of_mem_nhds, mem_closure_iff_clusterPt, mem_principal_self
-/
theorem isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a in upperBounds s) (hsf : a in closure s) :
    IsLUB s a := by
  rw [mem_closure_iff_clusterPt]; rw [ClusterPt]; rw [inf_comm] at hsf
  exact isLUB_of_mem_nhds hsa (mem_principal_self s)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isGLB_of_mem_nhds` / 定理 `isGLB_of_mem_nhds`

English:
theorem isGLB_of_mem_nhds
  statement: {s : Set α} {a : α} {f : Filter α} (hsa : a in lowerBounds s) (hsf : s in f)
  proof: isLUB_of_mem_nhds (α := αᵒᵈ) hsa hsf

中文:
定理 isGLB_of_mem_nhds
  结论: {s : 集合 α} {a : α} {f : 滤子 α} (hsa : a in lowerBounds s) (hsf : s in f)
  证明: isLUB_of_mem_nhds (α := αᵒᵈ) hsa hsf

Depends on / 依赖: isLUB_of_mem_nhds
-/
theorem isGLB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a in lowerBounds s) (hsf : s in f)
    [NeBot (f ⊓ 𝓝 a)] :
    IsGLB s a :=
  isLUB_of_mem_nhds (α := αᵒᵈ) hsa hsf

/--
theorem `isGLB_of_mem_closure` / 定理 `isGLB_of_mem_closure`

English:
theorem isGLB_of_mem_closure
  given: {s : Set α} {a : α} (hsa : a in lowerBounds s) (hsf : a in closure s)
  proof: isLUB_of_mem_closure (α := αᵒᵈ) hsa hsf

中文:
定理 isGLB_of_mem_closure
  条件: {s : 集合 α} {a : α} (hsa : a in lowerBounds s) (hsf : a in closure s)
  证明: isLUB_of_mem_closure (α := αᵒᵈ) hsa hsf

Depends on / 依赖: isLUB_of_mem_closure
-/
theorem isGLB_of_mem_closure {s : Set α} {a : α} (hsa : a in lowerBounds s) (hsf : a in closure s) :
    IsGLB s a :=
  isLUB_of_mem_closure (α := αᵒᵈ) hsa hsf

/--
theorem `IsLUB.mem_upperBounds_of_tendsto` / 定理 `IsLUB.mem_upperBounds_of_tendsto`

English:
theorem IsLUB.mem_upperBounds_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  replace ha := ha.inter_Ici_of_mem hx
  have := ha.nhdsWithin_neBot ⟨x, hx, le_rfl⟩
  refine ge_of_tendsto (hb.mono_left (nhdsWithin_mono a (inter_subset_left (t := Ici x)))) ?_
  exact mem_of_superset self_mem_nhdsWithin fun y hy => hf hx hy.1 hy.2

中文:
定理 IsLUB.mem_upperBounds_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ]
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  replace ha := ha.inter_Ici_of_mem hx
  have := ha.nhdsWithin_neBot ⟨x, hx, le_rfl⟩
  refine ge_of_tendsto (hb.mono_left (nhdsWithin_mono a (inter_subset_left (t := Ici x)))) ?_
  exact mem_of_superset self_mem_nhdsWithin fun y hy => hf hx hy.1 hy.2

Depends on / 依赖: ge_of_tendsto, ha.inter_Ici_of_mem, ha.nhdsWithin_neBot, hb.mono_left, inter_Ici_of_mem, inter_subset_left, le_rfl, mem_of_superset, mono_left, nhdsWithin_mono, nhdsWithin_neBot, replace, self_mem_nhdsWithin
-/
theorem IsLUB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLUB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in upperBounds (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  replace ha := ha.inter_Ici_of_mem hx
  have := ha.nhdsWithin_neBot ⟨x, hx, le_rfl⟩
  refine ge_of_tendsto (hb.mono_left (nhdsWithin_mono a (inter_subset_left (t := Ici x)))) ?_
  exact mem_of_superset self_mem_nhdsWithin fun y hy => hf hx hy.1 hy.2

-- For a version of this theorem in which the convergence considered on the domain `α` is as `x : α`
-- tends to infinity, rather than tending to a point `x` in `α`, see `isLUB_of_tendsto_atTop`
/--
theorem `IsLUB.isLUB_of_tendsto` / 定理 `IsLUB.isLUB_of_tendsto`

English:
theorem IsLUB.isLUB_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
  proof: haveI := ha.nhdsWithin_neBot hs
  ⟨ha.mem_upperBounds_of_tendsto hf hb, fun _b' hb' =>
    le_of_tendsto hb (mem_of_superset self_mem_nhdsWithin fun _ hx => hb' <| mem_image_of_mem _ hx)⟩

中文:
定理 IsLUB.isLUB_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ] {f : α -> γ}
  证明: haveI := ha.nhdsWithin_neBot hs
  ⟨ha.mem_upperBounds_of_tendsto hf hb, fun _b' hb' =>
    le_of_tendsto hb (mem_of_superset self_mem_nhdsWithin fun _ hx => hb' <| mem_image_of_mem _ hx)⟩

Depends on / 依赖: ha.mem_upperBounds_of_tendsto, ha.nhdsWithin_neBot, le_of_tendsto, mem_image_of_mem, mem_of_superset, mem_upperBounds_of_tendsto, nhdsWithin_neBot, self_mem_nhdsWithin
-/
theorem IsLUB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
    {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLUB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b :=
  haveI := ha.nhdsWithin_neBot hs
  ⟨ha.mem_upperBounds_of_tendsto hf hb, fun _b' hb' =>
    le_of_tendsto hb (mem_of_superset self_mem_nhdsWithin fun _ hx => hb' <| mem_image_of_mem _ hx)⟩

/--
theorem `IsGLB.mem_lowerBounds_of_tendsto` / 定理 `IsGLB.mem_lowerBounds_of_tendsto`

English:
theorem IsGLB.mem_lowerBounds_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
  proof: IsLUB.mem_upperBounds_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual ha hb

中文:
定理 IsGLB.mem_lowerBounds_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ]
  证明: IsLUB.mem_upperBounds_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual ha hb

Depends on / 依赖: IsLUB.mem_upperBounds_of_tendsto, hf.dual, mem_upperBounds_of_tendsto
-/
theorem IsGLB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsGLB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in lowerBounds (f '' s) :=
  IsLUB.mem_upperBounds_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual ha hb

-- For a version of this theorem in which the convergence considered on the domain `α` is as
-- `x : α` tends to negative infinity, rather than tending to a point `x` in `α`, see
-- `isGLB_of_tendsto_atBot`
@[to_dual existing]
/--
theorem `IsGLB.isGLB_of_tendsto` / 定理 `IsGLB.isGLB_of_tendsto`

English:
theorem IsGLB.isGLB_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
  proof: IsLUB.isLUB_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual

中文:
定理 IsGLB.isGLB_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ] {f : α -> γ}
  证明: IsLUB.isLUB_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual

Depends on / 依赖: IsLUB.isLUB_of_tendsto, hf.dual, isLUB_of_tendsto
-/
theorem IsGLB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
    {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) :
    IsGLB s a -> s.Nonempty -> Tendsto f (𝓝[s] a) (𝓝 b) -> IsGLB (f '' s) b :=
  IsLUB.isLUB_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual

/--
theorem `IsLUB.mem_lowerBounds_of_tendsto` / 定理 `IsLUB.mem_lowerBounds_of_tendsto`

English:
theorem IsLUB.mem_lowerBounds_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
  proof: IsLUB.mem_upperBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

中文:
定理 IsLUB.mem_lowerBounds_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ]
  证明: IsLUB.mem_upperBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

Depends on / 依赖: IsLUB.mem_upperBounds_of_tendsto, mem_upperBounds_of_tendsto
-/
theorem IsLUB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLUB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in lowerBounds (f '' s) :=
  IsLUB.mem_upperBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

/--
theorem `IsLUB.isGLB_of_tendsto` / 定理 `IsLUB.isGLB_of_tendsto`

English:
theorem IsLUB.isGLB_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
  proof: IsLUB.isLUB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

中文:
定理 IsLUB.isGLB_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ] {f : α -> γ}
  证明: IsLUB.isLUB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

Depends on / 依赖: IsLUB.isLUB_of_tendsto, isLUB_of_tendsto
-/
theorem IsLUB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
    {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLUB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsGLB (f '' s) b :=
  IsLUB.isLUB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

/--
theorem `IsGLB.mem_upperBounds_of_tendsto` / 定理 `IsGLB.mem_upperBounds_of_tendsto`

English:
theorem IsGLB.mem_upperBounds_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
  proof: IsGLB.mem_lowerBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

中文:
定理 IsGLB.mem_upperBounds_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ]
  证明: IsGLB.mem_lowerBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

Depends on / 依赖: IsGLB.mem_lowerBounds_of_tendsto, mem_lowerBounds_of_tendsto
-/
theorem IsGLB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGLB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in upperBounds (f '' s) :=
  IsGLB.mem_lowerBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

/--
theorem `IsGLB.isLUB_of_tendsto` / 定理 `IsGLB.isLUB_of_tendsto`

English:
theorem IsGLB.isLUB_of_tendsto
  statement: [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
  proof: IsGLB.isGLB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

中文:
定理 IsGLB.isLUB_of_tendsto
  结论: [预序 γ] [拓扑空间 γ] [OrderClosed拓扑 γ] {f : α -> γ}
  证明: IsGLB.isGLB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

Depends on / 依赖: IsGLB.isGLB_of_tendsto, isGLB_of_tendsto
-/
theorem IsGLB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ}
    {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGLB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b :=
  IsGLB.isGLB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

/--
theorem `IsLUB.mem_of_isClosed` / 定理 `IsLUB.mem_of_isClosed`

English:
theorem IsLUB.mem_of_isClosed
  statement: {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
  proof: sc.closure_subset ha.mem_closure hs

alias IsClosed.isLUB_mem := IsLUB.mem_of_isClosed

中文:
定理 IsLUB.mem_of_isClosed
  结论: {a : α} {s : 集合 α} (ha : IsLUB s a) (hs : s.非空)
  证明: sc.closure_subset ha.mem_closure hs

alias IsClosed.isLUB_mem := IsLUB.mem_of_isClosed

Depends on / 依赖: closure_subset, ha.mem_closure, mem_closure, sc.closure_subset
-/
theorem IsLUB.mem_of_isClosed {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
    (sc : IsClosed s) : a in s :=
sc.closure_subset ha.mem_closure hs

alias IsClosed.isLUB_mem := IsLUB.mem_of_isClosed

/--
theorem `IsGLB.mem_of_isClosed` / 定理 `IsGLB.mem_of_isClosed`

English:
theorem IsGLB.mem_of_isClosed
  statement: {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
  proof: sc.closure_subset ha.mem_closure hs

alias IsClosed.isGLB_mem := IsGLB.mem_of_isClosed

中文:
定理 IsGLB.mem_of_isClosed
  结论: {a : α} {s : 集合 α} (ha : IsGLB s a) (hs : s.非空)
  证明: sc.closure_subset ha.mem_closure hs

alias IsClosed.isGLB_mem := IsGLB.mem_of_isClosed

Depends on / 依赖: closure_subset, ha.mem_closure, mem_closure, sc.closure_subset
-/
theorem IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
    (sc : IsClosed s) : a in s :=
sc.closure_subset ha.mem_closure hs

alias IsClosed.isGLB_mem := IsGLB.mem_of_isClosed

/--
theorem `isLUB_iff_of_subset_of_subset_closure` / 定理 `isLUB_iff_of_subset_of_subset_closure`

English:
theorem isLUB_iff_of_subset_of_subset_closure
  statement: {α : Type*} [TopologicalSpace α] [Preorder α]
  proof: isLUB_congr (upperBounds_closure (s := s) ▸ upperBounds_mono_set hts).antisymm
    upperBounds_mono_set hst

中文:
定理 isLUB_iff_of_subset_of_subset_closure
  结论: {α : 类型} [拓扑空间 α] [预序 α]
  证明: isLUB_congr (upperBounds_closure (s := s) ▸ upperBounds_mono_set hts).antisymm
    upperBounds_mono_set hst

Depends on / 依赖: antisymm, isLUB_congr, upperBounds_closure, upperBounds_mono_set
-/
theorem isLUB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIicTopology α] {s t : Set α} (hst : s subseteq t) (hts : t subseteq closure s) {x : α} :
    IsLUB s x ↔ IsLUB t x :=
isLUB_congr (upperBounds_closure (s := s) ▸ upperBounds_mono_set hts).antisymm
    upperBounds_mono_set hst

/--
theorem `isGLB_iff_of_subset_of_subset_closure` / 定理 `isGLB_iff_of_subset_of_subset_closure`

English:
theorem isGLB_iff_of_subset_of_subset_closure
  statement: {α : Type*} [TopologicalSpace α] [Preorder α]
  proof: isLUB_iff_of_subset_of_subset_closure (α := αᵒᵈ) hst hts

中文:
定理 isGLB_iff_of_subset_of_subset_closure
  结论: {α : 类型} [拓扑空间 α] [预序 α]
  证明: isLUB_iff_of_subset_of_subset_closure (α := αᵒᵈ) hst hts

Depends on / 依赖: isLUB_iff_of_subset_of_subset_closure
-/
theorem isGLB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] {s t : Set α} (hst : s subseteq t) (hts : t subseteq closure s) {x : α} :
    IsGLB s x ↔ IsGLB t x :=
  isLUB_iff_of_subset_of_subset_closure (α := αᵒᵈ) hst hts

/--
theorem `Dense.isLUB_inter_iff` / 定理 `Dense.isLUB_inter_iff`

English:
theorem Dense.isLUB_inter_iff
  statement: {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α]
  proof: isLUB_iff_of_subset_of_subset_closure (by simp) hs.open_subset_closure_inter ht

中文:
定理 稠密.isLUB_inter_iff
  结论: {α : 类型} [拓扑空间 α] [预序 α] [ClosedIic拓扑 α]
  证明: isLUB_iff_of_subset_of_subset_closure (by simp) hs.open_subset_closure_inter ht

Depends on / 依赖: hs.open_subset_closure_inter, isLUB_iff_of_subset_of_subset_closure, open_subset_closure_inter
-/
theorem Dense.isLUB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsLUB (t inter s) x ↔ IsLUB t x :=
isLUB_iff_of_subset_of_subset_closure (by simp) hs.open_subset_closure_inter ht

/--
theorem `Dense.isGLB_inter_iff` / 定理 `Dense.isGLB_inter_iff`

English:
theorem Dense.isGLB_inter_iff
  statement: {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIciTopology α]
  proof: hs.isLUB_inter_iff (α := αᵒᵈ) ht

中文:
定理 稠密.isGLB_inter_iff
  结论: {α : 类型} [拓扑空间 α] [预序 α] [ClosedIci拓扑 α]
  证明: hs.isLUB_inter_iff (α := αᵒᵈ) ht

Depends on / 依赖: hs.isLUB_inter_iff, isLUB_inter_iff
-/
theorem Dense.isGLB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIciTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsGLB (t inter s) x ↔ IsGLB t x :=
  hs.isLUB_inter_iff (α := αᵒᵈ) ht

/--
theorem `Dense.upperBounds_image` / 定理 `Dense.upperBounds_image`

English:
theorem Dense.upperBounds_image
  statement: {α : Type*} [TopologicalSpace α] [Preorder α]
  proof: by
  refine subset_antisymm ?_ fun _ => upperBounds_mono (Set.image_subset_range f S) le_rfl
  refine subset_trans ?_ fun _ => upperBounds_mono (hf.range_subset_closure_image_dense hS) le_rfl
  intro x hx i hi
  rw [mem_closure_iff_frequently] at hi
  exact (hi.mono hx).mem_of_closed isClosed_Iic

中文:
定理 稠密.upperBounds_image
  结论: {α : 类型} [拓扑空间 α] [预序 α]
  证明: by
  refine subset_antisymm ?_ fun _ => upperBounds_mono (Set.image_subset_range f S) le_rfl
  refine subset_trans ?_ fun _ => upperBounds_mono (hf.range_subset_closure_image_dense hS) le_rfl
  intro x hx i hi
  rw [mem_closure_iff_frequently] at hi
  exact (hi.mono hx).mem_of_closed isClosed_Iic

Depends on / 依赖: Set.image_subset_range, hf.range_subset_closure_image_dense, hi.mono, image_subset_range, isClosed_Iic, le_rfl, mem_closure_iff_frequently, mem_of_closed, range_subset_closure_image_dense, subset_antisymm, subset_trans, upperBounds_mono
-/
theorem Dense.upperBounds_image {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S)
    (hf : Continuous f) :
    upperBounds (f '' S) = upperBounds (range f) := by
  refine subset_antisymm ?_ fun _ => upperBounds_mono (Set.image_subset_range f S) le_rfl
  refine subset_trans ?_ fun _ => upperBounds_mono (hf.range_subset_closure_image_dense hS) le_rfl
  intro x hx i hi
  rw [mem_closure_iff_frequently] at hi
  exact (hi.mono hx).mem_of_closed isClosed_Iic

/--
theorem `Dense.lowerBounds_image` / 定理 `Dense.lowerBounds_image`

English:
theorem Dense.lowerBounds_image
  statement: {α : Type*} [TopologicalSpace α] [Preorder α]
  proof: hS.upperBounds_image (α := αᵒᵈ) hf

中文:
定理 稠密.lowerBounds_image
  结论: {α : 类型} [拓扑空间 α] [预序 α]
  证明: hS.upperBounds_image (α := αᵒᵈ) hf

Depends on / 依赖: hS.upperBounds_image, upperBounds_image
-/
theorem Dense.lowerBounds_image {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S)
    (hf : Continuous f) :
    lowerBounds (f '' S) = lowerBounds (range f) :=
  hS.upperBounds_image (α := αᵒᵈ) hf

/--
theorem `Dense.ciSup` / 定理 `Dense.ciSup`

English:
theorem Dense.ciSup
  statement: {α : Type*} [TopologicalSpace α]
  proof: by
  rw [← sSup_range]; rw [← sSup_range]
  obtain (_ | _) := isEmpty_or_nonempty γ
  · simp [Set.range_eq_empty]
  refine ((isLUB_csSup (range_nonempty f) h).unique ?_).symm
  refine (isLUB_congr (hS.upperBounds_image hf)).mp (isLUB_ciSup_set ?_ hS.nonempty)
  exact h.mono (by grind)

中文:
定理 稠密.ciSup
  结论: {α : 类型} [拓扑空间 α]
  证明: by
  rw [← sSup_range]; rw [← sSup_range]
  obtain (_ | _) := isEmpty_or_nonempty γ
  · simp [Set.range_eq_empty]
  refine ((isLUB_csSup (range_nonempty f) h).unique ?_).symm
  refine (isLUB_congr (hS.upperBounds_image hf)).mp (isLUB_ciSup_set ?_ hS.nonempty)
  exact h.mono (by grind)

Depends on / 依赖: Set.range_eq_empty, h.mono, hS.nonempty, hS.upperBounds_image, isEmpty_or_nonempty, isLUB_ciSup_set, isLUB_congr, isLUB_csSup, nonempty, range_eq_empty, range_nonempty, sSup_range, unique, upperBounds_image
-/
theorem Dense.ciSup {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLattice α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) (h : BddAbove (range f)) :
    ⨆ s : S, f s = ⨆ i, f i := by
  rw [← sSup_range]; rw [← sSup_range]
  obtain (_ | _) := isEmpty_or_nonempty γ
  · simp [Set.range_eq_empty]
  refine ((isLUB_csSup (range_nonempty f) h).unique ?_).symm
  refine (isLUB_congr (hS.upperBounds_image hf)).mp (isLUB_ciSup_set ?_ hS.nonempty)
  exact h.mono (by grind)

/--
theorem `Dense.ciInf` / 定理 `Dense.ciInf`

English:
theorem Dense.ciInf
  statement: {α : Type*} [TopologicalSpace α]
  proof: hS.ciSup (α := αᵒᵈ) hf h

中文:
定理 稠密.ciInf
  结论: {α : 类型} [拓扑空间 α]
  证明: hS.ciSup (α := αᵒᵈ) hf h

Depends on / 依赖: hS.ciSup
-/
theorem Dense.ciInf {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLattice α] [ClosedIciTopology α] {f : γ -> α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) (h : BddBelow (range f)) :
    ⨅ s : S, f s = ⨅ i, f i :=
  hS.ciSup (α := αᵒᵈ) hf h

/--
theorem `Dense.ciSup'` / 定理 `Dense.ciSup'`

English:
theorem Dense.ciSup'
  statement: {α : Type*} [TopologicalSpace α]
  proof: by
  by_cases h : BddAbove (range (fun x : S => f x))
· refine hS.ciSup hf h.closure.mono ?_
    simpa [← Function.comp_def, range_comp] using hf.range_subset_closure_image_dense hS
  · suffices ¬ BddAbove (range f) by simp [ciSup_of_not_bddAbove, this, h]
    contrapose h
    grind [h.mono]

中文:
定理 稠密.ciSup'
  结论: {α : 类型} [拓扑空间 α]
  证明: by
  by_cases h : BddAbove (range (fun x : S => f x))
· refine hS.ciSup hf h.closure.mono ?_
    simpa [← Function.comp_def, range_comp] using hf.range_subset_closure_image_dense hS
  · suffices ¬ BddAbove (range f) by simp [ciSup_of_not_bddAbove, this, h]
    contrapose h
    grind [h.mono]

Depends on / 依赖: BddAbove, Function, Function.comp_def, ciSup_of_not_bddAbove, closure, comp_def, contrapose, h.closure.mono, h.mono, hS.ciSup, hf.range_subset_closure_image_dense, range_comp, range_subset_closure_image_dense
-/
theorem Dense.ciSup' {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) :
    ⨆ s : S, f s = ⨆ i, f i := by
  by_cases h : BddAbove (range (fun x : S => f x))
· refine hS.ciSup hf h.closure.mono ?_
    simpa [← Function.comp_def, range_comp] using hf.range_subset_closure_image_dense hS
  · suffices ¬ BddAbove (range f) by simp [ciSup_of_not_bddAbove, this, h]
    contrapose h
    grind [h.mono]

/--
theorem `Dense.ciInf'` / 定理 `Dense.ciInf'`

English:
theorem Dense.ciInf'
  statement: {α : Type*} [TopologicalSpace α]
  proof: hS.ciSup' (α := αᵒᵈ) hf

中文:
定理 稠密.ciInf'
  结论: {α : 类型} [拓扑空间 α]
  证明: hS.ciSup' (α := αᵒᵈ) hf

Depends on / 依赖: hS.ciSup
-/
theorem Dense.ciInf' {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [ClosedIciTopology α] {f : γ -> α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) :
    ⨅ s : S, f s = ⨅ i, f i :=
  hS.ciSup' (α := αᵒᵈ) hf

section ConditionallyCompleteLinearOrder

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/--
lemma `ConditionallyCompleteLinearOrder.isCompact_Icc` / 引理 `ConditionallyCompleteLinearOrder.isCompact_Icc`

English:
lemma ConditionallyCompleteLinearOrder.isCompact_Icc
  given: (a b : α)
  proof: by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff]
  refine (le_or_gt a b).elim (fun _ f hfab => ?_) (by simp [·])
  by_contra! hf
  have hpt : forall x in Icc a b, {x} ∉ f := fun x hx _ => hf x hx (le_trans (by simpa) (pure_le_nhds x))
  set s := { x in Icc a b | Icc a x ∉ f }
  have hsb : b in upperBounds s := fun x hx => hx.1.2
  have ha : a in s := by simp [s, *]
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup ⟨a, ha⟩ ⟨b, hsb⟩
  have hc : c in Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  have (i : _) (hic : i < c) : Ioi i in f := by
    have ⟨j, hj, hij, hjc⟩ := hsc.exists_between hic
    filter_upwards [f.compl_mem_iff_notMem.mpr hj.2, hfab]; grind
  have ⟨x, hx, hxf⟩ : exists x, c < x ∧ Iio x ∉ f := by simpa [nhds_eq_order, eq_true this] using hf c hc
  have : Icc a c ∉ f := mt (mem_of_superset · (by grind)) hxf
  have : x in Icc a b := ⟨by grind, le_of_not_gt fun h => hxf (mem_of_superset hfab (by grind))⟩
  have : Icc a x in f := by simpa [s, this.1, this.2] using notMem_of_csSup_lt hx ⟨b, hsb⟩
  exact hpt _ ‹_› (by filter_upwards [f.compl_mem_iff_notMem.mpr hxf, this]; grind)

中文:
引理 条件完备线性序.isCompact_Icc
  条件: (a b : α)
  证明: by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff]
  refine (le_or_gt a b).elim (fun _ f hfab => ?_) (by simp [·])
  by_contra! hf
  have hpt : forall x in Icc a b, {x} ∉ f := fun x hx _ => hf x hx (le_trans (by simpa) (pure_le_nhds x))
  set s := { x in Icc a b | Icc a x ∉ f }
  have hsb : b in upperBounds s := fun x hx => hx.1.2
  have ha : a in s := by simp [s, *]
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup ⟨a, ha⟩ ⟨b, hsb⟩
  have hc : c in Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  have (i : _) (hic : i < c) : Ioi i in f := by
    have ⟨j, hj, hij, hjc⟩ := hsc.exists_between hic
    filter_upwards [f.compl_mem_iff_notMem.mpr hj.2, hfab]; grind
  have ⟨x, hx, hxf⟩ : exists x, c < x ∧ Iio x ∉ f := by simpa [nhds_eq_order, eq_true this] using hf c hc
  have : Icc a c ∉ f := mt (mem_of_superset · (by grind)) hxf
  have : x in Icc a b := ⟨by grind, le_of_not_gt fun h => hxf (mem_of_superset hfab (by grind))⟩
  have : Icc a x in f := by simpa [s, this.1, this.2] using notMem_of_csSup_lt hx ⟨b, hsb⟩
  exact hpt _ ‹_› (by filter_upwards [f.compl_mem_iff_notMem.mpr hxf, this]; grind)
-/
protected lemma ConditionallyCompleteLinearOrder.isCompact_Icc (a b : α) :
    IsCompact (Icc a b) := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff]
  refine (le_or_gt a b).elim (fun _ f hfab => ?_) (by simp [·])
  by_contra! hf
  have hpt : forall x in Icc a b, {x} ∉ f := fun x hx _ => hf x hx (le_trans (by simpa) (pure_le_nhds x))
  set s := { x in Icc a b | Icc a x ∉ f }
  have hsb : b in upperBounds s := fun x hx => hx.1.2
  have ha : a in s := by simp [s, *]
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup ⟨a, ha⟩ ⟨b, hsb⟩
  have hc : c in Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  have (i : _) (hic : i < c) : Ioi i in f := by
    have ⟨j, hj, hij, hjc⟩ := hsc.exists_between hic
    filter_upwards [f.compl_mem_iff_notMem.mpr hj.2, hfab]; grind
  have ⟨x, hx, hxf⟩ : exists x, c < x ∧ Iio x ∉ f := by simpa [nhds_eq_order, eq_true this] using hf c hc
  have : Icc a c ∉ f := mt (mem_of_superset · (by grind)) hxf
  have : x in Icc a b := ⟨by grind, le_of_not_gt fun h => hxf (mem_of_superset hfab (by grind))⟩
  have : Icc a x in f := by simpa [s, this.1, this.2] using notMem_of_csSup_lt hx ⟨b, hsb⟩
  exact hpt _ ‹_› (by filter_upwards [f.compl_mem_iff_notMem.mpr hxf, this]; grind)

/--
lemma `upperClosure_eq_Ici_csInf` / 引理 `upperClosure_eq_Ici_csInf`

English:
lemma upperClosure_eq_Ici_csInf
  given: {s : Set α} (h₁ : s.Nonempty) (h₂ : BddBelow s) (hs : IsClosed s)
  proof: Set.ext fun _ => ⟨fun ⟨_, h, h'⟩ => csInf_le_of_le h₂ h h',
    (⟨_, (isGLB_csInf h₁ h₂).mem_of_isClosed h₁ hs, ·⟩)⟩

中文:
引理 upperClosure_eq_Ici_csInf
  条件: {s : 集合 α} (h₁ : s.非空) (h₂ : BddBelow s) (hs : 是闭集 s)
  证明: Set.ext fun _ => ⟨fun ⟨_, h, h'⟩ => csInf_le_of_le h₂ h h',
    (⟨_, (isGLB_csInf h₁ h₂).mem_of_isClosed h₁ hs, ·⟩)⟩

Depends on / 依赖: Set.ext, csInf_le_of_le, isGLB_csInf, mem_of_isClosed
-/
lemma upperClosure_eq_Ici_csInf {s : Set α} (h₁ : s.Nonempty) (h₂ : BddBelow s) (hs : IsClosed s) :
    upperClosure s = Ici (sInf s) :=
  Set.ext fun _ => ⟨fun ⟨_, h, h'⟩ => csInf_le_of_le h₂ h h',
    (⟨_, (isGLB_csInf h₁ h₂).mem_of_isClosed h₁ hs, ·⟩)⟩

/--
lemma `lowerClosure_eq_Iic_csSup` / 引理 `lowerClosure_eq_Iic_csSup`

English:
lemma lowerClosure_eq_Iic_csSup
  given: {s : Set α} (h₁ : s.Nonempty) (h₂ : BddAbove s) (hs : IsClosed s)
  proof: upperClosure_eq_Ici_csInf (α := αᵒᵈ) h₁ h₂ hs

中文:
引理 lowerClosure_eq_Iic_csSup
  条件: {s : 集合 α} (h₁ : s.非空) (h₂ : BddAbove s) (hs : 是闭集 s)
  证明: upperClosure_eq_Ici_csInf (α := αᵒᵈ) h₁ h₂ hs

Depends on / 依赖: upperClosure_eq_Ici_csInf
-/
lemma lowerClosure_eq_Iic_csSup {s : Set α} (h₁ : s.Nonempty) (h₂ : BddAbove s) (hs : IsClosed s) :
    lowerClosure s = Iic (sSup s) :=
  upperClosure_eq_Ici_csInf (α := αᵒᵈ) h₁ h₂ hs

/--
lemma `IsClosed.upperClosure` / 引理 `IsClosed.upperClosure`

English:
lemma IsClosed.upperClosure
  given: {s : Set α} (hs : IsClosed s)
  proof: by
  obtain rfl | h₁ := s.eq_empty_or_nonempty
  · simp
  by_cases h₂ : BddBelow s
  · exact upperClosure_eq_Ici_csInf h₁ h₂ hs ▸ isClosed_Ici
  · exact upperClosure_eq_bot h₂ ▸ isClosed_univ

中文:
引理 是闭集.upperClosure
  条件: {s : 集合 α} (hs : 是闭集 s)
  证明: by
  obtain rfl | h₁ := s.eq_empty_or_nonempty
  · simp
  by_cases h₂ : BddBelow s
  · exact upperClosure_eq_Ici_csInf h₁ h₂ hs ▸ isClosed_Ici
  · exact upperClosure_eq_bot h₂ ▸ isClosed_univ
-/
protected lemma IsClosed.upperClosure {s : Set α} (hs : IsClosed s) :
    IsClosed (upperClosure s : Set α) := by
  obtain rfl | h₁ := s.eq_empty_or_nonempty
  · simp
  by_cases h₂ : BddBelow s
  · exact upperClosure_eq_Ici_csInf h₁ h₂ hs ▸ isClosed_Ici
  · exact upperClosure_eq_bot h₂ ▸ isClosed_univ

/--
lemma `IsClosed.lowerClosure` / 引理 `IsClosed.lowerClosure`

English:
lemma IsClosed.lowerClosure
  given: {s : Set α} (hs : IsClosed s)
  proof: IsClosed.upperClosure (α := αᵒᵈ) hs

中文:
引理 是闭集.lowerClosure
  条件: {s : 集合 α} (hs : 是闭集 s)
  证明: IsClosed.upperClosure (α := αᵒᵈ) hs
-/
protected lemma IsClosed.lowerClosure {s : Set α} (hs : IsClosed s) :
    IsClosed (lowerClosure s).1 :=
  IsClosed.upperClosure (α := αᵒᵈ) hs

end ConditionallyCompleteLinearOrder


/--
theorem `IsLUB.exists_seq_strictMono_tendsto_of_notMem` / 定理 `IsLUB.exists_seq_strictMono_tendsto_of_notMem`

English:
theorem IsLUB.exists_seq_strictMono_tendsto_of_notMem
  statement: {t : Set α} {x : α}
  proof: by
  obtain ⟨v, hvx, hvt⟩ := exists_seq_forall_of_frequently (htx.frequently_mem ht)
  replace hvx := hvx.mono_right nhdsWithin_le_nhds
  have hvx' : forall {n}, v n < x := (htx.1 (hvt _)).lt_of_ne (ne_of_mem_of_not_mem (hvt _) notMem)
  have : forall k, forallᶠ l in atTop, v k < v l := fun k => hvx.eventually (lt_mem_nhds hvx')
  choose N hN hvN using fun k => ((eventually_gt_atTop k).and (this k)).exists
  refine ⟨fun k => v (N^[k] 0), strictMono_nat_of_lt_succ fun _ => ?_, fun _ => hvx',
    hvx.comp (strictMono_nat_of_lt_succ fun _ => ?_).tendsto_atTop, fun _ => hvt _⟩
  · rw [iterate_succ_apply']; exact hvN _
  · rw [iterate_succ_apply']; exact hN _

中文:
定理 IsLUB.存在_seq_strictMono_tendsto_of_notMem
  结论: {t : 集合 α} {x : α}
  证明: by
  obtain ⟨v, hvx, hvt⟩ := exists_seq_forall_of_frequently (htx.frequently_mem ht)
  replace hvx := hvx.mono_right nhdsWithin_le_nhds
  have hvx' : forall {n}, v n < x := (htx.1 (hvt _)).lt_of_ne (ne_of_mem_of_not_mem (hvt _) notMem)
  have : forall k, forallᶠ l in atTop, v k < v l := fun k => hvx.eventually (lt_mem_nhds hvx')
  choose N hN hvN using fun k => ((eventually_gt_atTop k).and (this k)).exists
  refine ⟨fun k => v (N^[k] 0), strictMono_nat_of_lt_succ fun _ => ?_, fun _ => hvx',
    hvx.comp (strictMono_nat_of_lt_succ fun _ => ?_).tendsto_atTop, fun _ => hvt _⟩
  · rw [iterate_succ_apply']; exact hvN _
  · rw [iterate_succ_apply']; exact hN _

Depends on / 依赖: eventually, eventually_gt_atTop, exists_seq_forall_of_frequently, frequently_mem, htx.frequently_mem, hvx.comp, hvx.eventually, hvx.mono_right, lt_mem_nhds, lt_of_ne, mono_right, ne_of_mem_of_not_mem, nhdsWithin_le_nhds, notMem, replace, strict, strictMono_nat_of_lt_succ
-/
theorem IsLUB.exists_seq_strictMono_tendsto_of_notMem {t : Set α} {x : α}
    [IsCountablyGenerated (𝓝 x)] (htx : IsLUB t x) (notMem : x ∉ t) (ht : t.Nonempty) :
    exists u : Nat -> α, StrictMono u ∧ (forall n, u n < x) ∧ Tendsto u atTop (𝓝 x) ∧ forall n, u n in t := by
  obtain ⟨v, hvx, hvt⟩ := exists_seq_forall_of_frequently (htx.frequently_mem ht)
  replace hvx := hvx.mono_right nhdsWithin_le_nhds
  have hvx' : forall {n}, v n < x := (htx.1 (hvt _)).lt_of_ne (ne_of_mem_of_not_mem (hvt _) notMem)
  have : forall k, forallᶠ l in atTop, v k < v l := fun k => hvx.eventually (lt_mem_nhds hvx')
  choose N hN hvN using fun k => ((eventually_gt_atTop k).and (this k)).exists
  refine ⟨fun k => v (N^[k] 0), strictMono_nat_of_lt_succ fun _ => ?_, fun _ => hvx',
    hvx.comp (strictMono_nat_of_lt_succ fun _ => ?_).tendsto_atTop, fun _ => hvt _⟩
  · rw [iterate_succ_apply']; exact hvN _
  · rw [iterate_succ_apply']; exact hN _

/--
theorem `IsLUB.exists_seq_monotone_tendsto` / 定理 `IsLUB.exists_seq_monotone_tendsto`

English:
theorem IsLUB.exists_seq_monotone_tendsto
  statement: {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
  proof: by
  by_cases h : x in t
  · exact ⟨fun _ => x, monotone_const, fun n => le_rfl, tendsto_const_nhds, fun _ => h⟩
  · rcases htx.exists_seq_strictMono_tendsto_of_notMem h ht with ⟨u, hu⟩
    exact ⟨u, hu.1.monotone, fun n => (hu.2.1 n).le, hu.2.2⟩

中文:
定理 IsLUB.存在_seq_monotone_tendsto
  结论: {t : 集合 α} {x : α} [是余untablyGenerated (𝓝 x)]
  证明: by
  by_cases h : x in t
  · exact ⟨fun _ => x, monotone_const, fun n => le_rfl, tendsto_const_nhds, fun _ => h⟩
  · rcases htx.exists_seq_strictMono_tendsto_of_notMem h ht with ⟨u, hu⟩
    exact ⟨u, hu.1.monotone, fun n => (hu.2.1 n).le, hu.2.2⟩

Depends on / 依赖: exists_seq_strictMono_tendsto_of_notMem, htx.exists_seq_strictMono_tendsto_of_notMem, le_rfl, monotone, monotone_const, tendsto_const_nhds
-/
theorem IsLUB.exists_seq_monotone_tendsto {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
    (htx : IsLUB t x) (ht : t.Nonempty) :
    exists u : Nat -> α, Monotone u ∧ (forall n, u n <= x) ∧ Tendsto u atTop (𝓝 x) ∧ forall n, u n in t := by
  by_cases h : x in t
  · exact ⟨fun _ => x, monotone_const, fun n => le_rfl, tendsto_const_nhds, fun _ => h⟩
  · rcases htx.exists_seq_strictMono_tendsto_of_notMem h ht with ⟨u, hu⟩
    exact ⟨u, hu.1.monotone, fun n => (hu.2.1 n).le, hu.2.2⟩

/--
theorem `exists_seq_strictMono_tendsto'` / 定理 `exists_seq_strictMono_tendsto'`

English:
theorem exists_seq_strictMono_tendsto'
  statement: {α : Type*} [LinearOrder α] [TopologicalSpace α]
  proof: by
  have hx : x ∉ Ioo y x := fun h => (lt_irrefl x h.2).elim
  have ht : Set.Nonempty (Ioo y x) := nonempty_Ioo.2 hy
  rcases (isLUB_Ioo hy).exists_seq_strictMono_tendsto_of_notMem hx ht with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2.symm⟩

中文:
定理 存在_seq_strictMono_tendsto'
  结论: {α : 类型} [线性序 α] [拓扑空间 α]
  证明: by
  have hx : x ∉ Ioo y x := fun h => (lt_irrefl x h.2).elim
  have ht : Set.Nonempty (Ioo y x) := nonempty_Ioo.2 hy
  rcases (isLUB_Ioo hy).exists_seq_strictMono_tendsto_of_notMem hx ht with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2.symm⟩

Depends on / 依赖: Nonempty, Set.Nonempty, exists_seq_strictMono_tendsto_of_notMem, isLUB_Ioo, lt_irrefl, nonempty_Ioo
-/
theorem exists_seq_strictMono_tendsto' {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [DenselyOrdered α] [OrderTopology α] [FirstCountableTopology α] {x y : α} (hy : y < x) :
    exists u : Nat -> α, StrictMono u ∧ (forall n, u n in Ioo y x) ∧ Tendsto u atTop (𝓝 x) := by
  have hx : x ∉ Ioo y x := fun h => (lt_irrefl x h.2).elim
  have ht : Set.Nonempty (Ioo y x) := nonempty_Ioo.2 hy
  rcases (isLUB_Ioo hy).exists_seq_strictMono_tendsto_of_notMem hx ht with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2.symm⟩

/--
theorem `exists_seq_strictMono_tendsto` / 定理 `exists_seq_strictMono_tendsto`

English:
theorem exists_seq_strictMono_tendsto
  statement: [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α]
  proof: by
  obtain ⟨y, hy⟩ : exists y, y < x := exists_lt x
  rcases exists_seq_strictMono_tendsto' hy with ⟨u, hu_mono, hu_mem, hux⟩
  exact ⟨u, hu_mono, fun n => (hu_mem n).2, hux⟩

中文:
定理 存在_seq_strictMono_tendsto
  结论: [稠密序 α] [NoMin序 α] [第一可数拓扑 α]
  证明: by
  obtain ⟨y, hy⟩ : exists y, y < x := exists_lt x
  rcases exists_seq_strictMono_tendsto' hy with ⟨u, hu_mono, hu_mem, hux⟩
  exact ⟨u, hu_mono, fun n => (hu_mem n).2, hux⟩

Depends on / 依赖: exists_lt, exists_seq_strictMono_tendsto, hu_mem, hu_mono
-/
theorem exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α]
    (x : α) : exists u : Nat -> α, StrictMono u ∧ (forall n, u n < x) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ : exists y, y < x := exists_lt x
  rcases exists_seq_strictMono_tendsto' hy with ⟨u, hu_mono, hu_mem, hux⟩
  exact ⟨u, hu_mono, fun n => (hu_mem n).2, hux⟩

/--
theorem `exists_seq_strictMono_tendsto_nhdsWithin` / 定理 `exists_seq_strictMono_tendsto_nhdsWithin`

English:
theorem exists_seq_strictMono_tendsto_nhdsWithin
  statement: [DenselyOrdered α] [NoMinOrder α]
  proof: let ⟨u, hu, hx, h⟩ := exists_seq_strictMono_tendsto x
⟨u, hu, hx, tendsto_nhdsWithin_mono_right (range_subset_iff.2 hx) tendsto_nhdsWithin_range.2 h⟩

中文:
定理 存在_seq_strictMono_tendsto_nhdsWithin
  结论: [稠密序 α] [NoMin序 α]
  证明: let ⟨u, hu, hx, h⟩ := exists_seq_strictMono_tendsto x
⟨u, hu, hx, tendsto_nhdsWithin_mono_right (range_subset_iff.2 hx) tendsto_nhdsWithin_range.2 h⟩

Depends on / 依赖: exists_seq_strictMono_tendsto, range_subset_iff, tendsto_nhdsWithin_mono_right, tendsto_nhdsWithin_range
-/
theorem exists_seq_strictMono_tendsto_nhdsWithin [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] (x : α) :
    exists u : Nat -> α, StrictMono u ∧ (forall n, u n < x) ∧ Tendsto u atTop (𝓝[<] x) :=
  let ⟨u, hu, hx, h⟩ := exists_seq_strictMono_tendsto x
⟨u, hu, hx, tendsto_nhdsWithin_mono_right (range_subset_iff.2 hx) tendsto_nhdsWithin_range.2 h⟩

/--
theorem `exists_seq_tendsto_sSup` / 定理 `exists_seq_tendsto_sSup`

English:
theorem exists_seq_tendsto_sSup
  statement: {α : Type*} [ConditionallyCompleteLinearOrder α]
  proof: by
  rcases (isLUB_csSup hS hS').exists_seq_monotone_tendsto hS with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2⟩

中文:
定理 存在_seq_tendsto_sSup
  结论: {α : 类型} [条件完备线性序 α]
  证明: by
  rcases (isLUB_csSup hS hS').exists_seq_monotone_tendsto hS with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2⟩

Depends on / 依赖: exists_seq_monotone_tendsto, isLUB_csSup
-/
theorem exists_seq_tendsto_sSup {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS : S.Nonempty)
    (hS' : BddAbove S) : exists u : Nat -> α, Monotone u ∧ Tendsto u atTop (𝓝 (sSup S)) ∧ forall n, u n in S := by
  rcases (isLUB_csSup hS hS').exists_seq_monotone_tendsto hS with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2⟩

/--
theorem `Dense.exists_seq_strictMono_tendsto_of_lt` / 定理 `Dense.exists_seq_strictMono_tendsto_of_lt`

English:
theorem Dense.exists_seq_strictMono_tendsto_of_lt
  statement: [DenselyOrdered α] [FirstCountableTopology α]
  proof: by
  have hnonempty : (Ioo y x inter s).Nonempty := by
    obtain ⟨z, hyz, hzx⟩ := hs.exists_between hy
    exact ⟨z, mem_inter hzx hyz⟩
.mpr isLUB_Ioo hy have hx : IsLUB (Ioo y x inter s) x := hs.isLUB_inter_iff isOpen_Ioo
.imp apply hx.exists_seq_strictMono_tendsto_of_notMem (by simp) hnonempty
  simp_all

中文:
定理 稠密.存在_seq_strictMono_tendsto_of_lt
  结论: [稠密序 α] [第一可数拓扑 α]
  证明: by
  have hnonempty : (Ioo y x inter s).Nonempty := by
    obtain ⟨z, hyz, hzx⟩ := hs.exists_between hy
    exact ⟨z, mem_inter hzx hyz⟩
.mpr isLUB_Ioo hy have hx : IsLUB (Ioo y x inter s) x := hs.isLUB_inter_iff isOpen_Ioo
.imp apply hx.exists_seq_strictMono_tendsto_of_notMem (by simp) hnonempty
  simp_all

Depends on / 依赖: Nonempty, exists_between, exists_seq_strictMono_tendsto_of_notMem, hnonempty, hs.exists_between, hs.isLUB_inter_iff, hx.exists_seq_strictMono_tendsto_of_notMem, isLUB_Ioo, isLUB_inter_iff, isOpen_Ioo, mem_inter
-/
theorem Dense.exists_seq_strictMono_tendsto_of_lt [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : y < x) :
    exists u : Nat -> α, StrictMono u ∧ (forall n, u n in (Ioo y x inter s)) ∧ Tendsto u atTop (𝓝 x) := by
  have hnonempty : (Ioo y x inter s).Nonempty := by
    obtain ⟨z, hyz, hzx⟩ := hs.exists_between hy
    exact ⟨z, mem_inter hzx hyz⟩
.mpr isLUB_Ioo hy have hx : IsLUB (Ioo y x inter s) x := hs.isLUB_inter_iff isOpen_Ioo
.imp apply hx.exists_seq_strictMono_tendsto_of_notMem (by simp) hnonempty
  simp_all

/--
theorem `Dense.exists_seq_strictMono_tendsto` / 定理 `Dense.exists_seq_strictMono_tendsto`

English:
theorem Dense.exists_seq_strictMono_tendsto
  statement: [DenselyOrdered α] [NoMinOrder α]
  proof: by
  obtain ⟨y, hy⟩ := exists_lt x
.imp apply hs.exists_seq_strictMono_tendsto_of_lt (exists_lt x).choose_spec
  simp_all

中文:
定理 稠密.存在_seq_strictMono_tendsto
  结论: [稠密序 α] [NoMin序 α]
  证明: by
  obtain ⟨y, hy⟩ := exists_lt x
.imp apply hs.exists_seq_strictMono_tendsto_of_lt (exists_lt x).choose_spec
  simp_all

Depends on / 依赖: choose_spec, exists_lt, exists_seq_strictMono_tendsto_of_lt, hs.exists_seq_strictMono_tendsto_of_lt
-/
theorem Dense.exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    exists u : Nat -> α, StrictMono u ∧ (forall n, u n in (Iio x inter s)) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ := exists_lt x
.imp apply hs.exists_seq_strictMono_tendsto_of_lt (exists_lt x).choose_spec
  simp_all

/--
theorem `DenseRange.exists_seq_strictMono_tendsto_of_lt` / 定理 `DenseRange.exists_seq_strictMono_tendsto_of_lt`

English:
theorem DenseRange.exists_seq_strictMono_tendsto_of_lt
  statement: {β : Type*} [LinearOrder β]
  proof: by
  rcases Dense.exists_seq_strictMono_tendsto_of_lt hf hlt with ⟨u, hu, huyxf, hlim⟩
  have huyx (n : Nat) : u n in Ioo y x := (huyxf n).1
  have huf (n : Nat) : u n in range f := (huyxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
exact ⟨v, fun a b hlt => hmono.reflect_lt hu hlt, huyx, hlim⟩

中文:
定理 DenseRange.存在_seq_strictMono_tendsto_of_lt
  结论: {β : 类型} [线性序 β]
  证明: by
  rcases Dense.exists_seq_strictMono_tendsto_of_lt hf hlt with ⟨u, hu, huyxf, hlim⟩
  have huyx (n : Nat) : u n in Ioo y x := (huyxf n).1
  have huf (n : Nat) : u n in range f := (huyxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
exact ⟨v, fun a b hlt => hmono.reflect_lt hu hlt, huyx, hlim⟩

Depends on / 依赖: Dense.exists_seq_strictMono_tendsto_of_lt, exists_seq_strictMono_tendsto_of_lt, hmono.reflect_lt, reflect_lt
-/
theorem DenseRange.exists_seq_strictMono_tendsto_of_lt {β : Type*} [LinearOrder β]
    [DenselyOrdered α] [FirstCountableTopology α] {f : β -> α} {x y : α} (hf : DenseRange f)
    (hmono : Monotone f) (hlt : y < x) :
    exists u : Nat -> β, StrictMono u ∧ (forall n, f (u n) in Ioo y x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  rcases Dense.exists_seq_strictMono_tendsto_of_lt hf hlt with ⟨u, hu, huyxf, hlim⟩
  have huyx (n : Nat) : u n in Ioo y x := (huyxf n).1
  have huf (n : Nat) : u n in range f := (huyxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
exact ⟨v, fun a b hlt => hmono.reflect_lt hu hlt, huyx, hlim⟩

/--
theorem `DenseRange.exists_seq_strictMono_tendsto` / 定理 `DenseRange.exists_seq_strictMono_tendsto`

English:
theorem DenseRange.exists_seq_strictMono_tendsto
  statement: {β : Type*} [LinearOrder β] [DenselyOrdered α]
  proof: by
  rcases Dense.exists_seq_strictMono_tendsto hf x with ⟨u, hu, huxf, hlim⟩
  have hux (n : Nat) : u n in Iio x := (huxf n).1
  have huf (n : Nat) : u n in range f := (huxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
exact ⟨v, fun a b hlt => hmono.reflect_lt hu hlt, hux, hlim⟩

中文:
定理 DenseRange.存在_seq_strictMono_tendsto
  结论: {β : 类型} [线性序 β] [稠密序 α]
  证明: by
  rcases Dense.exists_seq_strictMono_tendsto hf x with ⟨u, hu, huxf, hlim⟩
  have hux (n : Nat) : u n in Iio x := (huxf n).1
  have huf (n : Nat) : u n in range f := (huxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
exact ⟨v, fun a b hlt => hmono.reflect_lt hu hlt, hux, hlim⟩

Depends on / 依赖: Dense.exists_seq_strictMono_tendsto, exists_seq_strictMono_tendsto, hmono.reflect_lt, reflect_lt
-/
theorem DenseRange.exists_seq_strictMono_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α]
    [NoMinOrder α] [FirstCountableTopology α] {f : β -> α} (hf : DenseRange f) (hmono : Monotone f)
    (x : α) :
    exists u : Nat -> β, StrictMono u ∧ (forall n, f (u n) in Iio x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  rcases Dense.exists_seq_strictMono_tendsto hf x with ⟨u, hu, huxf, hlim⟩
  have hux (n : Nat) : u n in Iio x := (huxf n).1
  have huf (n : Nat) : u n in range f := (huxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
exact ⟨v, fun a b hlt => hmono.reflect_lt hu hlt, hux, hlim⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsGLB.exists_seq_strictAnti_tendsto_of_notMem` / 定理 `IsGLB.exists_seq_strictAnti_tendsto_of_notMem`

English:
theorem IsGLB.exists_seq_strictAnti_tendsto_of_notMem
  statement: {t : Set α} {x : α}
  proof: IsLUB.exists_seq_strictMono_tendsto_of_notMem (α := αᵒᵈ) htx notMem ht

中文:
定理 IsGLB.存在_seq_strictAnti_tendsto_of_notMem
  结论: {t : 集合 α} {x : α}
  证明: IsLUB.exists_seq_strictMono_tendsto_of_notMem (α := αᵒᵈ) htx notMem ht

Depends on / 依赖: IsLUB.exists_seq_strictMono_tendsto_of_notMem, exists_seq_strictMono_tendsto_of_notMem, notMem
-/
theorem IsGLB.exists_seq_strictAnti_tendsto_of_notMem {t : Set α} {x : α}
    [IsCountablyGenerated (𝓝 x)] (htx : IsGLB t x) (notMem : x ∉ t) (ht : t.Nonempty) :
    exists u : Nat -> α, StrictAnti u ∧ (forall n, x < u n) ∧ Tendsto u atTop (𝓝 x) ∧ forall n, u n in t :=
  IsLUB.exists_seq_strictMono_tendsto_of_notMem (α := αᵒᵈ) htx notMem ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsGLB.exists_seq_antitone_tendsto` / 定理 `IsGLB.exists_seq_antitone_tendsto`

English:
theorem IsGLB.exists_seq_antitone_tendsto
  statement: {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
  proof: IsLUB.exists_seq_monotone_tendsto (α := αᵒᵈ) htx ht

中文:
定理 IsGLB.存在_seq_antitone_tendsto
  结论: {t : 集合 α} {x : α} [是余untablyGenerated (𝓝 x)]
  证明: IsLUB.exists_seq_monotone_tendsto (α := αᵒᵈ) htx ht

Depends on / 依赖: IsLUB.exists_seq_monotone_tendsto, exists_seq_monotone_tendsto
-/
theorem IsGLB.exists_seq_antitone_tendsto {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
    (htx : IsGLB t x) (ht : t.Nonempty) :
    exists u : Nat -> α, Antitone u ∧ (forall n, x <= u n) ∧ Tendsto u atTop (𝓝 x) ∧ forall n, u n in t :=
  IsLUB.exists_seq_monotone_tendsto (α := αᵒᵈ) htx ht

/--
theorem `exists_seq_strictAnti_tendsto'` / 定理 `exists_seq_strictAnti_tendsto'`

English:
theorem exists_seq_strictAnti_tendsto'
  statement: [DenselyOrdered α] [FirstCountableTopology α] {x y : α}
  proof: by
  simpa using! exists_seq_strictMono_tendsto' (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

中文:
定理 存在_seq_strictAnti_tendsto'
  结论: [稠密序 α] [第一可数拓扑 α] {x y : α}
  证明: by
  simpa using! exists_seq_strictMono_tendsto' (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

Depends on / 依赖: OrderDual, OrderDual.toDual_lt_toDual, exists_seq_strictMono_tendsto, toDual_lt_toDual
-/
theorem exists_seq_strictAnti_tendsto' [DenselyOrdered α] [FirstCountableTopology α] {x y : α}
    (hy : x < y) : exists u : Nat -> α, StrictAnti u ∧ (forall n, u n in Ioo x y) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using! exists_seq_strictMono_tendsto' (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

/--
theorem `exists_seq_strictAnti_tendsto` / 定理 `exists_seq_strictAnti_tendsto`

English:
theorem exists_seq_strictAnti_tendsto
  statement: [DenselyOrdered α] [NoMaxOrder α] [FirstCountableTopology α]
  proof: exists_seq_strictMono_tendsto (α := αᵒᵈ) x

中文:
定理 存在_seq_strictAnti_tendsto
  结论: [稠密序 α] [NoMax序 α] [第一可数拓扑 α]
  证明: exists_seq_strictMono_tendsto (α := αᵒᵈ) x

Depends on / 依赖: exists_seq_strictMono_tendsto
-/
theorem exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α] [FirstCountableTopology α]
    (x : α) : exists u : Nat -> α, StrictAnti u ∧ (forall n, x < u n) ∧ Tendsto u atTop (𝓝 x) :=
  exists_seq_strictMono_tendsto (α := αᵒᵈ) x

/--
theorem `exists_seq_strictAnti_tendsto_nhdsWithin` / 定理 `exists_seq_strictAnti_tendsto_nhdsWithin`

English:
theorem exists_seq_strictAnti_tendsto_nhdsWithin
  statement: [DenselyOrdered α] [NoMaxOrder α]
  proof: exists_seq_strictMono_tendsto_nhdsWithin (α := αᵒᵈ) _

中文:
定理 存在_seq_strictAnti_tendsto_nhdsWithin
  结论: [稠密序 α] [NoMax序 α]
  证明: exists_seq_strictMono_tendsto_nhdsWithin (α := αᵒᵈ) _

Depends on / 依赖: exists_seq_strictMono_tendsto_nhdsWithin
-/
theorem exists_seq_strictAnti_tendsto_nhdsWithin [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] (x : α) :
    exists u : Nat -> α, StrictAnti u ∧ (forall n, x < u n) ∧ Tendsto u atTop (𝓝[>] x) :=
  exists_seq_strictMono_tendsto_nhdsWithin (α := αᵒᵈ) _

/--
theorem `exists_seq_strictAnti_strictMono_tendsto` / 定理 `exists_seq_strictAnti_strictMono_tendsto`

English:
theorem exists_seq_strictAnti_strictMono_tendsto
  statement: [DenselyOrdered α] [FirstCountableTopology α]
  proof: by
  rcases exists_seq_strictAnti_tendsto' h with ⟨u, hu_anti, hu_mem, hux⟩
  rcases exists_seq_strictMono_tendsto' (hu_mem 0).2 with ⟨v, hv_mono, hv_mem, hvy⟩
  exact
    ⟨u, v, hu_anti, hv_mono, hu_mem, fun l => ⟨(hu_mem 0).1.trans (hv_mem l).1, (hv_mem l).2⟩,
      fun k l => (hu_anti.antitone zero_le).trans_lt (hv_mem l).1, hux, hvy⟩

中文:
定理 存在_seq_strictAnti_strictMono_tendsto
  结论: [稠密序 α] [第一可数拓扑 α]
  证明: by
  rcases exists_seq_strictAnti_tendsto' h with ⟨u, hu_anti, hu_mem, hux⟩
  rcases exists_seq_strictMono_tendsto' (hu_mem 0).2 with ⟨v, hv_mono, hv_mem, hvy⟩
  exact
    ⟨u, v, hu_anti, hv_mono, hu_mem, fun l => ⟨(hu_mem 0).1.trans (hv_mem l).1, (hv_mem l).2⟩,
      fun k l => (hu_anti.antitone zero_le).trans_lt (hv_mem l).1, hux, hvy⟩

Depends on / 依赖: antitone, exists_seq_strictAnti_tendsto, exists_seq_strictMono_tendsto, hu_anti, hu_anti.antitone, hu_mem, hv_mem, hv_mono, trans_lt, zero_le
-/
theorem exists_seq_strictAnti_strictMono_tendsto [DenselyOrdered α] [FirstCountableTopology α]
    {x y : α} (h : x < y) :
    exists u v : Nat -> α, StrictAnti u ∧ StrictMono v ∧ (forall k, u k in Ioo x y) ∧ (forall l, v l in Ioo x y) ∧
      (forall k l, u k < v l) ∧ Tendsto u atTop (𝓝 x) ∧ Tendsto v atTop (𝓝 y) := by
  rcases exists_seq_strictAnti_tendsto' h with ⟨u, hu_anti, hu_mem, hux⟩
  rcases exists_seq_strictMono_tendsto' (hu_mem 0).2 with ⟨v, hv_mono, hv_mem, hvy⟩
  exact
    ⟨u, v, hu_anti, hv_mono, hu_mem, fun l => ⟨(hu_mem 0).1.trans (hv_mem l).1, (hv_mem l).2⟩,
      fun k l => (hu_anti.antitone zero_le).trans_lt (hv_mem l).1, hux, hvy⟩

/--
theorem `exists_seq_tendsto_sInf` / 定理 `exists_seq_tendsto_sInf`

English:
theorem exists_seq_tendsto_sInf
  statement: {α : Type*} [ConditionallyCompleteLinearOrder α]
  proof: exists_seq_tendsto_sSup (α := αᵒᵈ) hS hS'

中文:
定理 存在_seq_tendsto_sInf
  结论: {α : 类型} [条件完备线性序 α]
  证明: exists_seq_tendsto_sSup (α := αᵒᵈ) hS hS'

Depends on / 依赖: exists_seq_tendsto_sSup
-/
theorem exists_seq_tendsto_sInf {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS : S.Nonempty)
    (hS' : BddBelow S) : exists u : Nat -> α, Antitone u ∧ Tendsto u atTop (𝓝 (sInf S)) ∧ forall n, u n in S :=
  exists_seq_tendsto_sSup (α := αᵒᵈ) hS hS'

/--
theorem `Dense.exists_seq_strictAnti_tendsto_of_lt` / 定理 `Dense.exists_seq_strictAnti_tendsto_of_lt`

English:
theorem Dense.exists_seq_strictAnti_tendsto_of_lt
  statement: [DenselyOrdered α] [FirstCountableTopology α]
  proof: by
  simpa using! hs.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

中文:
定理 稠密.存在_seq_strictAnti_tendsto_of_lt
  结论: [稠密序 α] [第一可数拓扑 α]
  证明: by
  simpa using! hs.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

Depends on / 依赖: OrderDual, OrderDual.toDual_lt_toDual, exists_seq_strictMono_tendsto_of_lt, hs.exists_seq_strictMono_tendsto_of_lt, toDual_lt_toDual
-/
theorem Dense.exists_seq_strictAnti_tendsto_of_lt [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : x < y) :
    exists u : Nat -> α, StrictAnti u ∧ (forall n, u n in (Ioo x y inter s)) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using! hs.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

/--
theorem `Dense.exists_seq_strictAnti_tendsto` / 定理 `Dense.exists_seq_strictAnti_tendsto`

English:
theorem Dense.exists_seq_strictAnti_tendsto
  statement: [DenselyOrdered α] [NoMaxOrder α]
  proof: hs.exists_seq_strictMono_tendsto (α := αᵒᵈ) x

中文:
定理 稠密.存在_seq_strictAnti_tendsto
  结论: [稠密序 α] [NoMax序 α]
  证明: hs.exists_seq_strictMono_tendsto (α := αᵒᵈ) x

Depends on / 依赖: exists_seq_strictMono_tendsto, hs.exists_seq_strictMono_tendsto
-/
theorem Dense.exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    exists u : Nat -> α, StrictAnti u ∧ (forall n, u n in (Ioi x inter s)) ∧ Tendsto u atTop (𝓝 x) :=
  hs.exists_seq_strictMono_tendsto (α := αᵒᵈ) x

/--
theorem `DenseRange.exists_seq_strictAnti_tendsto_of_lt` / 定理 `DenseRange.exists_seq_strictAnti_tendsto_of_lt`

English:
theorem DenseRange.exists_seq_strictAnti_tendsto_of_lt
  statement: {β : Type*} [LinearOrder β]
  proof: by
  simpa using! hf.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual
    (OrderDual.toDual_lt_toDual.2 hlt)

中文:
定理 DenseRange.存在_seq_strictAnti_tendsto_of_lt
  结论: {β : 类型} [线性序 β]
  证明: by
  simpa using! hf.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual
    (OrderDual.toDual_lt_toDual.2 hlt)

Depends on / 依赖: OrderDual, OrderDual.toDual_lt_toDual, exists_seq_strictMono_tendsto_of_lt, hf.exists_seq_strictMono_tendsto_of_lt, hmono.dual, toDual_lt_toDual
-/
theorem DenseRange.exists_seq_strictAnti_tendsto_of_lt {β : Type*} [LinearOrder β]
    [DenselyOrdered α] [FirstCountableTopology α] {f : β -> α} {x y : α} (hf : DenseRange f)
    (hmono : Monotone f) (hlt : x < y) :
    exists u : Nat -> β, StrictAnti u ∧ (forall n, f (u n) in Ioo x y) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  simpa using! hf.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual
    (OrderDual.toDual_lt_toDual.2 hlt)

/--
theorem `DenseRange.exists_seq_strictAnti_tendsto` / 定理 `DenseRange.exists_seq_strictAnti_tendsto`

English:
theorem DenseRange.exists_seq_strictAnti_tendsto
  statement: {β : Type*} [LinearOrder β] [DenselyOrdered α]
  proof: hf.exists_seq_strictMono_tendsto (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual x

中文:
定理 DenseRange.存在_seq_strictAnti_tendsto
  结论: {β : 类型} [线性序 β] [稠密序 α]
  证明: hf.exists_seq_strictMono_tendsto (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual x

Depends on / 依赖: exists_seq_strictMono_tendsto, hf.exists_seq_strictMono_tendsto, hmono.dual
-/
theorem DenseRange.exists_seq_strictAnti_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α]
    [NoMaxOrder α] [FirstCountableTopology α] {f : β -> α} (hf : DenseRange f) (hmono : Monotone f)
    (x : α) :
    exists u : Nat -> β, StrictAnti u ∧ (forall n, f (u n) in Ioi x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) :=
  hf.exists_seq_strictMono_tendsto (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual x

/--
theorem `eventually_le_const_iff_forall_gt_eventually_lt_const` / 定理 `eventually_le_const_iff_forall_gt_eventually_lt_const`

English:
theorem eventually_le_const_iff_forall_gt_eventually_lt_const
  statement: [FirstCountableTopology α]
  proof: h.mono fun x hx => lt_of_le_of_lt hx hbc
  mpr h := by
    rcases exists_glb_Ioi a with ⟨d, hd⟩
    obtain rfl | H0 := glb_Ioi_eq_self_or_Ioi_eq_Ici _ hd
    · obtain h | _ := isTop_or_exists_gt d
      · exact .of_forall (fun _ => h _)
      obtain ⟨u, -, -, hu_tt, hu_gt⟩ := hd.exists_seq_antitone_tendsto (by simpa)
      replace h := fun n => h (u n) (by grind)
      rw [← eventually_countable_forall] at h
      filter_upwards [h] with x hx
exact ge_of_tendsto hu_tt .of_forall fun n => le_of_lt hx n
· specialize h d by simp [← Set.mem_Ioi, H0]
      filter_upwards [h] with x hx
      rw [← Set.compl_Iic]; rw [← Set.compl_Iio]; rw [compl_inj_iff] at H0
      simpa [← Set.mem_Iic, ← Set.mem_Iio, H0] using hx

中文:
定理 eventually_le_const_iff_对任意_gt_eventually_lt_const
  结论: [第一可数拓扑 α]
  证明: h.mono fun x hx => lt_of_le_of_lt hx hbc
  mpr h := by
    rcases exists_glb_Ioi a with ⟨d, hd⟩
    obtain rfl | H0 := glb_Ioi_eq_self_or_Ioi_eq_Ici _ hd
    · obtain h | _ := isTop_or_exists_gt d
      · exact .of_forall (fun _ => h _)
      obtain ⟨u, -, -, hu_tt, hu_gt⟩ := hd.exists_seq_antitone_tendsto (by simpa)
      replace h := fun n => h (u n) (by grind)
      rw [← eventually_countable_forall] at h
      filter_upwards [h] with x hx
exact ge_of_tendsto hu_tt .of_forall fun n => le_of_lt hx n
· specialize h d by simp [← Set.mem_Ioi, H0]
      filter_upwards [h] with x hx
      rw [← Set.compl_Iic]; rw [← Set.compl_Iio]; rw [compl_inj_iff] at H0
      simpa [← Set.mem_Iic, ← Set.mem_Iio, H0] using hx

Depends on / 依赖: h.mono, lt_of_le_of_lt
-/
theorem eventually_le_const_iff_forall_gt_eventually_lt_const [FirstCountableTopology α]
    {l : Filter γ} [CountableInterFilter l] {f : γ -> α} {a : α} :
    (forallᶠ x in l, f x <= a) ↔ forall b, a < b -> forallᶠ x in l, f x < b where
mp h c hbc := h.mono fun x hx => lt_of_le_of_lt hx hbc
  mpr h := by
    rcases exists_glb_Ioi a with ⟨d, hd⟩
    obtain rfl | H0 := glb_Ioi_eq_self_or_Ioi_eq_Ici _ hd
    · obtain h | _ := isTop_or_exists_gt d
      · exact .of_forall (fun _ => h _)
      obtain ⟨u, -, -, hu_tt, hu_gt⟩ := hd.exists_seq_antitone_tendsto (by simpa)
      replace h := fun n => h (u n) (by grind)
      rw [← eventually_countable_forall] at h
      filter_upwards [h] with x hx
exact ge_of_tendsto hu_tt .of_forall fun n => le_of_lt hx n
· specialize h d by simp [← Set.mem_Ioi, H0]
      filter_upwards [h] with x hx
      rw [← Set.compl_Iic]; rw [← Set.compl_Iio]; rw [compl_inj_iff] at H0
      simpa [← Set.mem_Iic, ← Set.mem_Iio, H0] using hx

/--
theorem `eventually_const_le_iff_forall_lt_eventually_const_lt` / 定理 `eventually_const_le_iff_forall_lt_eventually_const_lt`

English:
theorem eventually_const_le_iff_forall_lt_eventually_const_lt
  statement: [FirstCountableTopology α]
  proof: eventually_le_const_iff_forall_gt_eventually_lt_const (α := αᵒᵈ)

中文:
定理 eventually_const_le_iff_对任意_lt_eventually_const_lt
  结论: [第一可数拓扑 α]
  证明: eventually_le_const_iff_forall_gt_eventually_lt_const (α := αᵒᵈ)

Depends on / 依赖: eventually_le_const_iff_forall_gt_eventually_lt_const
-/
theorem eventually_const_le_iff_forall_lt_eventually_const_lt [FirstCountableTopology α]
    {l : Filter γ} [CountableInterFilter l] {f : γ -> α} {a : α} :
    (forallᶠ x in l, a <= f x) ↔ forall b, b < a -> forallᶠ x in l, b < f x :=
  eventually_le_const_iff_forall_gt_eventually_lt_const (α := αᵒᵈ)

end OrderTopology
