/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.AtTopBot.CompleteLattice
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Order.Basic

/-!
# Neighborhoods to the left and to the right on an `OrderTopology`

We've seen some properties of left and right neighborhood of a point in an `OrderClosedTopology`.
In an `OrderTopology`, such neighborhoods can be characterized as the sets containing suitable
intervals to the right or to the left of `a`. We give now these characterizations. -/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α]

section OrderTopology

variable [OrderTopology α]

open List in
/--
theorem `TFAE_mem_nhdsGT` / 定理 `TFAE_mem_nhdsGT`

English:
theorem TFAE_mem_nhdsGT
  given: {a b : α} (hab : a < b) (s : Set α)
  proof: by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
  tfae_have 4 -> 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 -> 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsGT hau) hu
  tfae_have 1 -> 4
  | h => by
    

中文:
定理 TFAE_mem_nhdsGT
  条件: {a b : α} (hab : a < b) (s : Set α)
  证明: by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
  tfae_have 4 -> 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 -> 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsGT hau) hu
  tfae_have 1 -> 4
  | h => by
    

Depends on / 依赖: Ioo_mem_nhdsGT, exists_Ico_subset_of_mem_nhds, le_of_lt, mem_nhdsWithin_iff_exists_mem_nhds_inter, mem_of_superset, nhdsWithin_Ioc_eq_nhdsGT, nhdsWithin_Ioo_eq_nhdsGT, tfae_finish, tfae_have
-/
theorem TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s in 𝓝[>] a,
      s in 𝓝[Ioc a b] a,
      s in 𝓝[Ioo a b] a,
      exists u in Ioc a b, Ioo a u subseteq s,
      exists u in Ioi a, Ioo a u subseteq s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
  tfae_have 4 -> 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 -> 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsGT hau) hu
  tfae_have 1 -> 4
  | h => by
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h with ⟨v, va, hv⟩
    rcases exists_Ico_subset_of_mem_nhds' va hab with ⟨u, au, hu⟩
    exact ⟨u, au, fun x hx => hv ⟨hu ⟨le_of_lt hx.1, hx.2⟩, hx.1⟩⟩
  tfae_finish

/--
theorem `mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset` / 定理 `mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset`

English:
theorem mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset
  given: {a u' : α} {s : Set α} (hu' : a < u')
  proof: (TFAE_mem_nhdsGT hu' s).out 0 3

中文:
定理 mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset
  条件: {a u' : α} {s : Set α} (hu' : a < u')
  证明: (TFAE_mem_nhdsGT hu' s).out 0 3

Depends on / 依赖: TFAE_mem_nhdsGT
-/
theorem mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s in 𝓝[>] a ↔ exists u in Ioc a u', Ioo a u subseteq s :=
  (TFAE_mem_nhdsGT hu' s).out 0 3

/--
theorem `mem_nhdsGT_iff_exists_Ioo_subset'` / 定理 `mem_nhdsGT_iff_exists_Ioo_subset'`

English:
theorem mem_nhdsGT_iff_exists_Ioo_subset'
  given: {a u' : α} {s : Set α} (hu' : a < u')
  proof: (TFAE_mem_nhdsGT hu' s).out 0 4

中文:
定理 mem_nhdsGT_iff_exists_Ioo_subset'
  条件: {a u' : α} {s : Set α} (hu' : a < u')
  证明: (TFAE_mem_nhdsGT hu' s).out 0 4

Depends on / 依赖: TFAE_mem_nhdsGT
-/
theorem mem_nhdsGT_iff_exists_Ioo_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subseteq s :=
  (TFAE_mem_nhdsGT hu' s).out 0 4

/--
theorem `nhdsGT_basis_of_exists_gt` / 定理 `nhdsGT_basis_of_exists_gt`

English:
theorem nhdsGT_basis_of_exists_gt
  given: {a : α} (h : exists b, a < b)
  statement: (𝓝[>] a).HasBasis (a < ·) (Ioo a)
  proof: let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsGT_iff_exists_Ioo_subset' h⟩

中文:
定理 nhdsGT_basis_of_exists_gt
  条件: {a : α} (h : 存在 b, a < b)
  结论: (𝓝[>] a).HasBasis (a < ·) (Ioo a)
  证明: let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsGT_iff_exists_Ioo_subset' h⟩

Depends on / 依赖: mem_nhdsGT_iff_exists_Ioo_subset
-/
theorem nhdsGT_basis_of_exists_gt {a : α} (h : exists b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsGT_iff_exists_Ioo_subset' h⟩

/--
lemma `nhdsGT_basis` / 引理 `nhdsGT_basis`

English:
lemma nhdsGT_basis
  given: [NoMaxOrder α] (a : α)
  statement: (𝓝[>] a).HasBasis (a < ·) (Ioo a)
  proof: nhdsGT_basis_of_exists_gt exists_gt a

中文:
引理 nhdsGT_basis
  条件: [NoMaxOrder α] (a : α)
  结论: (𝓝[>] a).HasBasis (a < ·) (Ioo a)
  证明: nhdsGT_basis_of_exists_gt exists_gt a

Depends on / 依赖: exists_gt, nhdsGT_basis_of_exists_gt
-/
lemma nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
nhdsGT_basis_of_exists_gt exists_gt a

/--
lemma `nhdsGT_basis_Ioc_of_exists_gt` / 引理 `nhdsGT_basis_Ioc_of_exists_gt`

English:
lemma nhdsGT_basis_Ioc_of_exists_gt
  given: [DenselyOrdered α] {a : α} (h : exists b, a < b)
  proof: .to_hasBasis' nhdsGT_basis_of_exists_gt h
    (fun _ hac =>
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hab, Ioc_subset_Ioo_right hbc⟩)
    fun _ hac => mem_of_superset ((nhdsGT_basis_of_exists_gt h).mem_of_mem hac) Ioo_subset_Ioc_self

中文:
引理 nhdsGT_basis_Ioc_of_exists_gt
  条件: [DenselyOrdered α] {a : α} (h : 存在 b, a < b)
  证明: .to_hasBasis' nhdsGT_basis_of_exists_gt h
    (fun _ hac =>
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hab, Ioc_subset_Ioo_right hbc⟩)
    fun _ hac => mem_of_superset ((nhdsGT_basis_of_exists_gt h).mem_of_mem hac) Ioo_subset_Ioc_self

Depends on / 依赖: Ioc_subset_Ioo_right, Ioo_subset_Ioc_self, exists_between, mem_of_mem, mem_of_superset, nhdsGT_basis_of_exists_gt, to_hasBasis
-/
lemma nhdsGT_basis_Ioc_of_exists_gt [DenselyOrdered α] {a : α} (h : exists b, a < b) :
    (𝓝[>] a).HasBasis (fun x => a < x) (Ioc a) :=
.to_hasBasis' nhdsGT_basis_of_exists_gt h
    (fun _ hac =>
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hab, Ioc_subset_Ioo_right hbc⟩)
    fun _ hac => mem_of_superset ((nhdsGT_basis_of_exists_gt h).mem_of_mem hac) Ioo_subset_Ioc_self

/--
lemma `nhdsGT_basis_Ioc` / 引理 `nhdsGT_basis_Ioc`

English:
lemma nhdsGT_basis_Ioc
  given: [DenselyOrdered α] [NoMaxOrder α] (a : α)
  proof: nhdsGT_basis_Ioc_of_exists_gt exists_gt a

中文:
引理 nhdsGT_basis_Ioc
  条件: [DenselyOrdered α] [NoMaxOrder α] (a : α)
  证明: nhdsGT_basis_Ioc_of_exists_gt exists_gt a

Depends on / 依赖: exists_gt, nhdsGT_basis_Ioc_of_exists_gt
-/
lemma nhdsGT_basis_Ioc [DenselyOrdered α] [NoMaxOrder α] (a : α) :
    (𝓝[>] a).HasBasis (fun x => a < x) (Ioc a) :=
nhdsGT_basis_Ioc_of_exists_gt exists_gt a

/--
theorem `nhdsGT_eq_bot_iff` / 定理 `nhdsGT_eq_bot_iff`

English:
theorem nhdsGT_eq_bot_iff
  given: {a : α}
  statement: 𝓝[>] a = ⊥ ↔ IsTop a ∨ exists b, a ⋖ b
  proof: by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax]; rw [not_isMax_iff] at ha
    simp only [(nhdsGT_basis_of_exists_gt ha).eq_bot_iff, covBy_iff_Ioo_eq]

中文:
定理 nhdsGT_eq_bot_iff
  条件: {a : α}
  结论: 𝓝[>] a = ⊥ ↔ IsTop a ∨ 存在 b, a ⋖ b
  证明: by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax]; rw [not_isMax_iff] at ha
    simp only [(nhdsGT_basis_of_exists_gt ha).eq_bot_iff, covBy_iff_Ioo_eq]

Depends on / 依赖: Ioi_eq, covBy_iff_Ioo_eq, eq_bot_iff, false_or, ha.isMax.Ioi_eq, isTop_iff_isMax, nhdsGT_basis_of_exists_gt, not_isMax_iff
-/
theorem nhdsGT_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ exists b, a ⋖ b := by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax]; rw [not_isMax_iff] at ha
    simp only [(nhdsGT_basis_of_exists_gt ha).eq_bot_iff, covBy_iff_Ioo_eq]

/--
theorem `mem_nhdsGT_iff_exists_Ioo_subset` / 定理 `mem_nhdsGT_iff_exists_Ioo_subset`

English:
theorem mem_nhdsGT_iff_exists_Ioo_subset
  given: [NoMaxOrder α] {a : α} {s : Set α}
  proof: let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsGT_iff_exists_Ioo_subset' hu'

中文:
定理 mem_nhdsGT_iff_exists_Ioo_subset
  条件: [NoMaxOrder α] {a : α} {s : Set α}
  证明: let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsGT_iff_exists_Ioo_subset' hu'

Depends on / 依赖: exists_gt, mem_nhdsGT_iff_exists_Ioo_subset
-/
theorem mem_nhdsGT_iff_exists_Ioo_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s in 𝓝[>] a ↔ exists u in Ioi a, Ioo a u subseteq s :=
  let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsGT_iff_exists_Ioo_subset' hu'

/--
theorem `countable_setOfPred_isolated_right` / 定理 `countable_setOfPred_isolated_right`

English:
theorem countable_setOfPred_isolated_right
  given: [SecondCountableTopology α]
  proof: by
  simp only [nhdsGT_eq_bot_iff, ofPred_or]
  exact (subsingleton_isTop α).countable.union countable_setOfPred_covBy_right

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_right := countable_setOfPred_isolated_right

中文:
定理 countable_setOfPred_isolated_right
  条件: [SecondCountableTopology α]
  证明: by
  simp only [nhdsGT_eq_bot_iff, ofPred_or]
  exact (subsingleton_isTop α).countable.union countable_setOfPred_covBy_right

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_right := countable_setOfPred_isolated_right

Depends on / 依赖: countable, countable.union, countable_setOfPred_covBy_right, nhdsGT_eq_bot_iff, ofPred_or, subsingleton_isTop
-/
theorem countable_setOfPred_isolated_right [SecondCountableTopology α] :
    { x : α | 𝓝[>] x = ⊥ }.Countable := by
  simp only [nhdsGT_eq_bot_iff, ofPred_or]
  exact (subsingleton_isTop α).countable.union countable_setOfPred_covBy_right

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_right := countable_setOfPred_isolated_right

/--
theorem `countable_setOfPred_isolated_left` / 定理 `countable_setOfPred_isolated_left`

English:
theorem countable_setOfPred_isolated_left
  given: [SecondCountableTopology α]
  proof: countable_setOfPred_isolated_right (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left := countable_setOfPred_isolated_left

中文:
定理 countable_setOfPred_isolated_left
  条件: [SecondCountableTopology α]
  证明: countable_setOfPred_isolated_right (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left := countable_setOfPred_isolated_left

Depends on / 依赖: countable_setOfPred_isolated_right
-/
theorem countable_setOfPred_isolated_left [SecondCountableTopology α] :
    { x : α | 𝓝[<] x = ⊥ }.Countable :=
  countable_setOfPred_isolated_right (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left := countable_setOfPred_isolated_left

/--
theorem `countable_setOfPred_isolated_right_within` / 定理 `countable_setOfPred_isolated_right_within`

English:
theorem countable_setOfPred_isolated_right_within
  given: [SecondCountableTopology α] {s : Set α}
  proof: by
  /- This does not follow from `countable_setOfPred_isolated_right`, which gives the result when `s`
  is the whole space, as one cannot use it inside the subspace since it doesn't have the order
  topology. Instead, we follow the main steps of its proof. -/
  let t := { x in s | 𝓝[s inter Ioi x]

中文:
定理 countable_setOfPred_isolated_right_within
  条件: [SecondCountableTopology α] {s : Set α}
  证明: by
  /- This does not follow from `countable_setOfPred_isolated_right`, which gives the result when `s`
  is the whole space, as one cannot use it inside the subspace since it doesn't have the order
  topology. Instead, we follow the main steps of its proof. -/
  let t := { x in s | 𝓝[s inter Ioi x]
-/
theorem countable_setOfPred_isolated_right_within [SecondCountableTopology α] {s : Set α} :
    { x in s | 𝓝[s inter Ioi x] x = ⊥ }.Countable := by
  /- This does not follow from `countable_setOfPred_isolated_right`, which gives the result when `s`
  is the whole space, as one cannot use it inside the subspace since it doesn't have the order
  topology. Instead, we follow the main steps of its proof. -/
  let t := { x in s | 𝓝[s inter Ioi x] x = ⊥ ∧ ¬ IsTop x}
  suffices H : t.Countable by
    have : { x in s | 𝓝[s inter Ioi x] x = ⊥ } subseteq t union {x | IsTop x} := by
      intro x hx
      by_cases h'x : IsTop x
      · simp [h'x]
      · simpa [-sep_and, t, h'x]
    apply Countable.mono this
    simp [H, (subsingleton_isTop α).countable]
  have (x) (hx : x in t) : exists y > x, s inter Ioo x y = ∅ := by
    simp only [← empty_mem_iff_bot, mem_nhdsWithin_iff_exists_mem_nhds_inter,
      subset_empty_iff, IsTop, not_forall, not_le, mem_ofPred_eq, t] at hx
    rcases hx.2.1 with ⟨u, hu, h'u⟩
    obtain ⟨y, hxy, hy⟩ : exists y, x < y ∧ Ico x y subseteq u := exists_Ico_subset_of_mem_nhds hu hx.2.2
    refine ⟨y, hxy, ?_⟩
    contrapose! h'u
    apply h'u.mono
    intro z hz
    exact ⟨hy ⟨hz.2.1.le, hz.2.2⟩, hz.1, hz.2.1⟩
  choose! y hy h'y using this
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := y) _ hy
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun]
  intro a ha b hb hab
  wlog! H : a < b generalizing a b with h
  · have : b < a := lt_of_le_of_ne H hab.symm
    exact (h hb ha hab.symm this).symm
  have : y a <= b := by
    by_contra!
    have : b in s inter Ioo a (y a) := by simp [hb.1, H, this]
    simp [h'y a ha] at this
  rw [disjoint_iff_forall_ne]
  exact fun u hu v hv => ((hu.2.trans_le this).trans hv.1).ne

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_right_within := countable_setOfPred_isolated_right_within

/--
theorem `countable_setOfPred_isolated_left_within` / 定理 `countable_setOfPred_isolated_left_within`

English:
theorem countable_setOfPred_isolated_left_within
  given: [SecondCountableTopology α] {s : Set α}
  proof: countable_setOfPred_isolated_right_within (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left_within := countable_setOfPred_isolated_left_within

中文:
定理 countable_setOfPred_isolated_left_within
  条件: [SecondCountableTopology α] {s : Set α}
  证明: countable_setOfPred_isolated_right_within (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left_within := countable_setOfPred_isolated_left_within

Depends on / 依赖: countable_setOfPred_isolated_right_within
-/
theorem countable_setOfPred_isolated_left_within [SecondCountableTopology α] {s : Set α} :
    { x in s | 𝓝[s inter Iio x] x = ⊥ }.Countable :=
  countable_setOfPred_isolated_right_within (α := αᵒᵈ)

@[deprecated (since := "2026-07-09")]
alias countable_setOf_isolated_left_within := countable_setOfPred_isolated_left_within

/--
theorem `mem_nhdsGT_iff_exists_Ioc_subset` / 定理 `mem_nhdsGT_iff_exists_Ioc_subset`

English:
theorem mem_nhdsGT_iff_exists_Ioc_subset
  given: [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α}
  proof: by
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩

中文:
定理 mem_nhdsGT_iff_exists_Ioc_subset
  条件: [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α}
  证明: by
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩

Depends on / 依赖: Ioo_subset_Ioc_self, Subset, Subset.trans, exists_between, lt_of_le_of_lt, mem_nhdsGT_iff_exists_Ioo_subset
-/
theorem mem_nhdsGT_iff_exists_Ioc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s in 𝓝[>] a ↔ exists u in Ioi a, Ioc a u subseteq s := by
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩

open List in
/--
theorem `TFAE_mem_nhdsLT` / 定理 `TFAE_mem_nhdsLT`

English:
theorem TFAE_mem_nhdsLT
  given: {a b : α} (h : a < b) (s : Set α)
  proof: by -- 4 : `s` includes `(l, b)` for some `l < b`
  simpa using! TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)

中文:
定理 TFAE_mem_nhdsLT
  条件: {a b : α} (h : a < b) (s : Set α)
  证明: by -- 4 : `s` includes `(l, b)` for some `l < b`
  simpa using! TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)

Depends on / 依赖: TFAE_mem_nhdsGT, h.dual, includes, ofDual
-/
theorem TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) :
    TFAE [s in 𝓝[<] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b)`
        s in 𝓝[Ico a b] b, -- 1 : `s` is a neighborhood of `b` within `[a, b)`
        s in 𝓝[Ioo a b] b, -- 2 : `s` is a neighborhood of `b` within `(a, b)`
        exists l in Ico a b, Ioo l b subseteq s, -- 3 : `s` includes `(l, b)` for some `l ∈ [a, b)`
        exists l in Iio b, Ioo l b subseteq s] := by -- 4 : `s` includes `(l, b)` for some `l < b`
  simpa using! TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)

/--
theorem `mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset` / 定理 `mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset`

English:
theorem mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset
  given: {a l' : α} {s : Set α} (hl' : l' < a)
  proof: (TFAE_mem_nhdsLT hl' s).out 0 3

中文:
定理 mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset
  条件: {a l' : α} {s : Set α} (hl' : l' < a)
  证明: (TFAE_mem_nhdsLT hl' s).out 0 3

Depends on / 依赖: TFAE_mem_nhdsLT
-/
theorem mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s in 𝓝[<] a ↔ exists l in Ico l' a, Ioo l a subseteq s :=
  (TFAE_mem_nhdsLT hl' s).out 0 3

/--
theorem `mem_nhdsLT_iff_exists_Ioo_subset'` / 定理 `mem_nhdsLT_iff_exists_Ioo_subset'`

English:
theorem mem_nhdsLT_iff_exists_Ioo_subset'
  given: {a l' : α} {s : Set α} (hl' : l' < a)
  proof: (TFAE_mem_nhdsLT hl' s).out 0 4

中文:
定理 mem_nhdsLT_iff_exists_Ioo_subset'
  条件: {a l' : α} {s : Set α} (hl' : l' < a)
  证明: (TFAE_mem_nhdsLT hl' s).out 0 4

Depends on / 依赖: TFAE_mem_nhdsLT
-/
theorem mem_nhdsLT_iff_exists_Ioo_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subseteq s :=
  (TFAE_mem_nhdsLT hl' s).out 0 4

/--
theorem `mem_nhdsLT_iff_exists_Ioo_subset` / 定理 `mem_nhdsLT_iff_exists_Ioo_subset`

English:
theorem mem_nhdsLT_iff_exists_Ioo_subset
  given: [NoMinOrder α] {a : α} {s : Set α}
  proof: let ⟨_, h⟩ := exists_lt a
  mem_nhdsLT_iff_exists_Ioo_subset' h

中文:
定理 mem_nhdsLT_iff_exists_Ioo_subset
  条件: [NoMinOrder α] {a : α} {s : Set α}
  证明: let ⟨_, h⟩ := exists_lt a
  mem_nhdsLT_iff_exists_Ioo_subset' h

Depends on / 依赖: exists_lt, mem_nhdsLT_iff_exists_Ioo_subset
-/
theorem mem_nhdsLT_iff_exists_Ioo_subset [NoMinOrder α] {a : α} {s : Set α} :
    s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a subseteq s :=
  let ⟨_, h⟩ := exists_lt a
  mem_nhdsLT_iff_exists_Ioo_subset' h

/--
theorem `mem_nhdsLT_iff_exists_Ico_subset` / 定理 `mem_nhdsLT_iff_exists_Ico_subset`

English:
theorem mem_nhdsLT_iff_exists_Ico_subset
  given: [NoMinOrder α] [DenselyOrdered α] {a : α} {s : Set α}
  proof: by
  have : ofDual ⁻¹' s in 𝓝[>] toDual a ↔ _ := mem_nhdsGT_iff_exists_Ioc_subset
  simpa using! this

中文:
定理 mem_nhdsLT_iff_exists_Ico_subset
  条件: [NoMinOrder α] [DenselyOrdered α] {a : α} {s : Set α}
  证明: by
  have : ofDual ⁻¹' s in 𝓝[>] toDual a ↔ _ := mem_nhdsGT_iff_exists_Ioc_subset
  simpa using! this

Depends on / 依赖: mem_nhdsGT_iff_exists_Ioc_subset, ofDual, toDual
-/
theorem mem_nhdsLT_iff_exists_Ico_subset [NoMinOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s in 𝓝[<] a ↔ exists l in Iio a, Ico l a subseteq s := by
  have : ofDual ⁻¹' s in 𝓝[>] toDual a ↔ _ := mem_nhdsGT_iff_exists_Ioc_subset
  simpa using! this

/--
theorem `nhdsLT_basis_of_exists_lt` / 定理 `nhdsLT_basis_of_exists_lt`

English:
theorem nhdsLT_basis_of_exists_lt
  given: {a : α} (h : exists b, b < a)
  statement: (𝓝[<] a).HasBasis (· < a) (Ioo · a)
  proof: let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsLT_iff_exists_Ioo_subset' h⟩

中文:
定理 nhdsLT_basis_of_exists_lt
  条件: {a : α} (h : 存在 b, b < a)
  结论: (𝓝[<] a).HasBasis (· < a) (Ioo · a)
  证明: let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsLT_iff_exists_Ioo_subset' h⟩

Depends on / 依赖: mem_nhdsLT_iff_exists_Ioo_subset
-/
theorem nhdsLT_basis_of_exists_lt {a : α} (h : exists b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsLT_iff_exists_Ioo_subset' h⟩

/--
theorem `nhdsLT_basis` / 定理 `nhdsLT_basis`

English:
theorem nhdsLT_basis
  given: [NoMinOrder α] (a : α)
  statement: (𝓝[<] a).HasBasis (· < a) (Ioo · a)
  proof: nhdsLT_basis_of_exists_lt exists_lt a

中文:
定理 nhdsLT_basis
  条件: [NoMinOrder α] (a : α)
  结论: (𝓝[<] a).HasBasis (· < a) (Ioo · a)
  证明: nhdsLT_basis_of_exists_lt exists_lt a

Depends on / 依赖: exists_lt, nhdsLT_basis_of_exists_lt
-/
theorem nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
nhdsLT_basis_of_exists_lt exists_lt a

/--
lemma `nhdsLT_basis_Ico_of_exists_lt` / 引理 `nhdsLT_basis_Ico_of_exists_lt`

English:
lemma nhdsLT_basis_Ico_of_exists_lt
  given: [DenselyOrdered α] {a : α} (h : exists b, b < a)
  proof: .to_hasBasis' nhdsLT_basis_of_exists_lt h
    (fun _ hac =>
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hbc, Ico_subset_Ioo_left hab⟩)
      fun _ hac => mem_of_superset ((nhdsLT_basis_of_exists_lt h).mem_of_mem hac) Ioo_subset_Ico_self

中文:
引理 nhdsLT_basis_Ico_of_exists_lt
  条件: [DenselyOrdered α] {a : α} (h : 存在 b, b < a)
  证明: .to_hasBasis' nhdsLT_basis_of_exists_lt h
    (fun _ hac =>
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hbc, Ico_subset_Ioo_left hab⟩)
      fun _ hac => mem_of_superset ((nhdsLT_basis_of_exists_lt h).mem_of_mem hac) Ioo_subset_Ico_self

Depends on / 依赖: Ico_subset_Ioo_left, Ioo_subset_Ico_self, exists_between, mem_of_mem, mem_of_superset, nhdsLT_basis_of_exists_lt, to_hasBasis
-/
lemma nhdsLT_basis_Ico_of_exists_lt [DenselyOrdered α] {a : α} (h : exists b, b < a) :
    (𝓝[<] a).HasBasis (· < a) (Ico · a) :=
.to_hasBasis' nhdsLT_basis_of_exists_lt h
    (fun _ hac =>
      have ⟨b, hab, hbc⟩ := exists_between hac
      ⟨b, hbc, Ico_subset_Ioo_left hab⟩)
      fun _ hac => mem_of_superset ((nhdsLT_basis_of_exists_lt h).mem_of_mem hac) Ioo_subset_Ico_self

/--
lemma `nhdsLT_basis_Ico` / 引理 `nhdsLT_basis_Ico`

English:
lemma nhdsLT_basis_Ico
  given: [DenselyOrdered α] [NoMinOrder α] (a : α)
  proof: nhdsLT_basis_Ico_of_exists_lt exists_lt a

中文:
引理 nhdsLT_basis_Ico
  条件: [DenselyOrdered α] [NoMinOrder α] (a : α)
  证明: nhdsLT_basis_Ico_of_exists_lt exists_lt a

Depends on / 依赖: exists_lt, nhdsLT_basis_Ico_of_exists_lt
-/
lemma nhdsLT_basis_Ico [DenselyOrdered α] [NoMinOrder α] (a : α) :
    (𝓝[<] a).HasBasis (· < a) (Ico · a) :=
nhdsLT_basis_Ico_of_exists_lt exists_lt a

/--
theorem `nhdsLT_eq_bot_iff` / 定理 `nhdsLT_eq_bot_iff`

English:
theorem nhdsLT_eq_bot_iff
  given: {a : α}
  statement: 𝓝[<] a = ⊥ ↔ IsBot a ∨ exists b, b ⋖ a
  proof: by
  convert! (config := { preTransparency := .default })
    nhdsGT_eq_bot_iff (a := OrderDual.toDual a) using 4
  exact ofDual_covBy_ofDual_iff

中文:
定理 nhdsLT_eq_bot_iff
  条件: {a : α}
  结论: 𝓝[<] a = ⊥ ↔ IsBot a ∨ 存在 b, b ⋖ a
  证明: by
  convert! (config := { preTransparency := .default })
    nhdsGT_eq_bot_iff (a := OrderDual.toDual a) using 4
  exact ofDual_covBy_ofDual_iff

Depends on / 依赖: OrderDual, OrderDual.toDual, config, convert, nhdsGT_eq_bot_iff, ofDual_covBy_ofDual_iff, preTransparency, toDual
-/
theorem nhdsLT_eq_bot_iff {a : α} : 𝓝[<] a = ⊥ ↔ IsBot a ∨ exists b, b ⋖ a := by
  convert! (config := { preTransparency := .default })
    nhdsGT_eq_bot_iff (a := OrderDual.toDual a) using 4
  exact ofDual_covBy_ofDual_iff

open List in
/--
theorem `TFAE_mem_nhdsGE` / 定理 `TFAE_mem_nhdsGE`

English:
theorem TFAE_mem_nhdsGE
  given: {a b : α} (hab : a < b) (s : Set α)
  proof: by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsGE hab]
  tfae_have 1 ↔ 5 := (nhdsGE_basis_of_exists_gt ⟨b, hab⟩).mem_iff
  tfae_have 4 -> 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 -> 4
  | ⟨u, hua, hus⟩ => ⟨min u b

中文:
定理 TFAE_mem_nhdsGE
  条件: {a b : α} (hab : a < b) (s : Set α)
  证明: by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsGE hab]
  tfae_have 1 ↔ 5 := (nhdsGE_basis_of_exists_gt ⟨b, hab⟩).mem_iff
  tfae_have 4 -> 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 -> 4
  | ⟨u, hua, hus⟩ => ⟨min u b

Depends on / 依赖: Ico_subset_Ico_right, lt_min, mem_iff, min_le_left, min_le_right, nhdsGE_basis_of_exists_gt, nhdsWithin_Icc_eq_nhdsGE, nhdsWithin_Ico_eq_nhdsGE, tfae_finish, tfae_have
-/
theorem TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s in 𝓝[>=] a,
      s in 𝓝[Icc a b] a,
      s in 𝓝[Ico a b] a,
      exists u in Ioc a b, Ico a u subseteq s,
      exists u in Ioi a, Ico a u subseteq s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsGE hab]
  tfae_have 1 ↔ 5 := (nhdsGE_basis_of_exists_gt ⟨b, hab⟩).mem_iff
  tfae_have 4 -> 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 -> 4
  | ⟨u, hua, hus⟩ => ⟨min u b, ⟨lt_min hua hab, min_le_right _ _⟩,
      (Ico_subset_Ico_right <| min_le_left _ _).trans hus⟩
  tfae_finish

/--
theorem `mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset` / 定理 `mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset`

English:
theorem mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset
  given: {a u' : α} {s : Set α} (hu' : a < u')
  proof: (TFAE_mem_nhdsGE hu' s).out 0 3 (by simp) (by simp)

中文:
定理 mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset
  条件: {a u' : α} {s : Set α} (hu' : a < u')
  证明: (TFAE_mem_nhdsGE hu' s).out 0 3 (by simp) (by simp)

Depends on / 依赖: TFAE_mem_nhdsGE
-/
theorem mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s in 𝓝[>=] a ↔ exists u in Ioc a u', Ico a u subseteq s :=
  (TFAE_mem_nhdsGE hu' s).out 0 3 (by simp) (by simp)

/--
theorem `mem_nhdsGE_iff_exists_Ico_subset'` / 定理 `mem_nhdsGE_iff_exists_Ico_subset'`

English:
theorem mem_nhdsGE_iff_exists_Ico_subset'
  given: {a u' : α} {s : Set α} (hu' : a < u')
  proof: (TFAE_mem_nhdsGE hu' s).out 0 4 (by simp) (by simp)

中文:
定理 mem_nhdsGE_iff_exists_Ico_subset'
  条件: {a u' : α} {s : Set α} (hu' : a < u')
  证明: (TFAE_mem_nhdsGE hu' s).out 0 4 (by simp) (by simp)

Depends on / 依赖: TFAE_mem_nhdsGE
-/
theorem mem_nhdsGE_iff_exists_Ico_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u subseteq s :=
  (TFAE_mem_nhdsGE hu' s).out 0 4 (by simp) (by simp)

/--
theorem `mem_nhdsGE_iff_exists_Ico_subset` / 定理 `mem_nhdsGE_iff_exists_Ico_subset`

English:
theorem mem_nhdsGE_iff_exists_Ico_subset
  given: [NoMaxOrder α] {a : α} {s : Set α}
  proof: let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsGE_iff_exists_Ico_subset' hu'

中文:
定理 mem_nhdsGE_iff_exists_Ico_subset
  条件: [NoMaxOrder α] {a : α} {s : Set α}
  证明: let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsGE_iff_exists_Ico_subset' hu'

Depends on / 依赖: exists_gt, mem_nhdsGE_iff_exists_Ico_subset
-/
theorem mem_nhdsGE_iff_exists_Ico_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u subseteq s :=
  let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsGE_iff_exists_Ico_subset' hu'

/--
theorem `nhdsGE_basis_Ico` / 定理 `nhdsGE_basis_Ico`

English:
theorem nhdsGE_basis_Ico
  given: [NoMaxOrder α] (a : α)
  statement: (𝓝[>=] a).HasBasis (fun u => a < u) (Ico a)
  proof: ⟨fun _ => mem_nhdsGE_iff_exists_Ico_subset⟩

中文:
定理 nhdsGE_basis_Ico
  条件: [NoMaxOrder α] (a : α)
  结论: (𝓝[>=] a).HasBasis (fun u => a < u) (Ico a)
  证明: ⟨fun _ => mem_nhdsGE_iff_exists_Ico_subset⟩

Depends on / 依赖: mem_nhdsGE_iff_exists_Ico_subset
-/
theorem nhdsGE_basis_Ico [NoMaxOrder α] (a : α) : (𝓝[>=] a).HasBasis (fun u => a < u) (Ico a) :=
  ⟨fun _ => mem_nhdsGE_iff_exists_Ico_subset⟩

/--
theorem `nhdsGE_basis_Icc` / 定理 `nhdsGE_basis_Icc`

English:
theorem nhdsGE_basis_Icc
  given: [NoMaxOrder α] [DenselyOrdered α] {a : α}
  proof: (nhdsGE_basis _).to_hasBasis
    (fun _u hu => (exists_between hu).imp fun _v hv => hv.imp_right Icc_subset_Ico_right) fun u hu =>
    ⟨u, hu, Ico_subset_Icc_self⟩

中文:
定理 nhdsGE_basis_Icc
  条件: [NoMaxOrder α] [DenselyOrdered α] {a : α}
  证明: (nhdsGE_basis _).to_hasBasis
    (fun _u hu => (exists_between hu).imp fun _v hv => hv.imp_right Icc_subset_Ico_right) fun u hu =>
    ⟨u, hu, Ico_subset_Icc_self⟩

Depends on / 依赖: Icc_subset_Ico_right, Ico_subset_Icc_self, exists_between, hv.imp_right, imp_right, nhdsGE_basis, to_hasBasis
-/
theorem nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[>=] a).HasBasis (a < ·) (Icc a) :=
  (nhdsGE_basis _).to_hasBasis
    (fun _u hu => (exists_between hu).imp fun _v hv => hv.imp_right Icc_subset_Ico_right) fun u hu =>
    ⟨u, hu, Ico_subset_Icc_self⟩

/--
theorem `mem_nhdsGE_iff_exists_Icc_subset` / 定理 `mem_nhdsGE_iff_exists_Icc_subset`

English:
theorem mem_nhdsGE_iff_exists_Icc_subset
  given: [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α}
  proof: nhdsGE_basis_Icc.mem_iff

中文:
定理 mem_nhdsGE_iff_exists_Icc_subset
  条件: [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α}
  证明: nhdsGE_basis_Icc.mem_iff

Depends on / 依赖: mem_iff, nhdsGE_basis_Icc, nhdsGE_basis_Icc.mem_iff
-/
theorem mem_nhdsGE_iff_exists_Icc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s in 𝓝[>=] a ↔ exists u, a < u ∧ Icc a u subseteq s :=
  nhdsGE_basis_Icc.mem_iff

open List in
/--
theorem `TFAE_mem_nhdsLE` / 定理 `TFAE_mem_nhdsLE`

English:
theorem TFAE_mem_nhdsLE
  given: {a b : α} (h : a < b) (s : Set α)
  proof: by -- 4 : `s` includes `(l, b]` for some `l < b`
  simpa using! TFAE_mem_nhdsGE h.dual (ofDual ⁻¹' s)

中文:
定理 TFAE_mem_nhdsLE
  条件: {a b : α} (h : a < b) (s : Set α)
  证明: by -- 4 : `s` includes `(l, b]` for some `l < b`
  simpa using! TFAE_mem_nhdsGE h.dual (ofDual ⁻¹' s)

Depends on / 依赖: TFAE_mem_nhdsGE, h.dual, includes, ofDual
-/
theorem TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) :
    TFAE [s in 𝓝[<=] b, -- 0 : `s` is a neighborhood of `b` within `(-∞, b]`
      s in 𝓝[Icc a b] b, -- 1 : `s` is a neighborhood of `b` within `[a, b]`
      s in 𝓝[Ioc a b] b, -- 2 : `s` is a neighborhood of `b` within `(a, b]`
      exists l in Ico a b, Ioc l b subseteq s, -- 3 : `s` includes `(l, b]` for some `l ∈ [a, b)`
      exists l in Iio b, Ioc l b subseteq s] := by -- 4 : `s` includes `(l, b]` for some `l < b`
  simpa using! TFAE_mem_nhdsGE h.dual (ofDual ⁻¹' s)

/--
theorem `mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset` / 定理 `mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset`

English:
theorem mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset
  given: {a l' : α} {s : Set α} (hl' : l' < a)
  proof: (TFAE_mem_nhdsLE hl' s).out 0 3 (by simp) (by simp)

中文:
定理 mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset
  条件: {a l' : α} {s : Set α} (hl' : l' < a)
  证明: (TFAE_mem_nhdsLE hl' s).out 0 3 (by simp) (by simp)

Depends on / 依赖: TFAE_mem_nhdsLE
-/
theorem mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s in 𝓝[<=] a ↔ exists l in Ico l' a, Ioc l a subseteq s :=
  (TFAE_mem_nhdsLE hl' s).out 0 3 (by simp) (by simp)

/--
theorem `mem_nhdsLE_iff_exists_Ioc_subset'` / 定理 `mem_nhdsLE_iff_exists_Ioc_subset'`

English:
theorem mem_nhdsLE_iff_exists_Ioc_subset'
  given: {a l' : α} {s : Set α} (hl' : l' < a)
  proof: (TFAE_mem_nhdsLE hl' s).out 0 4 (by simp) (by simp)

中文:
定理 mem_nhdsLE_iff_exists_Ioc_subset'
  条件: {a l' : α} {s : Set α} (hl' : l' < a)
  证明: (TFAE_mem_nhdsLE hl' s).out 0 4 (by simp) (by simp)

Depends on / 依赖: TFAE_mem_nhdsLE
-/
theorem mem_nhdsLE_iff_exists_Ioc_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s in 𝓝[<=] a ↔ exists l in Iio a, Ioc l a subseteq s :=
  (TFAE_mem_nhdsLE hl' s).out 0 4 (by simp) (by simp)

/--
theorem `mem_nhdsLE_iff_exists_Ioc_subset` / 定理 `mem_nhdsLE_iff_exists_Ioc_subset`

English:
theorem mem_nhdsLE_iff_exists_Ioc_subset
  given: [NoMinOrder α] {a : α} {s : Set α}
  proof: let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsLE_iff_exists_Ioc_subset' hl'

中文:
定理 mem_nhdsLE_iff_exists_Ioc_subset
  条件: [NoMinOrder α] {a : α} {s : Set α}
  证明: let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsLE_iff_exists_Ioc_subset' hl'

Depends on / 依赖: exists_lt, mem_nhdsLE_iff_exists_Ioc_subset
-/
theorem mem_nhdsLE_iff_exists_Ioc_subset [NoMinOrder α] {a : α} {s : Set α} :
    s in 𝓝[<=] a ↔ exists l in Iio a, Ioc l a subseteq s :=
  let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsLE_iff_exists_Ioc_subset' hl'

/--
theorem `mem_nhdsLE_iff_exists_Icc_subset` / 定理 `mem_nhdsLE_iff_exists_Icc_subset`

English:
theorem mem_nhdsLE_iff_exists_Icc_subset
  statement: [NoMinOrder α] [DenselyOrdered α] {a : α}
  proof: calc s in 𝓝[<=] a ↔ ofDual ⁻¹' s in 𝓝[>=] (toDual a) := Iff.rfl
  _ ↔ exists u : α, toDual a < toDual u ∧ Icc (toDual a) (toDual u) subseteq ofDual ⁻¹' s :=
    mem_nhdsGE_iff_exists_Icc_subset
  _ ↔ exists l, l < a ∧ Icc l a subseteq s := by simp

中文:
定理 mem_nhdsLE_iff_exists_Icc_subset
  结论: [NoMinOrder α] [DenselyOrdered α] {a : α}
  证明: calc s in 𝓝[<=] a ↔ ofDual ⁻¹' s in 𝓝[>=] (toDual a) := Iff.rfl
  _ ↔ exists u : α, toDual a < toDual u ∧ Icc (toDual a) (toDual u) subseteq ofDual ⁻¹' s :=
    mem_nhdsGE_iff_exists_Icc_subset
  _ ↔ exists l, l < a ∧ Icc l a subseteq s := by simp

Depends on / 依赖: Iff.rfl, mem_nhdsGE_iff_exists_Icc_subset, ofDual, subseteq, toDual
-/
theorem mem_nhdsLE_iff_exists_Icc_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s in 𝓝[<=] a ↔ exists l, l < a ∧ Icc l a subseteq s :=
  calc s in 𝓝[<=] a ↔ ofDual ⁻¹' s in 𝓝[>=] (toDual a) := Iff.rfl
  _ ↔ exists u : α, toDual a < toDual u ∧ Icc (toDual a) (toDual u) subseteq ofDual ⁻¹' s :=
    mem_nhdsGE_iff_exists_Icc_subset
  _ ↔ exists l, l < a ∧ Icc l a subseteq s := by simp

/--
theorem `nhdsLE_basis_Icc` / 定理 `nhdsLE_basis_Icc`

English:
theorem nhdsLE_basis_Icc
  given: [NoMinOrder α] [DenselyOrdered α] {a : α}
  proof: ⟨fun _ => mem_nhdsLE_iff_exists_Icc_subset⟩

中文:
定理 nhdsLE_basis_Icc
  条件: [NoMinOrder α] [DenselyOrdered α] {a : α}
  证明: ⟨fun _ => mem_nhdsLE_iff_exists_Icc_subset⟩

Depends on / 依赖: mem_nhdsLE_iff_exists_Icc_subset
-/
theorem nhdsLE_basis_Icc [NoMinOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[<=] a).HasBasis (· < a) (Icc · a) :=
  ⟨fun _ => mem_nhdsLE_iff_exists_Icc_subset⟩

end OrderTopology

end LinearOrder

section LinearOrderedCommGroup

variable [TopologicalSpace α] [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
  [OrderTopology α]
variable {l : Filter β} {f g : β -> α}

@[to_additive]
/--
theorem `nhds_eq_iInf_mabs_div` / 定理 `nhds_eq_iInf_mabs_div`

English:
theorem nhds_eq_iInf_mabs_div
  given: (a : α)
  statement: 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }
  proof: by
  simp only [nhds_eq_order, mabs_lt, ofPred_and, ← inf_principal, iInf_inf_eq]
  refine (congr_arg₂ _ ?_ ?_).trans (inf_comm ..)
  · refine (Equiv.divLeft a).iInf_congr fun x => ?_; simp [Ioi]
  · refine (Equiv.divRight a).iInf_congr fun x => ?_; simp [Iio]

@[to_additive]

中文:
定理 nhds_eq_iInf_mabs_div
  条件: (a : α)
  结论: 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }
  证明: by
  simp only [nhds_eq_order, mabs_lt, ofPred_and, ← inf_principal, iInf_inf_eq]
  refine (congr_arg₂ _ ?_ ?_).trans (inf_comm ..)
  · refine (Equiv.divLeft a).iInf_congr fun x => ?_; simp [Ioi]
  · refine (Equiv.divRight a).iInf_congr fun x => ?_; simp [Iio]

@[to_additive]

Depends on / 依赖: Equiv.divLeft, Equiv.divRight, divLeft, divRight, iInf_congr, iInf_inf_eq, inf_comm, inf_principal, mabs_lt, nhds_eq_order, ofPred_and
-/
theorem nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r } := by
  simp only [nhds_eq_order, mabs_lt, ofPred_and, ← inf_principal, iInf_inf_eq]
  refine (congr_arg₂ _ ?_ ?_).trans (inf_comm ..)
  · refine (Equiv.divLeft a).iInf_congr fun x => ?_; simp [Ioi]
  · refine (Equiv.divRight a).iInf_congr fun x => ?_; simp [Iio]

@[to_additive]
/--
theorem `orderTopology_of_nhds_mabs` / 定理 `orderTopology_of_nhds_mabs`

English:
theorem orderTopology_of_nhds_mabs
  statement: {α : Type*} [TopologicalSpace α] [CommGroup α] [LinearOrder α]
  proof: by
  refine ⟨TopologicalSpace.ext_nhds fun a => ?_⟩
  rw [h_nhds]
  let := Preorder.topology α; let : OrderTopology α := ⟨rfl⟩
  exact (nhds_eq_iInf_mabs_div a).symm

@[to_additive]

中文:
定理 orderTopology_of_nhds_mabs
  结论: {α : 类型} [TopologicalSpace α] [CommGroup α] [LinearOrder α]
  证明: by
  refine ⟨TopologicalSpace.ext_nhds fun a => ?_⟩
  rw [h_nhds]
  let := Preorder.topology α; let : OrderTopology α := ⟨rfl⟩
  exact (nhds_eq_iInf_mabs_div a).symm

@[to_additive]

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, TopologicalSpace.ext_nhds, ext_nhds, h_nhds, nhds_eq_iInf_mabs_div, topology
-/
theorem orderTopology_of_nhds_mabs {α : Type*} [TopologicalSpace α] [CommGroup α] [LinearOrder α]
    [IsOrderedMonoid α]
    (h_nhds : forall a : α, 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }) : OrderTopology α := by
  refine ⟨TopologicalSpace.ext_nhds fun a => ?_⟩
  rw [h_nhds]
  let := Preorder.topology α; let : OrderTopology α := ⟨rfl⟩
  exact (nhds_eq_iInf_mabs_div a).symm

@[to_additive]
/--
theorem `LinearOrderedCommGroup.tendsto_nhds` / 定理 `LinearOrderedCommGroup.tendsto_nhds`

English:
theorem LinearOrderedCommGroup.tendsto_nhds
  given: {x : Filter β} {a : α}
  proof: by
  simp [nhds_eq_iInf_mabs_div, mabs_div_comm a]

@[to_additive]

中文:
定理 LinearOrderedCommGroup.tendsto_nhds
  条件: {x : Filter β} {a : α}
  证明: by
  simp [nhds_eq_iInf_mabs_div, mabs_div_comm a]

@[to_additive]

Depends on / 依赖: mabs_div_comm, nhds_eq_iInf_mabs_div
-/
theorem LinearOrderedCommGroup.tendsto_nhds {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ forall ε > (1 : α), forallᶠ b in x, |f b / a|ₘ < ε := by
  simp [nhds_eq_iInf_mabs_div, mabs_div_comm a]

@[to_additive]
/--
theorem `eventually_mabs_div_lt` / 定理 `eventually_mabs_div_lt`

English:
theorem eventually_mabs_div_lt
  given: (a : α) {ε : α} (hε : 1 < ε)
  statement: forallᶠ x in 𝓝 a, |x / a|ₘ < ε
  proof: (nhds_eq_iInf_mabs_div a).symm ▸
    mem_iInf_of_mem ε (mem_iInf_of_mem hε <| by simp only [mabs_div_comm, mem_principal_self])

中文:
定理 eventually_mabs_div_lt
  条件: (a : α) {ε : α} (hε : 1 < ε)
  结论: 对任意ᶠ x in 𝓝 a, |x / a|ₘ < ε
  证明: (nhds_eq_iInf_mabs_div a).symm ▸
    mem_iInf_of_mem ε (mem_iInf_of_mem hε <| by simp only [mabs_div_comm, mem_principal_self])

Depends on / 依赖: mabs_div_comm, mem_iInf_of_mem, mem_principal_self, nhds_eq_iInf_mabs_div
-/
theorem eventually_mabs_div_lt (a : α) {ε : α} (hε : 1 < ε) : forallᶠ x in 𝓝 a, |x / a|ₘ < ε :=
  (nhds_eq_iInf_mabs_div a).symm ▸
    mem_iInf_of_mem ε (mem_iInf_of_mem hε <| by simp only [mabs_div_comm, mem_principal_self])

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `C` and `g` tends to `atTop` then `f * g` tends to `atTop`. -/
@[to_additive add_atTop /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `C` and `g` tends to `atTop` then `f + g` tends to `atTop`. -/]
/--
theorem `Filter.Tendsto.mul_atTop'` / 定理 `Filter.Tendsto.mul_atTop'`

English:
theorem Filter.Tendsto.mul_atTop'
  given: {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop)
  proof: by
  nontriviality α
  obtain ⟨C', hC'⟩ : exists C', C' < C := exists_lt C
  refine tendsto_atTop_mul_left_of_le' _ C' ?_ hg
  exact (hf.eventually (lt_mem_nhds hC')).mono fun x => le_of_lt

中文:
定理 Filter.Tendsto.mul_atTop'
  条件: {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop)
  证明: by
  nontriviality α
  obtain ⟨C', hC'⟩ : exists C', C' < C := exists_lt C
  refine tendsto_atTop_mul_left_of_le' _ C' ?_ hg
  exact (hf.eventually (lt_mem_nhds hC')).mono fun x => le_of_lt

Depends on / 依赖: eventually, exists_lt, hf.eventually, le_of_lt, lt_mem_nhds, nontriviality, tendsto_atTop_mul_left_of_le
-/
theorem Filter.Tendsto.mul_atTop' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop := by
  nontriviality α
  obtain ⟨C', hC'⟩ : exists C', C' < C := exists_lt C
  refine tendsto_atTop_mul_left_of_le' _ C' ?_ hg
  exact (hf.eventually (lt_mem_nhds hC')).mono fun x => le_of_lt

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `C` and `g` tends to `atBot` then `f * g` tends to `atBot`. -/
@[to_additive add_atBot /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `C` and `g` tends to `atBot` then `f + g` tends to `atBot`. -/]
/--
theorem `Filter.Tendsto.mul_atBot'` / 定理 `Filter.Tendsto.mul_atBot'`

English:
theorem Filter.Tendsto.mul_atBot'
  given: {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atBot)
  proof: Filter.Tendsto.mul_atTop' (α := αᵒᵈ) hf hg

中文:
定理 Filter.Tendsto.mul_atBot'
  条件: {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atBot)
  证明: Filter.Tendsto.mul_atTop' (α := αᵒᵈ) hf hg

Depends on / 依赖: Filter, Filter.Tendsto.mul_atTop, Tendsto, mul_atTop
-/
theorem Filter.Tendsto.mul_atBot' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  Filter.Tendsto.mul_atTop' (α := αᵒᵈ) hf hg

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `atTop` and `g` tends to `C` then `f * g` tends to `atTop`. -/
@[to_additive atTop_add /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `atTop` and `g` tends to `C` then `f + g` tends to `atTop`. -/]
/--
theorem `Filter.Tendsto.atTop_mul'` / 定理 `Filter.Tendsto.atTop_mul'`

English:
theorem Filter.Tendsto.atTop_mul'
  given: {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C))
  proof: by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atTop' hf

中文:
定理 Filter.Tendsto.atTop_mul'
  条件: {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C))
  证明: by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atTop' hf

Depends on / 依赖: hg.mul_atTop, mul_atTop, mul_comm
-/
theorem Filter.Tendsto.atTop_mul' {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x * g x) l atTop := by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atTop' hf

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `atBot` and `g` tends to `C` then `f * g` tends to `atBot`. -/
@[to_additive atBot_add /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `atBot` and `g` tends to `C` then `f + g` tends to `atBot`. -/]
/--
theorem `Filter.Tendsto.atBot_mul'` / 定理 `Filter.Tendsto.atBot_mul'`

English:
theorem Filter.Tendsto.atBot_mul'
  given: {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C))
  proof: by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atBot' hf

@[to_additive]

中文:
定理 Filter.Tendsto.atBot_mul'
  条件: {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C))
  证明: by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atBot' hf

@[to_additive]

Depends on / 依赖: hg.mul_atBot, mul_atBot, mul_comm
-/
theorem Filter.Tendsto.atBot_mul' {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x * g x) l atBot := by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atBot' hf

@[to_additive]
/--
theorem `nhds_basis_mabs_div_lt` / 定理 `nhds_basis_mabs_div_lt`

English:
theorem nhds_basis_mabs_div_lt
  given: [NoMaxOrder α] (a : α)
  proof: by
  simp only [nhds_eq_iInf_mabs_div, mabs_div_comm (a := a)]
  refine hasBasis_biInf_principal' (fun x hx y hy => ?_) (exists_gt _)
  exact ⟨min x y, lt_min hx hy, fun _ hz => hz.trans_le (min_le_left _ _),
    fun _ hz => hz.trans_le (min_le_right _ _)⟩

@[to_additive]

中文:
定理 nhds_basis_mabs_div_lt
  条件: [NoMaxOrder α] (a : α)
  证明: by
  simp only [nhds_eq_iInf_mabs_div, mabs_div_comm (a := a)]
  refine hasBasis_biInf_principal' (fun x hx y hy => ?_) (exists_gt _)
  exact ⟨min x y, lt_min hx hy, fun _ hz => hz.trans_le (min_le_left _ _),
    fun _ hz => hz.trans_le (min_le_right _ _)⟩

@[to_additive]

Depends on / 依赖: exists_gt, hasBasis_biInf_principal, hz.trans_le, lt_min, mabs_div_comm, min_le_left, min_le_right, nhds_eq_iInf_mabs_div, trans_le
-/
theorem nhds_basis_mabs_div_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b / a|ₘ < ε } := by
  simp only [nhds_eq_iInf_mabs_div, mabs_div_comm (a := a)]
  refine hasBasis_biInf_principal' (fun x hx y hy => ?_) (exists_gt _)
  exact ⟨min x y, lt_min hx hy, fun _ hz => hz.trans_le (min_le_left _ _),
    fun _ hz => hz.trans_le (min_le_right _ _)⟩

@[to_additive]
/--
theorem `nhds_basis_Ioo_one_lt` / 定理 `nhds_basis_Ioo_one_lt`

English:
theorem nhds_basis_Ioo_one_lt
  given: [NoMaxOrder α] (a : α)
  proof: by
  convert! nhds_basis_mabs_div_lt a
  simp only [Ioo, mabs_lt, ← div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, div_lt_comm]

@[to_additive]

中文:
定理 nhds_basis_Ioo_one_lt
  条件: [NoMaxOrder α] (a : α)
  证明: by
  convert! nhds_basis_mabs_div_lt a
  simp only [Ioo, mabs_lt, ← div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, div_lt_comm]

@[to_additive]

Depends on / 依赖: convert, div_lt_comm, div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, mabs_lt, nhds_basis_mabs_div_lt
-/
theorem nhds_basis_Ioo_one_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => Ioo (a / ε) (a * ε) := by
  convert! nhds_basis_mabs_div_lt a
  simp only [Ioo, mabs_lt, ← div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, div_lt_comm]

@[to_additive]
/--
theorem `nhds_basis_Icc_one_lt` / 定理 `nhds_basis_Icc_one_lt`

English:
theorem nhds_basis_Icc_one_lt
  given: [NoMaxOrder α] [DenselyOrdered α] (a : α)
  proof: (nhds_basis_Ioo_one_lt a).to_hasBasis
    (fun _ε ε₁ => let ⟨δ, δ₁, δε⟩ := exists_between ε₁
      ⟨δ, δ₁, Icc_subset_Ioo (by gcongr) (by gcongr)⟩)
    (fun ε ε₁ => ⟨ε, ε₁, Ioo_subset_Icc_self⟩)

中文:
定理 nhds_basis_Icc_one_lt
  条件: [NoMaxOrder α] [DenselyOrdered α] (a : α)
  证明: (nhds_basis_Ioo_one_lt a).to_hasBasis
    (fun _ε ε₁ => let ⟨δ, δ₁, δε⟩ := exists_between ε₁
      ⟨δ, δ₁, Icc_subset_Ioo (by gcongr) (by gcongr)⟩)
    (fun ε ε₁ => ⟨ε, ε₁, Ioo_subset_Icc_self⟩)

Depends on / 依赖: Icc_subset_Ioo, Ioo_subset_Icc_self, exists_between, nhds_basis_Ioo_one_lt, to_hasBasis
-/
theorem nhds_basis_Icc_one_lt [NoMaxOrder α] [DenselyOrdered α] (a : α) :
    (𝓝 a).HasBasis ((1 : α) < ·) fun ε => Icc (a / ε) (a * ε) :=
  (nhds_basis_Ioo_one_lt a).to_hasBasis
    (fun _ε ε₁ => let ⟨δ, δ₁, δε⟩ := exists_between ε₁
      ⟨δ, δ₁, Icc_subset_Ioo (by gcongr) (by gcongr)⟩)
    (fun ε ε₁ => ⟨ε, ε₁, Ioo_subset_Icc_self⟩)

variable (α) in
@[to_additive]
/--
theorem `nhds_basis_one_mabs_lt` / 定理 `nhds_basis_one_mabs_lt`

English:
theorem nhds_basis_one_mabs_lt
  given: [NoMaxOrder α]
  proof: by
  simpa using nhds_basis_mabs_div_lt (1 : α)

中文:
定理 nhds_basis_one_mabs_lt
  条件: [NoMaxOrder α]
  证明: by
  simpa using nhds_basis_mabs_div_lt (1 : α)

Depends on / 依赖: nhds_basis_mabs_div_lt
-/
theorem nhds_basis_one_mabs_lt [NoMaxOrder α] :
    (𝓝 (1 : α)).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b|ₘ < ε } := by
  simpa using nhds_basis_mabs_div_lt (1 : α)

/-- If `a > 1`, then open intervals `(a / ε, aε)`, `1 < ε ≤ a`,
form a basis of neighborhoods of `a`.

This upper bound for `ε` guarantees that all elements of these intervals are greater than one. -/
@[to_additive /-- If `a` is positive, then the intervals `(a - ε, a + ε)`, `0 < ε ≤ a`,
form a basis of neighborhoods of `a`.

This upper bound for `ε` guarantees that all elements of these intervals are positive. -/]
/--
theorem `nhds_basis_Ioo_one_lt_of_one_lt` / 定理 `nhds_basis_Ioo_one_lt_of_one_lt`

English:
theorem nhds_basis_Ioo_one_lt_of_one_lt
  given: [NoMaxOrder α] {a : α} (ha : 1 < a)
  proof: (nhds_basis_Ioo_one_lt a).restrict fun ε hε =>
    ⟨min a ε, lt_min ha hε, min_le_left _ _, by gcongr <;> apply min_le_right⟩

中文:
定理 nhds_basis_Ioo_one_lt_of_one_lt
  条件: [NoMaxOrder α] {a : α} (ha : 1 < a)
  证明: (nhds_basis_Ioo_one_lt a).restrict fun ε hε =>
    ⟨min a ε, lt_min ha hε, min_le_left _ _, by gcongr <;> apply min_le_right⟩

Depends on / 依赖: lt_min, min_le_left, min_le_right, nhds_basis_Ioo_one_lt, restrict
-/
theorem nhds_basis_Ioo_one_lt_of_one_lt [NoMaxOrder α] {a : α} (ha : 1 < a) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε ∧ ε <= a) fun ε => Ioo (a / ε) (a * ε) :=
  (nhds_basis_Ioo_one_lt a).restrict fun ε hε =>
    ⟨min a ε, lt_min ha hε, min_le_left _ _, by gcongr <;> apply min_le_right⟩

end LinearOrderedCommGroup

namespace Set.OrdConnected

section ClosedIciTopology

variable [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α] {S : Set α} {x y : α}

/--
lemma `mem_nhdsGE` / 引理 `mem_nhdsGE`

English:
lemma mem_nhdsGE
  given: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  statement: S in 𝓝[>=] x
  proof: mem_of_superset (Icc_mem_nhdsGE hxy) hS.out hx hy

中文:
引理 mem_nhdsGE
  条件: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  结论: S in 𝓝[>=] x
  证明: mem_of_superset (Icc_mem_nhdsGE hxy) hS.out hx hy

Depends on / 依赖: Icc_mem_nhdsGE, hS.out, mem_of_superset
-/
lemma mem_nhdsGE (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y) : S in 𝓝[>=] x :=
mem_of_superset (Icc_mem_nhdsGE hxy) hS.out hx hy

/--
lemma `mem_nhdsGT` / 引理 `mem_nhdsGT`

English:
lemma mem_nhdsGT
  given: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  statement: S in 𝓝[>] x
  proof: nhdsWithin_mono _ Ioi_subset_Ici_self hS.mem_nhdsGE hx hy hxy

中文:
引理 mem_nhdsGT
  条件: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  结论: S in 𝓝[>] x
  证明: nhdsWithin_mono _ Ioi_subset_Ici_self hS.mem_nhdsGE hx hy hxy

Depends on / 依赖: Ioi_subset_Ici_self, hS.mem_nhdsGE, mem_nhdsGE, nhdsWithin_mono
-/
lemma mem_nhdsGT (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y) : S in 𝓝[>] x :=
nhdsWithin_mono _ Ioi_subset_Ici_self hS.mem_nhdsGE hx hy hxy

end ClosedIciTopology

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] {S : Set α} {x y : α}

/--
lemma `mem_nhdsLE` / 引理 `mem_nhdsLE`

English:
lemma mem_nhdsLE
  given: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  statement: S in 𝓝[<=] y
  proof: hS.dual.mem_nhdsGE hy hx hxy

中文:
引理 mem_nhdsLE
  条件: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  结论: S in 𝓝[<=] y
  证明: hS.dual.mem_nhdsGE hy hx hxy

Depends on / 依赖: hS.dual.mem_nhdsGE, mem_nhdsGE
-/
lemma mem_nhdsLE (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y) : S in 𝓝[<=] y :=
  hS.dual.mem_nhdsGE hy hx hxy

/--
lemma `mem_nhdsLT` / 引理 `mem_nhdsLT`

English:
lemma mem_nhdsLT
  given: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  statement: S in 𝓝[<] y
  proof: hS.dual.mem_nhdsGT hy hx hxy

中文:
引理 mem_nhdsLT
  条件: (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y)
  结论: S in 𝓝[<] y
  证明: hS.dual.mem_nhdsGT hy hx hxy

Depends on / 依赖: hS.dual.mem_nhdsGT, mem_nhdsGT
-/
lemma mem_nhdsLT (hS : OrdConnected S) (hx : x in S) (hy : y in S) (hxy : x < y) : S in 𝓝[<] y :=
  hS.dual.mem_nhdsGT hy hx hxy

end OrdConnected

end Set
