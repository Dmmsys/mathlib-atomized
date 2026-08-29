/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Lindelöf sets and Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof s`: Two definitions are possible here. The more standard definition is that
  every open cover that contains `s` contains a countable subcover. We choose for the equivalent
  definition where we require that every nontrivial filter on `s` with the countable intersection
  property has a cluster point. Equivalence is established in `isLindelof_iff_countable_subcover`.
* `LindelofSpace X`: `X` is Lindelöf if it is Lindelöf as a set.
* `NonLindelofSpace`: a space that is not a Lindelöf space, e.g. the Long Line.

## Main results

* `isLindelof_iff_countable_subcover`: A set is Lindelöf iff every open cover has a
  countable subcover.

## Implementation details

* This API is mainly based on the API for IsCompact and follows notation and style as much
  as possible.
-/

@[expose] public section
open Set Filter Topology TopologicalSpace


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Lindelof

/--
Definition of `IsLindelof` / `IsLindelof` 的定义

English:
definition IsLindelof
  signature: (s : Set X)
  body: forall ⦃f⦄ [NeBot f] [CountableInterFilter f], f <= 𝓟 s -> exists x in s, ClusterPt x f

中文:
定义 IsLindelof
  签名: (s : Set X)
  定义体: forall ⦃f⦄ [NeBot f] [CountableInterFilter f], f <= 𝓟 s -> exists x in s, ClusterPt x f

Depends on / 依赖: ClusterPt, CountableInterFilter
-/
def IsLindelof (s : Set X) :=
  forall ⦃f⦄ [NeBot f] [CountableInterFilter f], f <= 𝓟 s -> exists x in s, ClusterPt x f

/--
theorem `IsLindelof.compl_mem_sets` / 定理 `IsLindelof.compl_mem_sets`

English:
theorem IsLindelof.compl_mem_sets
  statement: (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
  proof: by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

中文:
定理 IsLindelof.compl_mem_sets
  结论: (hs : IsLindelof s) {f : Filter X} [Countable整数erFilter f]
  证明: by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

Depends on / 依赖: compl_compl, contrapose, inf_assoc, inf_le_right, notMem_iff_inf_principal_compl
-/
theorem IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
    (hf : forall x in s, sᶜ in 𝓝 x ⊓ f) : sᶜ in f := by
  contrapose! hf
  simp only [notMem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  exact hs inf_le_right

/--
theorem `IsLindelof.compl_mem_sets_of_nhdsWithin` / 定理 `IsLindelof.compl_mem_sets_of_nhdsWithin`

English:
theorem IsLindelof.compl_mem_sets_of_nhdsWithin
  statement: (hs : IsLindelof s) {f : Filter X}
  proof: by
  refine hs.compl_mem_sets fun x hx => ?_
  rw [← disjoint_principal_right]; rw [disjoint_right_comm]; rw [(basis_sets _).disjoint_iff_left]
  exact hf x hx

中文:
定理 IsLindelof.compl_mem_sets_of_nhdsWithin
  结论: (hs : IsLindelof s) {f : Filter X}
  证明: by
  refine hs.compl_mem_sets fun x hx => ?_
  rw [← disjoint_principal_right]; rw [disjoint_right_comm]; rw [(basis_sets _).disjoint_iff_left]
  exact hf x hx

Depends on / 依赖: basis_sets, compl_mem_sets, disjoint_iff_left, disjoint_principal_right, disjoint_right_comm, hs.compl_mem_sets
-/
theorem IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
    [CountableInterFilter f] (hf : forall x in s, exists t in 𝓝[s] x, tᶜ in f) : sᶜ in f := by
  refine hs.compl_mem_sets fun x hx => ?_
  rw [← disjoint_principal_right]; rw [disjoint_right_comm]; rw [(basis_sets _).disjoint_iff_left]
  exact hf x hx

set_option backward.isDefEq.respectTransparency false in
/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
/--
theorem `IsLindelof.induction_on` / 定理 `IsLindelof.induction_on`

English:
theorem IsLindelof.induction_on
  statement: (hs : IsLindelof s) {p : Set X -> Prop}
  proof: by
  let f : Filter X := ofCountableUnion {t | p t} hcountable_union (fun t ht _ hsub => hmono hsub ht)
  have : sᶜ in f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using! hnhds)
  rwa [← compl_compl s]

中文:
定理 IsLindelof.induction_on
  结论: (hs : IsLindelof s) {p : Set X -> 命题}
  证明: by
  let f : Filter X := ofCountableUnion {t | p t} hcountable_union (fun t ht _ hsub => hmono hsub ht)
  have : sᶜ in f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using! hnhds)
  rwa [← compl_compl s]

Depends on / 依赖: Filter, compl_compl, compl_mem_sets_of_nhdsWithin, hcountable_union, hs.compl_mem_sets_of_nhdsWithin, ofCountableUnion
-/
theorem IsLindelof.induction_on (hs : IsLindelof s) {p : Set X -> Prop}
    (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s)
    (hcountable_union : forall (S : Set (Set X)), S.Countable -> (forall s in S, p s) -> p (⋃₀ S))
    (hnhds : forall x in s, exists t in 𝓝[s] x, p t) : p s := by
  let f : Filter X := ofCountableUnion {t | p t} hcountable_union (fun t ht _ hsub => hmono hsub ht)
  have : sᶜ in f := hs.compl_mem_sets_of_nhdsWithin (by simpa [f] using! hnhds)
  rwa [← compl_compl s]

/--
theorem `IsLindelof.inter_right` / 定理 `IsLindelof.inter_right`

English:
theorem IsLindelof.inter_right
  given: (hs : IsLindelof s) (ht : IsClosed t)
  statement: IsLindelof (s inter t)
  proof: by
  intro f hnf _ hstf
  rw [← inf_principal]; rw [le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : exists x in s, ClusterPt x f := hs hstf.1
have hxt : x in t := ht.mem_of_nhdsWithin_neBot hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

中文:
定理 IsLindelof.inter_right
  条件: (hs : IsLindelof s) (ht : IsClosed t)
  结论: IsLindelof (s inter t)
  证明: by
  intro f hnf _ hstf
  rw [← inf_principal]; rw [le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : exists x in s, ClusterPt x f := hs hstf.1
have hxt : x in t := ht.mem_of_nhdsWithin_neBot hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

Depends on / 依赖: ClusterPt, ht.mem_of_nhdsWithin_neBot, hx.mono, inf_principal, le_inf_iff, mem_of_nhdsWithin_neBot
-/
theorem IsLindelof.inter_right (hs : IsLindelof s) (ht : IsClosed t) : IsLindelof (s inter t) := by
  intro f hnf _ hstf
  rw [← inf_principal]; rw [le_inf_iff] at hstf
  obtain ⟨x, hsx, hx⟩ : exists x in s, ClusterPt x f := hs hstf.1
have hxt : x in t := ht.mem_of_nhdsWithin_neBot hx.mono hstf.2
  exact ⟨x, ⟨hsx, hxt⟩, hx⟩

/--
theorem `IsLindelof.inter_left` / 定理 `IsLindelof.inter_left`

English:
theorem IsLindelof.inter_left
  given: (ht : IsLindelof t) (hs : IsClosed s)
  statement: IsLindelof (s inter t)
  proof: inter_comm t s ▸ ht.inter_right hs

中文:
定理 IsLindelof.inter_left
  条件: (ht : IsLindelof t) (hs : IsClosed s)
  结论: IsLindelof (s inter t)
  证明: inter_comm t s ▸ ht.inter_right hs

Depends on / 依赖: ht.inter_right, inter_comm, inter_right
-/
theorem IsLindelof.inter_left (ht : IsLindelof t) (hs : IsClosed s) : IsLindelof (s inter t) :=
  inter_comm t s ▸ ht.inter_right hs

/--
theorem `IsLindelof.diff` / 定理 `IsLindelof.diff`

English:
theorem IsLindelof.diff
  given: (hs : IsLindelof s) (ht : IsOpen t)
  statement: IsLindelof (s \ t)
  proof: hs.inter_right (isClosed_compl_iff.mpr ht)

中文:
定理 IsLindelof.diff
  条件: (hs : IsLindelof s) (ht : IsOpen t)
  结论: IsLindelof (s \ t)
  证明: hs.inter_right (isClosed_compl_iff.mpr ht)

Depends on / 依赖: hs.inter_right, inter_right, isClosed_compl_iff, isClosed_compl_iff.mpr
-/
theorem IsLindelof.diff (hs : IsLindelof s) (ht : IsOpen t) : IsLindelof (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/--
theorem `IsLindelof.of_isClosed_subset` / 定理 `IsLindelof.of_isClosed_subset`

English:
theorem IsLindelof.of_isClosed_subset
  given: (hs : IsLindelof s) (ht : IsClosed t) (h : t subseteq s)
  proof: inter_eq_self_of_subset_right h ▸ hs.inter_right ht

中文:
定理 IsLindelof.of_isClosed_subset
  条件: (hs : IsLindelof s) (ht : IsClosed t) (h : t subseteq s)
  证明: inter_eq_self_of_subset_right h ▸ hs.inter_right ht

Depends on / 依赖: hs.inter_right, inter_eq_self_of_subset_right, inter_right
-/
theorem IsLindelof.of_isClosed_subset (hs : IsLindelof s) (ht : IsClosed t) (h : t subseteq s) :
    IsLindelof t := inter_eq_self_of_subset_right h ▸ hs.inter_right ht

/--
theorem `IsLindelof.image_of_continuousOn` / 定理 `IsLindelof.image_of_continuousOn`

English:
theorem IsLindelof.image_of_continuousOn
  given: {f : X -> Y} (hs : IsLindelof s) (hf : ContinuousOn f s)
  proof: by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : exists x in s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (

中文:
定理 IsLindelof.image_of_continuousOn
  条件: {f : X -> Y} (hs : IsLindelof s) (hf : ContinuousOn f s)
  证明: by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : exists x in s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (

Depends on / 依赖: ClusterPt, Tendsto, comap_inf_principal_neBot_of_image_mem, convert, hx.neBot, inf_le_right, l.comap, le_principal_iff, mem_image_of_mem, nhdsWithin, tendsto_comap, this.neBot
-/
theorem IsLindelof.image_of_continuousOn {f : X -> Y} (hs : IsLindelof s) (hf : ContinuousOn f s) :
    IsLindelof (f '' s) := by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : exists x in s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  have := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert! (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

/--
theorem `IsLindelof.image` / 定理 `IsLindelof.image`

English:
theorem IsLindelof.image
  given: {f : X -> Y} (hs : IsLindelof s) (hf : Continuous f)
  proof: hs.image_of_continuousOn hf.continuousOn

中文:
定理 IsLindelof.image
  条件: {f : X -> Y} (hs : IsLindelof s) (hf : Continuous f)
  证明: hs.image_of_continuousOn hf.continuousOn

Depends on / 依赖: continuousOn, hf.continuousOn, hs.image_of_continuousOn, image_of_continuousOn
-/
theorem IsLindelof.image {f : X -> Y} (hs : IsLindelof s) (hf : Continuous f) :
    IsLindelof (f '' s) := hs.image_of_continuousOn hf.continuousOn

/--
theorem `IsLindelof.adherence_nhdset` / 定理 `IsLindelof.adherence_nhdset`

English:
theorem IsLindelof.adherence_nhdset
  statement: {f : Filter X} [CountableInterFilter f] (hs : IsLindelof s)
  proof: (eq_or_neBot _).casesOn mem_of_eq_bot fun _ =>
let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ inf_le_of_left_le hf₂
    have : x in t := ht₂ x hx hfx.of_inf_left
    have : tᶜ inter t in 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 compl_inter_self t ▸ th

中文:
定理 IsLindelof.adherence_nhdset
  结论: {f : Filter X} [Countable整数erFilter f] (hs : IsLindelof s)
  证明: (eq_or_neBot _).casesOn mem_of_eq_bot fun _ =>
let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ inf_le_of_left_le hf₂
    have : x in t := ht₂ x hx hfx.of_inf_left
    have : tᶜ inter t in 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 compl_inter_self t ▸ th

Depends on / 依赖: absurd, casesOn, compl_inter_self, empty_mem_iff_bot, eq_or_neBot, hfx.of_inf_left, hfx.of_inf_right.ne, inf_le_of_left_le, inter_mem_nhdsWithin, mem_nhds, mem_of_eq_bot, of_inf_left, of_inf_right
-/
theorem IsLindelof.adherence_nhdset {f : Filter X} [CountableInterFilter f] (hs : IsLindelof s)
    (hf₂ : f <= 𝓟 s) (ht₁ : IsOpen t) (ht₂ : forall x in s, ClusterPt x f -> x in t) : t in f :=
  (eq_or_neBot _).casesOn mem_of_eq_bot fun _ =>
let ⟨x, hx, hfx⟩ := @hs (f ⊓ 𝓟 tᶜ) _ _ inf_le_of_left_le hf₂
    have : x in t := ht₂ x hx hfx.of_inf_left
    have : tᶜ inter t in 𝓝[tᶜ] x := inter_mem_nhdsWithin _ (ht₁.mem_nhds this)
have A : 𝓝[tᶜ] x = ⊥ := empty_mem_iff_bot.1 compl_inter_self t ▸ this
    have : 𝓝[tᶜ] x != ⊥ := hfx.of_inf_right.ne
    absurd A this

/--
theorem `IsLindelof.elim_countable_subcover` / 定理 `IsLindelof.elim_countable_subcover`

English:
theorem IsLindelof.elim_countable_subcover
  statement: {ι : Type v} (hs : IsLindelof s) (U : ι -> Set X)
  proof: by
  have hmono : forall ⦃s t : Set X⦄, s subseteq t -> (exists r : Set ι, r.Countable ∧ t subseteq ⋃ i in r, U i)
      -> (exists r : Set ι, r.Countable ∧ s subseteq ⋃ i in r, U i) := by
    intro _ _ hst ⟨r, ⟨hrcountable, hsub⟩⟩
    exact ⟨r, hrcountable, Subset.trans hst hsub⟩
  have hcountable_

中文:
定理 IsLindelof.elim_countable_subcover
  结论: {ι : 类型v} (hs : IsLindelof s) (U : ι -> Set X)
  证明: by
  have hmono : forall ⦃s t : Set X⦄, s subseteq t -> (exists r : Set ι, r.Countable ∧ t subseteq ⋃ i in r, U i)
      -> (exists r : Set ι, r.Countable ∧ s subseteq ⋃ i in r, U i) := by
    intro _ _ hst ⟨r, ⟨hrcountable, hsub⟩⟩
    exact ⟨r, hrcountable, Subset.trans hst hsub⟩
  have hcountable_

Depends on / 依赖: Countable, S.Countable, Subset, Subset.trans, hcountable_union, hrcountable, r.Countable, subseteq
-/
theorem IsLindelof.elim_countable_subcover {ι : Type v} (hs : IsLindelof s) (U : ι -> Set X)
    (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i) :
    exists r : Set ι, r.Countable ∧ (s subseteq ⋃ i in r, U i) := by
  have hmono : forall ⦃s t : Set X⦄, s subseteq t -> (exists r : Set ι, r.Countable ∧ t subseteq ⋃ i in r, U i)
      -> (exists r : Set ι, r.Countable ∧ s subseteq ⋃ i in r, U i) := by
    intro _ _ hst ⟨r, ⟨hrcountable, hsub⟩⟩
    exact ⟨r, hrcountable, Subset.trans hst hsub⟩
  have hcountable_union : forall (S : Set (Set X)), S.Countable
      -> (forall s in S, exists r : Set ι, r.Countable ∧ (s subseteq ⋃ i in r, U i))
      -> exists r : Set ι, r.Countable ∧ (⋃₀ S subseteq ⋃ i in r, U i) := by
    intro S hS hsr
    choose! r hr using hsr
    refine ⟨⋃ s in S, r s, hS.biUnion_iff.mpr (fun s hs => (hr s hs).1), ?_⟩
    refine sUnion_subset ?h.right.h
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    exact fun i is x hx => mem_biUnion is ((hr i is).2 hx)
  have h_nhds : forall x in s, exists t in 𝓝[s] x, exists r : Set ι, r.Countable ∧ (t subseteq ⋃ i in r, U i) := by
    intro x hx
    let ⟨i, hi⟩ := mem_iUnion.1 (hsU hx)
    refine ⟨U i, mem_nhdsWithin_of_mem_nhds ((hUo i).mem_nhds hi), {i}, by simp, ?_⟩
    simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
    exact Subset.refl _
  exact hs.induction_on hmono hcountable_union h_nhds

/--
theorem `IsLindelof.elim_nhds_subcover'` / 定理 `IsLindelof.elim_nhds_subcover'`

English:
theorem IsLindelof.elim_nhds_subcover'
  statement: (hs : IsLindelof s) (U : forall x in s, Set X)
  proof: by
  have := hs.elim_countable_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior)
    fun x hx =>
mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 hU _ _⟩
  rcases this with ⟨r, ⟨hr, hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.tran

中文:
定理 IsLindelof.elim_nhds_subcover'
  结论: (hs : IsLindelof s) (U : 对任意 x in s, Set X)
  证明: by
  have := hs.elim_countable_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior)
    fun x hx =>
mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 hU _ _⟩
  rcases this with ⟨r, ⟨hr, hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.tran

Depends on / 依赖: Subset, Subset.refl, Subset.trans, elim_countable_subcover, hs.elim_countable_subcover, interior, interior_subset, isOpen_interior, mem_iUnion, mem_interior_iff_mem_nhds, subset_iUnion_of_subset
-/
theorem IsLindelof.elim_nhds_subcover' (hs : IsLindelof s) (U : forall x in s, Set X)
    (hU : forall x (hx : x in s), U x ‹x in s› in 𝓝 x) :
    exists t : Set s, t.Countable ∧ s subseteq ⋃ x in t, U (x : s) x.2 := by
  have := hs.elim_countable_subcover (fun x : s => interior (U x x.2)) (fun _ => isOpen_interior)
    fun x hx =>
mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 hU _ _⟩
  rcases this with ⟨r, ⟨hr, hs⟩⟩
  use r, hr
  apply Subset.trans hs
  apply iUnion₂_subset
  intro i hi
  apply Subset.trans interior_subset
  exact subset_iUnion_of_subset i (subset_iUnion_of_subset hi (Subset.refl _))

/--
theorem `IsLindelof.elim_nhds_subcover` / 定理 `IsLindelof.elim_nhds_subcover`

English:
theorem IsLindelof.elim_nhds_subcover
  statement: (hs : IsLindelof s) (U : X -> Set X)
  proof: by
  let ⟨t, ⟨htc, htsub⟩⟩ := hs.elim_nhds_subcover' (fun x _ => U x) hU
  refine ⟨↑t, Countable.image htc Subtype.val, ?_⟩
  constructor
  · intro _
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    tauto
  · have : ⋃ x in t, U ↑x = ⋃ x in Subtype

中文:
定理 IsLindelof.elim_nhds_subcover
  结论: (hs : IsLindelof s) (U : X -> Set X)
  证明: by
  let ⟨t, ⟨htc, htsub⟩⟩ := hs.elim_nhds_subcover' (fun x _ => U x) hU
  refine ⟨↑t, Countable.image htc Subtype.val, ?_⟩
  constructor
  · intro _
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    tauto
  · have : ⋃ x in t, U ↑x = ⋃ x in Subtype

Depends on / 依赖: Countable, Countable.image, Subtype, Subtype.exists, Subtype.val, biUnion_image, biUnion_image.symm, elim_nhds_subcover, exists_and_right, exists_eq_right, forall_exists_index, hs.elim_nhds_subcover, mem_image
-/
theorem IsLindelof.elim_nhds_subcover (hs : IsLindelof s) (U : X -> Set X)
    (hU : forall x in s, U x in 𝓝 x) :
    exists t : Set X, t.Countable ∧ (forall x in t, x in s) ∧ s subseteq ⋃ x in t, U x := by
  let ⟨t, ⟨htc, htsub⟩⟩ := hs.elim_nhds_subcover' (fun x _ => U x) hU
  refine ⟨↑t, Countable.image htc Subtype.val, ?_⟩
  constructor
  · intro _
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index]
    tauto
  · have : ⋃ x in t, U ↑x = ⋃ x in Subtype.val '' t, U x := biUnion_image.symm
    rwa [← this]

/--
theorem `IsLindelof.indexed_countable_subcover` / 定理 `IsLindelof.indexed_countable_subcover`

English:
theorem IsLindelof.indexed_countable_subcover
  statement: {ι : Type v} [Nonempty ι]
  proof: by
  obtain ⟨c, ⟨c_count, c_cov⟩⟩ := hs.elim_countable_subcover U hUo hsU
  rcases c.eq_empty_or_nonempty with rfl | c_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at c_cov
    simp only [subset_eq_empty c_cov rfl, empty_subset, exists_const]
  obtain ⟨f, f_surj⟩ := (S

中文:
定理 IsLindelof.indexed_countable_subcover
  结论: {ι : 类型v} [Nonempty ι]
  证明: by
  obtain ⟨c, ⟨c_count, c_cov⟩⟩ := hs.elim_countable_subcover U hUo hsU
  rcases c.eq_empty_or_nonempty with rfl | c_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at c_cov
    simp only [subset_eq_empty c_cov rfl, empty_subset, exists_const]
  obtain ⟨f, f_surj⟩ := (S

Depends on / 依赖: Set.countable_iff_exists_surjective, _subset_iff.mpr, c.eq_empty_or_nonempty, c_count, c_cov, c_cov.trans, c_nonempty, countable_iff_exists_surjective, elim_countable_subcover, empty_subset, eq_empty_or_nonempty, exists_const, f_surj, hs.elim_countable_subcover, iUnion_empty, iUnion_of_empty, mem_empty_iff_false, subset_eq_empty, subseteq
-/
theorem IsLindelof.indexed_countable_subcover {ι : Type v} [Nonempty ι]
    (hs : IsLindelof s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s subseteq ⋃ i, U i) :
    exists f : Nat -> ι, s subseteq ⋃ n, U (f n) := by
  obtain ⟨c, ⟨c_count, c_cov⟩⟩ := hs.elim_countable_subcover U hUo hsU
  rcases c.eq_empty_or_nonempty with rfl | c_nonempty
  · simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at c_cov
    simp only [subset_eq_empty c_cov rfl, empty_subset, exists_const]
  obtain ⟨f, f_surj⟩ := (Set.countable_iff_exists_surjective c_nonempty).mp c_count
refine ⟨fun x => f x, c_cov.trans iUnion₂_subset_iff.mpr (?_ : forall i in c, U i subseteq ⋃ n, U (f n))⟩
  intro x hx
  obtain ⟨n, hn⟩ := f_surj ⟨x, hx⟩
exact subset_iUnion_of_subset n subset_of_eq (by rw [hn])

/--
theorem `IsLindelof.disjoint_nhdsSet_left` / 定理 `IsLindelof.disjoint_nhdsSet_left`

English:
theorem IsLindelof.disjoint_nhdsSet_left
  statement: {l : Filter X} [CountableInterFilter l]
  proof: by
refine ⟨fun h x hx => h.mono_left nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, htc, hts, hst⟩
  refine (hasBa

中文:
定理 IsLindelof.disjoint_nhdsSet_left
  结论: {l : Filter X} [Countable整数erFilter l]
  证明: by
refine ⟨fun h x hx => h.mono_left nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, htc, hts, hst⟩
  refine (hasBa

Depends on / 依赖: countable_bInter_mem, disjoint_iff_left, elim_nhds_subcover, h.mono_left, hasBasis_nhdsSet, hs.elim_nhds_subcover, isOpen_biUnion, mem_nhds, mono_left, nhds_basis_opens, nhds_le_nhdsSet
-/
theorem IsLindelof.disjoint_nhdsSet_left {l : Filter X} [CountableInterFilter l]
    (hs : IsLindelof s) :
    Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l := by
refine ⟨fun h x hx => h.mono_left nhds_le_nhdsSet hx, fun H => ?_⟩
  choose! U hxU hUl using fun x hx => (nhds_basis_opens x).disjoint_iff_left.1 (H x hx)
  choose hxU hUo using hxU
  rcases hs.elim_nhds_subcover U fun x hx => (hUo x hx).mem_nhds (hxU x hx) with ⟨t, htc, hts, hst⟩
  refine (hasBasis_nhdsSet _).disjoint_iff_left.2
    ⟨⋃ x in t, U x, ⟨isOpen_biUnion fun x hx => hUo x (hts x hx), hst⟩, ?_⟩
  rw [compl_iUnion₂]
  exact (countable_bInter_mem htc).mpr (fun i hi => hUl _ (hts _ hi))

/--
theorem `IsLindelof.disjoint_nhdsSet_right` / 定理 `IsLindelof.disjoint_nhdsSet_right`

English:
theorem IsLindelof.disjoint_nhdsSet_right
  statement: {l : Filter X} [CountableInterFilter l]
  proof: by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

中文:
定理 IsLindelof.disjoint_nhdsSet_right
  结论: {l : Filter X} [Countable整数erFilter l]
  证明: by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

Depends on / 依赖: disjoint_comm, disjoint_nhdsSet_left, hs.disjoint_nhdsSet_left
-/
theorem IsLindelof.disjoint_nhdsSet_right {l : Filter X} [CountableInterFilter l]
    (hs : IsLindelof s) : Disjoint l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 x) := by
  simpa only [disjoint_comm] using hs.disjoint_nhdsSet_left

/--
theorem `IsLindelof.elim_countable_subfamily_closed` / 定理 `IsLindelof.elim_countable_subfamily_closed`

English:
theorem IsLindelof.elim_countable_subfamily_closed
  statement: {ι : Type v} (hs : IsLindelof s)
  proof: by
  let U := tᶜ
  have hUo : forall i, IsOpen (U i) := by simp only [U, Pi.compl_apply, isOpen_compl_iff]; exact htc
  have hsU : s subseteq ⋃ i, U i := by
    simp only [U, Pi.compl_apply]
    rw [← compl_iInter]
    apply disjoint_compl_left_iff_subset.mp
    simp only [compl_iInter, compl_iUnion

中文:
定理 IsLindelof.elim_countable_subfamily_closed
  结论: {ι : 类型v} (hs : IsLindelof s)
  证明: by
  let U := tᶜ
  have hUo : forall i, IsOpen (U i) := by simp only [U, Pi.compl_apply, isOpen_compl_iff]; exact htc
  have hsU : s subseteq ⋃ i, U i := by
    simp only [U, Pi.compl_apply]
    rw [← compl_iInter]
    apply disjoint_compl_left_iff_subset.mp
    simp only [compl_iInter, compl_iUnion

Depends on / 依赖: Disjoint, Disjoint.symm, IsOpen, Pi.compl_apply, compl_apply, compl_compl, compl_iInter, compl_iUnion, disjoint_compl_left_iff_subset, disjoint_compl_left_iff_subset.mp, disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mpr, elim_countable_subcover, hs.elim_countable_subcover, hucount, isOpen_compl_iff, subseteq
-/
theorem IsLindelof.elim_countable_subfamily_closed {ι : Type v} (hs : IsLindelof s)
    (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst : (s inter ⋂ i, t i) = ∅) :
    exists u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅ := by
  let U := tᶜ
  have hUo : forall i, IsOpen (U i) := by simp only [U, Pi.compl_apply, isOpen_compl_iff]; exact htc
  have hsU : s subseteq ⋃ i, U i := by
    simp only [U, Pi.compl_apply]
    rw [← compl_iInter]
    apply disjoint_compl_left_iff_subset.mp
    simp only [compl_iInter, compl_iUnion, compl_compl]
    apply Disjoint.symm
    exact disjoint_iff_inter_eq_empty.mpr hst
  rcases hs.elim_countable_subcover U hUo hsU with ⟨u, ⟨hucount, husub⟩⟩
  use u, hucount
  rw [← disjoint_compl_left_iff_subset] at husub
  simp only [U, Pi.compl_apply, compl_iUnion, compl_compl] at husub
  exact disjoint_iff_inter_eq_empty.mp (Disjoint.symm husub)

/--
theorem `IsLindelof.inter_iInter_nonempty` / 定理 `IsLindelof.inter_iInter_nonempty`

English:
theorem IsLindelof.inter_iInter_nonempty
  statement: {ι : Type v} (hs : IsLindelof s) (t : ι -> Set X)
  proof: by
  contrapose! hst
  rcases hs.elim_countable_subfamily_closed t htc hst with ⟨u, ⟨_, husub⟩⟩
  exact ⟨u, fun _ => husub⟩

中文:
定理 IsLindelof.inter_iInter_nonempty
  结论: {ι : 类型v} (hs : IsLindelof s) (t : ι -> Set X)
  证明: by
  contrapose! hst
  rcases hs.elim_countable_subfamily_closed t htc hst with ⟨u, ⟨_, husub⟩⟩
  exact ⟨u, fun _ => husub⟩

Depends on / 依赖: contrapose, elim_countable_subfamily_closed, hs.elim_countable_subfamily_closed
-/
theorem IsLindelof.inter_iInter_nonempty {ι : Type v} (hs : IsLindelof s) (t : ι -> Set X)
    (htc : forall i, IsClosed (t i)) (hst : forall u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i).Nonempty) :
    (s inter ⋂ i, t i).Nonempty := by
  contrapose! hst
  rcases hs.elim_countable_subfamily_closed t htc hst with ⟨u, ⟨_, husub⟩⟩
  exact ⟨u, fun _ => husub⟩

/--
theorem `IsLindelof.elim_countable_subcover_image` / 定理 `IsLindelof.elim_countable_subcover_image`

English:
theorem IsLindelof.elim_countable_subcover_image
  statement: {b : Set ι} {c : ι -> Set X} (hs : IsLindelof s)
  proof: by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_countable_subcover (fun i => c i : b -> Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, by simp, Countable.image hd.1 Subtype.val, ?_⟩
  rw [biUnion_image]
  exact hd.2

中文:
定理 IsLindelof.elim_countable_subcover_image
  结论: {b : Set ι} {c : ι -> Set X} (hs : IsLindelof s)
  证明: by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_countable_subcover (fun i => c i : b -> Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, by simp, Countable.image hd.1 Subtype.val, ?_⟩
  rw [biUnion_image]
  exact hd.2

Depends on / 依赖: Countable, Countable.image, Subtype, Subtype.forall, Subtype.val, biUnion_eq_iUnion, biUnion_image, elim_countable_subcover, hs.elim_countable_subcover
-/
theorem IsLindelof.elim_countable_subcover_image {b : Set ι} {c : ι -> Set X} (hs : IsLindelof s)
    (hc₁ : forall i in b, IsOpen (c i)) (hc₂ : s subseteq ⋃ i in b, c i) :
    exists b', b' subseteq b ∧ Set.Countable b' ∧ s subseteq ⋃ i in b', c i := by
  simp only [Subtype.forall', biUnion_eq_iUnion] at hc₁ hc₂
  rcases hs.elim_countable_subcover (fun i => c i : b -> Set X) hc₁ hc₂ with ⟨d, hd⟩
  refine ⟨Subtype.val '' d, by simp, Countable.image hd.1 Subtype.val, ?_⟩
  rw [biUnion_image]
  exact hd.2


/--
theorem `isLindelof_of_countable_subcover` / 定理 `isLindelof_of_countable_subcover`

English:
theorem isLindelof_of_countable_subcover
  proof: fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_⟩
  intro t ht h
  have uinf := f.

中文:
定理 isLindelof_of_countable_subcover
  证明: fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_⟩
  intro t ht h
  have uinf := f.

Depends on / 依赖: ClusterPt, SetCoe, SetCoe.forall, compl_comp, compl_notMem, contrapose, countable_bInter_mem, disjoint_iff, disjoint_iff_left, f.sets_of_superset, le_principal_iff, mem_iUnion, nhds_basis_opens, not_neBot, sets_of_superset
-/
theorem isLindelof_of_countable_subcover
    (h : forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) ->
    exists t : Set ι, t.Countable ∧ s subseteq ⋃ i in t, U i) :
    IsLindelof s := fun f hf hfs => by
  contrapose! h
  simp only [ClusterPt, not_neBot, ← disjoint_iff, SetCoe.forall',
    (nhds_basis_opens _).disjoint_iff_left] at h
  choose fsub U hU hUf using h
  refine ⟨s, U, fun x => (hU x).2, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hU _).1 ⟩, ?_⟩
  intro t ht h
  have uinf := f.sets_of_superset (le_principal_iff.1 fsub) h
  have uninf : ⋂ i in t, (U i)ᶜ in f := (countable_bInter_mem ht).mpr (fun _ _ => hUf _)
  rw [← compl_iUnion₂] at uninf
  have uninf := compl_notMem uninf
  simp only [compl_compl] at uninf
  contradiction

/--
theorem `isLindelof_of_countable_subfamily_closed` / 定理 `isLindelof_of_countable_subfamily_closed`

English:
theorem isLindelof_of_countable_subfamily_closed
  proof: isLindelof_of_countable_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset]; rw [compl_iUnion]; rw [disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂,

中文:
定理 isLindelof_of_countable_subfamily_closed
  证明: isLindelof_of_countable_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset]; rw [compl_iUnion]; rw [disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂,

Depends on / 依赖: compl_iUnion, disjoint_compl_right_iff_subset, disjoint_iff, isClosed_compl, isLindelof_of_countable_subcover
-/
theorem isLindelof_of_countable_subfamily_closed
    (h :
      forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅ ->
        exists u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅) :
    IsLindelof s :=
  isLindelof_of_countable_subcover fun U hUo hsU => by
    rw [← disjoint_compl_right_iff_subset]; rw [compl_iUnion]; rw [disjoint_iff] at hsU
    rcases h (fun i => (U i)ᶜ) (fun i => (hUo _).isClosed_compl) hsU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rwa [← disjoint_compl_right_iff_subset, compl_iUnion₂, disjoint_iff]

/--
theorem `isLindelof_iff_countable_subcover` / 定理 `isLindelof_iff_countable_subcover`

English:
theorem isLindelof_iff_countable_subcover
  proof: ⟨fun hs => hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

中文:
定理 isLindelof_iff_countable_subcover
  证明: ⟨fun hs => hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

Depends on / 依赖: elim_countable_subcover, hs.elim_countable_subcover, isLindelof_of_countable_subcover
-/
theorem isLindelof_iff_countable_subcover :
    IsLindelof s ↔ forall {ι : Type u} (U : ι -> Set X),
      (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) -> exists t : Set ι, t.Countable ∧ s subseteq ⋃ i in t, U i :=
  ⟨fun hs => hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

/--
theorem `isLindelof_iff_countable_subfamily_closed` / 定理 `isLindelof_iff_countable_subfamily_closed`

English:
theorem isLindelof_iff_countable_subfamily_closed
  proof: ⟨fun hs => hs.elim_countable_subfamily_closed, isLindelof_of_countable_subfamily_closed⟩

中文:
定理 isLindelof_iff_countable_subfamily_closed
  证明: ⟨fun hs => hs.elim_countable_subfamily_closed, isLindelof_of_countable_subfamily_closed⟩

Depends on / 依赖: elim_countable_subfamily_closed, hs.elim_countable_subfamily_closed, isLindelof_of_countable_subfamily_closed
-/
theorem isLindelof_iff_countable_subfamily_closed :
    IsLindelof s ↔ forall {ι : Type u} (t : ι -> Set X),
    (forall i, IsClosed (t i)) -> (s inter ⋂ i, t i) = ∅
    -> exists u : Set ι, u.Countable ∧ (s inter ⋂ i in u, t i) = ∅ :=
  ⟨fun hs => hs.elim_countable_subfamily_closed, isLindelof_of_countable_subfamily_closed⟩

/-- The empty set is a Lindelof set. -/
@[simp]
/--
theorem `isLindelof_empty` / 定理 `isLindelof_empty`

English:
theorem isLindelof_empty
  statement: IsLindelof (∅ : Set X)
  proof: fun _f hnf _ hsf =>
Not.elim hnf.ne empty_mem_iff_bot.1 le_principal_iff.1 hsf

中文:
定理 isLindelof_empty
  结论: IsLindelof (∅ : Set X)
  证明: fun _f hnf _ hsf =>
Not.elim hnf.ne empty_mem_iff_bot.1 le_principal_iff.1 hsf
-/
theorem isLindelof_empty : IsLindelof (∅ : Set X) := fun _f hnf _ hsf =>
Not.elim hnf.ne empty_mem_iff_bot.1 le_principal_iff.1 hsf

/-- A singleton set is a Lindelof set. -/
@[simp]
/--
theorem `isLindelof_singleton` / 定理 `isLindelof_singleton`

English:
theorem isLindelof_singleton
  given: {x : X}
  statement: IsLindelof ({x} : Set X)
  proof: fun _ hf _ hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

中文:
定理 isLindelof_singleton
  条件: {x : X}
  结论: IsLindelof ({x} : Set X)
  证明: fun _ hf _ hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩
-/
theorem isLindelof_singleton {x : X} : IsLindelof ({x} : Set X) := fun _ hf _ hfa =>
  ⟨x, rfl, ClusterPt.of_le_nhds'
    (hfa.trans <| by simpa only [principal_singleton] using pure_le_nhds x) hf⟩

/--
theorem `Set.Subsingleton.isLindelof` / 定理 `Set.Subsingleton.isLindelof`

English:
theorem Set.Subsingleton.isLindelof
  given: (hs : s.Subsingleton)
  statement: IsLindelof s
  proof: Subsingleton.induction_on hs isLindelof_empty fun _ => isLindelof_singleton

中文:
定理 Set.Subsingleton.isLindelof
  条件: (hs : s.Subsingleton)
  结论: IsLindelof s
  证明: Subsingleton.induction_on hs isLindelof_empty fun _ => isLindelof_singleton

Depends on / 依赖: Subsingleton, Subsingleton.induction_on, induction_on, isLindelof_empty, isLindelof_singleton
-/
theorem Set.Subsingleton.isLindelof (hs : s.Subsingleton) : IsLindelof s :=
  Subsingleton.induction_on hs isLindelof_empty fun _ => isLindelof_singleton

/--
theorem `Set.Countable.isLindelof_biUnion` / 定理 `Set.Countable.isLindelof_biUnion`

English:
theorem Set.Countable.isLindelof_biUnion
  statement: {s : Set ι} {f : ι -> Set X} (hs : s.Countable)
  proof: by
  apply isLindelof_of_countable_subcover
  intro i U hU hUcover
  have hiU : forall i in s, f i subseteq ⋃ i, U i :=
    fun _ is => _root_.subset_trans (subset_biUnion_of_mem is) hUcover
  have iSets := fun i is => (hf i is).elim_countable_subcover U hU (hiU i is)
  choose! r hr using iSets
  us

中文:
定理 Set.Countable.isLindelof_biUnion
  结论: {s : Set ι} {f : ι -> Set X} (hs : s.Countable)
  证明: by
  apply isLindelof_of_countable_subcover
  intro i U hU hUcover
  have hiU : forall i in s, f i subseteq ⋃ i, U i :=
    fun _ is => _root_.subset_trans (subset_biUnion_of_mem is) hUcover
  have iSets := fun i is => (hf i is).elim_countable_subcover U hU (hiU i is)
  choose! r hr using iSets
  us

Depends on / 依赖: Countable, Countable.biUnion_iff, _root_, _root_.subset_trans, biUnion_and, biUnion_iff, elim_countable_subcover, exists_prop, h.left.a, h.right.h, hUcover, iUnion_exists, isLindelof_of_countable_subcover, mem_iUnion, subset_biUnion_of_mem, subset_trans, subseteq
-/
theorem Set.Countable.isLindelof_biUnion {s : Set ι} {f : ι -> Set X} (hs : s.Countable)
    (hf : forall i in s, IsLindelof (f i)) : IsLindelof (⋃ i in s, f i) := by
  apply isLindelof_of_countable_subcover
  intro i U hU hUcover
  have hiU : forall i in s, f i subseteq ⋃ i, U i :=
    fun _ is => _root_.subset_trans (subset_biUnion_of_mem is) hUcover
  have iSets := fun i is => (hf i is).elim_countable_subcover U hU (hiU i is)
  choose! r hr using iSets
  use ⋃ i in s, r i
  constructor
  · refine (Countable.biUnion_iff hs).mpr ?h.left.a
    exact fun s hs => (hr s hs).1
  · refine iUnion₂_subset ?h.right.h
    intro i is
    simp only [mem_iUnion, exists_prop, iUnion_exists, biUnion_and']
    intro x hx
    exact mem_biUnion is ((hr i is).2 hx)


/--
theorem `Set.Finite.isLindelof_biUnion` / 定理 `Set.Finite.isLindelof_biUnion`

English:
theorem Set.Finite.isLindelof_biUnion
  statement: {s : Set ι} {f : ι -> Set X} (hs : s.Finite)
  proof: Set.Countable.isLindelof_biUnion (countable hs) hf

中文:
定理 Set.Finite.isLindelof_biUnion
  结论: {s : Set ι} {f : ι -> Set X} (hs : s.Finite)
  证明: Set.Countable.isLindelof_biUnion (countable hs) hf

Depends on / 依赖: Countable, Set.Countable.isLindelof_biUnion, countable, isLindelof_biUnion
-/
theorem Set.Finite.isLindelof_biUnion {s : Set ι} {f : ι -> Set X} (hs : s.Finite)
    (hf : forall i in s, IsLindelof (f i)) : IsLindelof (⋃ i in s, f i) :=
  Set.Countable.isLindelof_biUnion (countable hs) hf

/--
theorem `Finset.isLindelof_biUnion` / 定理 `Finset.isLindelof_biUnion`

English:
theorem Finset.isLindelof_biUnion
  given: (s : Finset ι) {f : ι -> Set X} (hf : forall i in s, IsLindelof (f i))
  proof: s.finite_toSet.isLindelof_biUnion hf

中文:
定理 Finset.isLindelof_biUnion
  条件: (s : Finset ι) {f : ι -> Set X} (hf : 对任意 i in s, IsLindelof (f i))
  证明: s.finite_toSet.isLindelof_biUnion hf

Depends on / 依赖: finite_toSet, isLindelof_biUnion, s.finite_toSet.isLindelof_biUnion
-/
theorem Finset.isLindelof_biUnion (s : Finset ι) {f : ι -> Set X} (hf : forall i in s, IsLindelof (f i)) :
    IsLindelof (⋃ i in s, f i) :=
  s.finite_toSet.isLindelof_biUnion hf

/--
theorem `isLindelof_accumulate` / 定理 `isLindelof_accumulate`

English:
theorem isLindelof_accumulate
  given: {K : Nat -> Set X} (hK : forall n, IsLindelof (K n)) (n : Nat)
  proof: (finite_le_nat n).isLindelof_biUnion fun k _ => hK k

中文:
定理 isLindelof_accumulate
  条件: {K : 自然数 -> Set X} (hK : 对任意 n, IsLindelof (K n)) (n : 自然数)
  证明: (finite_le_nat n).isLindelof_biUnion fun k _ => hK k

Depends on / 依赖: finite_le_nat, isLindelof_biUnion
-/
theorem isLindelof_accumulate {K : Nat -> Set X} (hK : forall n, IsLindelof (K n)) (n : Nat) :
    IsLindelof (accumulate K n) :=
  (finite_le_nat n).isLindelof_biUnion fun k _ => hK k

/--
theorem `Set.Countable.isLindelof_sUnion` / 定理 `Set.Countable.isLindelof_sUnion`

English:
theorem Set.Countable.isLindelof_sUnion
  statement: {S : Set (Set X)} (hf : S.Countable)
  proof: by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

中文:
定理 Set.Countable.isLindelof_sUnion
  结论: {S : Set (Set X)} (hf : S.Countable)
  证明: by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

Depends on / 依赖: hf.isLindelof_biUnion, isLindelof_biUnion, sUnion_eq_biUnion
-/
theorem Set.Countable.isLindelof_sUnion {S : Set (Set X)} (hf : S.Countable)
    (hc : forall s in S, IsLindelof s) : IsLindelof (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

/--
theorem `Set.Finite.isLindelof_sUnion` / 定理 `Set.Finite.isLindelof_sUnion`

English:
theorem Set.Finite.isLindelof_sUnion
  statement: {S : Set (Set X)} (hf : S.Finite)
  proof: by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

中文:
定理 Set.Finite.isLindelof_sUnion
  结论: {S : Set (Set X)} (hf : S.Finite)
  证明: by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

Depends on / 依赖: hf.isLindelof_biUnion, isLindelof_biUnion, sUnion_eq_biUnion
-/
theorem Set.Finite.isLindelof_sUnion {S : Set (Set X)} (hf : S.Finite)
    (hc : forall s in S, IsLindelof s) : IsLindelof (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isLindelof_biUnion hc

/--
theorem `isLindelof_iUnion` / 定理 `isLindelof_iUnion`

English:
theorem isLindelof_iUnion
  given: {ι : Sort*} {f : ι -> Set X} [Countable ι] (h : forall i, IsLindelof (f i))
  proof: (countable_range f).isLindelof_sUnion forall_mem_range.2 h

中文:
定理 isLindelof_iUnion
  条件: {ι : Sort*} {f : ι -> Set X} [Countable ι] (h : 对任意 i, IsLindelof (f i))
  证明: (countable_range f).isLindelof_sUnion forall_mem_range.2 h

Depends on / 依赖: countable_range, forall_mem_range, isLindelof_sUnion
-/
theorem isLindelof_iUnion {ι : Sort*} {f : ι -> Set X} [Countable ι] (h : forall i, IsLindelof (f i)) :
IsLindelof (⋃ i, f i) := (countable_range f).isLindelof_sUnion forall_mem_range.2 h

/--
theorem `Set.Countable.isLindelof` / 定理 `Set.Countable.isLindelof`

English:
theorem Set.Countable.isLindelof
  given: (hs : s.Countable)
  statement: IsLindelof s
  proof: biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

中文:
定理 Set.Countable.isLindelof
  条件: (hs : s.Countable)
  结论: IsLindelof s
  证明: biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

Depends on / 依赖: biUnion_of_singleton, hs.isLindelof_biUnion, isLindelof_biUnion, isLindelof_singleton
-/
theorem Set.Countable.isLindelof (hs : s.Countable) : IsLindelof s :=
  biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

/--
theorem `Set.Finite.isLindelof` / 定理 `Set.Finite.isLindelof`

English:
theorem Set.Finite.isLindelof
  given: (hs : s.Finite)
  statement: IsLindelof s
  proof: biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

中文:
定理 Set.Finite.isLindelof
  条件: (hs : s.Finite)
  结论: IsLindelof s
  证明: biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

Depends on / 依赖: biUnion_of_singleton, hs.isLindelof_biUnion, isLindelof_biUnion, isLindelof_singleton
-/
theorem Set.Finite.isLindelof (hs : s.Finite) : IsLindelof s :=
  biUnion_of_singleton s ▸ hs.isLindelof_biUnion fun _ _ => isLindelof_singleton

/--
theorem `IsLindelof.countable_of_discrete` / 定理 `IsLindelof.countable_of_discrete`

English:
theorem IsLindelof.countable_of_discrete
  given: [DiscreteTopology X] (hs : IsLindelof s)
  proof: by
  have : forall x : X, ({x} : Set X) in 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, ht, _, hssubt⟩
  rw [biUnion_of_singleton] at hssubt
  exact ht.mono hssubt

中文:
定理 IsLindelof.countable_of_discrete
  条件: [DiscreteTopology X] (hs : IsLindelof s)
  证明: by
  have : forall x : X, ({x} : Set X) in 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, ht, _, hssubt⟩
  rw [biUnion_of_singleton] at hssubt
  exact ht.mono hssubt

Depends on / 依赖: biUnion_of_singleton, elim_nhds_subcover, hs.elim_nhds_subcover, hssubt, ht.mono, nhds_discrete
-/
theorem IsLindelof.countable_of_discrete [DiscreteTopology X] (hs : IsLindelof s) :
    s.Countable := by
  have : forall x : X, ({x} : Set X) in 𝓝 x := by simp [nhds_discrete]
  rcases hs.elim_nhds_subcover (fun x => {x}) fun x _ => this x with ⟨t, ht, _, hssubt⟩
  rw [biUnion_of_singleton] at hssubt
  exact ht.mono hssubt

/--
theorem `isLindelof_iff_countable` / 定理 `isLindelof_iff_countable`

English:
theorem isLindelof_iff_countable
  given: [DiscreteTopology X]
  statement: IsLindelof s ↔ s.Countable
  proof: ⟨fun h => h.countable_of_discrete, fun h => h.isLindelof⟩

中文:
定理 isLindelof_iff_countable
  条件: [DiscreteTopology X]
  结论: IsLindelof s ↔ s.Countable
  证明: ⟨fun h => h.countable_of_discrete, fun h => h.isLindelof⟩

Depends on / 依赖: countable_of_discrete, h.countable_of_discrete, h.isLindelof, isLindelof
-/
theorem isLindelof_iff_countable [DiscreteTopology X] : IsLindelof s ↔ s.Countable :=
  ⟨fun h => h.countable_of_discrete, fun h => h.isLindelof⟩

/--
theorem `IsLindelof.union` / 定理 `IsLindelof.union`

English:
theorem IsLindelof.union
  given: (hs : IsLindelof s) (ht : IsLindelof t)
  statement: IsLindelof (s union t)
  proof: by
  rw [union_eq_iUnion]; exact isLindelof_iUnion fun b => by cases b <;> assumption

中文:
定理 IsLindelof.union
  条件: (hs : IsLindelof s) (ht : IsLindelof t)
  结论: IsLindelof (s union t)
  证明: by
  rw [union_eq_iUnion]; exact isLindelof_iUnion fun b => by cases b <;> assumption

Depends on / 依赖: isLindelof_iUnion, union_eq_iUnion
-/
theorem IsLindelof.union (hs : IsLindelof s) (ht : IsLindelof t) : IsLindelof (s union t) := by
  rw [union_eq_iUnion]; exact isLindelof_iUnion fun b => by cases b <;> assumption

/--
theorem `IsLindelof.insert` / 定理 `IsLindelof.insert`

English:
theorem IsLindelof.insert
  given: (hs : IsLindelof s) (a)
  statement: IsLindelof (insert a s)
  proof: isLindelof_singleton.union hs

中文:
定理 IsLindelof.insert
  条件: (hs : IsLindelof s) (a)
  结论: IsLindelof (insert a s)
  证明: isLindelof_singleton.union hs
-/
protected theorem IsLindelof.insert (hs : IsLindelof s) (a) : IsLindelof (insert a s) :=
  isLindelof_singleton.union hs

/--
theorem `isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis` / 定理 `isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis`

English:
theorem isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis
  statement: (b : ι -> Set X)
  proof: by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Y, f, rfl, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_countable_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) Subset.rfl
    refine ⟨t.i

中文:
定理 isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis
  结论: (b : ι -> Set X)
  证明: by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Y, f, rfl, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_countable_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) Subset.rfl
    refine ⟨t.i

Depends on / 依赖: Countable, Countable.image, Set.Subset.trans, Set.iUnion_subset_iff, Set.iUnion_subtype, Set.mem_range_self, Set.subset_iUnion, Subset, Subset.rfl, elim_countable_subcover, hb.isOpen, hb.open_eq_iUnion, iUnion_subset_iff, iUnion_subtype, isOpen, le_antisymm, mem_range_self, open_eq_iUnion, subset_iUnion, t.image
-/
theorem isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis (b : ι -> Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hb' : forall i, IsLindelof (b i)) (U : Set X) :
    IsLindelof U ∧ IsOpen U ↔ exists s : Set ι, s.Countable ∧ U = ⋃ i in s, b i := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨Y, f, rfl, hf⟩ := hb.open_eq_iUnion h₂
    choose f' hf' using hf
    have : b ∘ f' = f := funext hf'
    subst this
    obtain ⟨t, ht⟩ :=
      h₁.elim_countable_subcover (b ∘ f') (fun i => hb.isOpen (Set.mem_range_self _)) Subset.rfl
    refine ⟨t.image f', Countable.image (ht.1) f', le_antisymm ?_ ?_⟩
    · refine Set.Subset.trans ht.2 ?_
      simp only [Set.iUnion_subset_iff]
      intro i hi
      rw [← Set.iUnion_subtype (fun x : ι => x in t.image f') fun i => b i.1]
      exact Set.subset_iUnion (fun i : t.image f' => b i) ⟨_, mem_image_of_mem _ hi⟩
    · apply Set.iUnion₂_subset
      rintro i hi
      obtain ⟨j, -, rfl⟩ := (mem_image ..).mp hi
      exact Set.subset_iUnion (b ∘ f') j
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact hs.isLindelof_biUnion fun i _ => hb' i
    · exact isOpen_biUnion fun i _ => hb.isOpen (Set.mem_range_self _)

/--
Definition of `Filter.coLindelof` / `Filter.coLindelof` 的定义

English:
definition Filter.coLindelof
  signature: (X : Type*) [TopologicalSpace X]
  body: --`Filter.coLindelof` is the filter generated by complements to Lindelöf sets.
  ⨅ (s : Set X) (_ : IsLindelof s), 𝓟 sᶜ

中文:
定义 Filter.coLindelof
  签名: (X : 类型) [TopologicalSpace X]
  定义体: --`Filter.coLindelof` is the filter generated by complements to Lindelöf sets.
  ⨅ (s : Set X) (_ : IsLindelof s), 𝓟 sᶜ
-/
def Filter.coLindelof (X : Type*) [TopologicalSpace X] : Filter X :=
  --`Filter.coLindelof` is the filter generated by complements to Lindelöf sets.
  ⨅ (s : Set X) (_ : IsLindelof s), 𝓟 sᶜ

/--
theorem `hasBasis_coLindelof` / 定理 `hasBasis_coLindelof`

English:
theorem hasBasis_coLindelof
  statement: (coLindelof X).HasBasis IsLindelof compl
  proof: hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s union t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isLindelof_empty⟩

中文:
定理 hasBasis_coLindelof
  结论: (coLindelof X).HasBasis IsLindelof compl
  证明: hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s union t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isLindelof_empty⟩

Depends on / 依赖: compl_subset_compl, hasBasis_biInf_principal, hs.union, isLindelof_empty, subset_union_left, subset_union_right
-/
theorem hasBasis_coLindelof : (coLindelof X).HasBasis IsLindelof compl :=
  hasBasis_biInf_principal'
    (fun s hs t ht =>
      ⟨s union t, hs.union ht, compl_subset_compl.2 subset_union_left,
        compl_subset_compl.2 subset_union_right⟩)
    ⟨∅, isLindelof_empty⟩

/--
theorem `mem_coLindelof` / 定理 `mem_coLindelof`

English:
theorem mem_coLindelof
  statement: s in coLindelof X ↔ exists t, IsLindelof t ∧ tᶜ subseteq s
  proof: hasBasis_coLindelof.mem_iff

中文:
定理 mem_coLindelof
  结论: s in coLindelof X ↔ 存在 t, IsLindelof t ∧ tᶜ subseteq s
  证明: hasBasis_coLindelof.mem_iff

Depends on / 依赖: hasBasis_coLindelof, hasBasis_coLindelof.mem_iff, mem_iff
-/
theorem mem_coLindelof : s in coLindelof X ↔ exists t, IsLindelof t ∧ tᶜ subseteq s :=
  hasBasis_coLindelof.mem_iff

/--
theorem `mem_coLindelof'` / 定理 `mem_coLindelof'`

English:
theorem mem_coLindelof'
  statement: s in coLindelof X ↔ exists t, IsLindelof t ∧ sᶜ subseteq t
  proof: mem_coLindelof.trans exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

中文:
定理 mem_coLindelof'
  结论: s in coLindelof X ↔ 存在 t, IsLindelof t ∧ sᶜ subseteq t
  证明: mem_coLindelof.trans exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

Depends on / 依赖: and_congr_right, compl_subset_comm, exists_congr, mem_coLindelof, mem_coLindelof.trans
-/
theorem mem_coLindelof' : s in coLindelof X ↔ exists t, IsLindelof t ∧ sᶜ subseteq t :=
mem_coLindelof.trans exists_congr fun _ => and_congr_right fun _ => compl_subset_comm

/--
theorem `_root_.IsLindelof.compl_mem_coLindelof` / 定理 `_root_.IsLindelof.compl_mem_coLindelof`

English:
theorem _root_.IsLindelof.compl_mem_coLindelof
  given: (hs : IsLindelof s)
  statement: sᶜ in coLindelof X
  proof: hasBasis_coLindelof.mem_of_mem hs

中文:
定理 _root_.IsLindelof.compl_mem_coLindelof
  条件: (hs : IsLindelof s)
  结论: sᶜ in coLindelof X
  证明: hasBasis_coLindelof.mem_of_mem hs

Depends on / 依赖: hasBasis_coLindelof, hasBasis_coLindelof.mem_of_mem, mem_of_mem
-/
theorem _root_.IsLindelof.compl_mem_coLindelof (hs : IsLindelof s) : sᶜ in coLindelof X :=
  hasBasis_coLindelof.mem_of_mem hs

/--
theorem `coLindelof_le_cofinite` / 定理 `coLindelof_le_cofinite`

English:
theorem coLindelof_le_cofinite
  statement: coLindelof X <= cofinite
  proof: fun s hs =>
  compl_compl s ▸ hs.isLindelof.compl_mem_coLindelof

中文:
定理 coLindelof_le_cofinite
  结论: coLindelof X <= cofinite
  证明: fun s hs =>
  compl_compl s ▸ hs.isLindelof.compl_mem_coLindelof
-/
theorem coLindelof_le_cofinite : coLindelof X <= cofinite := fun s hs =>
  compl_compl s ▸ hs.isLindelof.compl_mem_coLindelof

/--
theorem `Tendsto.isLindelof_insert_range_of_coLindelof` / 定理 `Tendsto.isLindelof_insert_range_of_coLindelof`

English:
theorem Tendsto.isLindelof_insert_range_of_coLindelof
  statement: {f : X -> Y} {y}
  proof: by
  intro l hne _ hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_coLindelof.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K in l := by

中文:
定理 Tendsto.isLindelof_insert_range_of_coLindelof
  结论: {f : X -> Y} {y}
  证明: by
  intro l hne _ hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_coLindelof.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K in l := by

Depends on / 依赖: ClusterPt, Or.inl, clusterPt_iff_nonempty, exacts, filter_upwards, hd.le_bot, le_bot, le_principal_iff, mem_coLindelof, mem_image_of_mem, mem_of_mem_nhds, not_disjoint_iff_nonempty_inter, not_forall, not_not
-/
theorem Tendsto.isLindelof_insert_range_of_coLindelof {f : X -> Y} {y}
    (hf : Tendsto f (coLindelof X) (𝓝 y)) (hfc : Continuous f) :
    IsLindelof (insert y (range f)) := by
  intro l hne _ hle
  by_cases hy : ClusterPt y l
  · exact ⟨y, Or.inl rfl, hy⟩
  simp only [clusterPt_iff_nonempty, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hy
  rcases hy with ⟨s, hsy, t, htl, hd⟩
  rcases mem_coLindelof.1 (hf hsy) with ⟨K, hKc, hKs⟩
  have : f '' K in l := by
    filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf
    rcases hyf with (rfl | ⟨x, rfl⟩)
    exacts [(hd.le_bot ⟨mem_of_mem_nhds hsy, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 fun hxK => hd.le_bot ⟨hKs hxK, hyt⟩)]
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩
exact ⟨y, Or.inr image_subset_range _ _ hy, hyl⟩

/--
Definition of `Filter.coclosedLindelof` / `Filter.coclosedLindelof` 的定义

English:
definition Filter.coclosedLindelof
  signature: (X : Type*) [TopologicalSpace X]
  body: -- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets.
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsLindelof s), 𝓟 sᶜ

中文:
定义 Filter.coclosedLindelof
  签名: (X : 类型) [TopologicalSpace X]
  定义体: -- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets.
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsLindelof s), 𝓟 sᶜ
-/
def Filter.coclosedLindelof (X : Type*) [TopologicalSpace X] : Filter X :=
  -- `Filter.coclosedLindelof` is the filter generated by complements to closed Lindelof sets.
  ⨅ (s : Set X) (_ : IsClosed s) (_ : IsLindelof s), 𝓟 sᶜ

/--
theorem `hasBasis_coclosedLindelof` / 定理 `hasBasis_coclosedLindelof`

English:
theorem hasBasis_coclosedLindelof
  proof: by
  simp only [Filter.coclosedLindelof, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isLindelof_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s union t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩

中文:
定理 hasBasis_coclosedLindelof
  证明: by
  simp only [Filter.coclosedLindelof, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isLindelof_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s union t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩

Depends on / 依赖: Filter, Filter.coclosedLindelof, coclosedLindelof, compl_subset_compl, hasBasis_biInf_principal, iInf_and, isClosed_empty, isLindelof_empty, subset_union_left, subset_union_right
-/
theorem hasBasis_coclosedLindelof :
    (Filter.coclosedLindelof X).HasBasis (fun s => IsClosed s ∧ IsLindelof s) compl := by
  simp only [Filter.coclosedLindelof, iInf_and']
  refine hasBasis_biInf_principal' ?_ ⟨∅, isClosed_empty, isLindelof_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact ⟨s union t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 subset_union_left,
    compl_subset_compl.2 subset_union_right⟩⟩

/--
theorem `mem_coclosedLindelof` / 定理 `mem_coclosedLindelof`

English:
theorem mem_coclosedLindelof
  statement: s in coclosedLindelof X ↔
  proof: by
  simp only [hasBasis_coclosedLindelof.mem_iff, and_assoc]

中文:
定理 mem_coclosedLindelof
  结论: s in coclosedLindelof X ↔
  证明: by
  simp only [hasBasis_coclosedLindelof.mem_iff, and_assoc]

Depends on / 依赖: and_assoc, hasBasis_coclosedLindelof, hasBasis_coclosedLindelof.mem_iff, mem_iff
-/
theorem mem_coclosedLindelof : s in coclosedLindelof X ↔
    exists t, IsClosed t ∧ IsLindelof t ∧ tᶜ subseteq s := by
  simp only [hasBasis_coclosedLindelof.mem_iff, and_assoc]

/--
theorem `mem_coclosed_Lindelof'` / 定理 `mem_coclosed_Lindelof'`

English:
theorem mem_coclosed_Lindelof'
  statement: s in coclosedLindelof X ↔
  proof: by
  simp only [mem_coclosedLindelof, compl_subset_comm]

中文:
定理 mem_coclosed_Lindelof'
  结论: s in coclosedLindelof X ↔
  证明: by
  simp only [mem_coclosedLindelof, compl_subset_comm]

Depends on / 依赖: compl_subset_comm, mem_coclosedLindelof
-/
theorem mem_coclosed_Lindelof' : s in coclosedLindelof X ↔
    exists t, IsClosed t ∧ IsLindelof t ∧ sᶜ subseteq t := by
  simp only [mem_coclosedLindelof, compl_subset_comm]

/--
theorem `coLindelof_le_coclosedLindelof` / 定理 `coLindelof_le_coclosedLindelof`

English:
theorem coLindelof_le_coclosedLindelof
  statement: coLindelof X <= coclosedLindelof X
  proof: iInf_mono fun _ => le_iInf fun _ => le_rfl

中文:
定理 coLindelof_le_coclosedLindelof
  结论: coLindelof X <= coclosedLindelof X
  证明: iInf_mono fun _ => le_iInf fun _ => le_rfl

Depends on / 依赖: iInf_mono, le_iInf, le_rfl
-/
theorem coLindelof_le_coclosedLindelof : coLindelof X <= coclosedLindelof X :=
  iInf_mono fun _ => le_iInf fun _ => le_rfl

/--
theorem `IsLindeof.compl_mem_coclosedLindelof_of_isClosed` / 定理 `IsLindeof.compl_mem_coclosedLindelof_of_isClosed`

English:
theorem IsLindeof.compl_mem_coclosedLindelof_of_isClosed
  given: (hs : IsLindelof s) (hs' : IsClosed s)
  proof: hasBasis_coclosedLindelof.mem_of_mem ⟨hs', hs⟩

中文:
定理 IsLindeof.compl_mem_coclosedLindelof_of_isClosed
  条件: (hs : IsLindelof s) (hs' : IsClosed s)
  证明: hasBasis_coclosedLindelof.mem_of_mem ⟨hs', hs⟩

Depends on / 依赖: hasBasis_coclosedLindelof, hasBasis_coclosedLindelof.mem_of_mem, mem_of_mem
-/
theorem IsLindeof.compl_mem_coclosedLindelof_of_isClosed (hs : IsLindelof s) (hs' : IsClosed s) :
    sᶜ in Filter.coclosedLindelof X :=
  hasBasis_coclosedLindelof.mem_of_mem ⟨hs', hs⟩

/--
Definition of `LindelofSpace` / `LindelofSpace` 的定义

English:
class LindelofSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - isLindelof_univ : IsLindelof (univ : Set X)

中文:
类 LindelofSpace
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - isLindelof_univ : IsLindelof (univ : Set X)
-/
class LindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Lindelöf space, `Set.univ` is a Lindelöf set. -/
  isLindelof_univ : IsLindelof (univ : Set X)

instance (priority := 10) Subsingleton.lindelofSpace [Subsingleton X] : LindelofSpace X :=
  ⟨subsingleton_univ.isLindelof⟩

/--
theorem `isLindelof_univ_iff` / 定理 `isLindelof_univ_iff`

English:
theorem isLindelof_univ_iff
  statement: IsLindelof (univ : Set X) ↔ LindelofSpace X
  proof: ⟨fun h => ⟨h⟩, fun h => h.1⟩

中文:
定理 isLindelof_univ_iff
  结论: IsLindelof (univ : Set X) ↔ LindelofSpace X
  证明: ⟨fun h => ⟨h⟩, fun h => h.1⟩
-/
theorem isLindelof_univ_iff : IsLindelof (univ : Set X) ↔ LindelofSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

/--
theorem `isLindelof_univ` / 定理 `isLindelof_univ`

English:
theorem isLindelof_univ
  given: [h : LindelofSpace X]
  statement: IsLindelof (univ : Set X)
  proof: h.isLindelof_univ

中文:
定理 isLindelof_univ
  条件: [h : LindelofSpace X]
  结论: IsLindelof (univ : Set X)
  证明: h.isLindelof_univ

Depends on / 依赖: h.isLindelof_univ, isLindelof_univ
-/
theorem isLindelof_univ [h : LindelofSpace X] : IsLindelof (univ : Set X) :=
  h.isLindelof_univ

/--
theorem `cluster_point_of_Lindelof` / 定理 `cluster_point_of_Lindelof`

English:
theorem cluster_point_of_Lindelof
  statement: [LindelofSpace X] (f : Filter X) [NeBot f]
  proof: by
  simpa using isLindelof_univ (show f <= 𝓟 univ by simp)

中文:
定理 cluster_point_of_Lindelof
  结论: [LindelofSpace X] (f : Filter X) [NeBot f]
  证明: by
  simpa using isLindelof_univ (show f <= 𝓟 univ by simp)

Depends on / 依赖: isLindelof_univ
-/
theorem cluster_point_of_Lindelof [LindelofSpace X] (f : Filter X) [NeBot f]
    [CountableInterFilter f] : exists x, ClusterPt x f := by
  simpa using isLindelof_univ (show f <= 𝓟 univ by simp)

/--
theorem `LindelofSpace.elim_nhds_subcover` / 定理 `LindelofSpace.elim_nhds_subcover`

English:
theorem LindelofSpace.elim_nhds_subcover
  given: [LindelofSpace X] (U : X -> Set X) (hU : forall x, U x in 𝓝 x)
  proof: by
  obtain ⟨t, tc, -, s⟩ := IsLindelof.elim_nhds_subcover isLindelof_univ U fun x _ => hU x
  use t, tc
  apply top_unique s

中文:
定理 LindelofSpace.elim_nhds_subcover
  条件: [LindelofSpace X] (U : X -> Set X) (hU : 对任意 x, U x in 𝓝 x)
  证明: by
  obtain ⟨t, tc, -, s⟩ := IsLindelof.elim_nhds_subcover isLindelof_univ U fun x _ => hU x
  use t, tc
  apply top_unique s

Depends on / 依赖: IsLindelof, IsLindelof.elim_nhds_subcover, elim_nhds_subcover, isLindelof_univ, top_unique
-/
theorem LindelofSpace.elim_nhds_subcover [LindelofSpace X] (U : X -> Set X) (hU : forall x, U x in 𝓝 x) :
    exists t : Set X, t.Countable ∧ ⋃ x in t, U x = univ := by
  obtain ⟨t, tc, -, s⟩ := IsLindelof.elim_nhds_subcover isLindelof_univ U fun x _ => hU x
  use t, tc
  apply top_unique s

/--
theorem `lindelofSpace_of_countable_subfamily_closed` / 定理 `lindelofSpace_of_countable_subfamily_closed`

English:
theorem lindelofSpace_of_countable_subfamily_closed
  proof: isLindelof_of_countable_subfamily_closed fun t => by simpa using h t

中文:
定理 lindelofSpace_of_countable_subfamily_closed
  证明: isLindelof_of_countable_subfamily_closed fun t => by simpa using h t

Depends on / 依赖: isLindelof_of_countable_subfamily_closed
-/
theorem lindelofSpace_of_countable_subfamily_closed
    (h : forall {ι : Type u} (t : ι -> Set X), (forall i, IsClosed (t i)) -> ⋂ i, t i = ∅ ->
      exists u : Set ι, u.Countable ∧ ⋂ i in u, t i = ∅) :
    LindelofSpace X where
  isLindelof_univ := isLindelof_of_countable_subfamily_closed fun t => by simpa using h t

/--
theorem `IsClosed.isLindelof` / 定理 `IsClosed.isLindelof`

English:
theorem IsClosed.isLindelof
  given: [LindelofSpace X] (h : IsClosed s)
  statement: IsLindelof s
  proof: isLindelof_univ.of_isClosed_subset h (subset_univ _)

中文:
定理 IsClosed.isLindelof
  条件: [LindelofSpace X] (h : IsClosed s)
  结论: IsLindelof s
  证明: isLindelof_univ.of_isClosed_subset h (subset_univ _)

Depends on / 依赖: isLindelof_univ, isLindelof_univ.of_isClosed_subset, of_isClosed_subset, subset_univ
-/
theorem IsClosed.isLindelof [LindelofSpace X] (h : IsClosed s) : IsLindelof s :=
  isLindelof_univ.of_isClosed_subset h (subset_univ _)

/--
theorem `IsCompact.isLindelof` / 定理 `IsCompact.isLindelof`

English:
theorem IsCompact.isLindelof
  given: (hs : IsCompact s)
  proof: by tauto

中文:
定理 IsCompact.isLindelof
  条件: (hs : IsCompact s)
  证明: by tauto
-/
theorem IsCompact.isLindelof (hs : IsCompact s) :
    IsLindelof s := by tauto

/--
theorem `IsSigmaCompact.isLindelof` / 定理 `IsSigmaCompact.isLindelof`

English:
theorem IsSigmaCompact.isLindelof
  given: (hs : IsSigmaCompact s)
  proof: by
  rw [IsSigmaCompact] at hs
  rcases hs with ⟨K, ⟨hc, huniv⟩⟩
  rw [← huniv]
  have hl : forall n, IsLindelof (K n) := fun n => IsCompact.isLindelof (hc n)
  exact isLindelof_iUnion hl

中文:
定理 IsSigmaCompact.isLindelof
  条件: (hs : IsSigmaCompact s)
  证明: by
  rw [IsSigmaCompact] at hs
  rcases hs with ⟨K, ⟨hc, huniv⟩⟩
  rw [← huniv]
  have hl : forall n, IsLindelof (K n) := fun n => IsCompact.isLindelof (hc n)
  exact isLindelof_iUnion hl

Depends on / 依赖: IsCompact, IsCompact.isLindelof, IsLindelof, IsSigmaCompact, isLindelof, isLindelof_iUnion
-/
theorem IsSigmaCompact.isLindelof (hs : IsSigmaCompact s) :
    IsLindelof s := by
  rw [IsSigmaCompact] at hs
  rcases hs with ⟨K, ⟨hc, huniv⟩⟩
  rw [← huniv]
  have hl : forall n, IsLindelof (K n) := fun n => IsCompact.isLindelof (hc n)
  exact isLindelof_iUnion hl

/-- A compact space `X` is Lindelöf. -/
instance (priority := 100) [CompactSpace X] : LindelofSpace X :=
  { isLindelof_univ := isCompact_univ.isLindelof }

/-- A sigma-compact space `X` is Lindelöf. -/
instance (priority := 100) [SigmaCompactSpace X] : LindelofSpace X :=
  { isLindelof_univ := isSigmaCompact_univ.isLindelof }

/--
Definition of `NonLindelofSpace` / `NonLindelofSpace` 的定义

English:
class NonLindelofSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - nonLindelof_univ : ¬IsLindelof (univ : Set X)

中文:
类 NonLindelofSpace
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - nonLindelof_univ : ¬IsLindelof (univ : Set X)
-/
class NonLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a non-Lindelöf space, `Set.univ` is not a Lindelöf set. -/
  nonLindelof_univ : ¬IsLindelof (univ : Set X)

/--
lemma `nonLindelof_univ` / 引理 `nonLindelof_univ`

English:
lemma nonLindelof_univ
  given: (X : Type*) [TopologicalSpace X] [NonLindelofSpace X]
  proof: NonLindelofSpace.nonLindelof_univ

中文:
引理 nonLindelof_univ
  条件: (X : 类型) [TopologicalSpace X] [NonLindelofSpace X]
  证明: NonLindelofSpace.nonLindelof_univ

Depends on / 依赖: NonLindelofSpace, NonLindelofSpace.nonLindelof_univ, nonLindelof_univ
-/
lemma nonLindelof_univ (X : Type*) [TopologicalSpace X] [NonLindelofSpace X] :
    ¬IsLindelof (univ : Set X) :=
  NonLindelofSpace.nonLindelof_univ

/--
theorem `IsLindelof.ne_univ` / 定理 `IsLindelof.ne_univ`

English:
theorem IsLindelof.ne_univ
  given: [NonLindelofSpace X] (hs : IsLindelof s)
  statement: s != univ
  proof: fun h =>
  nonLindelof_univ X (h ▸ hs)

中文:
定理 IsLindelof.ne_univ
  条件: [NonLindelofSpace X] (hs : IsLindelof s)
  结论: s != univ
  证明: fun h =>
  nonLindelof_univ X (h ▸ hs)
-/
theorem IsLindelof.ne_univ [NonLindelofSpace X] (hs : IsLindelof s) : s != univ := fun h =>
  nonLindelof_univ X (h ▸ hs)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonLindelofSpace
  signature: X] : NeBot (Filter.coLindelof X)
  body: by
  refine hasBasis_coLindelof.neBot_iff.2 fun {s} hs => ?_
  contrapose hs
  rw [not_nonempty_iff_eq_empty]; rw [compl_empty_iff] at hs
  rw [hs]
  exact nonLindelof_univ X

@[simp]

中文:
实例 [NonLindelofSpace
  签名: X] : NeBot (Filter.coLindelof X)
  定义体: by
  refine hasBasis_coLindelof.neBot_iff.2 fun {s} hs => ?_
  contrapose hs
  rw [not_nonempty_iff_eq_empty]; rw [compl_empty_iff] at hs
  rw [hs]
  exact nonLindelof_univ X

@[simp]

Depends on / 依赖: compl_empty_iff, contrapose, hasBasis_coLindelof, hasBasis_coLindelof.neBot_iff, neBot_iff, nonLindelof_univ, not_nonempty_iff_eq_empty
-/
instance [NonLindelofSpace X] : NeBot (Filter.coLindelof X) := by
  refine hasBasis_coLindelof.neBot_iff.2 fun {s} hs => ?_
  contrapose hs
  rw [not_nonempty_iff_eq_empty]; rw [compl_empty_iff] at hs
  rw [hs]
  exact nonLindelof_univ X

@[simp]
/--
theorem `Filter.coLindelof_eq_bot` / 定理 `Filter.coLindelof_eq_bot`

English:
theorem Filter.coLindelof_eq_bot
  given: [LindelofSpace X]
  statement: Filter.coLindelof X = ⊥
  proof: hasBasis_coLindelof.eq_bot_iff.mpr ⟨Set.univ, isLindelof_univ, Set.compl_univ⟩

中文:
定理 Filter.coLindelof_eq_bot
  条件: [LindelofSpace X]
  结论: Filter.coLindelof X = ⊥
  证明: hasBasis_coLindelof.eq_bot_iff.mpr ⟨Set.univ, isLindelof_univ, Set.compl_univ⟩

Depends on / 依赖: Set.compl_univ, Set.univ, compl_univ, eq_bot_iff, hasBasis_coLindelof, hasBasis_coLindelof.eq_bot_iff.mpr, isLindelof_univ
-/
theorem Filter.coLindelof_eq_bot [LindelofSpace X] : Filter.coLindelof X = ⊥ :=
  hasBasis_coLindelof.eq_bot_iff.mpr ⟨Set.univ, isLindelof_univ, Set.compl_univ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonLindelofSpace
  signature: X] : NeBot (Filter.coclosedLindelof X)
  body: neBot_of_le coLindelof_le_coclosedLindelof

中文:
实例 [NonLindelofSpace
  签名: X] : NeBot (Filter.coclosedLindelof X)
  定义体: neBot_of_le coLindelof_le_coclosedLindelof

Depends on / 依赖: coLindelof_le_coclosedLindelof, neBot_of_le
-/
instance [NonLindelofSpace X] : NeBot (Filter.coclosedLindelof X) :=
  neBot_of_le coLindelof_le_coclosedLindelof

/--
theorem `nonLindelofSpace_of_neBot` / 定理 `nonLindelofSpace_of_neBot`

English:
theorem nonLindelofSpace_of_neBot
  given: (_ : NeBot (Filter.coLindelof X))
  statement: NonLindelofSpace X
  proof: ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_coLindelof).ne_empty compl_univ⟩

中文:
定理 nonLindelofSpace_of_neBot
  条件: (_ : NeBot (Filter.coLindelof X))
  结论: NonLindelofSpace X
  证明: ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_coLindelof).ne_empty compl_univ⟩

Depends on / 依赖: Filter, Filter.nonempty_of_mem, compl_mem_coLindelof, compl_univ, ne_empty, nonempty_of_mem
-/
theorem nonLindelofSpace_of_neBot (_ : NeBot (Filter.coLindelof X)) : NonLindelofSpace X :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_coLindelof).ne_empty compl_univ⟩

/--
theorem `Filter.coLindelof_neBot_iff` / 定理 `Filter.coLindelof_neBot_iff`

English:
theorem Filter.coLindelof_neBot_iff
  statement: NeBot (Filter.coLindelof X) ↔ NonLindelofSpace X
  proof: ⟨nonLindelofSpace_of_neBot, fun _ => inferInstance⟩

中文:
定理 Filter.coLindelof_neBot_iff
  结论: NeBot (Filter.coLindelof X) ↔ NonLindelofSpace X
  证明: ⟨nonLindelofSpace_of_neBot, fun _ => inferInstance⟩

Depends on / 依赖: nonLindelofSpace_of_neBot
-/
theorem Filter.coLindelof_neBot_iff : NeBot (Filter.coLindelof X) ↔ NonLindelofSpace X :=
  ⟨nonLindelofSpace_of_neBot, fun _ => inferInstance⟩


/--
theorem `not_LindelofSpace_iff` / 定理 `not_LindelofSpace_iff`

English:
theorem not_LindelofSpace_iff
  statement: ¬LindelofSpace X ↔ NonLindelofSpace X
  proof: ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

中文:
定理 not_LindelofSpace_iff
  结论: ¬LindelofSpace X ↔ NonLindelofSpace X
  证明: ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩
-/
theorem not_LindelofSpace_iff : ¬LindelofSpace X ↔ NonLindelofSpace X :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

/--
theorem `countable_of_Lindelof_of_discrete` / 定理 `countable_of_Lindelof_of_discrete`

English:
theorem countable_of_Lindelof_of_discrete
  given: [LindelofSpace X] [DiscreteTopology X]
  statement: Countable X
  proof: countable_univ_iff.mp isLindelof_univ.countable_of_discrete

中文:
定理 countable_of_Lindelof_of_discrete
  条件: [LindelofSpace X] [DiscreteTopology X]
  结论: Countable X
  证明: countable_univ_iff.mp isLindelof_univ.countable_of_discrete

Depends on / 依赖: countable_of_discrete, countable_univ_iff, countable_univ_iff.mp, isLindelof_univ, isLindelof_univ.countable_of_discrete
-/
theorem countable_of_Lindelof_of_discrete [LindelofSpace X] [DiscreteTopology X] : Countable X :=
  countable_univ_iff.mp isLindelof_univ.countable_of_discrete

/--
theorem `countable_cover_nhds_interior` / 定理 `countable_cover_nhds_interior`

English:
theorem countable_cover_nhds_interior
  given: [LindelofSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x)
  proof: let ⟨t, ht⟩ := isLindelof_univ.elim_countable_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, ⟨ht.1, univ_subset_iff.1 ht.2⟩⟩

中文:
定理 countable_cover_nhds_interior
  条件: [LindelofSpace X] {U : X -> Set X} (hU : 对任意 x, U x in 𝓝 x)
  证明: let ⟨t, ht⟩ := isLindelof_univ.elim_countable_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, ⟨ht.1, univ_subset_iff.1 ht.2⟩⟩

Depends on / 依赖: elim_countable_subcover, interior, isLindelof_univ, isLindelof_univ.elim_countable_subcover, isOpen_interior, mem_iUnion, mem_interior_iff_mem_nhds, univ_subset_iff
-/
theorem countable_cover_nhds_interior [LindelofSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x) :
    exists t : Set X, t.Countable ∧ ⋃ x in t, interior (U x) = univ :=
  let ⟨t, ht⟩ := isLindelof_univ.elim_countable_subcover (fun x => interior (U x))
    (fun _ => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, ⟨ht.1, univ_subset_iff.1 ht.2⟩⟩

/--
theorem `countable_cover_nhds` / 定理 `countable_cover_nhds`

English:
theorem countable_cover_nhds
  given: [LindelofSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x)
  proof: let ⟨t, ht⟩ := countable_cover_nhds_interior hU
⟨t, ⟨ht.1, univ_subset_iff.1 ht.2.symm.subset.trans
    iUnion₂_mono fun _ _ => interior_subset⟩⟩

中文:
定理 countable_cover_nhds
  条件: [LindelofSpace X] {U : X -> Set X} (hU : 对任意 x, U x in 𝓝 x)
  证明: let ⟨t, ht⟩ := countable_cover_nhds_interior hU
⟨t, ⟨ht.1, univ_subset_iff.1 ht.2.symm.subset.trans
    iUnion₂_mono fun _ _ => interior_subset⟩⟩

Depends on / 依赖: countable_cover_nhds_interior, interior_subset, subset, symm.subset.trans, univ_subset_iff
-/
theorem countable_cover_nhds [LindelofSpace X] {U : X -> Set X} (hU : forall x, U x in 𝓝 x) :
    exists t : Set X, t.Countable ∧ ⋃ x in t, U x = univ :=
  let ⟨t, ht⟩ := countable_cover_nhds_interior hU
⟨t, ⟨ht.1, univ_subset_iff.1 ht.2.symm.subset.trans
    iUnion₂_mono fun _ _ => interior_subset⟩⟩

/--
theorem `Filter.comap_coLindelof_le` / 定理 `Filter.comap_coLindelof_le`

English:
theorem Filter.comap_coLindelof_le
  given: {f : X -> Y} (hf : Continuous f)
  proof: by
  rw [(hasBasis_coLindelof.comap f).le_basis_iff hasBasis_coLindelof]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

中文:
定理 Filter.comap_coLindelof_le
  条件: {f : X -> Y} (hf : Continuous f)
  证明: by
  rw [(hasBasis_coLindelof.comap f).le_basis_iff hasBasis_coLindelof]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

Depends on / 依赖: hasBasis_coLindelof, hasBasis_coLindelof.comap, ht.image, le_basis_iff, subset_preimage_image, t.subset_preimage_image
-/
theorem Filter.comap_coLindelof_le {f : X -> Y} (hf : Continuous f) :
    (Filter.coLindelof Y).comap f <= Filter.coLindelof X := by
  rw [(hasBasis_coLindelof.comap f).le_basis_iff hasBasis_coLindelof]
  intro t ht
  refine ⟨f '' t, ht.image hf, ?_⟩
  simpa using t.subset_preimage_image f

/--
theorem `isLindelof_range` / 定理 `isLindelof_range`

English:
theorem isLindelof_range
  given: [LindelofSpace X] {f : X -> Y} (hf : Continuous f)
  proof: by rw [← image_univ]; exact isLindelof_univ.image hf

中文:
定理 isLindelof_range
  条件: [LindelofSpace X] {f : X -> Y} (hf : Continuous f)
  证明: by rw [← image_univ]; exact isLindelof_univ.image hf

Depends on / 依赖: image_univ, isLindelof_univ, isLindelof_univ.image
-/
theorem isLindelof_range [LindelofSpace X] {f : X -> Y} (hf : Continuous f) :
    IsLindelof (range f) := by rw [← image_univ]; exact isLindelof_univ.image hf

/--
theorem `isLindelof_diagonal` / 定理 `isLindelof_diagonal`

English:
theorem isLindelof_diagonal
  given: [LindelofSpace X]
  statement: IsLindelof (diagonal X)
  proof: @range_diag X ▸ isLindelof_range (continuous_id.prodMk continuous_id)

中文:
定理 isLindelof_diagonal
  条件: [LindelofSpace X]
  结论: IsLindelof (diagonal X)
  证明: @range_diag X ▸ isLindelof_range (continuous_id.prodMk continuous_id)

Depends on / 依赖: continuous_id, continuous_id.prodMk, isLindelof_range, prodMk, range_diag
-/
theorem isLindelof_diagonal [LindelofSpace X] : IsLindelof (diagonal X) :=
  @range_diag X ▸ isLindelof_range (continuous_id.prodMk continuous_id)

/--
theorem `Topology.IsInducing.isLindelof_iff` / 定理 `Topology.IsInducing.isLindelof_iff`

English:
theorem Topology.IsInducing.isLindelof_iff
  given: {f : X -> Y} (hf : IsInducing f)
  proof: by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot _ F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

中文:
定理 Topology.IsInducing.isLindelof_iff
  条件: {f : X -> Y} (hf : IsInducing f)
  证明: by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot _ F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

Depends on / 依赖: ClusterPt, F_le, F_ne_bot, continuous, hf.continuous, hf.mapClusterPt_iff, hs.image, mapClusterPt_iff, map_mono, map_principal, trans_eq, x_in
-/
theorem Topology.IsInducing.isLindelof_iff {f : X -> Y} (hf : IsInducing f) :
    IsLindelof s ↔ IsLindelof (f '' s) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot _ F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x in s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/--
theorem `Topology.IsEmbedding.isLindelof_iff` / 定理 `Topology.IsEmbedding.isLindelof_iff`

English:
theorem Topology.IsEmbedding.isLindelof_iff
  given: {f : X -> Y} (hf : IsEmbedding f)
  proof: hf.isInducing.isLindelof_iff

中文:
定理 Topology.IsEmbedding.isLindelof_iff
  条件: {f : X -> Y} (hf : IsEmbedding f)
  证明: hf.isInducing.isLindelof_iff

Depends on / 依赖: hf.isInducing.isLindelof_iff, isInducing, isLindelof_iff
-/
theorem Topology.IsEmbedding.isLindelof_iff {f : X -> Y} (hf : IsEmbedding f) :
    IsLindelof s ↔ IsLindelof (f '' s) := hf.isInducing.isLindelof_iff

/--
theorem `Topology.IsInducing.isLindelof_preimage` / 定理 `Topology.IsInducing.isLindelof_preimage`

English:
theorem Topology.IsInducing.isLindelof_preimage
  statement: {f : X -> Y} (hf : IsInducing f)
  proof: by
  replace hK := hK.inter_right hf'
  rwa [hf.isLindelof_iff, image_preimage_eq_inter_range]

中文:
定理 Topology.IsInducing.isLindelof_preimage
  结论: {f : X -> Y} (hf : IsInducing f)
  证明: by
  replace hK := hK.inter_right hf'
  rwa [hf.isLindelof_iff, image_preimage_eq_inter_range]

Depends on / 依赖: hK.inter_right, hf.isLindelof_iff, image_preimage_eq_inter_range, inter_right, isLindelof_iff, replace
-/
theorem Topology.IsInducing.isLindelof_preimage {f : X -> Y} (hf : IsInducing f)
    (hf' : IsClosed (range f)) {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K) := by
  replace hK := hK.inter_right hf'
  rwa [hf.isLindelof_iff, image_preimage_eq_inter_range]

/--
theorem `Topology.IsClosedEmbedding.isLindelof_preimage` / 定理 `Topology.IsClosedEmbedding.isLindelof_preimage`

English:
theorem Topology.IsClosedEmbedding.isLindelof_preimage
  statement: {f : X -> Y} (hf : IsClosedEmbedding f)
  proof: hf.isInducing.isLindelof_preimage (hf.isClosed_range) hK

中文:
定理 Topology.IsClosedEmbedding.isLindelof_preimage
  结论: {f : X -> Y} (hf : IsClosedEmbedding f)
  证明: hf.isInducing.isLindelof_preimage (hf.isClosed_range) hK

Depends on / 依赖: hf.isClosed_range, hf.isInducing.isLindelof_preimage, isClosed_range, isInducing, isLindelof_preimage
-/
theorem Topology.IsClosedEmbedding.isLindelof_preimage {f : X -> Y} (hf : IsClosedEmbedding f)
    {K : Set Y} (hK : IsLindelof K) : IsLindelof (f ⁻¹' K) :=
  hf.isInducing.isLindelof_preimage (hf.isClosed_range) hK

/--
theorem `Topology.IsClosedEmbedding.tendsto_coLindelof` / 定理 `Topology.IsClosedEmbedding.tendsto_coLindelof`

English:
theorem Topology.IsClosedEmbedding.tendsto_coLindelof
  given: {f : X -> Y} (hf : IsClosedEmbedding f)
  proof: hasBasis_coLindelof.tendsto_right_iff.mpr fun _K hK =>
    (hf.isLindelof_preimage hK).compl_mem_coLindelof

中文:
定理 Topology.IsClosedEmbedding.tendsto_coLindelof
  条件: {f : X -> Y} (hf : IsClosedEmbedding f)
  证明: hasBasis_coLindelof.tendsto_right_iff.mpr fun _K hK =>
    (hf.isLindelof_preimage hK).compl_mem_coLindelof

Depends on / 依赖: compl_mem_coLindelof, hasBasis_coLindelof, hasBasis_coLindelof.tendsto_right_iff.mpr, hf.isLindelof_preimage, isLindelof_preimage, tendsto_right_iff
-/
theorem Topology.IsClosedEmbedding.tendsto_coLindelof {f : X -> Y} (hf : IsClosedEmbedding f) :
    Tendsto f (Filter.coLindelof X) (Filter.coLindelof Y) :=
  hasBasis_coLindelof.tendsto_right_iff.mpr fun _K hK =>
    (hf.isLindelof_preimage hK).compl_mem_coLindelof

/--
theorem `Subtype.isLindelof_iff` / 定理 `Subtype.isLindelof_iff`

English:
theorem Subtype.isLindelof_iff
  given: {p : X -> Prop} {s : Set { x // p x }}
  proof: IsEmbedding.subtypeVal.isLindelof_iff

中文:
定理 Subtype.isLindelof_iff
  条件: {p : X -> 命题} {s : Set { x // p x }}
  证明: IsEmbedding.subtypeVal.isLindelof_iff

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isLindelof_iff, isLindelof_iff, subtypeVal
-/
theorem Subtype.isLindelof_iff {p : X -> Prop} {s : Set { x // p x }} :
    IsLindelof s ↔ IsLindelof ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isLindelof_iff

/--
theorem `isLindelof_iff_isLindelof_univ` / 定理 `isLindelof_iff_isLindelof_univ`

English:
theorem isLindelof_iff_isLindelof_univ
  statement: IsLindelof s ↔ IsLindelof (univ : Set s)
  proof: by
  rw [Subtype.isLindelof_iff]; rw [image_univ]; rw [Subtype.range_coe]

中文:
定理 isLindelof_iff_isLindelof_univ
  结论: IsLindelof s ↔ IsLindelof (univ : Set s)
  证明: by
  rw [Subtype.isLindelof_iff]; rw [image_univ]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.isLindelof_iff, Subtype.range_coe, image_univ, isLindelof_iff, range_coe
-/
theorem isLindelof_iff_isLindelof_univ : IsLindelof s ↔ IsLindelof (univ : Set s) := by
  rw [Subtype.isLindelof_iff]; rw [image_univ]; rw [Subtype.range_coe]

/--
theorem `isLindelof_iff_lindelofSpace` / 定理 `isLindelof_iff_lindelofSpace`

English:
theorem isLindelof_iff_lindelofSpace
  statement: IsLindelof s ↔ LindelofSpace s
  proof: isLindelof_iff_isLindelof_univ.trans isLindelof_univ_iff

@[deprecated (since := "2026-01-12")]
alias isLindelof_iff_LindelofSpace := isLindelof_iff_lindelofSpace

中文:
定理 isLindelof_iff_lindelofSpace
  结论: IsLindelof s ↔ LindelofSpace s
  证明: isLindelof_iff_isLindelof_univ.trans isLindelof_univ_iff

@[deprecated (since := "2026-01-12")]
alias isLindelof_iff_LindelofSpace := isLindelof_iff_lindelofSpace

Depends on / 依赖: isLindelof_iff_isLindelof_univ, isLindelof_iff_isLindelof_univ.trans, isLindelof_univ_iff
-/
theorem isLindelof_iff_lindelofSpace : IsLindelof s ↔ LindelofSpace s :=
  isLindelof_iff_isLindelof_univ.trans isLindelof_univ_iff

@[deprecated (since := "2026-01-12")]
alias isLindelof_iff_LindelofSpace := isLindelof_iff_lindelofSpace

/--
lemma `IsLindelof.of_coe` / 引理 `IsLindelof.of_coe`

English:
lemma IsLindelof.of_coe
  given: [LindelofSpace s]
  statement: IsLindelof s
  proof: isLindelof_iff_lindelofSpace.mpr ‹_›

中文:
引理 IsLindelof.of_coe
  条件: [LindelofSpace s]
  结论: IsLindelof s
  证明: isLindelof_iff_lindelofSpace.mpr ‹_›

Depends on / 依赖: isLindelof_iff_lindelofSpace, isLindelof_iff_lindelofSpace.mpr
-/
lemma IsLindelof.of_coe [LindelofSpace s] : IsLindelof s := isLindelof_iff_lindelofSpace.mpr ‹_›

/--
theorem `IsLindelof.countable` / 定理 `IsLindelof.countable`

English:
theorem IsLindelof.countable
  given: (hs : IsLindelof s) (hs' : DiscreteTopology s)
  statement: s.Countable
  proof: countable_coe_iff.mp
  (@countable_of_Lindelof_of_discrete _ _ (isLindelof_iff_lindelofSpace.mp hs) hs')

中文:
定理 IsLindelof.countable
  条件: (hs : IsLindelof s) (hs' : DiscreteTopology s)
  结论: s.Countable
  证明: countable_coe_iff.mp
  (@countable_of_Lindelof_of_discrete _ _ (isLindelof_iff_lindelofSpace.mp hs) hs')

Depends on / 依赖: countable_coe_iff, countable_coe_iff.mp, countable_of_Lindelof_of_discrete, isLindelof_iff_lindelofSpace, isLindelof_iff_lindelofSpace.mp
-/
theorem IsLindelof.countable (hs : IsLindelof s) (hs' : DiscreteTopology s) : s.Countable :=
  countable_coe_iff.mp
  (@countable_of_Lindelof_of_discrete _ _ (isLindelof_iff_lindelofSpace.mp hs) hs')

/--
theorem `IsLindelof.countable_of_isDiscrete` / 定理 `IsLindelof.countable_of_isDiscrete`

English:
theorem IsLindelof.countable_of_isDiscrete
  given: (hs : IsLindelof s) (hs' : IsDiscrete s)
  proof: hs.countable hs'.to_subtype

中文:
定理 IsLindelof.countable_of_isDiscrete
  条件: (hs : IsLindelof s) (hs' : IsDiscrete s)
  证明: hs.countable hs'.to_subtype

Depends on / 依赖: countable, hs.countable, to_subtype
-/
theorem IsLindelof.countable_of_isDiscrete (hs : IsLindelof s) (hs' : IsDiscrete s) :
    s.Countable := hs.countable hs'.to_subtype

/--
theorem `Topology.IsClosedEmbedding.nonLindelofSpace` / 定理 `Topology.IsClosedEmbedding.nonLindelofSpace`

English:
theorem Topology.IsClosedEmbedding.nonLindelofSpace
  statement: [NonLindelofSpace X] {f : X -> Y}
  proof: nonLindelofSpace_of_neBot hf.tendsto_coLindelof.neBot

中文:
定理 Topology.IsClosedEmbedding.nonLindelofSpace
  结论: [NonLindelofSpace X] {f : X -> Y}
  证明: nonLindelofSpace_of_neBot hf.tendsto_coLindelof.neBot
-/
protected theorem Topology.IsClosedEmbedding.nonLindelofSpace [NonLindelofSpace X] {f : X -> Y}
    (hf : IsClosedEmbedding f) : NonLindelofSpace Y :=
  nonLindelofSpace_of_neBot hf.tendsto_coLindelof.neBot

/--
theorem `Topology.IsClosedEmbedding.LindelofSpace` / 定理 `Topology.IsClosedEmbedding.LindelofSpace`

English:
theorem Topology.IsClosedEmbedding.LindelofSpace
  statement: [h : LindelofSpace Y] {f : X -> Y}
  proof: ⟨by rw [hf.isInducing.isLindelof_iff, image_univ]; exact hf.isClosed_range.isLindelof⟩

中文:
定理 Topology.IsClosedEmbedding.LindelofSpace
  结论: [h : LindelofSpace Y] {f : X -> Y}
  证明: ⟨by rw [hf.isInducing.isLindelof_iff, image_univ]; exact hf.isClosed_range.isLindelof⟩
-/
protected theorem Topology.IsClosedEmbedding.LindelofSpace [h : LindelofSpace Y] {f : X -> Y}
    (hf : IsClosedEmbedding f) : LindelofSpace X :=
  ⟨by rw [hf.isInducing.isLindelof_iff, image_univ]; exact hf.isClosed_range.isLindelof⟩

/-- Countable topological spaces are Lindelof. -/
instance (priority := 100) Countable.LindelofSpace [Countable X] : LindelofSpace X where
  isLindelof_univ := countable_univ.isLindelof

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LindelofSpace
  signature: X] [LindelofSpace Y] : LindelofSpace (X oplus Y) where
  body: by
    rw [← range_inl_union_range_inr]
    exact (isLindelof_range continuous_inl).union (isLindelof_range continuous_inr)

中文:
实例 [LindelofSpace
  签名: X] [LindelofSpace Y] : LindelofSpace (X oplus Y) where
  定义体: by
    rw [← range_inl_union_range_inr]
    exact (isLindelof_range continuous_inl).union (isLindelof_range continuous_inr)

Depends on / 依赖: continuous_inl, continuous_inr, isLindelof_range, range_inl_union_range_inr
-/
instance [LindelofSpace X] [LindelofSpace Y] : LindelofSpace (X oplus Y) where
  isLindelof_univ := by
    rw [← range_inl_union_range_inr]
    exact (isLindelof_range continuous_inl).union (isLindelof_range continuous_inr)

instance {X : ι -> Type*} [Countable ι] [forall i, TopologicalSpace (X i)] [forall i, LindelofSpace (X i)] :
    LindelofSpace (Σ i, X i) where
  isLindelof_univ := by
    rw [Sigma.univ]
    exact isLindelof_iUnion fun i => isLindelof_range continuous_sigmaMk

/--
Instance `Quot.lindelofSpace` / 实例 `Quot.lindelofSpace`

English:
instance Quot.lindelofSpace
  signature: {r : X -> X -> Prop} [LindelofSpace X]
  body: by
    rw [← range_quot_mk]
    exact isLindelof_range continuous_quot_mk

@[deprecated (since := "2026-01-12")]
alias Quot.LindelofSpace := Quot.lindelofSpace

中文:
实例 Quot.lindelofSpace
  签名: {r : X -> X -> 命题} [LindelofSpace X]
  定义体: by
    rw [← range_quot_mk]
    exact isLindelof_range continuous_quot_mk

@[deprecated (since := "2026-01-12")]
alias Quot.LindelofSpace := Quot.lindelofSpace

Depends on / 依赖: continuous_quot_mk, isLindelof_range, range_quot_mk
-/
instance Quot.lindelofSpace {r : X -> X -> Prop} [LindelofSpace X] : LindelofSpace (Quot r) where
  isLindelof_univ := by
    rw [← range_quot_mk]
    exact isLindelof_range continuous_quot_mk

@[deprecated (since := "2026-01-12")]
alias Quot.LindelofSpace := Quot.lindelofSpace

/--
Instance `Quotient.lindelofSpace` / 实例 `Quotient.lindelofSpace`

English:
instance Quotient.lindelofSpace
  signature: {s : Setoid X} [LindelofSpace X]
  body: Quot.lindelofSpace

@[deprecated (since := "2026-01-12")]
alias Quotient.LindelofSpace := Quotient.lindelofSpace

中文:
实例 Quotient.lindelofSpace
  签名: {s : Setoid X} [LindelofSpace X]
  定义体: Quot.lindelofSpace

@[deprecated (since := "2026-01-12")]
alias Quotient.LindelofSpace := Quotient.lindelofSpace

Depends on / 依赖: Quot.lindelofSpace, lindelofSpace
-/
instance Quotient.lindelofSpace {s : Setoid X} [LindelofSpace X] : LindelofSpace (Quotient s) :=
  Quot.lindelofSpace

@[deprecated (since := "2026-01-12")]
alias Quotient.LindelofSpace := Quotient.lindelofSpace

/--
theorem `LindelofSpace.of_continuous_surjective` / 定理 `LindelofSpace.of_continuous_surjective`

English:
theorem LindelofSpace.of_continuous_surjective
  statement: {f : X -> Y} [LindelofSpace X] (hf : Continuous f)
  proof: by
    rw [← Set.image_univ_of_surjective hsur]
    exact IsLindelof.image (isLindelof_univ_iff.mpr ‹_›) hf

中文:
定理 LindelofSpace.of_continuous_surjective
  结论: {f : X -> Y} [LindelofSpace X] (hf : Continuous f)
  证明: by
    rw [← Set.image_univ_of_surjective hsur]
    exact IsLindelof.image (isLindelof_univ_iff.mpr ‹_›) hf

Depends on / 依赖: IsLindelof, IsLindelof.image, Set.image_univ_of_surjective, image_univ_of_surjective, isLindelof_univ_iff, isLindelof_univ_iff.mpr
-/
theorem LindelofSpace.of_continuous_surjective {f : X -> Y} [LindelofSpace X] (hf : Continuous f)
    (hsur : Function.Surjective f) : LindelofSpace Y where
  isLindelof_univ := by
    rw [← Set.image_univ_of_surjective hsur]
    exact IsLindelof.image (isLindelof_univ_iff.mpr ‹_›) hf

/--
Definition of `IsHereditarilyLindelof` / `IsHereditarilyLindelof` 的定义

English:
definition IsHereditarilyLindelof
  signature: (s : Set X)
  body: forall t subseteq s, IsLindelof t

中文:
定义 IsHereditarilyLindelof
  签名: (s : Set X)
  定义体: forall t subseteq s, IsLindelof t

Depends on / 依赖: IsLindelof, subseteq
-/
def IsHereditarilyLindelof (s : Set X) :=
  forall t subseteq s, IsLindelof t

/--
Definition of `HereditarilyLindelofSpace` / `HereditarilyLindelofSpace` 的定义

English:
class HereditarilyLindelofSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - isHereditarilyLindelof_univ : IsHereditarilyLindelof (univ : Set X)

中文:
类 HereditarilyLindelofSpace
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - isHereditarilyLindelof_univ : IsHereditarilyLindelof (univ : Set X)
-/
class HereditarilyLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Hereditarily Lindelöf space, `Set.univ` is a Hereditarily Lindelöf set. -/
  isHereditarilyLindelof_univ : IsHereditarilyLindelof (univ : Set X)

/--
lemma `IsHereditarilyLindelof.isLindelof_subset` / 引理 `IsHereditarilyLindelof.isLindelof_subset`

English:
lemma IsHereditarilyLindelof.isLindelof_subset
  given: (hs : IsHereditarilyLindelof s) (ht : t subseteq s)
  proof: hs t ht

中文:
引理 IsHereditarilyLindelof.isLindelof_subset
  条件: (hs : IsHereditarilyLindelof s) (ht : t subseteq s)
  证明: hs t ht
-/
lemma IsHereditarilyLindelof.isLindelof_subset (hs : IsHereditarilyLindelof s) (ht : t subseteq s) :
    IsLindelof t := hs t ht

/--
lemma `IsHereditarilyLindelof.isLindelof` / 引理 `IsHereditarilyLindelof.isLindelof`

English:
lemma IsHereditarilyLindelof.isLindelof
  given: (hs : IsHereditarilyLindelof s)
  proof: hs.isLindelof_subset Subset.rfl

中文:
引理 IsHereditarilyLindelof.isLindelof
  条件: (hs : IsHereditarilyLindelof s)
  证明: hs.isLindelof_subset Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, hs.isLindelof_subset, isLindelof_subset
-/
lemma IsHereditarilyLindelof.isLindelof (hs : IsHereditarilyLindelof s) :
    IsLindelof s := hs.isLindelof_subset Subset.rfl

instance (priority := 100) HereditarilyLindelof.to_Lindelof [HereditarilyLindelofSpace X] :
    LindelofSpace X where
  isLindelof_univ := HereditarilyLindelofSpace.isHereditarilyLindelof_univ.isLindelof

/--
theorem `HereditarilyLindelofSpace.isLindelof` / 定理 `HereditarilyLindelofSpace.isLindelof`

English:
theorem HereditarilyLindelofSpace.isLindelof
  given: [HereditarilyLindelofSpace X] (s : Set X)
  proof: by
  apply HereditarilyLindelofSpace.isHereditarilyLindelof_univ
  exact subset_univ s

@[deprecated (since := "2026-01-12")]
alias HereditarilyLindelof_LindelofSets := HereditarilyLindelofSpace.isLindelof

中文:
定理 HereditarilyLindelofSpace.isLindelof
  条件: [HereditarilyLindelofSpace X] (s : Set X)
  证明: by
  apply HereditarilyLindelofSpace.isHereditarilyLindelof_univ
  exact subset_univ s

@[deprecated (since := "2026-01-12")]
alias HereditarilyLindelof_LindelofSets := HereditarilyLindelofSpace.isLindelof

Depends on / 依赖: HereditarilyLindelofSpace, HereditarilyLindelofSpace.isHereditarilyLindelof_univ, isHereditarilyLindelof_univ, subset_univ
-/
theorem HereditarilyLindelofSpace.isLindelof [HereditarilyLindelofSpace X] (s : Set X) :
    IsLindelof s := by
  apply HereditarilyLindelofSpace.isHereditarilyLindelof_univ
  exact subset_univ s

@[deprecated (since := "2026-01-12")]
alias HereditarilyLindelof_LindelofSets := HereditarilyLindelofSpace.isLindelof

/--
theorem `HereditarilyLindelofSpace.of_forall_isOpen` / 定理 `HereditarilyLindelofSpace.of_forall_isOpen`

English:
theorem HereditarilyLindelofSpace.of_forall_isOpen
  given: (H : forall s : Set X, IsOpen s -> IsLindelof s)
  proof: by
  refine ⟨fun s _ => isLindelof_of_countable_subcover fun U U_open hU => ?_⟩
  obtain ⟨t, t_count, ht⟩ := H (⋃ i, U i) (isOpen_iUnion U_open)
.elim_countable_subcover U U_open subset_rfl
  exact ⟨t, t_count, hU.trans ht⟩

中文:
定理 HereditarilyLindelofSpace.of_forall_isOpen
  条件: (H : 对任意 s : Set X, IsOpen s -> IsLindelof s)
  证明: by
  refine ⟨fun s _ => isLindelof_of_countable_subcover fun U U_open hU => ?_⟩
  obtain ⟨t, t_count, ht⟩ := H (⋃ i, U i) (isOpen_iUnion U_open)
.elim_countable_subcover U U_open subset_rfl
  exact ⟨t, t_count, hU.trans ht⟩

Depends on / 依赖: U_open, elim_countable_subcover, hU.trans, isLindelof_of_countable_subcover, isOpen_iUnion, subset_rfl, t_count
-/
theorem HereditarilyLindelofSpace.of_forall_isOpen (H : forall s : Set X, IsOpen s -> IsLindelof s) :
    HereditarilyLindelofSpace X := by
  refine ⟨fun s _ => isLindelof_of_countable_subcover fun U U_open hU => ?_⟩
  obtain ⟨t, t_count, ht⟩ := H (⋃ i, U i) (isOpen_iUnion U_open)
.elim_countable_subcover U U_open subset_rfl
  exact ⟨t, t_count, hU.trans ht⟩

instance (priority := 100) SecondCountableTopology.toHereditarilyLindelof
    [SecondCountableTopology X] : HereditarilyLindelofSpace X where
  isHereditarilyLindelof_univ t _ _ := by
    apply isLindelof_iff_countable_subcover.mpr
    intro ι U hι hcover
    have := @isOpen_iUnion_countable X _ _ ι U hι
    rcases this with ⟨t, ⟨htc, htu⟩⟩
    use t, htc
    exact subset_of_subset_of_eq hcover (id htu.symm)

/--
lemma `eq_open_union_countable` / 引理 `eq_open_union_countable`

English:
lemma eq_open_union_countable
  statement: [HereditarilyLindelofSpace X] {ι : Type*} (U : ι -> Set X)
  proof: by
  have : IsLindelof (⋃ i, U i) := HereditarilyLindelofSpace.isLindelof (⋃ i, U i)
  rcases this.elim_countable_subcover U h (Eq.subset rfl) with ⟨t, ⟨htc, htu⟩⟩
  use t, htc
  apply eq_of_subset_of_subset (iUnion₂_subset_iUnion (fun i => i in t) fun i => U i) htu

中文:
引理 eq_open_union_countable
  结论: [HereditarilyLindelofSpace X] {ι : 类型} (U : ι -> Set X)
  证明: by
  have : IsLindelof (⋃ i, U i) := HereditarilyLindelofSpace.isLindelof (⋃ i, U i)
  rcases this.elim_countable_subcover U h (Eq.subset rfl) with ⟨t, ⟨htc, htu⟩⟩
  use t, htc
  apply eq_of_subset_of_subset (iUnion₂_subset_iUnion (fun i => i in t) fun i => U i) htu

Depends on / 依赖: Eq.subset, HereditarilyLindelofSpace, HereditarilyLindelofSpace.isLindelof, IsLindelof, elim_countable_subcover, eq_of_subset_of_subset, isLindelof, subset, this.elim_countable_subcover
-/
lemma eq_open_union_countable [HereditarilyLindelofSpace X] {ι : Type*} (U : ι -> Set X)
    (h : forall i, IsOpen (U i)) : exists t : Set ι, t.Countable ∧ ⋃ i in t, U i = ⋃ i, U i := by
  have : IsLindelof (⋃ i, U i) := HereditarilyLindelofSpace.isLindelof (⋃ i, U i)
  rcases this.elim_countable_subcover U h (Eq.subset rfl) with ⟨t, ⟨htc, htu⟩⟩
  use t, htc
  apply eq_of_subset_of_subset (iUnion₂_subset_iUnion (fun i => i in t) fun i => U i) htu

/--
lemma `eq_open_union_nat` / 引理 `eq_open_union_nat`

English:
lemma eq_open_union_nat
  statement: [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (U : ι -> Set X)
  proof: by
  obtain ⟨t, htc, htu⟩ := eq_open_union_countable U h
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · simp_rw [mem_empty_iff_false, iUnion_false, iUnion_empty, eq_comm (a := ∅), iUnion_eq_empty]
      at htu
    simp [htu]
  · obtain ⟨k, rfl⟩ := htc.exists_eq_range t_ne
    use k
    rwa [biU

中文:
引理 eq_open_union_nat
  结论: [HereditarilyLindelofSpace X] {ι : 类型} [Nonempty ι] (U : ι -> Set X)
  证明: by
  obtain ⟨t, htc, htu⟩ := eq_open_union_countable U h
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · simp_rw [mem_empty_iff_false, iUnion_false, iUnion_empty, eq_comm (a := ∅), iUnion_eq_empty]
      at htu
    simp [htu]
  · obtain ⟨k, rfl⟩ := htc.exists_eq_range t_ne
    use k
    rwa [biU

Depends on / 依赖: biUnion_range, eq_comm, eq_empty_or_nonempty, eq_open_union_countable, exists_eq_range, htc.exists_eq_range, iUnion_empty, iUnion_eq_empty, iUnion_false, mem_empty_iff_false, simp_rw, t_ne
-/
lemma eq_open_union_nat [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (U : ι -> Set X)
    (h : forall i, IsOpen (U i)) : exists k : Nat -> ι, ⋃ n, U (k n) = ⋃ i, U i := by
  obtain ⟨t, htc, htu⟩ := eq_open_union_countable U h
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · simp_rw [mem_empty_iff_false, iUnion_false, iUnion_empty, eq_comm (a := ∅), iUnion_eq_empty]
      at htu
    simp [htu]
  · obtain ⟨k, rfl⟩ := htc.exists_eq_range t_ne
    use k
    rwa [biUnion_range] at htu

/--
lemma `eq_closed_inter_countable` / 引理 `eq_closed_inter_countable`

English:
lemma eq_closed_inter_countable
  statement: [HereditarilyLindelofSpace X] {ι : Type*} (C : ι -> Set X)
  proof: by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_countable (fun i => (C i)ᶜ) (fun i => (h i).isOpen_compl)

中文:
引理 eq_closed_inter_countable
  结论: [HereditarilyLindelofSpace X] {ι : 类型} (C : ι -> Set X)
  证明: by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_countable (fun i => (C i)ᶜ) (fun i => (h i).isOpen_compl)

Depends on / 依赖: compl_inj_iff, eq_open_union_countable, isOpen_compl
-/
lemma eq_closed_inter_countable [HereditarilyLindelofSpace X] {ι : Type*} (C : ι -> Set X)
    (h : forall i, IsClosed (C i)) : exists t : Set ι, t.Countable ∧ ⋂ i in t, C i = ⋂ i, C i := by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_countable (fun i => (C i)ᶜ) (fun i => (h i).isOpen_compl)

/--
lemma `eq_closed_inter_nat` / 引理 `eq_closed_inter_nat`

English:
lemma eq_closed_inter_nat
  statement: [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (C : ι -> Set X)
  proof: by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_nat (fun i => (C i)ᶜ) (fun i => (h i).isOpen_compl)

中文:
引理 eq_closed_inter_nat
  结论: [HereditarilyLindelofSpace X] {ι : 类型} [Nonempty ι] (C : ι -> Set X)
  证明: by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_nat (fun i => (C i)ᶜ) (fun i => (h i).isOpen_compl)

Depends on / 依赖: compl_inj_iff, eq_open_union_nat, isOpen_compl
-/
lemma eq_closed_inter_nat [HereditarilyLindelofSpace X] {ι : Type*} [Nonempty ι] (C : ι -> Set X)
    (h : forall i, IsClosed (C i)) : exists k : Nat -> ι, ⋂ n, C (k n) = ⋂ i, C i := by
  conv in _ = _ => rw [← compl_inj_iff]; simp
  exact eq_open_union_nat (fun i => (C i)ᶜ) (fun i => (h i).isOpen_compl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HereditarilyLindelofSpace
  signature: X] (p
  body: HereditarilyLindelofSpace.of_forall_isOpen fun _ _ =>
Subtype.isLindelof_iff.2 HereditarilyLindelofSpace.isLindelof _

中文:
实例 [HereditarilyLindelofSpace
  签名: X] (p
  定义体: HereditarilyLindelofSpace.of_forall_isOpen fun _ _ =>
Subtype.isLindelof_iff.2 HereditarilyLindelofSpace.isLindelof _

Depends on / 依赖: HereditarilyLindelofSpace, HereditarilyLindelofSpace.isLindelof, HereditarilyLindelofSpace.of_forall_isOpen, Subtype, Subtype.isLindelof_iff, isLindelof, isLindelof_iff, of_forall_isOpen
-/
instance [HereditarilyLindelofSpace X] (p : X -> Prop) :
    HereditarilyLindelofSpace {x // p x} :=
  HereditarilyLindelofSpace.of_forall_isOpen fun _ _ =>
Subtype.isLindelof_iff.2 HereditarilyLindelofSpace.isLindelof _

end Lindelof
