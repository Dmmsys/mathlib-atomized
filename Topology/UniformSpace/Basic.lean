/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Rel
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.ContinuousOn

/-!
# Basic results on uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups.

## Main definitions

In this file we define a complete lattice structure on the type `UniformSpace X`
of uniform structures on `X`, as well as the pullback (`UniformSpace.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `Set (X × X)`.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

@[expose] public section

open Set Filter Topology
open scoped SetRel Uniformity

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open scoped SetRel in
/--
lemma `IsOpen.relComp` / 引理 `IsOpen.relComp`

English:
lemma IsOpen.relComp
  statement: [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  proof: by
  conv =>
    arg 1; equals ⋃ b, (fun p => (p.1, b)) ⁻¹' s inter (fun p => (b, p.2)) ⁻¹' t => ext ⟨_, _⟩; simp
.inter ht.preimage (by fun_prop) exact isOpen_iUnion fun a => hs.preimage (by fun_prop)

中文:
引理 是开集.relComp
  结论: [拓扑空间 α] [拓扑空间 β] [拓扑空间 γ]
  证明: by
  conv =>
    arg 1; equals ⋃ b, (fun p => (p.1, b)) ⁻¹' s inter (fun p => (b, p.2)) ⁻¹' t => ext ⟨_, _⟩; simp
.inter ht.preimage (by fun_prop) exact isOpen_iUnion fun a => hs.preimage (by fun_prop)

Depends on / 依赖: equals, fun_prop, hs.preimage, ht.preimage, isOpen_iUnion, preimage
-/
lemma IsOpen.relComp [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {s : SetRel α β} {t : SetRel β γ} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ○ t) := by
  conv =>
    arg 1; equals ⋃ b, (fun p => (p.1, b)) ⁻¹' s inter (fun p => (b, p.2)) ⁻¹' t => ext ⟨_, _⟩; simp
.inter ht.preimage (by fun_prop) exact isOpen_iUnion fun a => hs.preimage (by fun_prop)

/--
lemma `IsOpen.relInv` / 引理 `IsOpen.relInv`

English:
lemma IsOpen.relInv
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: hs.preimage continuous_swap

中文:
引理 是开集.relInv
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: hs.preimage continuous_swap

Depends on / 依赖: continuous_swap, hs.preimage, preimage
-/
lemma IsOpen.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) : IsOpen s.inv :=
  hs.preimage continuous_swap

/--
lemma `IsOpen.relImage` / 引理 `IsOpen.relImage`

English:
lemma IsOpen.relImage
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
exact isOpen_biUnion fun _ _ => hs.preimage .prodMk_right _

中文:
引理 是开集.relImage
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
exact isOpen_biUnion fun _ _ => hs.preimage .prodMk_right _

Depends on / 依赖: Set.ofPred_exists, SetRel, SetRel.image, exists_prop, hs.preimage, isOpen_biUnion, ofPred_exists, preimage, prodMk_right, simp_rw
-/
lemma IsOpen.relImage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
exact isOpen_biUnion fun _ _ => hs.preimage .prodMk_right _

/--
lemma `IsOpen.relPreimage` / 引理 `IsOpen.relPreimage`

English:
lemma IsOpen.relPreimage
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: hs.relInv.relImage

中文:
引理 是开集.relPreimage
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: hs.relInv.relImage

Depends on / 依赖: hs.relInv.relImage, relImage, relInv
-/
lemma IsOpen.relPreimage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set β} : IsOpen (s.preimage t) :=
  hs.relInv.relImage

/--
lemma `IsClosed.relInv` / 引理 `IsClosed.relInv`

English:
lemma IsClosed.relInv
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: hs.preimage continuous_swap

中文:
引理 是闭集.relInv
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: hs.preimage continuous_swap

Depends on / 依赖: continuous_swap, hs.preimage, preimage
-/
lemma IsClosed.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) : IsClosed s.inv :=
  hs.preimage continuous_swap

/--
lemma `IsClosed.relImage_of_finite` / 引理 `IsClosed.relImage_of_finite`

English:
lemma IsClosed.relImage_of_finite
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
exact ht.isClosed_biUnion fun _ _ => hs.preimage .prodMk_right _

中文:
引理 是闭集.relImage_of_finite
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
exact ht.isClosed_biUnion fun _ _ => hs.preimage .prodMk_right _

Depends on / 依赖: Set.ofPred_exists, SetRel, SetRel.image, exists_prop, hs.preimage, ht.isClosed_biUnion, isClosed_biUnion, ofPred_exists, preimage, prodMk_right, simp_rw
-/
lemma IsClosed.relImage_of_finite [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set α} (ht : t.Finite) : IsClosed (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.ofPred_exists]
exact ht.isClosed_biUnion fun _ _ => hs.preimage .prodMk_right _

/--
lemma `IsClosed.relPreimage_of_finite` / 引理 `IsClosed.relPreimage_of_finite`

English:
lemma IsClosed.relPreimage_of_finite
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: hs.relInv.relImage_of_finite ht

中文:
引理 是闭集.relPreimage_of_finite
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: hs.relInv.relImage_of_finite ht

Depends on / 依赖: hs.relInv.relImage_of_finite, relImage_of_finite, relInv
-/
lemma IsClosed.relPreimage_of_finite [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsClosed s) {t : Set β} (ht : t.Finite) : IsClosed (s.preimage t) :=
  hs.relInv.relImage_of_finite ht

section UniformSpace

variable [UniformSpace α]

/--
theorem `eventually_uniformity_iterate_comp_subset` / 定理 `eventually_uniformity_iterate_comp_subset`

English:
theorem eventually_uniformity_iterate_comp_subset
  given: {s : SetRel α α} (hs : s in 𝓤 α) (n : Nat)
  proof: by
  suffices forallᶠ t in (𝓤 α).smallSets, t subseteq s ∧ (t ○ ·)^[n] t subseteq s from (eventually_and.1 this).2
  induction n generalizing s with
  | zero => simpa
  | succ _ ihn =>
    rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
    refine (ihn htU).mono fun U hU => ?_
    rw [Function

中文:
定理 eventually_uniformity_iterate_comp_subset
  条件: {s : SetRel α α} (hs : s in 𝓤 α) (n : 自然数)
  证明: by
  suffices forallᶠ t in (𝓤 α).smallSets, t subseteq s ∧ (t ○ ·)^[n] t subseteq s from (eventually_and.1 this).2
  induction n generalizing s with
  | zero => simpa
  | succ _ ihn =>
    rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
    refine (ihn htU).mono fun U hU => ?_
    rw [Function

Depends on / 依赖: Function, Function.iterate_succ_apply, SetRel, SetRel.comp_subset_comp, SetRel.left_subset_comp.trans, comp_mem_uniformity_sets, comp_subset_comp, eventually_and, generalizing, isRefl_of_mem_uniformity, iterate_succ_apply, left_subset_comp, smallSets, subseteq
-/
theorem eventually_uniformity_iterate_comp_subset {s : SetRel α α} (hs : s in 𝓤 α) (n : Nat) :
    forallᶠ t in (𝓤 α).smallSets, (t ○ ·)^[n] t subseteq s := by
  suffices forallᶠ t in (𝓤 α).smallSets, t subseteq s ∧ (t ○ ·)^[n] t subseteq s from (eventually_and.1 this).2
  induction n generalizing s with
  | zero => simpa
  | succ _ ihn =>
    rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
    refine (ihn htU).mono fun U hU => ?_
    rw [Function.iterate_succ_apply']
    have := isRefl_of_mem_uniformity htU
exact ⟨hU.1.trans SetRel.left_subset_comp.trans hts,
     (SetRel.comp_subset_comp hU.1 hU.2).trans hts⟩

/--
theorem `eventually_uniformity_comp_subset` / 定理 `eventually_uniformity_comp_subset`

English:
theorem eventually_uniformity_comp_subset
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  proof: eventually_uniformity_iterate_comp_subset hs 1

中文:
定理 eventually_uniformity_comp_subset
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  证明: eventually_uniformity_iterate_comp_subset hs 1

Depends on / 依赖: eventually_uniformity_iterate_comp_subset
-/
theorem eventually_uniformity_comp_subset {s : SetRel α α} (hs : s in 𝓤 α) :
    forallᶠ t in (𝓤 α).smallSets, t ○ t subseteq s :=
  eventually_uniformity_iterate_comp_subset hs 1

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

open UniformSpace (ball)

/--
lemma `isOpen_ball` / 引理 `isOpen_ball`

English:
lemma isOpen_ball
  given: (x : α) {V : SetRel α α} (hV : IsOpen V)
  statement: IsOpen (ball x V)
  proof: hV.preimage .prodMk_right _

中文:
引理 isOpen_ball
  条件: (x : α) {V : SetRel α α} (hV : 是开集 V)
  结论: 是开集 (ball x V)
  证明: hV.preimage .prodMk_right _

Depends on / 依赖: hV.preimage, preimage, prodMk_right
-/
lemma isOpen_ball (x : α) {V : SetRel α α} (hV : IsOpen V) : IsOpen (ball x V) :=
hV.preimage .prodMk_right _

/--
lemma `isClosed_ball` / 引理 `isClosed_ball`

English:
lemma isClosed_ball
  given: (x : α) {V : SetRel α α} (hV : IsClosed V)
  statement: IsClosed (ball x V)
  proof: hV.preimage .prodMk_right _

中文:
引理 isClosed_ball
  条件: (x : α) {V : SetRel α α} (hV : 是闭集 V)
  结论: 是闭集 (ball x V)
  证明: hV.preimage .prodMk_right _

Depends on / 依赖: hV.preimage, preimage, prodMk_right
-/
lemma isClosed_ball (x : α) {V : SetRel α α} (hV : IsClosed V) : IsClosed (ball x V) :=
hV.preimage .prodMk_right _


/--
theorem `hasBasis_nhds_prod` / 定理 `hasBasis_nhds_prod`

English:
theorem hasBasis_nhds_prod
  given: (x y : α)
  proof: by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U inter V, ⟨(𝓤 α).inter_sets U_in V_in, inferInstance⟩, ball_inter_left x U V,
    ball_inter_right y U V⟩

中文:
定理 hasBasis_nhds_prod
  条件: (x y : α)
  证明: by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U inter V, ⟨(𝓤 α).inter_sets U_in V_in, inferInstance⟩, ball_inter_left x U V,
    ball_inter_right y U V⟩

Depends on / 依赖: U_in, U_symm, V_in, V_symm, ball_inter_left, ball_inter_right, hasBasis_nhds, inter_sets, nhds_prod_eq, prod_same_index
-/
theorem hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U inter V, ⟨(𝓤 α).inter_sets U_in V_in, inferInstance⟩, ball_inter_left x U V,
    ball_inter_right y U V⟩

end UniformSpace

open UniformSpace

/--
theorem `nhds_eq_uniformity_prod` / 定理 `nhds_eq_uniformity_prod`

English:
theorem nhds_eq_uniformity_prod
  given: {a b : α}
  proof: by
  rw [nhds_prod_eq]; rw [nhds_nhds_eq_uniformity_uniformity_prod]; rw [lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))

中文:
定理 nhds_eq_uniformity_prod
  条件: {a b : α}
  证明: by
  rw [nhds_prod_eq]; rw [nhds_nhds_eq_uniformity_uniformity_prod]; rw [lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))

Depends on / 依赖: Monotone, Monotone.set_prod, _same_eq_lift, lift_lift, monotone_const, monotone_const.set_prod, monotone_preimage, nhds_nhds_eq_uniformity_uniformity_prod, nhds_prod_eq, set_prod
-/
theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : SetRel α α => { y : α | (y, a) in s } ×ˢ { y : α | (b, y) in s } := by
  rw [nhds_prod_eq]; rw [nhds_nhds_eq_uniformity_uniformity_prod]; rw [lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))

/--
theorem `nhdset_of_mem_uniformity` / 定理 `nhdset_of_mem_uniformity`

English:
theorem nhdset_of_mem_uniformity
  given: {d : SetRel α α} (s : SetRel α α) (hd : d in 𝓤 α)
  proof: by
  let cl_d := { p : α × α | exists x y, (p.1, x) in d ∧ (x, y) in s ∧ (y, p.2) in d }
  have : forall p in s, exists t, t subseteq cl_d ∧ IsOpen t ∧ p in t := fun ⟨x, y⟩ hp =>
mem_nhds_iff.mp
      show cl_d in 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod]; rw [mem_lift'_sets]
        · exact 

中文:
定理 nhdset_of_mem_uniformity
  条件: {d : SetRel α α} (s : SetRel α α) (hd : d in 𝓤 α)
  证明: by
  let cl_d := { p : α × α | exists x y, (p.1, x) in d ∧ (x, y) in s ∧ (y, p.2) in d }
  have : forall p in s, exists t, t subseteq cl_d ∧ IsOpen t ∧ p in t := fun ⟨x, y⟩ hp =>
mem_nhds_iff.mp
      show cl_d in 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod]; rw [mem_lift'_sets]
        · exact 

Depends on / 依赖: IsOpen, SetRel, _sets, cl_d, isOpen_iUnion, mem_lift, mem_nhds_iff, mem_nhds_iff.mp, nhds_eq_uniformity_prod, subseteq
-/
theorem nhdset_of_mem_uniformity {d : SetRel α α} (s : SetRel α α) (hd : d in 𝓤 α) :
    exists t : SetRel α α, IsOpen t ∧ s subseteq t ∧
      t subseteq { p | exists x y, (p.1, x) in d ∧ (x, y) in s ∧ (y, p.2) in d } := by
  let cl_d := { p : α × α | exists x y, (p.1, x) in d ∧ (x, y) in s ∧ (y, p.2) in d }
  have : forall p in s, exists t, t subseteq cl_d ∧ IsOpen t ∧ p in t := fun ⟨x, y⟩ hp =>
mem_nhds_iff.mp
      show cl_d in 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod]; rw [mem_lift'_sets]
        · exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        · exact fun _ _ h _ h' => ⟨h h'.1, h h'.2⟩
  choose t ht using this
  exact ⟨(⋃ p : α × α, ⋃ h : p in s, t p h : SetRel α α),
    isOpen_iUnion fun p : α × α => isOpen_iUnion fun hp => (ht p hp).right.left,
    fun ⟨a, b⟩ hp => by
      simp only [mem_iUnion, Prod.exists]; exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
    iUnion_subset fun p => iUnion_subset fun hp => (ht p hp).left⟩

/--
theorem `nhds_le_uniformity` / 定理 `nhds_le_uniformity`

English:
theorem nhds_le_uniformity
  given: (x : α)
  statement: 𝓝 (x, x) <= 𝓤 α
  proof: by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w in 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_

中文:
定理 nhds_le_uniformity
  条件: (x : α)
  结论: 𝓝 (x, x) <= 𝓤 α
  证明: by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w in 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_

Depends on / 依赖: V_in, ball_mem_nhds, comp_symm_mem_uniformity_sets, mem_comp_of_mem_ball, mem_of_superset, nhds_prod_eq, prod_mem_prod, u_in, v_in, w_in, w_sub, w_symm
-/
theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w in 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball u_in v_in)

/--
theorem `iSup_nhds_le_uniformity` / 定理 `iSup_nhds_le_uniformity`

English:
theorem iSup_nhds_le_uniformity
  statement: ⨆ x : α, 𝓝 (x, x) <= 𝓤 α
  proof: iSup_le nhds_le_uniformity

中文:
定理 iSup_nhds_le_uniformity
  结论: ⨆ x : α, 𝓝 (x, x) <= 𝓤 α
  证明: iSup_le nhds_le_uniformity

Depends on / 依赖: iSup_le, nhds_le_uniformity
-/
theorem iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) <= 𝓤 α :=
  iSup_le nhds_le_uniformity

/--
theorem `nhdsSet_diagonal_le_uniformity` / 定理 `nhdsSet_diagonal_le_uniformity`

English:
theorem nhdsSet_diagonal_le_uniformity
  statement: 𝓝ˢ (diagonal α) <= 𝓤 α
  proof: (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

中文:
定理 nhdsSet_diagonal_le_uniformity
  结论: 𝓝ˢ (diagonal α) <= 𝓤 α
  证明: (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

Depends on / 依赖: iSup_nhds_le_uniformity, nhdsSet_diagonal, trans_le
-/
theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) <= 𝓤 α :=
  (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

section

variable (α)

/--
theorem `UniformSpace.has_seq_basis` / 定理 `UniformSpace.has_seq_basis`

English:
theorem UniformSpace.has_seq_basis
  given: [IsCountablyGenerated <| 𝓤 α]
  proof: let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

中文:
定理 一致空间.has_seq_basis
  条件: [是余untablyGenerated <| 𝓤 α]
  证明: let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_symmetric, exists_antitone_subbasis, hasBasis_symmetric, hbasis
-/
theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    exists V : Nat -> SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ forall n, SetRel.IsSymm (V n) :=
  let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

end


/--
theorem `closure_eq_uniformity` / 定理 `closure_eq_uniformity`

English:
theorem closure_eq_uniformity
  given: (s : Set <| α × α)
  proof: by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_ofPred_eq,
      and_imp, mem_comp_comp, ← mem_inter_iff, inter_comm, Set.Nonempty]

中文:
定理 closure_eq_uniformity
  条件: (s : 集合 <| α × α)
  证明: by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_ofPred_eq,
      and_imp, mem_comp_comp, ← mem_inter_iff, inter_comm, Set.Nonempty]

Depends on / 依赖: Nonempty, Set.Nonempty, UniformSpace, UniformSpace.hasBasis_nhds_prod, and_imp, contextual, hasBasis_nhds_prod, inter_comm, mem_closure_iff_nhds_basis, mem_comp_comp, mem_iInter, mem_inter_iff, mem_ofPred_eq
-/
theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V in {V | V in 𝓤 α ∧ SetRel.IsSymm V}, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_ofPred_eq,
      and_imp, mem_comp_comp, ← mem_inter_iff, inter_comm, Set.Nonempty]

/--
theorem `uniformity_hasBasis_closed` / 定理 `uniformity_hasBasis_closed`

English:
theorem uniformity_hasBasis_closed
  proof: by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iIn

中文:
定理 uniformity_hasBasis_closed
  证明: by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iIn

Depends on / 依赖: Filter, Filter.hasBasis_self, Subset, Subset.trans, closure, closure_eq_uniformity, comp_comp_symm_mem_uniformity_sets, hasBasis_self, iInter_subset, iInter_subset_of_subset, isClosed_closure, mem_of_superset, subset_closure, w_in, w_symm
-/
theorem uniformity_hasBasis_closed :
    HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsClosed V) id := by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iInter_subset
  exact ⟨w_in, w_symm⟩

/--
theorem `uniformity_eq_uniformity_closure` / 定理 `uniformity_eq_uniformity_closure`

English:
theorem uniformity_eq_uniformity_closure
  statement: 𝓤 α = (𝓤 α).lift' closure
  proof: Eq.symm uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right

中文:
定理 uniformity_eq_uniformity_closure
  结论: 𝓤 α = (𝓤 α).lift' closure
  证明: Eq.symm uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right

Depends on / 依赖: And.right, Eq.symm, _closure_eq_self, uniformity_hasBasis_closed, uniformity_hasBasis_closed.lift
-/
theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
Eq.symm uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right

/--
theorem `Filter.HasBasis.uniformity_closure` / 定理 `Filter.HasBasis.uniformity_closure`

English:
theorem Filter.HasBasis.uniformity_closure
  statement: {p : ι -> Prop} {U : ι -> SetRel α α}
  proof: (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

中文:
定理 滤子.有基.uniformity_closure
  结论: {p : ι -> 命题} {U : ι -> SetRel α α}
  证明: (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

Depends on / 依赖: _closure, h.lift, uniformity_eq_uniformity_closure
-/
theorem Filter.HasBasis.uniformity_closure {p : ι -> Prop} {U : ι -> SetRel α α}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

/--
theorem `uniformity_hasBasis_closure` / 定理 `uniformity_hasBasis_closure`

English:
theorem uniformity_hasBasis_closure
  statement: HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α) closure
  proof: (𝓤 α).basis_sets.uniformity_closure

中文:
定理 uniformity_hasBasis_closure
  结论: 有基 (𝓤 α) (fun V : SetRel α α => V in 𝓤 α) closure
  证明: (𝓤 α).basis_sets.uniformity_closure

Depends on / 依赖: basis_sets, basis_sets.uniformity_closure, uniformity_closure
-/
theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure

/--
theorem `closure_eq_inter_uniformity` / 定理 `closure_eq_inter_uniformity`

English:
theorem closure_eq_inter_uniformity
  given: {t : SetRel α α}
  statement: closure t = ⋂ d in 𝓤 α, d ○ (t ○ d)
  proof: calc
    closure t = ⋂ (V) (_ : V in 𝓤 α ∧ SetRel.IsSymm V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V in 𝓤 α, V ○ t ○ V :=
Eq.symm UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV => by gcongr
    _ = ⋂ V in 𝓤 α, V ○ (t ○ V) := by simp [SetRel.comp_assoc]

中文:
定理 closure_eq_inter_uniformity
  条件: {t : SetRel α α}
  结论: closure t = ⋂ d in 𝓤 α, d ○ (t ○ d)
  证明: calc
    closure t = ⋂ (V) (_ : V in 𝓤 α ∧ SetRel.IsSymm V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V in 𝓤 α, V ○ t ○ V :=
Eq.symm UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV => by gcongr
    _ = ⋂ V in 𝓤 α, V ○ (t ○ V) := by simp [SetRel.comp_assoc]

Depends on / 依赖: Eq.symm, IsSymm, SetRel, SetRel.IsSymm, SetRel.comp_assoc, UniformSpace, UniformSpace.hasBasis_symmetric.biInter_mem, biInter_mem, closure, closure_eq_uniformity, comp_assoc, hasBasis_symmetric
-/
theorem closure_eq_inter_uniformity {t : SetRel α α} : closure t = ⋂ d in 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (_ : V in 𝓤 α ∧ SetRel.IsSymm V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V in 𝓤 α, V ○ t ○ V :=
Eq.symm UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV => by gcongr
    _ = ⋂ V in 𝓤 α, V ○ (t ○ V) := by simp [SetRel.comp_assoc]

/--
theorem `uniformity_eq_uniformity_interior` / 定理 `uniformity_eq_uniformity_interior`

English:
theorem uniformity_eq_uniformity_interior
  statement: 𝓤 α = (𝓤 α).lift' interior
  proof: le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s subseteq interior d :=
        calc
          s subseteq t := hst
          _ subseteq interior d :=
            ht.subset_in

中文:
定理 uniformity_eq_uniformity_interior
  结论: 𝓤 α = (𝓤 α).lift' interior
  证明: le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s subseteq interior d :=
        calc
          s subseteq t := hst
          _ subseteq interior d :=
            ht.subset_in

Depends on / 依赖: comp3_mem_uniformity, filter_upwards, hs_comp, ht.subset_interior_iff.mpr, ht_comp, interior, interior_subset, le_antisymm, mem_lift, nhdset_of_mem_uniformity, sets_of_superset, subset_interior_iff, subseteq
-/
theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s subseteq interior d :=
        calc
          s subseteq t := hst
          _ subseteq interior d :=
            ht.subset_interior_iff.mpr fun x (hx : x in t) =>
              let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
              hs_comp ⟨x, h₁, y, h₂, h₃⟩
      have : interior d in 𝓤 α := by filter_upwards [hs] using this
      simp [this])
    fun _ hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset

/--
theorem `interior_mem_uniformity` / 定理 `interior_mem_uniformity`

English:
theorem interior_mem_uniformity
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  statement: interior s in 𝓤 α
  proof: by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

中文:
定理 interior_mem_uniformity
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  结论: interior s in 𝓤 α
  证明: by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

Depends on / 依赖: mem_lift, uniformity_eq_uniformity_interior
-/
theorem interior_mem_uniformity {s : SetRel α α} (hs : s in 𝓤 α) : interior s in 𝓤 α := by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

/--
theorem `mem_uniformity_isClosed` / 定理 `mem_uniformity_isClosed`

English:
theorem mem_uniformity_isClosed
  given: {s : SetRel α α} (h : s in 𝓤 α)
  statement: exists t in 𝓤 α, IsClosed t ∧ t subseteq s
  proof: let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩

中文:
定理 mem_uniformity_isClosed
  条件: {s : SetRel α α} (h : s in 𝓤 α)
  结论: 存在 t in 𝓤 α, 是闭集 t ∧ t subseteq s
  证明: let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩

Depends on / 依赖: ht_mem, mem_iff, uniformity_hasBasis_closed, uniformity_hasBasis_closed.mem_iff
-/
theorem mem_uniformity_isClosed {s : SetRel α α} (h : s in 𝓤 α) : exists t in 𝓤 α, IsClosed t ∧ t subseteq s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩

/--
theorem `isOpen_iff_isOpen_ball_subset` / 定理 `isOpen_iff_isOpen_ball_subset`

English:
theorem isOpen_iff_isOpen_ball_subset
  given: {s : Set α}
  proof: by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩

中文:
定理 isOpen_iff_isOpen_ball_subset
  条件: {s : 集合 α}
  证明: by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩

Depends on / 依赖: ball_mono, interior, interior_mem_uniformity, interior_subset, isOpen_iff_ball_subset, isOpen_interior
-/
theorem isOpen_iff_isOpen_ball_subset {s : Set α} :
    IsOpen s ↔ forall x in s, exists V in 𝓤 α, IsOpen V ∧ ball x V subseteq s := by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩

/--
theorem `closure_ball_subset` / 定理 `closure_ball_subset`

English:
theorem closure_ball_subset
  given: {x : α} {V : SetRel α α}
  statement: closure (ball x V) subseteq ball x (closure V)
  proof: (Continuous.prodMk_right x).closure_preimage_subset V

中文:
定理 closure_ball_subset
  条件: {x : α} {V : SetRel α α}
  结论: closure (ball x V) subseteq ball x (closure V)
  证明: (Continuous.prodMk_right x).closure_preimage_subset V

Depends on / 依赖: Continuous, Continuous.prodMk_right, closure_preimage_subset, prodMk_right
-/
theorem closure_ball_subset {x : α} {V : SetRel α α} : closure (ball x V) subseteq ball x (closure V) :=
  (Continuous.prodMk_right x).closure_preimage_subset V

/--
theorem `Dense.biUnion_uniformity_ball` / 定理 `Dense.biUnion_uniformity_ball`

English:
theorem Dense.biUnion_uniformity_ball
  given: {s : Set α} {U : SetRel α α} (hs : Dense s) (hU : U in 𝓤 α)
  proof: by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) in U⟩
  exact ⟨x, hxs, hxy⟩

中文:
定理 稠密.biUnion_uniformity_ball
  条件: {s : 集合 α} {U : SetRel α α} (hs : 稠密 s) (hU : U in 𝓤 α)
  证明: by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) in U⟩
  exact ⟨x, hxs, hxy⟩

Depends on / 依赖: hs.inter_nhds_nonempty, inter_nhds_nonempty, mem_nhds_right
-/
theorem Dense.biUnion_uniformity_ball {s : Set α} {U : SetRel α α} (hs : Dense s) (hU : U in 𝓤 α) :
    ⋃ x in s, ball x U = univ := by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) in U⟩
  exact ⟨x, hxs, hxy⟩

/--
lemma `DenseRange.iUnion_uniformity_ball` / 引理 `DenseRange.iUnion_uniformity_ball`

English:
lemma DenseRange.iUnion_uniformity_ball
  statement: {ι : Type*} {xs : ι -> α}
  proof: by
  rw [← biUnion_range (f := xs) (g := fun x => UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

中文:
引理 DenseRange.iUnion_uniformity_ball
  结论: {ι : 类型} {xs : ι -> α}
  证明: by
  rw [← biUnion_range (f := xs) (g := fun x => UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

Depends on / 依赖: Dense.biUnion_uniformity_ball, UniformSpace, UniformSpace.ball, biUnion_range, biUnion_uniformity_ball, xs_dense
-/
lemma DenseRange.iUnion_uniformity_ball {ι : Type*} {xs : ι -> α}
    (xs_dense : DenseRange xs) {U : SetRel α α} (hU : U in uniformity α) :
    ⋃ i, UniformSpace.ball (xs i) U = univ := by
  rw [← biUnion_range (f := xs) (g := fun x => UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

/-!
### Uniformity bases
-/

/--
theorem `uniformity_hasBasis_open` / 定理 `uniformity_hasBasis_open`

English:
theorem uniformity_hasBasis_open
  statement: HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
  proof: hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩

中文:
定理 uniformity_hasBasis_open
  结论: 有基 (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ 是开集 V) id
  证明: hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩

Depends on / 依赖: hasBasis_self, interior, interior_mem_uniformity, interior_subset, isOpen_interior
-/
theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩

/--
theorem `Filter.HasBasis.mem_uniformity_iff` / 定理 `Filter.HasBasis.mem_uniformity_iff`

English:
theorem Filter.HasBasis.mem_uniformity_iff
  statement: {p : β -> Prop} {s : β -> SetRel α α}
  proof: h.mem_iff.trans by simp only [Prod.forall, subset_def]

中文:
定理 滤子.有基.mem_uniformity_iff
  结论: {p : β -> 命题} {s : β -> SetRel α α}
  证明: h.mem_iff.trans by simp only [Prod.forall, subset_def]

Depends on / 依赖: Prod.forall, h.mem_iff.trans, mem_iff, subset_def
-/
theorem Filter.HasBasis.mem_uniformity_iff {p : β -> Prop} {s : β -> SetRel α α}
    (h : (𝓤 α).HasBasis p s) {t : SetRel α α} :
    t in 𝓤 α ↔ exists i, p i ∧ forall a b, (a, b) in s i -> (a, b) in t :=
h.mem_iff.trans by simp only [Prod.forall, subset_def]

/--
theorem `uniformity_hasBasis_open_symmetric` / 定理 `uniformity_hasBasis_open_symmetric`

English:
theorem uniformity_hasBasis_open_symmetric
  proof: by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨SetRel.symmetrize s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      inferInstance, SetRel.symmetrize_subset_self⟩

中文:
定理 uniformity_hasBasis_open_symmetric
  证明: by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨SetRel.symmetrize s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      inferInstance, SetRel.symmetrize_subset_self⟩

Depends on / 依赖: IsOpen, IsOpen.inter, SetRel, SetRel.symmetrize, SetRel.symmetrize_subset_self, and_assoc, continuous_swap, preimage, restrict, symmetrize, symmetrize_mem_uniformity, symmetrize_subset_self, uniformity_hasBasis_open, uniformity_hasBasis_open.restrict
-/
theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : SetRel α α => V in 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id := by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨SetRel.symmetrize s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      inferInstance, SetRel.symmetrize_subset_self⟩

/--
theorem `comp_open_symm_mem_uniformity_sets` / 定理 `comp_open_symm_mem_uniformity_sets`

English:
theorem comp_open_symm_mem_uniformity_sets
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  proof: by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u subseteq t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (SetRel.comp_subset_comp hu₄ hu₄).trans ht₂⟩

中文:
定理 comp_open_symm_mem_uniformity_sets
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  证明: by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u subseteq t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (SetRel.comp_subset_comp hu₄ hu₄).trans ht₂⟩

Depends on / 依赖: SetRel, SetRel.comp_subset_comp, comp_mem_uniformity_sets, comp_subset_comp, mem_iff, subseteq, uniformity_hasBasis_open_symmetric, uniformity_hasBasis_open_symmetric.mem_iff.mp
-/
theorem comp_open_symm_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) :
    exists t in 𝓤 α, IsOpen t ∧ SetRel.IsSymm t ∧ t ○ t subseteq s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u subseteq t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (SetRel.comp_subset_comp hu₄ hu₄).trans ht₂⟩

end UniformSpace

open uniformity

section Constructions

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (UniformSpace α)
  body: PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext

中文:
实例 :
  签名: 偏序 (一致空间 α)
  定义体: PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext
-/
instance : PartialOrder (UniformSpace α) :=
  PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext

/--
theorem `UniformSpace.le_def` / 定理 `UniformSpace.le_def`

English:
theorem UniformSpace.le_def
  given: {u₁ u₂ : UniformSpace α}
  statement: u₁ <= u₂ ↔ 𝓤[u₁] <= 𝓤[u₂]
  proof: Iff.rfl

中文:
定理 一致空间.le_def
  条件: {u₁ u₂ : 一致空间 α}
  结论: u₁ <= u₂ ↔ 𝓤[u₁] <= 𝓤[u₂]
  证明: Iff.rfl
-/
protected theorem UniformSpace.le_def {u₁ u₂ : UniformSpace α} : u₁ <= u₂ ↔ 𝓤[u₁] <= 𝓤[u₂] := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (UniformSpace α)
  body: ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u in s, 𝓤[u]
        refl := le_iInf fun u => le_iInf fun _ => u.toCore.refl
        symm := le_iInf₂ fun u hu =>
          le_trans (map_mono <| iInf_le_of_le _ <| iInf_le _ hu) u.symm
        comp := le_iInf₂ fun u hu =>
          le_trans 

中文:
实例 :
  签名: 下确界集 (一致空间 α)
  定义体: ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u in s, 𝓤[u]
        refl := le_iInf fun u => le_iInf fun _ => u.toCore.refl
        symm := le_iInf₂ fun u hu =>
          le_trans (map_mono <| iInf_le_of_le _ <| iInf_le _ hu) u.symm
        comp := le_iInf₂ fun u hu =>
          le_trans 
-/
instance : InfSet (UniformSpace α) :=
  ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u in s, 𝓤[u]
        refl := le_iInf fun u => le_iInf fun _ => u.toCore.refl
        symm := le_iInf₂ fun u hu =>
          le_trans (map_mono <| iInf_le_of_le _ <| iInf_le _ hu) u.symm
        comp := le_iInf₂ fun u hu =>
          le_trans (lift'_mono (iInf_le_of_le _ <| iInf_le _ hu) <| le_rfl) u.comp }⟩

/--
theorem `UniformSpace.sInf_le` / 定理 `UniformSpace.sInf_le`

English:
theorem UniformSpace.sInf_le
  statement: {tt : Set (UniformSpace α)} {t : UniformSpace α}
  proof: show ⨅ u in tt, 𝓤[u] <= 𝓤[t] from iInf₂_le t h

中文:
定理 一致空间.sInf_le
  结论: {tt : 集合 (一致空间 α)} {t : 一致空间 α}
  证明: show ⨅ u in tt, 𝓤[u] <= 𝓤[t] from iInf₂_le t h
-/
protected theorem UniformSpace.sInf_le {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : t in tt) : sInf tt <= t :=
  show ⨅ u in tt, 𝓤[u] <= 𝓤[t] from iInf₂_le t h

/--
theorem `UniformSpace.le_sInf` / 定理 `UniformSpace.le_sInf`

English:
theorem UniformSpace.le_sInf
  statement: {tt : Set (UniformSpace α)} {t : UniformSpace α}
  proof: show 𝓤[t] <= ⨅ u in tt, 𝓤[u] from le_iInf₂ h

中文:
定理 一致空间.le_sInf
  结论: {tt : 集合 (一致空间 α)} {t : 一致空间 α}
  证明: show 𝓤[t] <= ⨅ u in tt, 𝓤[u] from le_iInf₂ h
-/
protected theorem UniformSpace.le_sInf {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : forall t' in tt, t <= t') : t <= sInf tt :=
  show 𝓤[t] <= ⨅ u in tt, 𝓤[u] from le_iInf₂ h

/--
theorem `UniformSpace.isGLB_sInf` / 定理 `UniformSpace.isGLB_sInf`

English:
theorem UniformSpace.isGLB_sInf
  given: {tt : Set (UniformSpace α)}
  statement: IsGLB tt (sInf tt)
  proof: ⟨fun _ => UniformSpace.sInf_le, fun _ => UniformSpace.le_sInf⟩

中文:
定理 一致空间.isGLB_sInf
  条件: {tt : 集合 (一致空间 α)}
  结论: IsGLB tt (sInf tt)
  证明: ⟨fun _ => UniformSpace.sInf_le, fun _ => UniformSpace.le_sInf⟩
-/
protected theorem UniformSpace.isGLB_sInf {tt : Set (UniformSpace α)} : IsGLB tt (sInf tt) :=
  ⟨fun _ => UniformSpace.sInf_le, fun _ => UniformSpace.le_sInf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (UniformSpace α)
  body: ⟨@UniformSpace.mk α ⊤ ⊤ le_top le_top fun x => by simp only [nhds_top, comap_top]⟩

中文:
实例 :
  签名: 顶元素 (一致空间 α)
  定义体: ⟨@UniformSpace.mk α ⊤ ⊤ le_top le_top fun x => by simp only [nhds_top, comap_top]⟩
-/
instance : Top (UniformSpace α) :=
  ⟨@UniformSpace.mk α ⊤ ⊤ le_top le_top fun x => by simp only [nhds_top, comap_top]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (UniformSpace α)
  body: ⟨{ toTopologicalSpace := ⊥
      uniformity := 𝓟 SetRel.id
      symm := by simp [Tendsto, SetRel.id]
comp := lift'_le (mem_principal_self _) principal_mono.2 (SetRel.id_comp _).subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot

中文:
实例 :
  签名: 底元素 (一致空间 α)
  定义体: ⟨{ toTopologicalSpace := ⊥
      uniformity := 𝓟 SetRel.id
      symm := by simp [Tendsto, SetRel.id]
comp := lift'_le (mem_principal_self _) principal_mono.2 (SetRel.id_comp _).subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot
-/
instance : Bot (UniformSpace α) :=
  ⟨{ toTopologicalSpace := ⊥
      uniformity := 𝓟 SetRel.id
      symm := by simp [Tendsto, SetRel.id]
comp := lift'_le (mem_principal_self _) principal_mono.2 (SetRel.id_comp _).subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot α
        simp [SetRel.id] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (UniformSpace α)
  body: ⟨fun u₁ u₂ =>
    { uniformity := 𝓤[u₁] ⊓ 𝓤[u₂]
      symm := u₁.symm.inf u₂.symm
comp := (lift'_inf_le _ _ _).trans inf_le_inf u₁.comp u₂.comp
      toTopologicalSpace := u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace
      nhds_eq_comap_uniformity := fun _ => by
        rw [@nhds_inf _ u₁.toTopolog

中文:
实例 :
  签名: 最小值 (一致空间 α)
  定义体: ⟨fun u₁ u₂ =>
    { uniformity := 𝓤[u₁] ⊓ 𝓤[u₂]
      symm := u₁.symm.inf u₂.symm
comp := (lift'_inf_le _ _ _).trans inf_le_inf u₁.comp u₂.comp
      toTopologicalSpace := u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace
      nhds_eq_comap_uniformity := fun _ => by
        rw [@nhds_inf _ u₁.toTopolog

Depends on / 依赖: _inf_le, comap_inf, inf_le_inf, nhds_eq_comap_uniformity, nhds_inf, symm.inf, toTopologicalSpace, uniformity
-/
instance : Min (UniformSpace α) :=
  ⟨fun u₁ u₂ =>
    { uniformity := 𝓤[u₁] ⊓ 𝓤[u₂]
      symm := u₁.symm.inf u₂.symm
comp := (lift'_inf_le _ _ _).trans inf_le_inf u₁.comp u₂.comp
      toTopologicalSpace := u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace
      nhds_eq_comap_uniformity := fun _ => by
        rw [@nhds_inf _ u₁.toTopologicalSpace _]; rw [@nhds_eq_comap_uniformity _ u₁]; rw [@nhds_eq_comap_uniformity _ u₂]; rw [comap_inf] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (UniformSpace α)
  body: sInf { x | a <= x ∧ b <= x }
  le_sup_left _ _ := UniformSpace.le_sInf fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := UniformSpace.le_sInf fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := UniformSpace.sInf_le ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf a _ _ h₁ h₂ := show a.uniformity <= _ from le_inf h₁ h₂
  inf_le_left 

中文:
实例 :
  签名: 完备格 (一致空间 α)
  定义体: sInf { x | a <= x ∧ b <= x }
  le_sup_left _ _ := UniformSpace.le_sInf fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := UniformSpace.le_sInf fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := UniformSpace.sInf_le ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf a _ _ h₁ h₂ := show a.uniformity <= _ from le_inf h₁ h₂
  inf_le_left 
-/
instance : CompleteLattice (UniformSpace α) where
  sup a b := sInf { x | a <= x ∧ b <= x }
  le_sup_left _ _ := UniformSpace.le_sInf fun _ ⟨h, _⟩ => h
  le_sup_right _ _ := UniformSpace.le_sInf fun _ ⟨_, h⟩ => h
  sup_le _ _ _ h₁ h₂ := UniformSpace.sInf_le ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf a _ _ h₁ h₂ := show a.uniformity <= _ from le_inf h₁ h₂
  inf_le_left a _ := show _ <= a.uniformity from inf_le_left
  inf_le_right _ b := show _ <= b.uniformity from inf_le_right
  le_top a := show a.uniformity <= ⊤ from le_top
  bot_le u := u.toCore.refl
  sSup tt := sInf { t | forall t' in tt, t' <= t }
  isLUB_sSup _ := isGLB_upperBounds.mp UniformSpace.isGLB_sInf
  isGLB_sInf _ := UniformSpace.isGLB_sInf

/--
theorem `iInf_uniformity` / 定理 `iInf_uniformity`

English:
theorem iInf_uniformity
  given: {ι : Sort*} {u : ι -> UniformSpace α}
  statement: 𝓤[iInf u] = ⨅ i, 𝓤[u i]
  proof: iInf_range

中文:
定理 iInf_uniformity
  条件: {ι : 类型层*} {u : ι -> 一致空间 α}
  结论: 𝓤[iInf u] = ⨅ i, 𝓤[u i]
  证明: iInf_range

Depends on / 依赖: iInf_range
-/
theorem iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} : 𝓤[iInf u] = ⨅ i, 𝓤[u i] :=
  iInf_range

/--
theorem `inf_uniformity` / 定理 `inf_uniformity`

English:
theorem inf_uniformity
  given: {u v : UniformSpace α}
  statement: 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v]
  proof: rfl

中文:
定理 inf_uniformity
  条件: {u v : 一致空间 α}
  结论: 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v]
  证明: rfl
-/
theorem inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] := rfl

/--
lemma `bot_uniformity` / 引理 `bot_uniformity`

English:
lemma bot_uniformity
  statement: 𝓤[(⊥ : UniformSpace α)] = 𝓟 SetRel.id
  proof: rfl

中文:
引理 bot_uniformity
  结论: 𝓤[(⊥ : 一致空间 α)] = 𝓟 SetRel.id
  证明: rfl
-/
lemma bot_uniformity : 𝓤[(⊥ : UniformSpace α)] = 𝓟 SetRel.id := rfl

/--
lemma `top_uniformity` / 引理 `top_uniformity`

English:
lemma top_uniformity
  statement: 𝓤[(⊤ : UniformSpace α)] = ⊤
  proof: rfl

中文:
引理 top_uniformity
  结论: 𝓤[(⊤ : 一致空间 α)] = ⊤
  证明: rfl
-/
lemma top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤ := rfl

/--
Instance `inhabitedUniformSpace` / 实例 `inhabitedUniformSpace`

English:
instance inhabitedUniformSpace
  signature: : Inhabited (UniformSpace α)
  body: ⟨⊥⟩

中文:
实例 inhabitedUniformSpace
  签名: : 可居 (一致空间 α)
  定义体: ⟨⊥⟩
-/
instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩

/--
Instance `inhabitedUniformSpaceCore` / 实例 `inhabitedUniformSpaceCore`

English:
instance inhabitedUniformSpaceCore
  signature: : Inhabited (UniformSpace.Core α)
  body: ⟨@UniformSpace.toCore _ default⟩

中文:
实例 inhabitedUniformSpaceCore
  签名: : 可居 (一致空间.核 α)
  定义体: ⟨@UniformSpace.toCore _ default⟩

Depends on / 依赖: UniformSpace, UniformSpace.toCore, toCore
-/
instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Unique (UniformSpace α) where
  body: bot_unique le_principal_iff.2 by
    rw [SetRel.id]; rw [← diagonal]; rw [diagonal_eq_univ]; exact univ_mem

中文:
实例 [子单例
  签名: α] : 唯一 (一致空间 α) where
  定义体: bot_unique le_principal_iff.2 by
    rw [SetRel.id]; rw [← diagonal]; rw [diagonal_eq_univ]; exact univ_mem

Depends on / 依赖: SetRel, SetRel.id, bot_unique, diagonal, diagonal_eq_univ, le_principal_iff, univ_mem
-/
instance [Subsingleton α] : Unique (UniformSpace α) where
uniq u := bot_unique le_principal_iff.2 by
    rw [SetRel.id]; rw [← diagonal]; rw [diagonal_eq_univ]; exact univ_mem

/--
Definition of `UniformSpace.comap` / `UniformSpace.comap` 的定义

English:
abbreviation UniformSpace.comap
  signature: (f : α -> β) (u : UniformSpace β)
  body: 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq]; rw [comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · ex

中文:
缩写 一致空间.comap
  签名: (f : α -> β) (u : 一致空间 β)
  定义体: 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq]; rw [comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · ex
-/
abbrev UniformSpace.comap (f : α -> β) (u : UniformSpace β) : UniformSpace α where
  uniformity := 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq]; rw [comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · exact monotone_id.relComp monotone_id)
    (comap_mono u.comp)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  nhds_eq_comap_uniformity x := by
    simp only [nhds_induced, nhds_eq_comap_uniformity, comap_comap, Function.comp_def]

/--
theorem `uniformity_comap` / 定理 `uniformity_comap`

English:
theorem uniformity_comap
  given: {_ : UniformSpace β} (f : α -> β)
  proof: rfl

中文:
定理 uniformity_comap
  条件: {_ : 一致空间 β} (f : α -> β)
  证明: rfl
-/
theorem uniformity_comap {_ : UniformSpace β} (f : α -> β) :
    𝓤[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β) :=
  rfl

/--
lemma `ball_preimage` / 引理 `ball_preimage`

English:
lemma ball_preimage
  given: {f : α -> β} {U : SetRel β β} {x : α}
  proof: by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

中文:
引理 ball_preimage
  条件: {f : α -> β} {U : SetRel β β} {x : α}
  证明: by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

Depends on / 依赖: Prod.map_apply, UniformSpace, UniformSpace.ball, map_apply, mem_preimage
-/
lemma ball_preimage {f : α -> β} {U : SetRel β β} {x : α} :
    UniformSpace.ball x (Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U := by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `uniformSpace_comap_id` / 定理 `uniformSpace_comap_id`

English:
theorem uniformSpace_comap_id
  given: {α : Type*}
  statement: UniformSpace.comap (id : α -> α) = id
  proof: by
  ext : 2
  rw [uniformity_comap]; rw [Prod.map_id]; rw [comap_id]

中文:
定理 uniformSpace_comap_id
  条件: {α : 类型}
  结论: 一致空间.comap (id : α -> α) = id
  证明: by
  ext : 2
  rw [uniformity_comap]; rw [Prod.map_id]; rw [comap_id]

Depends on / 依赖: Prod.map_id, comap_id, map_id, uniformity_comap
-/
theorem uniformSpace_comap_id {α : Type*} : UniformSpace.comap (id : α -> α) = id := by
  ext : 2
  rw [uniformity_comap]; rw [Prod.map_id]; rw [comap_id]

/--
theorem `UniformSpace.comap_comap` / 定理 `UniformSpace.comap_comap`

English:
theorem UniformSpace.comap_comap
  given: {α β γ} {uγ : UniformSpace γ} {f : α -> β} {g : β -> γ}
  proof: by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]

中文:
定理 一致空间.comap_comap
  条件: {α β γ} {uγ : 一致空间 γ} {f : α -> β} {g : β -> γ}
  证明: by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]

Depends on / 依赖: Filter, Filter.comap_comap, Prod.map_comp_map, comap_comap, map_comp_map, uniformity_comap
-/
theorem UniformSpace.comap_comap {α β γ} {uγ : UniformSpace γ} {f : α -> β} {g : β -> γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) := by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]

/--
theorem `UniformSpace.comap_inf` / 定理 `UniformSpace.comap_inf`

English:
theorem UniformSpace.comap_inf
  given: {α γ} {u₁ u₂ : UniformSpace γ} {f : α -> γ}
  proof: UniformSpace.ext Filter.comap_inf

中文:
定理 一致空间.comap_inf
  条件: {α γ} {u₁ u₂ : 一致空间 γ} {f : α -> γ}
  证明: UniformSpace.ext Filter.comap_inf

Depends on / 依赖: Filter, Filter.comap_inf, UniformSpace, UniformSpace.ext, comap_inf
-/
theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α -> γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  UniformSpace.ext Filter.comap_inf

/--
theorem `UniformSpace.comap_iInf` / 定理 `UniformSpace.comap_iInf`

English:
theorem UniformSpace.comap_iInf
  given: {ι α γ} {u : ι -> UniformSpace γ} {f : α -> γ}
  proof: by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]

中文:
定理 一致空间.comap_iInf
  条件: {ι α γ} {u : ι -> 一致空间 γ} {f : α -> γ}
  证明: by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]

Depends on / 依赖: iInf_uniformity, uniformity_comap
-/
theorem UniformSpace.comap_iInf {ι α γ} {u : ι -> UniformSpace γ} {f : α -> γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f := by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]

/--
theorem `UniformSpace.comap_mono` / 定理 `UniformSpace.comap_mono`

English:
theorem UniformSpace.comap_mono
  given: {α γ} {f : α -> γ}
  proof: fun _ _ hu =>
  Filter.comap_mono hu

中文:
定理 一致空间.comap_mono
  条件: {α γ} {f : α -> γ}
  证明: fun _ _ hu =>
  Filter.comap_mono hu
-/
theorem UniformSpace.comap_mono {α γ} {f : α -> γ} :
    Monotone fun u : UniformSpace γ => u.comap f := fun _ _ hu =>
  Filter.comap_mono hu

/--
theorem `uniformContinuous_iff_le_comap` / 定理 `uniformContinuous_iff_le_comap`

English:
theorem uniformContinuous_iff_le_comap
  statement: {α β} {uα : UniformSpace α} {uβ : UniformSpace β}
  proof: Filter.map_le_iff_le_comap

@[deprecated (since := "2026-05-23")]
alias uniformContinuous_iff := uniformContinuous_iff_le_comap

中文:
定理 uniformContinuous_iff_le_comap
  结论: {α β} {uα : 一致空间 α} {uβ : 一致空间 β}
  证明: Filter.map_le_iff_le_comap

@[deprecated (since := "2026-05-23")]
alias uniformContinuous_iff := uniformContinuous_iff_le_comap

Depends on / 依赖: Filter, Filter.map_le_iff_le_comap, map_le_iff_le_comap
-/
theorem uniformContinuous_iff_le_comap {α β} {uα : UniformSpace α} {uβ : UniformSpace β}
    {f : α -> β} : UniformContinuous f ↔ uα <= uβ.comap f :=
  Filter.map_le_iff_le_comap

@[deprecated (since := "2026-05-23")]
alias uniformContinuous_iff := uniformContinuous_iff_le_comap

/--
theorem `le_iff_uniformContinuous_id` / 定理 `le_iff_uniformContinuous_id`

English:
theorem le_iff_uniformContinuous_id
  given: {u v : UniformSpace α}
  proof: by
  rw [uniformContinuous_iff_le_comap]; rw [uniformSpace_comap_id]; rw [id]

中文:
定理 le_iff_uniformContinuous_id
  条件: {u v : 一致空间 α}
  证明: by
  rw [uniformContinuous_iff_le_comap]; rw [uniformSpace_comap_id]; rw [id]

Depends on / 依赖: uniformContinuous_iff_le_comap, uniformSpace_comap_id
-/
theorem le_iff_uniformContinuous_id {u v : UniformSpace α} :
    u <= v ↔ @UniformContinuous _ _ u v id := by
  rw [uniformContinuous_iff_le_comap]; rw [uniformSpace_comap_id]; rw [id]

/--
theorem `uniformContinuous_comap` / 定理 `uniformContinuous_comap`

English:
theorem uniformContinuous_comap
  given: {f : α -> β} [u : UniformSpace β]
  proof: tendsto_comap

中文:
定理 uniformContinuous_comap
  条件: {f : α -> β} [u : 一致空间 β]
  证明: tendsto_comap

Depends on / 依赖: tendsto_comap
-/
theorem uniformContinuous_comap {f : α -> β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap

/--
theorem `uniformContinuous_comap'` / 定理 `uniformContinuous_comap'`

English:
theorem uniformContinuous_comap'
  statement: {f : γ -> β} {g : α -> γ} [v : UniformSpace β] [u : UniformSpace α]
  proof: tendsto_comap_iff.2 h

中文:
定理 uniformContinuous_comap'
  结论: {f : γ -> β} {g : α -> γ} [v : 一致空间 β] [u : 一致空间 α]
  证明: tendsto_comap_iff.2 h

Depends on / 依赖: tendsto_comap_iff
-/
theorem uniformContinuous_comap' {f : γ -> β} {g : α -> γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h

namespace UniformSpace

/--
theorem `to_nhds_mono` / 定理 `to_nhds_mono`

English:
theorem to_nhds_mono
  given: {u₁ u₂ : UniformSpace α} (h : u₁ <= u₂) (a : α)
  proof: by
  rw [@nhds_eq_uniformity α u₁ a]; rw [@nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl

中文:
定理 to_nhds_mono
  条件: {u₁ u₂ : 一致空间 α} (h : u₁ <= u₂) (a : α)
  证明: by
  rw [@nhds_eq_uniformity α u₁ a]; rw [@nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl

Depends on / 依赖: _mono, le_rfl, nhds_eq_uniformity
-/
theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ <= u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a <=
      @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a := by
  rw [@nhds_eq_uniformity α u₁ a]; rw [@nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl

/--
theorem `toTopologicalSpace_mono` / 定理 `toTopologicalSpace_mono`

English:
theorem toTopologicalSpace_mono
  given: {u₁ u₂ : UniformSpace α} (h : u₁ <= u₂)
  proof: le_of_nhds_le_nhds to_nhds_mono h

中文:
定理 toTopologicalSpace_mono
  条件: {u₁ u₂ : 一致空间 α} (h : u₁ <= u₂)
  证明: le_of_nhds_le_nhds to_nhds_mono h

Depends on / 依赖: le_of_nhds_le_nhds, to_nhds_mono
-/
theorem toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ <= u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ <= @UniformSpace.toTopologicalSpace _ u₂ :=
le_of_nhds_le_nhds to_nhds_mono h

/--
theorem `toTopologicalSpace_comap` / 定理 `toTopologicalSpace_comap`

English:
theorem toTopologicalSpace_comap
  given: {f : α -> β} {u : UniformSpace β}
  proof: rfl

中文:
定理 toTopologicalSpace_comap
  条件: {f : α -> β} {u : 一致空间 β}
  证明: rfl
-/
theorem toTopologicalSpace_comap {f : α -> β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl

/--
lemma `uniformSpace_eq_bot` / 引理 `uniformSpace_eq_bot`

English:
lemma uniformSpace_eq_bot
  given: {u : UniformSpace α}
  statement: u = ⊥ ↔ SetRel.id in 𝓤[u]
  proof: le_bot_iff.symm.trans le_principal_iff

中文:
引理 uniformSpace_eq_bot
  条件: {u : 一致空间 α}
  结论: u = ⊥ ↔ SetRel.id in 𝓤[u]
  证明: le_bot_iff.symm.trans le_principal_iff

Depends on / 依赖: le_bot_iff, le_bot_iff.symm.trans, le_principal_iff
-/
lemma uniformSpace_eq_bot {u : UniformSpace α} : u = ⊥ ↔ SetRel.id in 𝓤[u] :=
  le_bot_iff.symm.trans le_principal_iff

/--
lemma `_root_.Filter.HasBasis.uniformSpace_eq_bot` / 引理 `_root_.Filter.HasBasis.uniformSpace_eq_bot`

English:
lemma _root_.Filter.HasBasis.uniformSpace_eq_bot
  statement: {ι p} {s : ι -> SetRel α α}
  proof: by
  simp [uniformSpace_eq_bot, h.mem_iff, subset_def, Pairwise, not_imp_not]

中文:
引理 _root_.滤子.有基.uniformSpace_eq_bot
  结论: {ι p} {s : ι -> SetRel α α}
  证明: by
  simp [uniformSpace_eq_bot, h.mem_iff, subset_def, Pairwise, not_imp_not]
-/
protected lemma _root_.Filter.HasBasis.uniformSpace_eq_bot {ι p} {s : ι -> SetRel α α}
    {u : UniformSpace α} (h : 𝓤[u].HasBasis p s) :
    u = ⊥ ↔ exists i, p i ∧ Pairwise fun x y : α => (x, y) ∉ s i := by
  simp [uniformSpace_eq_bot, h.mem_iff, subset_def, Pairwise, not_imp_not]

/--
theorem `toTopologicalSpace_bot` / 定理 `toTopologicalSpace_bot`

English:
theorem toTopologicalSpace_bot
  statement: @UniformSpace.toTopologicalSpace α ⊥ = ⊥
  proof: rfl

中文:
定理 toTopologicalSpace_bot
  结论: @一致空间.toTopologicalSpace α ⊥ = ⊥
  证明: rfl
-/
theorem toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ := rfl

/--
theorem `toTopologicalSpace_top` / 定理 `toTopologicalSpace_top`

English:
theorem toTopologicalSpace_top
  statement: @UniformSpace.toTopologicalSpace α ⊤ = ⊤
  proof: rfl

中文:
定理 toTopologicalSpace_top
  结论: @一致空间.toTopologicalSpace α ⊤ = ⊤
  证明: rfl
-/
theorem toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ := rfl

/--
theorem `toTopologicalSpace_iInf` / 定理 `toTopologicalSpace_iInf`

English:
theorem toTopologicalSpace_iInf
  given: {ι : Sort*} {u : ι -> UniformSpace α}
  proof: TopologicalSpace.ext_nhds fun a => by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]

中文:
定理 toTopologicalSpace_iInf
  条件: {ι : 类型层*} {u : ι -> 一致空间 α}
  证明: TopologicalSpace.ext_nhds fun a => by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]

Depends on / 依赖: Filter, Filter.comap_iInf, TopologicalSpace, TopologicalSpace.ext_nhds, comap_iInf, ext_nhds, iInf_uniformity, nhds_eq_comap_uniformity, nhds_iInf
-/
theorem toTopologicalSpace_iInf {ι : Sort*} {u : ι -> UniformSpace α} :
    (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a => by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]

/--
theorem `toTopologicalSpace_sInf` / 定理 `toTopologicalSpace_sInf`

English:
theorem toTopologicalSpace_sInf
  given: {s : Set (UniformSpace α)}
  proof: by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]

中文:
定理 toTopologicalSpace_sInf
  条件: {s : 集合 (一致空间 α)}
  证明: by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]

Depends on / 依赖: sInf_eq_iInf, toTopologicalSpace_iInf
-/
theorem toTopologicalSpace_sInf {s : Set (UniformSpace α)} :
    (sInf s).toTopologicalSpace = ⨅ i in s, @UniformSpace.toTopologicalSpace α i := by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]

/--
theorem `toTopologicalSpace_inf` / 定理 `toTopologicalSpace_inf`

English:
theorem toTopologicalSpace_inf
  given: {u v : UniformSpace α}
  proof: rfl

中文:
定理 toTopologicalSpace_inf
  条件: {u v : 一致空间 α}
  证明: rfl
-/
theorem toTopologicalSpace_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl

end UniformSpace

section

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] {f : α -> β} {s t : Set α}

@[fun_prop]
/--
theorem `UniformContinuous.continuous` / 定理 `UniformContinuous.continuous`

English:
theorem UniformContinuous.continuous
  given: (hf : UniformContinuous f)
  statement: Continuous f
  proof: continuous_iff_le_induced.mpr UniformSpace.toTopologicalSpace_mono
    uniformContinuous_iff_le_comap.1 hf

@[fun_prop]

中文:
定理 一致连续.continuous
  条件: (hf : 一致连续 f)
  结论: 连续 f
  证明: continuous_iff_le_induced.mpr UniformSpace.toTopologicalSpace_mono
    uniformContinuous_iff_le_comap.1 hf

@[fun_prop]

Depends on / 依赖: UniformSpace, UniformSpace.toTopologicalSpace_mono, continuous_iff_le_induced, continuous_iff_le_induced.mpr, toTopologicalSpace_mono, uniformContinuous_iff_le_comap
-/
theorem UniformContinuous.continuous (hf : UniformContinuous f) : Continuous f :=
continuous_iff_le_induced.mpr UniformSpace.toTopologicalSpace_mono
    uniformContinuous_iff_le_comap.1 hf

@[fun_prop]
/--
lemma `UniformContinuous.uniformContinuousOn` / 引理 `UniformContinuous.uniformContinuousOn`

English:
lemma UniformContinuous.uniformContinuousOn
  given: (hf : UniformContinuous f)
  proof: tendsto_inf_left hf

中文:
引理 一致连续.uniformContinuousOn
  条件: (hf : 一致连续 f)
  证明: tendsto_inf_left hf

Depends on / 依赖: tendsto_inf_left
-/
lemma UniformContinuous.uniformContinuousOn (hf : UniformContinuous f) :
    UniformContinuousOn f s :=
  tendsto_inf_left hf

/--
lemma `UniformContinuousOn.mono` / 引理 `UniformContinuousOn.mono`

English:
lemma UniformContinuousOn.mono
  given: (hf : UniformContinuousOn f s) (ht : t subseteq s)
  proof: Tendsto.mono_left hf (inf_le_inf le_rfl (by simp [ht]))

中文:
引理 UniformContinuousOn.mono
  条件: (hf : UniformContinuousOn f s) (ht : t subseteq s)
  证明: Tendsto.mono_left hf (inf_le_inf le_rfl (by simp [ht]))

Depends on / 依赖: Tendsto, Tendsto.mono_left, inf_le_inf, le_rfl, mono_left
-/
lemma UniformContinuousOn.mono (hf : UniformContinuousOn f s) (ht : t subseteq s) :
    UniformContinuousOn f t :=
  Tendsto.mono_left hf (inf_le_inf le_rfl (by simp [ht]))

/--
lemma `UniformContinuousOn.congr` / 引理 `UniformContinuousOn.congr`

English:
lemma UniformContinuousOn.congr
  statement: {f g : α -> β} {s : Set α}
  proof: by
  apply hf.congr'
  apply EventuallyEq.filter_mono _ inf_le_right
  filter_upwards [mem_principal_self _] with ⟨a, b⟩ ⟨ha, hb⟩ using by simp [h ha, h hb]

@[fun_prop]

中文:
引理 UniformContinuousOn.congr
  结论: {f g : α -> β} {s : 集合 α}
  证明: by
  apply hf.congr'
  apply EventuallyEq.filter_mono _ inf_le_right
  filter_upwards [mem_principal_self _] with ⟨a, b⟩ ⟨ha, hb⟩ using by simp [h ha, h hb]

@[fun_prop]

Depends on / 依赖: EventuallyEq, EventuallyEq.filter_mono, filter_mono, filter_upwards, hf.congr, inf_le_right, mem_principal_self
-/
lemma UniformContinuousOn.congr {f g : α -> β} {s : Set α}
    (hf : UniformContinuousOn f s) (h : EqOn f g s) :
    UniformContinuousOn g s := by
  apply hf.congr'
  apply EventuallyEq.filter_mono _ inf_le_right
  filter_upwards [mem_principal_self _] with ⟨a, b⟩ ⟨ha, hb⟩ using by simp [h ha, h hb]

@[fun_prop]
/--
lemma `UniformContinuousOn.comp` / 引理 `UniformContinuousOn.comp`

English:
lemma UniformContinuousOn.comp
  statement: {g : β -> γ} {t : Set β} (hg : UniformContinuousOn g t)
  proof: by
  change Tendsto ((fun x => (g x.1, g x.2)) ∘ (fun x => (f x.1, f x.2))) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 γ)
  apply Tendsto.comp hg
  refine tendsto_inf.2 ⟨hf, tendsto_inf_right ?_⟩
  simp only [tendsto_principal, mem_prod, eventually_principal, and_imp, Prod.forall]
  exact fun a b ha hb => ⟨hst ha, hst h

中文:
引理 UniformContinuousOn.comp
  结论: {g : β -> γ} {t : 集合 β} (hg : UniformContinuousOn g t)
  证明: by
  change Tendsto ((fun x => (g x.1, g x.2)) ∘ (fun x => (f x.1, f x.2))) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 γ)
  apply Tendsto.comp hg
  refine tendsto_inf.2 ⟨hf, tendsto_inf_right ?_⟩
  simp only [tendsto_principal, mem_prod, eventually_principal, and_imp, Prod.forall]
  exact fun a b ha hb => ⟨hst ha, hst h

Depends on / 依赖: Prod.forall, Tendsto, Tendsto.comp, and_imp, eventually_principal, mem_prod, tendsto_inf, tendsto_inf_right, tendsto_principal
-/
lemma UniformContinuousOn.comp {g : β -> γ} {t : Set β} (hg : UniformContinuousOn g t)
    (hf : UniformContinuousOn f s) (hst : MapsTo f s t) : UniformContinuousOn (g ∘ f) s := by
  change Tendsto ((fun x => (g x.1, g x.2)) ∘ (fun x => (f x.1, f x.2))) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 γ)
  apply Tendsto.comp hg
  refine tendsto_inf.2 ⟨hf, tendsto_inf_right ?_⟩
  simp only [tendsto_principal, mem_prod, eventually_principal, and_imp, Prod.forall]
  exact fun a b ha hb => ⟨hst ha, hst hb⟩

@[fun_prop]
/--
lemma `UniformContinuous.comp_uniformContinuousOn` / 引理 `UniformContinuous.comp_uniformContinuousOn`

English:
lemma UniformContinuous.comp_uniformContinuousOn
  statement: {g : β -> γ}
  proof: (hg.uniformContinuousOn (s := univ)).comp hf (mapsTo_univ _ _)

中文:
引理 一致连续.comp_uniformContinuousOn
  结论: {g : β -> γ}
  证明: (hg.uniformContinuousOn (s := univ)).comp hf (mapsTo_univ _ _)

Depends on / 依赖: hg.uniformContinuousOn, mapsTo_univ, uniformContinuousOn
-/
lemma UniformContinuous.comp_uniformContinuousOn {g : β -> γ}
    (hg : UniformContinuous g) (hf : UniformContinuousOn f s) : UniformContinuousOn (g ∘ f) s :=
  (hg.uniformContinuousOn (s := univ)).comp hf (mapsTo_univ _ _)

end

/--
Instance `ULift.uniformSpace` / 实例 `ULift.uniformSpace`

English:
instance ULift.uniformSpace
  signature: [UniformSpace α]
  body: UniformSpace.comap ULift.down ‹_›

中文:
实例 类型层提升.uniformSpace
  签名: [一致空间 α]
  定义体: UniformSpace.comap ULift.down ‹_›

Depends on / 依赖: ULift.down, UniformSpace, UniformSpace.comap
-/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›

/--
Instance `OrderDual.instUniformSpace` / 实例 `OrderDual.instUniformSpace`

English:
instance OrderDual.instUniformSpace
  signature: [UniformSpace α]
  body: ‹UniformSpace α›

中文:
实例 OrderDual.instUniformSpace
  签名: [一致空间 α]
  定义体: ‹UniformSpace α›

Depends on / 依赖: UniformSpace
-/
instance OrderDual.instUniformSpace [UniformSpace α] : UniformSpace (αᵒᵈ) :=
  ‹UniformSpace α›

section UniformContinuousInfi

-- TODO: add an `iff` lemma?
/--
theorem `UniformContinuous.inf_rng` / 定理 `UniformContinuous.inf_rng`

English:
theorem UniformContinuous.inf_rng
  statement: {f : α -> β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
  proof: tendsto_inf.mpr ⟨h₁, h₂⟩

中文:
定理 一致连续.inf_rng
  结论: {f : α -> β} {u₁ : 一致空间 α} {u₂ u₃ : 一致空间 β}
  证明: tendsto_inf.mpr ⟨h₁, h₂⟩

Depends on / 依赖: tendsto_inf, tendsto_inf.mpr
-/
theorem UniformContinuous.inf_rng {f : α -> β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : UniformContinuous[u₁, u₂] f) (h₂ : UniformContinuous[u₁, u₃] f) :
    UniformContinuous[u₁, u₂ ⊓ u₃] f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩

/--
theorem `UniformContinuous.inf_dom_left` / 定理 `UniformContinuous.inf_dom_left`

English:
theorem UniformContinuous.inf_dom_left
  statement: {f : α -> β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
  proof: tendsto_inf_left hf

中文:
定理 一致连续.inf_dom_left
  结论: {f : α -> β} {u₁ u₂ : 一致空间 α} {u₃ : 一致空间 β}
  证明: tendsto_inf_left hf

Depends on / 依赖: tendsto_inf_left
-/
theorem UniformContinuous.inf_dom_left {f : α -> β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₁, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_left hf

/--
theorem `UniformContinuous.inf_dom_right` / 定理 `UniformContinuous.inf_dom_right`

English:
theorem UniformContinuous.inf_dom_right
  statement: {f : α -> β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
  proof: tendsto_inf_right hf

中文:
定理 一致连续.inf_dom_right
  结论: {f : α -> β} {u₁ u₂ : 一致空间 α} {u₃ : 一致空间 β}
  证明: tendsto_inf_right hf

Depends on / 依赖: tendsto_inf_right
-/
theorem UniformContinuous.inf_dom_right {f : α -> β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₂, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_right hf

/--
theorem `uniformContinuous_sInf_dom` / 定理 `uniformContinuous_sInf_dom`

English:
theorem uniformContinuous_sInf_dom
  statement: {f : α -> β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
  proof: by
  delta UniformContinuous
  rw [sInf_eq_iInf']; rw [iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf

中文:
定理 uniformContinuous_sInf_dom
  结论: {f : α -> β} {u₁ : 集合 (一致空间 α)} {u₂ : 一致空间 β}
  证明: by
  delta UniformContinuous
  rw [sInf_eq_iInf']; rw [iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf

Depends on / 依赖: UniformContinuous, iInf_uniformity, sInf_eq_iInf, tendsto_iInf
-/
theorem uniformContinuous_sInf_dom {f : α -> β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
    {u : UniformSpace α} (h₁ : u in u₁) (hf : UniformContinuous[u, u₂] f) :
    UniformContinuous[sInf u₁, u₂] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf']; rw [iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf

/--
theorem `uniformContinuous_sInf_rng` / 定理 `uniformContinuous_sInf_rng`

English:
theorem uniformContinuous_sInf_rng
  given: {f : α -> β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)}
  proof: by
  delta UniformContinuous
  rw [sInf_eq_iInf']; rw [iInf_uniformity]; rw [tendsto_iInf]; rw [SetCoe.forall]

中文:
定理 uniformContinuous_sInf_rng
  条件: {f : α -> β} {u₁ : 一致空间 α} {u₂ : 集合 (一致空间 β)}
  证明: by
  delta UniformContinuous
  rw [sInf_eq_iInf']; rw [iInf_uniformity]; rw [tendsto_iInf]; rw [SetCoe.forall]

Depends on / 依赖: SetCoe, SetCoe.forall, UniformContinuous, iInf_uniformity, sInf_eq_iInf, tendsto_iInf
-/
theorem uniformContinuous_sInf_rng {f : α -> β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)} :
    UniformContinuous[u₁, sInf u₂] f ↔ forall u in u₂, UniformContinuous[u₁, u] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf']; rw [iInf_uniformity]; rw [tendsto_iInf]; rw [SetCoe.forall]

/--
theorem `uniformContinuous_iInf_dom` / 定理 `uniformContinuous_iInf_dom`

English:
theorem uniformContinuous_iInf_dom
  statement: {f : α -> β} {u₁ : ι -> UniformSpace α} {u₂ : UniformSpace β}
  proof: by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf

中文:
定理 uniformContinuous_iInf_dom
  结论: {f : α -> β} {u₁ : ι -> 一致空间 α} {u₂ : 一致空间 β}
  证明: by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf

Depends on / 依赖: UniformContinuous, iInf_uniformity, tendsto_iInf
-/
theorem uniformContinuous_iInf_dom {f : α -> β} {u₁ : ι -> UniformSpace α} {u₂ : UniformSpace β}
    {i : ι} (hf : UniformContinuous[u₁ i, u₂] f) : UniformContinuous[iInf u₁, u₂] f := by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf

/--
theorem `uniformContinuous_iInf_rng` / 定理 `uniformContinuous_iInf_rng`

English:
theorem uniformContinuous_iInf_rng
  given: {f : α -> β} {u₁ : UniformSpace α} {u₂ : ι -> UniformSpace β}
  proof: by
  delta UniformContinuous
  rw [iInf_uniformity]; rw [tendsto_iInf]

中文:
定理 uniformContinuous_iInf_rng
  条件: {f : α -> β} {u₁ : 一致空间 α} {u₂ : ι -> 一致空间 β}
  证明: by
  delta UniformContinuous
  rw [iInf_uniformity]; rw [tendsto_iInf]

Depends on / 依赖: UniformContinuous, iInf_uniformity, tendsto_iInf
-/
theorem uniformContinuous_iInf_rng {f : α -> β} {u₁ : UniformSpace α} {u₂ : ι -> UniformSpace β} :
    UniformContinuous[u₁, iInf u₂] f ↔ forall i, UniformContinuous[u₁, u₂ i] f := by
  delta UniformContinuous
  rw [iInf_uniformity]; rw [tendsto_iInf]

end UniformContinuousInfi

/--
theorem `discreteTopology_of_discrete_uniformity` / 定理 `discreteTopology_of_discrete_uniformity`

English:
theorem discreteTopology_of_discrete_uniformity
  statement: [hα : UniformSpace α]
  proof: ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩

中文:
定理 discreteTopology_of_discrete_uniformity
  结论: [hα : 一致空间 α]
  证明: ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩

Depends on / 依赖: UniformSpace, UniformSpace.ext, h.symm
-/
theorem discreteTopology_of_discrete_uniformity [hα : UniformSpace α]
    (h : uniformity α = 𝓟 SetRel.id) : DiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace Empty
  body: ⊥

中文:
实例 :
  签名: 一致空间 空
  定义体: ⊥
-/
instance : UniformSpace Empty := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace PUnit
  body: ⊥

中文:
实例 :
  签名: 一致空间 命题单元
  定义体: ⊥
-/
instance : UniformSpace PUnit := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace Bool
  body: ⊥

中文:
实例 :
  签名: 一致空间 布尔值
  定义体: ⊥
-/
instance : UniformSpace Bool := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace Nat
  body: ⊥

中文:
实例 :
  签名: 一致空间 自然数
  定义体: ⊥
-/
instance : UniformSpace Nat := ⊥
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace Int
  body: ⊥

中文:
实例 :
  签名: 一致空间 整数
  定义体: ⊥
-/
instance : UniformSpace Int := ⊥

section

variable [UniformSpace α]

open Additive Multiplicative

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (Additive α)
  body: ‹UniformSpace α›

中文:
实例 :
  签名: 一致空间 (加性 α)
  定义体: ‹UniformSpace α›
-/
instance : UniformSpace (Additive α) := ‹UniformSpace α›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (Multiplicative α)
  body: ‹UniformSpace α›

@[fun_prop]

中文:
实例 :
  签名: 一致空间 (Multiplicative α)
  定义体: ‹UniformSpace α›

@[fun_prop]

Depends on / 依赖: UniformSpace
-/
instance : UniformSpace (Multiplicative α) := ‹UniformSpace α›

@[fun_prop]
/--
theorem `uniformContinuous_ofMul` / 定理 `uniformContinuous_ofMul`

English:
theorem uniformContinuous_ofMul
  statement: UniformContinuous (ofMul : α -> Additive α)
  proof: uniformContinuous_id

@[fun_prop]

中文:
定理 uniformContinuous_ofMul
  结论: 一致连续 (ofMul : α -> 加性 α)
  证明: uniformContinuous_id

@[fun_prop]

Depends on / 依赖: uniformContinuous_id
-/
theorem uniformContinuous_ofMul : UniformContinuous (ofMul : α -> Additive α) :=
  uniformContinuous_id

@[fun_prop]
/--
theorem `uniformContinuous_toMul` / 定理 `uniformContinuous_toMul`

English:
theorem uniformContinuous_toMul
  statement: UniformContinuous (toMul : Additive α -> α)
  proof: uniformContinuous_id

@[fun_prop]

中文:
定理 uniformContinuous_toMul
  结论: 一致连续 (toMul : 加性 α -> α)
  证明: uniformContinuous_id

@[fun_prop]

Depends on / 依赖: uniformContinuous_id
-/
theorem uniformContinuous_toMul : UniformContinuous (toMul : Additive α -> α) :=
  uniformContinuous_id

@[fun_prop]
/--
theorem `uniformContinuous_ofAdd` / 定理 `uniformContinuous_ofAdd`

English:
theorem uniformContinuous_ofAdd
  statement: UniformContinuous (ofAdd : α -> Multiplicative α)
  proof: uniformContinuous_id

@[fun_prop]

中文:
定理 uniformContinuous_ofAdd
  结论: 一致连续 (ofAdd : α -> Multiplicative α)
  证明: uniformContinuous_id

@[fun_prop]

Depends on / 依赖: uniformContinuous_id
-/
theorem uniformContinuous_ofAdd : UniformContinuous (ofAdd : α -> Multiplicative α) :=
  uniformContinuous_id

@[fun_prop]
/--
theorem `uniformContinuous_toAdd` / 定理 `uniformContinuous_toAdd`

English:
theorem uniformContinuous_toAdd
  statement: UniformContinuous (toAdd : Multiplicative α -> α)
  proof: uniformContinuous_id

中文:
定理 uniformContinuous_toAdd
  结论: 一致连续 (toAdd : Multiplicative α -> α)
  证明: uniformContinuous_id

Depends on / 依赖: uniformContinuous_id
-/
theorem uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α -> α) :=
  uniformContinuous_id

/--
theorem `uniformity_additive` / 定理 `uniformity_additive`

English:
theorem uniformity_additive
  statement: 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul)
  proof: rfl

中文:
定理 uniformity_additive
  结论: 𝓤 (加性 α) = (𝓤 α).map (积类型.map ofMul ofMul)
  证明: rfl
-/
theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) := rfl

/--
theorem `uniformity_multiplicative` / 定理 `uniformity_multiplicative`

English:
theorem uniformity_multiplicative
  statement: 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd)
  proof: rfl

中文:
定理 uniformity_multiplicative
  结论: 𝓤 (Multiplicative α) = (𝓤 α).map (积类型.map ofAdd ofAdd)
  证明: rfl
-/
theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) := rfl

end

/--
Instance `instUniformSpaceSubtype` / 实例 `instUniformSpaceSubtype`

English:
instance instUniformSpaceSubtype
  signature: {p : α -> Prop} [t : UniformSpace α]
  body: UniformSpace.comap Subtype.val t

中文:
实例 instUniformSpaceSubtype
  签名: {p : α -> 命题} [t : 一致空间 α]
  定义体: UniformSpace.comap Subtype.val t

Depends on / 依赖: Subtype, Subtype.val, UniformSpace, UniformSpace.comap
-/
instance instUniformSpaceSubtype {p : α -> Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

/--
theorem `uniformity_subtype` / 定理 `uniformity_subtype`

English:
theorem uniformity_subtype
  given: {p : α -> Prop} [UniformSpace α]
  proof: rfl

中文:
定理 uniformity_subtype
  条件: {p : α -> 命题} [一致空间 α]
  证明: rfl
-/
theorem uniformity_subtype {p : α -> Prop} [UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl

/--
theorem `uniformity_setCoe` / 定理 `uniformity_setCoe`

English:
theorem uniformity_setCoe
  given: {s : Set α} [UniformSpace α]
  proof: rfl

中文:
定理 uniformity_setCoe
  条件: {s : 集合 α} [一致空间 α]
  证明: rfl
-/
theorem uniformity_setCoe {s : Set α} [UniformSpace α] :
    𝓤 s = comap (Prod.map ((↑) : s -> α) ((↑) : s -> α)) (𝓤 α) :=
  rfl

/--
theorem `map_uniformity_set_coe` / 定理 `map_uniformity_set_coe`

English:
theorem map_uniformity_set_coe
  given: {s : Set α} [UniformSpace α]
  proof: by
  rw [uniformity_setCoe]; rw [map_comap]; rw [range_prodMap]; rw [Subtype.range_val]

@[fun_prop]

中文:
定理 map_uniformity_set_coe
  条件: {s : 集合 α} [一致空间 α]
  证明: by
  rw [uniformity_setCoe]; rw [map_comap]; rw [range_prodMap]; rw [Subtype.range_val]

@[fun_prop]

Depends on / 依赖: Subtype, Subtype.range_val, map_comap, range_prodMap, range_val, uniformity_setCoe
-/
theorem map_uniformity_set_coe {s : Set α} [UniformSpace α] :
    map (Prod.map (↑) (↑)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s) := by
  rw [uniformity_setCoe]; rw [map_comap]; rw [range_prodMap]; rw [Subtype.range_val]

@[fun_prop]
/--
theorem `uniformContinuous_subtype_val` / 定理 `uniformContinuous_subtype_val`

English:
theorem uniformContinuous_subtype_val
  given: {p : α -> Prop} [UniformSpace α]
  proof: uniformContinuous_comap

@[fun_prop]

中文:
定理 uniformContinuous_subtype_val
  条件: {p : α -> 命题} [一致空间 α]
  证明: uniformContinuous_comap

@[fun_prop]

Depends on / 依赖: uniformContinuous_comap
-/
theorem uniformContinuous_subtype_val {p : α -> Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } -> α) :=
  uniformContinuous_comap

@[fun_prop]
/--
theorem `UniformContinuous.subtype_mk` / 定理 `UniformContinuous.subtype_mk`

English:
theorem UniformContinuous.subtype_mk
  statement: {p : α -> Prop} [UniformSpace α] [UniformSpace β] {f : β -> α}
  proof: uniformContinuous_comap' hf

中文:
定理 一致连续.subtype_mk
  结论: {p : α -> 命题} [一致空间 α] [一致空间 β] {f : β -> α}
  证明: uniformContinuous_comap' hf

Depends on / 依赖: uniformContinuous_comap
-/
theorem UniformContinuous.subtype_mk {p : α -> Prop} [UniformSpace α] [UniformSpace β] {f : β -> α}
    (hf : UniformContinuous f) (h : forall x, p (f x)) :
    UniformContinuous (fun x => ⟨f x, h x⟩ : β -> Subtype p) :=
  uniformContinuous_comap' hf

/--
theorem `UniformContinuous.subtype_map` / 定理 `UniformContinuous.subtype_map`

English:
theorem UniformContinuous.subtype_map
  statement: [UniformSpace α] [UniformSpace β] {p : α -> Prop}
  proof: (hf.comp uniformContinuous_subtype_val).subtype_mk _

中文:
定理 一致连续.subtype_map
  结论: [一致空间 α] [一致空间 β] {p : α -> 命题}
  证明: (hf.comp uniformContinuous_subtype_val).subtype_mk _

Depends on / 依赖: hf.comp, subtype_mk, uniformContinuous_subtype_val
-/
theorem UniformContinuous.subtype_map [UniformSpace α] [UniformSpace β] {p : α -> Prop}
    {q : β -> Prop} {f : α -> β} (hf : UniformContinuous f) (h : forall x, p x -> q (f x)) :
    UniformContinuous (Subtype.map f h) :=
  (hf.comp uniformContinuous_subtype_val).subtype_mk _

/--
theorem `uniformContinuousOn_iff_restrict` / 定理 `uniformContinuousOn_iff_restrict`

English:
theorem uniformContinuousOn_iff_restrict
  given: [UniformSpace α] [UniformSpace β] {f : α -> β} {s : Set α}
  proof: by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe]; rw [tendsto_map'_iff]; rfl

alias ⟨UniformContinuousOn.restrict, UniformContinuousOn.of_restrict⟩ :=
  uniformContinuousOn_iff_restrict

中文:
定理 uniformContinuousOn_iff_restrict
  条件: [一致空间 α] [一致空间 β] {f : α -> β} {s : 集合 α}
  证明: by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe]; rw [tendsto_map'_iff]; rfl

alias ⟨UniformContinuousOn.restrict, UniformContinuousOn.of_restrict⟩ :=
  uniformContinuousOn_iff_restrict

Depends on / 依赖: UniformContinuous, UniformContinuousOn, _iff, map_uniformity_set_coe, tendsto_map
-/
theorem uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α -> β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.domRestrict f) := by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe]; rw [tendsto_map'_iff]; rfl

alias ⟨UniformContinuousOn.restrict, UniformContinuousOn.of_restrict⟩ :=
  uniformContinuousOn_iff_restrict

/--
theorem `tendsto_of_uniformContinuous_subtype` / 定理 `tendsto_of_uniformContinuous_subtype`

English:
theorem tendsto_of_uniformContinuous_subtype
  statement: [UniformSpace α] [UniformSpace β] {f : α -> β}
  proof: by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ (· in s) a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt

@[fun_prop]

中文:
定理 tendsto_of_uniformContinuous_subtype
  结论: [一致空间 α] [一致空间 β] {f : α -> β}
  证明: by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ (· in s) a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt

@[fun_prop]

Depends on / 依赖: continuous, continuousAt, hf.continuous.continuousAt, map_nhds_subtype_coe_eq_nhds, mem_of_mem_nhds, tendsto_map
-/
theorem tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f : α -> β}
    {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha : s in 𝓝 a) :
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ (· in s) a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt

@[fun_prop]
/--
theorem `UniformContinuousOn.continuousOn` / 定理 `UniformContinuousOn.continuousOn`

English:
theorem UniformContinuousOn.continuousOn
  statement: [UniformSpace α] [UniformSpace β] {f : α -> β} {s : Set α}
  proof: by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_domRestrict]
  exact h.continuous

中文:
定理 UniformContinuousOn.continuousOn
  结论: [一致空间 α] [一致空间 β] {f : α -> β} {s : 集合 α}
  证明: by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_domRestrict]
  exact h.continuous

Depends on / 依赖: continuous, continuousOn_iff_continuous_domRestrict, h.continuous, uniformContinuousOn_iff_restrict
-/
theorem UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α -> β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_domRestrict]
  exact h.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: α] [(𝓤 α).IsCountablyGenerated] (s
  body: Filter.comap.isCountablyGenerated _ _

@[to_additive]

中文:
实例 [一致空间
  签名: α] [(𝓤 α).是余untablyGenerated] (s
  定义体: Filter.comap.isCountablyGenerated _ _

@[to_additive]

Depends on / 依赖: Filter, Filter.comap.isCountablyGenerated, isCountablyGenerated
-/
instance [UniformSpace α] [(𝓤 α).IsCountablyGenerated] (s : Set α) : (𝓤 s).IsCountablyGenerated :=
  Filter.comap.isCountablyGenerated _ _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: α] : UniformSpace αᵐᵒᵖ
  body: UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]

中文:
实例 [一致空间
  签名: α] : 一致空间 αᵐᵒᵖ
  定义体: UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.unop, UniformSpace, UniformSpace.comap
-/
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]
/--
theorem `uniformity_mulOpposite` / 定理 `uniformity_mulOpposite`

English:
theorem uniformity_mulOpposite
  given: [UniformSpace α]
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 uniformity_mulOpposite
  条件: [一致空间 α]
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem uniformity_mulOpposite [UniformSpace α] :
    𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_uniformity_mulOpposite` / 定理 `comap_uniformity_mulOpposite`

English:
theorem comap_uniformity_mulOpposite
  given: [UniformSpace α]
  proof: by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using! comap_id

中文:
定理 comap_uniformity_mulOpposite
  条件: [一致空间 α]
  证明: by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using! comap_id

Depends on / 依赖: comap_comap, comap_id, uniformity_mulOpposite
-/
theorem comap_uniformity_mulOpposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using! comap_id

namespace MulOpposite

@[to_additive (attr := fun_prop)]
/--
theorem `uniformContinuous_unop` / 定理 `uniformContinuous_unop`

English:
theorem uniformContinuous_unop
  given: [UniformSpace α]
  statement: UniformContinuous (unop : αᵐᵒᵖ -> α)
  proof: uniformContinuous_comap

@[to_additive (attr := fun_prop)]

中文:
定理 uniformContinuous_unop
  条件: [一致空间 α]
  结论: 一致连续 (unop : αᵐᵒᵖ -> α)
  证明: uniformContinuous_comap

@[to_additive (attr := fun_prop)]

Depends on / 依赖: uniformContinuous_comap
-/
theorem uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ -> α) :=
  uniformContinuous_comap

@[to_additive (attr := fun_prop)]
/--
theorem `uniformContinuous_op` / 定理 `uniformContinuous_op`

English:
theorem uniformContinuous_op
  given: [UniformSpace α]
  statement: UniformContinuous (op : α -> αᵐᵒᵖ)
  proof: uniformContinuous_comap' uniformContinuous_id

中文:
定理 uniformContinuous_op
  条件: [一致空间 α]
  结论: 一致连续 (op : α -> αᵐᵒᵖ)
  证明: uniformContinuous_comap' uniformContinuous_id

Depends on / 依赖: uniformContinuous_comap, uniformContinuous_id
-/
theorem uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α -> αᵐᵒᵖ) :=
  uniformContinuous_comap' uniformContinuous_id

end MulOpposite

section Prod

open UniformSpace

/--
Instance `instUniformSpaceProd` / 实例 `instUniformSpaceProd`

English:
instance instUniformSpaceProd
  signature: [u₁ : UniformSpace α] [u₂ : UniformSpace β]
  body: u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

中文:
实例 instUniformSpaceProd
  签名: [u₁ : 一致空间 α] [u₂ : 一致空间 β]
  定义体: u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

Depends on / 依赖: Prod.fst, Prod.snd
-/
instance instUniformSpaceProd [u₁ : UniformSpace α] [u₂ : UniformSpace β] : UniformSpace (α × β) :=
  u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

-- check the above produces no diamond for `simp` and typeclass search
example [UniformSpace α] [UniformSpace β] :
    (instTopologicalSpaceProd : TopologicalSpace (α × β)) = UniformSpace.toTopologicalSpace := by
  with_reducible_and_instances rfl

/--
theorem `uniformity_prod` / 定理 `uniformity_prod`

English:
theorem uniformity_prod
  given: [UniformSpace α] [UniformSpace β]
  proof: rfl

中文:
定理 uniformity_prod
  条件: [一致空间 α] [一致空间 β]
  证明: rfl
-/
theorem uniformity_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓
        (𝓤 β).comap fun p : (α × β) × α × β => (p.1.2, p.2.2) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: α] [IsCountablyGenerated (𝓤 α)]
  body: by
  rw [uniformity_prod]
  infer_instance

中文:
实例 [一致空间
  签名: α] [是余untablyGenerated (𝓤 α)]
  定义体: by
  rw [uniformity_prod]
  infer_instance

Depends on / 依赖: infer_instance, uniformity_prod
-/
instance [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [UniformSpace β] [IsCountablyGenerated (𝓤 β)] : IsCountablyGenerated (𝓤 (α × β)) := by
  rw [uniformity_prod]
  infer_instance

/--
theorem `uniformity_prod_eq_comap_prod` / 定理 `uniformity_prod_eq_comap_prod`

English:
theorem uniformity_prod_eq_comap_prod
  given: [UniformSpace α] [UniformSpace β]
  proof: by
  simp_rw [uniformity_prod, prod_eq_inf, Filter.comap_inf, Filter.comap_comap, Function.comp_def]

中文:
定理 uniformity_prod_eq_comap_prod
  条件: [一致空间 α] [一致空间 β]
  证明: by
  simp_rw [uniformity_prod, prod_eq_inf, Filter.comap_inf, Filter.comap_comap, Function.comp_def]

Depends on / 依赖: Filter, Filter.comap_comap, Filter.comap_inf, Function, Function.comp_def, comap_comap, comap_inf, comp_def, prod_eq_inf, simp_rw, uniformity_prod
-/
theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  simp_rw [uniformity_prod, prod_eq_inf, Filter.comap_inf, Filter.comap_comap, Function.comp_def]

/--
theorem `uniformity_prod_eq_prod` / 定理 `uniformity_prod_eq_prod`

English:
theorem uniformity_prod_eq_prod
  given: [UniformSpace α] [UniformSpace β]
  proof: by
  rw [map_swap4_eq_comap]; rw [uniformity_prod_eq_comap_prod]

中文:
定理 uniformity_prod_eq_prod
  条件: [一致空间 α] [一致空间 β]
  证明: by
  rw [map_swap4_eq_comap]; rw [uniformity_prod_eq_comap_prod]

Depends on / 依赖: map_swap4_eq_comap, uniformity_prod_eq_comap_prod
-/
theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  rw [map_swap4_eq_comap]; rw [uniformity_prod_eq_comap_prod]

/--
theorem `mem_uniformity_of_uniformContinuous_invariant` / 定理 `mem_uniformity_of_uniformContinuous_invariant`

English:
theorem mem_uniformity_of_uniformContinuous_invariant
  statement: [UniformSpace α] [UniformSpace β]
  proof: by
  rw [UniformContinuous]; rw [uniformity_prod_eq_prod]; rw [tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩

中文:
定理 mem_uniformity_of_uniformContinuous_invariant
  结论: [一致空间 α] [一致空间 β]
  证明: by
  rw [UniformContinuous]; rw [uniformity_prod_eq_prod]; rw [tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩

Depends on / 依赖: UniformContinuous, _iff, mem_map, mem_prod_iff, refl_mem_uniformity, tendsto_map, uniformity_prod_eq_prod
-/
theorem mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpace β]
    {s : SetRel β β} {f : α -> α -> β} (hf : UniformContinuous fun p : α × α => f p.1 p.2)
    (hs : s in 𝓤 β) : exists u in 𝓤 α, forall a b c, (a, b) in u -> (f a c, f b c) in s := by
  rw [UniformContinuous]; rw [uniformity_prod_eq_prod]; rw [tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩

/--
Definition of `entourageProd` / `entourageProd` 的定义

English:
definition entourageProd
  signature: (u : SetRel α α) (v : SetRel β β)
  body: {((a₁, b₁), (a₂, b₂)) | (a₁, a₂) in u ∧ (b₁, b₂) in v}

中文:
定义 entourageProd
  签名: (u : SetRel α α) (v : SetRel β β)
  定义体: {((a₁, b₁), (a₂, b₂)) | (a₁, a₂) in u ∧ (b₁, b₂) in v}
-/
def entourageProd (u : SetRel α α) (v : SetRel β β) : SetRel (α × β) (α × β) :=
  {((a₁, b₁), (a₂, b₂)) | (a₁, a₂) in u ∧ (b₁, b₂) in v}

/--
theorem `mem_entourageProd` / 定理 `mem_entourageProd`

English:
theorem mem_entourageProd
  given: {u : SetRel α α} {v : SetRel β β} {p : (α × β) × α × β}
  proof: Iff.rfl

中文:
定理 mem_entourageProd
  条件: {u : SetRel α α} {v : SetRel β β} {p : (α × β) × α × β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_entourageProd {u : SetRel α α} {v : SetRel β β} {p : (α × β) × α × β} :
    p in entourageProd u v ↔ (p.1.1, p.2.1) in u ∧ (p.1.2, p.2.2) in v := Iff.rfl

/--
theorem `entourageProd_mem_uniformity` / 定理 `entourageProd_mem_uniformity`

English:
theorem entourageProd_mem_uniformity
  statement: [t₁ : UniformSpace α] [t₂ : UniformSpace β] {u : SetRel α α}
  proof: by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap hu) (preimage_mem_comap hv)

中文:
定理 entourageProd_mem_uniformity
  结论: [t₁ : 一致空间 α] [t₂ : 一致空间 β] {u : SetRel α α}
  证明: by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap hu) (preimage_mem_comap hv)

Depends on / 依赖: inter_mem_inf, preimage_mem_comap, uniformity_prod
-/
theorem entourageProd_mem_uniformity [t₁ : UniformSpace α] [t₂ : UniformSpace β] {u : SetRel α α}
    {v : SetRel β β} (hu : u in 𝓤 α) (hv : v in 𝓤 β) :
    entourageProd u v in 𝓤 (α × β) := by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap hu) (preimage_mem_comap hv)

/--
theorem `ball_entourageProd` / 定理 `ball_entourageProd`

English:
theorem ball_entourageProd
  given: (u : SetRel α α) (v : SetRel β β) (x : α × β)
  proof: by
  ext p; simp only [ball, entourageProd, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_preimage]

中文:
定理 ball_entourageProd
  条件: (u : SetRel α α) (v : SetRel β β) (x : α × β)
  证明: by
  ext p; simp only [ball, entourageProd, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_preimage]

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, entourageProd, mem_ofPred_eq, mem_preimage, mem_prod
-/
theorem ball_entourageProd (u : SetRel α α) (v : SetRel β β) (x : α × β) :
    ball x (entourageProd u v) = ball x.1 u ×ˢ ball x.2 v := by
  ext p; simp only [ball, entourageProd, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_preimage]

/--
Instance `IsSymm_entourageProd` / 实例 `IsSymm_entourageProd`

English:
instance IsSymm_entourageProd
  signature: {u : SetRel α α} {v : SetRel β β} [u.IsSymm] [v.IsSymm]
  body: .imp u.symm v.symm

@[simp]

中文:
实例 IsSymm_entourageProd
  签名: {u : SetRel α α} {v : SetRel β β} [u.是Symm] [v.是Symm]
  定义体: .imp u.symm v.symm

@[simp]

Depends on / 依赖: u.symm, v.symm
-/
instance IsSymm_entourageProd {u : SetRel α α} {v : SetRel β β} [u.IsSymm] [v.IsSymm] :
    (entourageProd u v).IsSymm where
  symm _ _ := .imp u.symm v.symm

@[simp]
/--
theorem `inv_entourageProd` / 定理 `inv_entourageProd`

English:
theorem inv_entourageProd
  given: (u : SetRel α α) (v : SetRel β β)
  proof: rfl

@[simp]

中文:
定理 inv_entourageProd
  条件: (u : SetRel α α) (v : SetRel β β)
  证明: rfl

@[simp]
-/
theorem inv_entourageProd (u : SetRel α α) (v : SetRel β β) :
    (entourageProd u v).inv = entourageProd u.inv v.inv :=
  rfl

@[simp]
/--
theorem `image_entourageProd_prod` / 定理 `image_entourageProd_prod`

English:
theorem image_entourageProd_prod
  given: (u : SetRel α α) (v : SetRel β β) (s : Set α) (t : Set β)
  proof: by
  ext
  simp only [mem_entourageProd, SetRel.mem_image, Set.mem_prod, Prod.exists]
  grind

@[simp]

中文:
定理 image_entourageProd_prod
  条件: (u : SetRel α α) (v : SetRel β β) (s : 集合 α) (t : 集合 β)
  证明: by
  ext
  simp only [mem_entourageProd, SetRel.mem_image, Set.mem_prod, Prod.exists]
  grind

@[simp]

Depends on / 依赖: Prod.exists, Set.mem_prod, SetRel, SetRel.mem_image, mem_entourageProd, mem_image, mem_prod
-/
theorem image_entourageProd_prod (u : SetRel α α) (v : SetRel β β) (s : Set α) (t : Set β) :
    (entourageProd u v).image (s ×ˢ t) = u.image s ×ˢ v.image t := by
  ext
  simp only [mem_entourageProd, SetRel.mem_image, Set.mem_prod, Prod.exists]
  grind

@[simp]
/--
theorem `preimage_entourageProd_prod` / 定理 `preimage_entourageProd_prod`

English:
theorem preimage_entourageProd_prod
  given: (u : SetRel α α) (v : SetRel β β) (s : Set α) (t : Set β)
  proof: image_entourageProd_prod u.inv v.inv s t

中文:
定理 preimage_entourageProd_prod
  条件: (u : SetRel α α) (v : SetRel β β) (s : 集合 α) (t : 集合 β)
  证明: image_entourageProd_prod u.inv v.inv s t

Depends on / 依赖: image_entourageProd_prod, u.inv, v.inv
-/
theorem preimage_entourageProd_prod (u : SetRel α α) (v : SetRel β β) (s : Set α) (t : Set β) :
    (entourageProd u v).preimage (s ×ˢ t) = u.preimage s ×ˢ v.preimage t :=
  image_entourageProd_prod u.inv v.inv s t

/--
theorem `Filter.HasBasis.uniformity_prod` / 定理 `Filter.HasBasis.uniformity_prod`

English:
theorem Filter.HasBasis.uniformity_prod
  statement: {ιa ιb : Type*} [UniformSpace α] [UniformSpace β]
  proof: (ha.comap _).inf (hb.comap _)

中文:
定理 滤子.有基.uniformity_prod
  结论: {ιa ιb : 类型} [一致空间 α] [一致空间 β]
  证明: (ha.comap _).inf (hb.comap _)

Depends on / 依赖: ha.comap, hb.comap
-/
theorem Filter.HasBasis.uniformity_prod {ιa ιb : Type*} [UniformSpace α] [UniformSpace β]
    {pa : ιa -> Prop} {pb : ιb -> Prop} {sa : ιa -> SetRel α α} {sb : ιb -> SetRel β β}
    (ha : (𝓤 α).HasBasis pa sa) (hb : (𝓤 β).HasBasis pb sb) :
    (𝓤 (α × β)).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2)
    (fun i => entourageProd (sa i.1) (sb i.2)) :=
  (ha.comap _).inf (hb.comap _)

/--
theorem `entourageProd_subset` / 定理 `entourageProd_subset`

English:
theorem entourageProd_subset
  statement: [UniformSpace α] [UniformSpace β]
  proof: by
  rcases (((𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets).mem_iff' s).1 h with ⟨w, hw⟩
  use w.1, hw.1.1, w.2, hw.1.2, hw.2

中文:
定理 entourageProd_subset
  结论: [一致空间 α] [一致空间 β]
  证明: by
  rcases (((𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets).mem_iff' s).1 h with ⟨w, hw⟩
  use w.1, hw.1.1, w.2, hw.1.2, hw.2

Depends on / 依赖: basis_sets, basis_sets.uniformity_prod, mem_iff, uniformity_prod
-/
theorem entourageProd_subset [UniformSpace α] [UniformSpace β]
    {s : Set ((α × β) × α × β)} (h : s in 𝓤 (α × β)) :
    exists u in 𝓤 α, exists v in 𝓤 β, entourageProd u v subseteq s := by
  rcases (((𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets).mem_iff' s).1 h with ⟨w, hw⟩
  use w.1, hw.1.1, w.2, hw.1.2, hw.2

/--
theorem `tendsto_prod_uniformity_fst` / 定理 `tendsto_prod_uniformity_fst`

English:
theorem tendsto_prod_uniformity_fst
  given: [UniformSpace α] [UniformSpace β]
  proof: le_trans (map_mono inf_le_left) map_comap_le

中文:
定理 tendsto_prod_uniformity_fst
  条件: [一致空间 α] [一致空间 β]
  证明: le_trans (map_mono inf_le_left) map_comap_le

Depends on / 依赖: inf_le_left, le_trans, map_comap_le, map_mono
-/
theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le

/--
theorem `tendsto_prod_uniformity_snd` / 定理 `tendsto_prod_uniformity_snd`

English:
theorem tendsto_prod_uniformity_snd
  given: [UniformSpace α] [UniformSpace β]
  proof: le_trans (map_mono inf_le_right) map_comap_le

@[fun_prop]

中文:
定理 tendsto_prod_uniformity_snd
  条件: [一致空间 α] [一致空间 β]
  证明: le_trans (map_mono inf_le_right) map_comap_le

@[fun_prop]

Depends on / 依赖: inf_le_right, le_trans, map_comap_le, map_mono
-/
theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le

@[fun_prop]
/--
theorem `uniformContinuous_fst` / 定理 `uniformContinuous_fst`

English:
theorem uniformContinuous_fst
  given: [UniformSpace α] [UniformSpace β]
  proof: tendsto_prod_uniformity_fst

@[fun_prop]

中文:
定理 uniformContinuous_fst
  条件: [一致空间 α] [一致空间 β]
  证明: tendsto_prod_uniformity_fst

@[fun_prop]

Depends on / 依赖: tendsto_prod_uniformity_fst
-/
theorem uniformContinuous_fst [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst

@[fun_prop]
/--
theorem `uniformContinuous_snd` / 定理 `uniformContinuous_snd`

English:
theorem uniformContinuous_snd
  given: [UniformSpace α] [UniformSpace β]
  proof: tendsto_prod_uniformity_snd

中文:
定理 uniformContinuous_snd
  条件: [一致空间 α] [一致空间 β]
  证明: tendsto_prod_uniformity_snd

Depends on / 依赖: tendsto_prod_uniformity_snd
-/
theorem uniformContinuous_snd [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

@[fun_prop]
/--
theorem `UniformContinuous.prodMk` / 定理 `UniformContinuous.prodMk`

English:
theorem UniformContinuous.prodMk
  statement: {f₁ : α -> β} {f₂ : α -> γ} (h₁ : UniformContinuous f₁)
  proof: by
  rw [UniformContinuous]; rw [uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

中文:
定理 一致连续.prodMk
  结论: {f₁ : α -> β} {f₂ : α -> γ} (h₁ : 一致连续 f₁)
  证明: by
  rw [UniformContinuous]; rw [uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

Depends on / 依赖: UniformContinuous, tendsto_comap_iff, tendsto_inf, uniformity_prod
-/
theorem UniformContinuous.prodMk {f₁ : α -> β} {f₂ : α -> γ} (h₁ : UniformContinuous f₁)
    (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous]; rw [uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

/--
theorem `UniformContinuous.prodMk_left` / 定理 `UniformContinuous.prodMk_left`

English:
theorem UniformContinuous.prodMk_left
  given: {f : α × β -> γ} (h : UniformContinuous f) (b)
  proof: h.comp (uniformContinuous_id.prodMk uniformContinuous_const)

中文:
定理 一致连续.prodMk_left
  条件: {f : α × β -> γ} (h : 一致连续 f) (b)
  证明: h.comp (uniformContinuous_id.prodMk uniformContinuous_const)

Depends on / 依赖: h.comp, prodMk, uniformContinuous_const, uniformContinuous_id, uniformContinuous_id.prodMk
-/
theorem UniformContinuous.prodMk_left {f : α × β -> γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniformContinuous_id.prodMk uniformContinuous_const)

/--
theorem `UniformContinuous.prodMk_right` / 定理 `UniformContinuous.prodMk_right`

English:
theorem UniformContinuous.prodMk_right
  given: {f : α × β -> γ} (h : UniformContinuous f) (a)
  proof: h.comp (uniformContinuous_const.prodMk uniformContinuous_id)

@[fun_prop]

中文:
定理 一致连续.prodMk_right
  条件: {f : α × β -> γ} (h : 一致连续 f) (a)
  证明: h.comp (uniformContinuous_const.prodMk uniformContinuous_id)

@[fun_prop]

Depends on / 依赖: h.comp, prodMk, uniformContinuous_const, uniformContinuous_const.prodMk, uniformContinuous_id
-/
theorem UniformContinuous.prodMk_right {f : α × β -> γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniformContinuous_const.prodMk uniformContinuous_id)

@[fun_prop]
/--
theorem `UniformContinuous.prodMap` / 定理 `UniformContinuous.prodMap`

English:
theorem UniformContinuous.prodMap
  statement: [UniformSpace δ] {f : α -> γ} {g : β -> δ}
  proof: (hf.comp uniformContinuous_fst).prodMk (hg.comp uniformContinuous_snd)

@[fun_prop]

中文:
定理 一致连续.prodMap
  结论: [一致空间 δ] {f : α -> γ} {g : β -> δ}
  证明: (hf.comp uniformContinuous_fst).prodMk (hg.comp uniformContinuous_snd)

@[fun_prop]

Depends on / 依赖: hf.comp, hg.comp, prodMk, uniformContinuous_fst, uniformContinuous_snd
-/
theorem UniformContinuous.prodMap [UniformSpace δ] {f : α -> γ} {g : β -> δ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniformContinuous_fst).prodMk (hg.comp uniformContinuous_snd)

@[fun_prop]
/--
lemma `uniformContinuous_swap` / 引理 `uniformContinuous_swap`

English:
lemma uniformContinuous_swap
  proof: uniformContinuous_snd.prodMk uniformContinuous_fst

中文:
引理 uniformContinuous_swap
  证明: uniformContinuous_snd.prodMk uniformContinuous_fst

Depends on / 依赖: prodMk, uniformContinuous_fst, uniformContinuous_snd, uniformContinuous_snd.prodMk
-/
lemma uniformContinuous_swap :
    UniformContinuous (Prod.swap : α × β -> β × α) :=
  uniformContinuous_snd.prodMk uniformContinuous_fst

/--
theorem `toTopologicalSpace_prod` / 定理 `toTopologicalSpace_prod`

English:
theorem toTopologicalSpace_prod
  given: {α} {β} [u : UniformSpace α] [v : UniformSpace β]
  proof: rfl

中文:
定理 toTopologicalSpace_prod
  条件: {α} {β} [u : 一致空间 α] [v : 一致空间 β]
  证明: rfl
-/
theorem toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) instUniformSpaceProd =
      @instTopologicalSpaceProd α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl

/--
theorem `uniformContinuous_inf_dom_left₂` / 定理 `uniformContinuous_inf_dom_left₂`

English:
theorem uniformContinuous_inf_dom_left₂
  statement: {α β γ} {f : α -> β -> γ} {ua1 ua2 : UniformSpace α}
  proof: ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _

中文:
定理 uniformContinuous_inf_dom_left₂
  结论: {α β γ} {f : α -> β -> γ} {ua1 ua2 : 一致空间 α}
  证明: ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _

Depends on / 依赖: UniformContinuous
-/
theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α -> β -> γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1; haveI := ub1; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/--
theorem `uniformContinuous_inf_dom_right₂` / 定理 `uniformContinuous_inf_dom_right₂`

English:
theorem uniformContinuous_inf_dom_right₂
  statement: {α β γ} {f : α -> β -> γ} {ua1 ua2 : UniformSpace α}
  proof: ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right 

中文:
定理 uniformContinuous_inf_dom_right₂
  结论: {α β γ} {f : α -> β -> γ} {ua1 ua2 : 一致空间 α}
  证明: ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right 

Depends on / 依赖: UniformContinuous
-/
theorem uniformContinuous_inf_dom_right₂ {α β γ} {f : α -> β -> γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua2; haveI := ub2; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right _ _ id ub1 ub2 ub2 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/--
theorem `uniformContinuous_sInf_dom₂` / 定理 `uniformContinuous_sInf_dom₂`

English:
theorem uniformContinuous_sInf_dom₂
  statement: {α β γ} {f : α -> β -> γ} {uas : Set (UniformSpace α)}
  proof: sInf uas; haveI := sInf ubs
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_

中文:
定理 uniformContinuous_sInf_dom₂
  结论: {α β γ} {f : α -> β -> γ} {uas : 集合 (一致空间 α)}
  证明: sInf uas; haveI := sInf ubs
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_
-/
theorem uniformContinuous_sInf_dom₂ {α β γ} {f : α -> β -> γ} {uas : Set (UniformSpace α)}
    {ubs : Set (UniformSpace β)} {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ}
    (ha : ua in uas) (hb : ub in ubs) (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := sInf uas; haveI := sInf ubs
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_cont_id := @UniformContinuous.prodMap _ _ _ _ (sInf uas) (sInf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id

end Prod

section

open UniformSpace Function

variable {δ' : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
  [UniformSpace δ']
local notation f " ∘₂ " g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
@[fun_prop]
/--
Definition of `UniformContinuous₂` / `UniformContinuous₂` 的定义

English:
definition UniformContinuous₂
  signature: (f : α -> β -> γ)
  body: UniformContinuous (uncurry f)

中文:
定义 UniformContinuous₂
  签名: (f : α -> β -> γ)
  定义体: UniformContinuous (uncurry f)

Depends on / 依赖: UniformContinuous, uncurry
-/
def UniformContinuous₂ (f : α -> β -> γ) :=
  UniformContinuous (uncurry f)

/--
theorem `uniformContinuous₂_def` / 定理 `uniformContinuous₂_def`

English:
theorem uniformContinuous₂_def
  given: (f : α -> β -> γ)
  proof: Iff.rfl

中文:
定理 uniformContinuous₂_def
  条件: (f : α -> β -> γ)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem uniformContinuous₂_def (f : α -> β -> γ) :
    UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl

/--
theorem `UniformContinuous₂.uniformContinuous` / 定理 `UniformContinuous₂.uniformContinuous`

English:
theorem UniformContinuous₂.uniformContinuous
  given: {f : α -> β -> γ} (h : UniformContinuous₂ f)
  proof: h

中文:
定理 UniformContinuous₂.uniformContinuous
  条件: {f : α -> β -> γ} (h : UniformContinuous₂ f)
  证明: h
-/
theorem UniformContinuous₂.uniformContinuous {f : α -> β -> γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h

/--
theorem `uniformContinuous₂_curry` / 定理 `uniformContinuous₂_curry`

English:
theorem uniformContinuous₂_curry
  given: (f : α × β -> γ)
  proof: by
  rw [UniformContinuous₂]; rw [uncurry_curry]

@[fun_prop]

中文:
定理 uniformContinuous₂_curry
  条件: (f : α × β -> γ)
  证明: by
  rw [UniformContinuous₂]; rw [uncurry_curry]

@[fun_prop]

Depends on / 依赖: uncurry_curry
-/
theorem uniformContinuous₂_curry (f : α × β -> γ) :
    UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂]; rw [uncurry_curry]

@[fun_prop]
/--
theorem `UniformContinuous₂.comp` / 定理 `UniformContinuous₂.comp`

English:
theorem UniformContinuous₂.comp
  statement: {f : α -> β -> γ} {g : γ -> δ} (hg : UniformContinuous g)
  proof: hg.comp hf

@[fun_prop]

中文:
定理 UniformContinuous₂.comp
  结论: {f : α -> β -> γ} {g : γ -> δ} (hg : 一致连续 g)
  证明: hg.comp hf

@[fun_prop]

Depends on / 依赖: hg.comp
-/
theorem UniformContinuous₂.comp {f : α -> β -> γ} {g : γ -> δ} (hg : UniformContinuous g)
    (hf : UniformContinuous₂ f) : UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf

@[fun_prop]
/--
theorem `UniformContinuous₂.bicompl` / 定理 `UniformContinuous₂.bicompl`

English:
theorem UniformContinuous₂.bicompl
  statement: {f : α -> β -> γ} {ga : δ -> α} {gb : δ' -> β}
  proof: hf.uniformContinuous.comp (hga.prodMap hgb)

中文:
定理 UniformContinuous₂.bicompl
  结论: {f : α -> β -> γ} {ga : δ -> α} {gb : δ' -> β}
  证明: hf.uniformContinuous.comp (hga.prodMap hgb)

Depends on / 依赖: hf.uniformContinuous.comp, hga.prodMap, prodMap, uniformContinuous
-/
theorem UniformContinuous₂.bicompl {f : α -> β -> γ} {ga : δ -> α} {gb : δ' -> β}
    (hf : UniformContinuous₂ f) (hga : UniformContinuous ga) (hgb : UniformContinuous gb) :
    UniformContinuous₂ (bicompl f ga gb) :=
  hf.uniformContinuous.comp (hga.prodMap hgb)

end

/--
theorem `toTopologicalSpace_subtype` / 定理 `toTopologicalSpace_subtype`

English:
theorem toTopologicalSpace_subtype
  given: [u : UniformSpace α] {p : α -> Prop}
  proof: rfl

中文:
定理 toTopologicalSpace_subtype
  条件: [u : 一致空间 α] {p : α -> 命题}
  证明: rfl
-/
theorem toTopologicalSpace_subtype [u : UniformSpace α] {p : α -> Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) instUniformSpaceSubtype =
      @instTopologicalSpaceSubtype α p u.toTopologicalSpace :=
  rfl

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

-- Obsolete auxiliary definitions and lemmas

/--
Instance `Sum.instUniformSpace` / 实例 `Sum.instUniformSpace`

English:
instance Sum.instUniformSpace
  signature: : UniformSpace (α oplus β) where
  body: map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun _ hs => ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
  comp := fun s hs => by
    rcases comp_mem_uniformity_sets hs.1 with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets hs.

中文:
实例 和.instUniformSpace
  签名: : 一致空间 (α oplus β) where
  定义体: map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun _ hs => ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
  comp := fun s hs => by
    rcases comp_mem_uniformity_sets hs.1 with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets hs.
-/
instance Sum.instUniformSpace : UniformSpace (α oplus β) where
  uniformity := map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun _ hs => ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
  comp := fun s hs => by
    rcases comp_mem_uniformity_sets hs.1 with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets hs.2 with ⟨tβ, htβ, Htβ⟩
    filter_upwards [mem_lift' (union_mem_sup (image_mem_map htα) (image_mem_map htβ))]
    rintro ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩, ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩
    exacts [@Htα (_, _) ⟨b, hab, hbc⟩, @Htβ (_, _) ⟨b, hab, hbc⟩]
  nhds_eq_comap_uniformity x := by
    ext
    cases x <;> simp [mem_comap', -mem_comap, nhds_inl, nhds_inr, nhds_eq_comap_uniformity,
      Prod.ext_iff]

/--
theorem `union_mem_uniformity_sum` / 定理 `union_mem_uniformity_sum`

English:
theorem union_mem_uniformity_sum
  given: {a : SetRel α α} (ha : a in 𝓤 α) {b : SetRel β β} (hb : b in 𝓤 β)
  proof: union_mem_sup (image_mem_map ha) (image_mem_map hb)

中文:
定理 union_mem_uniformity_sum
  条件: {a : SetRel α α} (ha : a in 𝓤 α) {b : SetRel β β} (hb : b in 𝓤 β)
  证明: union_mem_sup (image_mem_map ha) (image_mem_map hb)

Depends on / 依赖: image_mem_map, union_mem_sup
-/
theorem union_mem_uniformity_sum {a : SetRel α α} (ha : a in 𝓤 α) {b : SetRel β β} (hb : b in 𝓤 β) :
    Prod.map inl inl '' a union Prod.map inr inr '' b in 𝓤 (α oplus β) :=
  union_mem_sup (image_mem_map ha) (image_mem_map hb)

/--
theorem `Sum.uniformity` / 定理 `Sum.uniformity`

English:
theorem Sum.uniformity
  statement: 𝓤 (α oplus β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β)
  proof: rfl

中文:
定理 和.uniformity
  结论: 𝓤 (α oplus β) = map (积类型.map inl inl) (𝓤 α) ⊔ map (积类型.map inr inr) (𝓤 β)
  证明: rfl
-/
theorem Sum.uniformity : 𝓤 (α oplus β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β) :=
  rfl

/--
lemma `uniformContinuous_inl` / 引理 `uniformContinuous_inl`

English:
lemma uniformContinuous_inl
  statement: UniformContinuous (Sum.inl : α -> α oplus β)
  proof: le_sup_left

中文:
引理 uniformContinuous_inl
  结论: 一致连续 (和.inl : α -> α oplus β)
  证明: le_sup_left
-/
@[fun_prop] lemma uniformContinuous_inl : UniformContinuous (Sum.inl : α -> α oplus β) := le_sup_left
/--
lemma `uniformContinuous_inr` / 引理 `uniformContinuous_inr`

English:
lemma uniformContinuous_inr
  statement: UniformContinuous (Sum.inr : β -> α oplus β)
  proof: le_sup_right

中文:
引理 uniformContinuous_inr
  结论: 一致连续 (和.inr : β -> α oplus β)
  证明: le_sup_right
-/
@[fun_prop] lemma uniformContinuous_inr : UniformContinuous (Sum.inr : β -> α oplus β) := le_sup_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCountablyGenerated
  signature: (𝓤 α)] [IsCountablyGenerated (𝓤 β)] :
  body: by
  rw [Sum.uniformity]
  infer_instance

中文:
实例 [是余untablyGenerated
  签名: (𝓤 α)] [是余untablyGenerated (𝓤 β)] :
  定义体: by
  rw [Sum.uniformity]
  infer_instance
-/
instance [IsCountablyGenerated (𝓤 α)] [IsCountablyGenerated (𝓤 β)] :
    IsCountablyGenerated (𝓤 (α oplus β)) := by
  rw [Sum.uniformity]
  infer_instance

end Sum

end Constructions

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `Uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace α]

/--
theorem `tendsto_nhds_right` / 定理 `tendsto_nhds_right`

English:
theorem tendsto_nhds_right
  given: {f : Filter β} {u : β -> α} {a : α}
  proof: by
  rw [nhds_eq_comap_uniformity]; rw [tendsto_comap_iff]; rfl

中文:
定理 tendsto_nhds_right
  条件: {f : 滤子 β} {u : β -> α} {a : α}
  证明: by
  rw [nhds_eq_comap_uniformity]; rw [tendsto_comap_iff]; rfl

Depends on / 依赖: nhds_eq_comap_uniformity, tendsto_comap_iff
-/
theorem tendsto_nhds_right {f : Filter β} {u : β -> α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity]; rw [tendsto_comap_iff]; rfl

/--
theorem `tendsto_nhds_left` / 定理 `tendsto_nhds_left`

English:
theorem tendsto_nhds_left
  given: {f : Filter β} {u : β -> α} {a : α}
  proof: by
  rw [nhds_eq_comap_uniformity']; rw [tendsto_comap_iff]; rfl

中文:
定理 tendsto_nhds_left
  条件: {f : 滤子 β} {u : β -> α} {a : α}
  证明: by
  rw [nhds_eq_comap_uniformity']; rw [tendsto_comap_iff]; rfl

Depends on / 依赖: nhds_eq_comap_uniformity, tendsto_comap_iff
-/
theorem tendsto_nhds_left {f : Filter β} {u : β -> α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity']; rw [tendsto_comap_iff]; rfl

/--
theorem `continuousAt_iff'_right` / 定理 `continuousAt_iff'_right`

English:
theorem continuousAt_iff'_right
  given: [TopologicalSpace β] {f : β -> α} {b : β}
  proof: by
  rw [ContinuousAt]; rw [tendsto_nhds_right]

中文:
定理 continuousAt_iff'_right
  条件: [拓扑空间 β] {f : β -> α} {b : β}
  证明: by
  rw [ContinuousAt]; rw [tendsto_nhds_right]

Depends on / 依赖: ContinuousAt, tendsto_nhds_right
-/
theorem continuousAt_iff'_right [TopologicalSpace β] {f : β -> α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt]; rw [tendsto_nhds_right]

/--
theorem `continuousAt_iff'_left` / 定理 `continuousAt_iff'_left`

English:
theorem continuousAt_iff'_left
  given: [TopologicalSpace β] {f : β -> α} {b : β}
  proof: by
  rw [ContinuousAt]; rw [tendsto_nhds_left]

中文:
定理 continuousAt_iff'_left
  条件: [拓扑空间 β] {f : β -> α} {b : β}
  证明: by
  rw [ContinuousAt]; rw [tendsto_nhds_left]
-/
theorem continuousAt_iff'_left [TopologicalSpace β] {f : β -> α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt]; rw [tendsto_nhds_left]

/--
theorem `continuousAt_iff_prod` / 定理 `continuousAt_iff_prod`

English:
theorem continuousAt_iff_prod
  given: [TopologicalSpace β] {f : β -> α} {b : β}
  proof: ⟨fun H => le_trans (H.prodMap' H) (nhds_le_uniformity _), fun H =>
continuousAt_iff'_left.2 H.comp tendsto_id.prodMk_nhds tendsto_const_nhds⟩

中文:
定理 continuousAt_iff_prod
  条件: [拓扑空间 β] {f : β -> α} {b : β}
  证明: ⟨fun H => le_trans (H.prodMap' H) (nhds_le_uniformity _), fun H =>
continuousAt_iff'_left.2 H.comp tendsto_id.prodMk_nhds tendsto_const_nhds⟩

Depends on / 依赖: H.comp, H.prodMap, _left, continuousAt_iff, le_trans, nhds_le_uniformity, prodMap, prodMk_nhds, tendsto_const_nhds, tendsto_id, tendsto_id.prodMk_nhds
-/
theorem continuousAt_iff_prod [TopologicalSpace β] {f : β -> α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prodMap' H) (nhds_le_uniformity _), fun H =>
continuousAt_iff'_left.2 H.comp tendsto_id.prodMk_nhds tendsto_const_nhds⟩

/--
theorem `continuousWithinAt_iff'_right` / 定理 `continuousWithinAt_iff'_right`

English:
theorem continuousWithinAt_iff'_right
  given: [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β}
  proof: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds_right]

中文:
定理 continuousWithinAt_iff'_right
  条件: [拓扑空间 β] {f : β -> α} {b : β} {s : 集合 β}
  证明: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds_right]

Depends on / 依赖: ContinuousWithinAt, tendsto_nhds_right
-/
theorem continuousWithinAt_iff'_right [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt]; rw [tendsto_nhds_right]

/--
theorem `continuousWithinAt_iff'_left` / 定理 `continuousWithinAt_iff'_left`

English:
theorem continuousWithinAt_iff'_left
  given: [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β}
  proof: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds_left]

中文:
定理 continuousWithinAt_iff'_left
  条件: [拓扑空间 β] {f : β -> α} {b : β} {s : 集合 β}
  证明: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds_left]
-/
theorem continuousWithinAt_iff'_left [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt]; rw [tendsto_nhds_left]

/--
theorem `continuousOn_iff'_right` / 定理 `continuousOn_iff'_right`

English:
theorem continuousOn_iff'_right
  given: [TopologicalSpace β] {f : β -> α} {s : Set β}
  proof: by
  simp [ContinuousOn, continuousWithinAt_iff'_right]

中文:
定理 continuousOn_iff'_right
  条件: [拓扑空间 β] {f : β -> α} {s : 集合 β}
  证明: by
  simp [ContinuousOn, continuousWithinAt_iff'_right]

Depends on / 依赖: ContinuousOn, _right, continuousWithinAt_iff
-/
theorem continuousOn_iff'_right [TopologicalSpace β] {f : β -> α} {s : Set β} :
    ContinuousOn f s ↔ forall b in s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_right]

/--
theorem `continuousOn_iff'_left` / 定理 `continuousOn_iff'_left`

English:
theorem continuousOn_iff'_left
  given: [TopologicalSpace β] {f : β -> α} {s : Set β}
  proof: by
  simp [ContinuousOn, continuousWithinAt_iff'_left]

中文:
定理 continuousOn_iff'_left
  条件: [拓扑空间 β] {f : β -> α} {s : 集合 β}
  证明: by
  simp [ContinuousOn, continuousWithinAt_iff'_left]
-/
theorem continuousOn_iff'_left [TopologicalSpace β] {f : β -> α} {s : Set β} :
    ContinuousOn f s ↔ forall b in s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_left]

/--
theorem `continuous_iff'_right` / 定理 `continuous_iff'_right`

English:
theorem continuous_iff'_right
  given: [TopologicalSpace β] {f : β -> α}
  proof: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_right

中文:
定理 continuous_iff'_right
  条件: [拓扑空间 β] {f : β -> α}
  证明: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_right

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.trans, forall_congr, tendsto_nhds_right
-/
theorem continuous_iff'_right [TopologicalSpace β] {f : β -> α} :
    Continuous f ↔ forall b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_right

/--
theorem `continuous_iff'_left` / 定理 `continuous_iff'_left`

English:
theorem continuous_iff'_left
  given: [TopologicalSpace β] {f : β -> α}
  proof: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_left

中文:
定理 continuous_iff'_left
  条件: [拓扑空间 β] {f : β -> α}
  证明: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_left
-/
theorem continuous_iff'_left [TopologicalSpace β] {f : β -> α} :
    Continuous f ↔ forall b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_left

/--
lemma `exists_is_open_mem_uniformity_of_forall_mem_eq` / 引理 `exists_is_open_mem_uniformity_of_forall_mem_eq`

English:
lemma exists_is_open_mem_uniformity_of_forall_mem_eq
  proof: by
  have A : forall x in s, exists t, IsOpen t ∧ x in t ∧ forall z in t, (f z, g z) in r := by
    intro x hx
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    have A : {z | (f x, f z) in t} in 𝓝 x := (hf x hx).preimage_mem_nhds (mem_nhds_left (f x) ht)
    have B : {z | (g x,

中文:
引理 存在_is_open_mem_uniformity_of_对任意_mem_eq
  证明: by
  have A : forall x in s, exists t, IsOpen t ∧ x in t ∧ forall z in t, (f z, g z) in r := by
    intro x hx
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    have A : {z | (f x, f z) in t} in 𝓝 x := (hf x hx).preimage_mem_nhds (mem_nhds_left (f x) ht)
    have B : {z | (g x,

Depends on / 依赖: IsOpen, _root_, _root_.mem_nhds_iff, comp_symm_mem_uniformity_sets, htsymm, inter_mem, mem_nhds_iff, mem_nhds_left, preimage_mem_nhds, u_open
-/
lemma exists_is_open_mem_uniformity_of_forall_mem_eq
    [TopologicalSpace β] {r : SetRel α α} {s : Set β}
    {f g : β -> α} (hf : forall x in s, ContinuousAt f x) (hg : forall x in s, ContinuousAt g x)
    (hfg : s.EqOn f g) (hr : r in 𝓤 α) :
    exists t, IsOpen t ∧ s subseteq t ∧ forall x in t, (f x, g x) in r := by
  have A : forall x in s, exists t, IsOpen t ∧ x in t ∧ forall z in t, (f z, g z) in r := by
    intro x hx
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    have A : {z | (f x, f z) in t} in 𝓝 x := (hf x hx).preimage_mem_nhds (mem_nhds_left (f x) ht)
    have B : {z | (g x, g z) in t} in 𝓝 x := (hg x hx).preimage_mem_nhds (mem_nhds_left (g x) ht)
    rcases _root_.mem_nhds_iff.1 (inter_mem A B) with ⟨u, hu, u_open, xu⟩
    refine ⟨u, u_open, xu, fun y hy => ?_⟩
    have I1 : (f y, f x) in t := SetRel.symm t (hu hy).1
    have I2 : (g x, g y) in t := (hu hy).2
    rw [hfg hx] at I1
    exact htr (SetRel.prodMk_mem_comp I1 I2)
  choose! t t_open xt ht using A
  refine ⟨⋃ x in s, t x, isOpen_biUnion t_open, fun x hx => mem_biUnion hx (xt x hx), ?_⟩
  rintro x hx
  simp only [mem_iUnion, exists_prop] at hx
  rcases hx with ⟨y, ys, hy⟩
  exact ht y ys x hy

end Uniform

/--
theorem `Filter.Tendsto.congr_uniformity` / 定理 `Filter.Tendsto.congr_uniformity`

English:
theorem Filter.Tendsto.congr_uniformity
  statement: {α β} [UniformSpace β] {f g : α -> β} {l : Filter α} {b : β}
  proof: Uniform.tendsto_nhds_right.2 (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

中文:
定理 滤子.收敛.congr_uniformity
  结论: {α β} [一致空间 β] {f g : α -> β} {l : 滤子 α} {b : β}
  证明: Uniform.tendsto_nhds_right.2 (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

Depends on / 依赖: Uniform, Uniform.tendsto_nhds_right, tendsto_nhds_right, uniformity_trans
-/
theorem Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α -> β} {l : Filter α} {b : β}
    (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto g l (𝓝 b) :=
Uniform.tendsto_nhds_right.2 (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

/--
theorem `Uniform.tendsto_congr` / 定理 `Uniform.tendsto_congr`

English:
theorem Uniform.tendsto_congr
  statement: {α β} [UniformSpace β] {f g : α -> β} {l : Filter α} {b : β}
  proof: ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩

中文:
定理 一致.tendsto_congr
  结论: {α β} [一致空间 β] {f g : α -> β} {l : 滤子 α} {b : β}
  证明: ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩

Depends on / 依赖: congr_uniformity, h.congr_uniformity, hfg.uniformity_symm, uniformity_symm
-/
theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α -> β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩
