/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Separation properties: profinite spaces
-/

public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Profinite

/--
theorem `totallySeparatedSpace_of_t0_of_basis_clopen` / 定理 `totallySeparatedSpace_of_t0_of_basis_clopen`

English:
theorem totallySeparatedSpace_of_t0_of_basis_clopen
  statement: [T0Space X]
  proof: by
  constructor
  rintro x - y - hxy
  choose U hU using exists_isOpen_xor_mem hxy
  obtain ⟨hU₀, hU₁⟩ := hU
  rcases hU₁ with hx | hy
  · choose V hV using h.isOpen_iff.mp hU₀ x hx.1
    exact ⟨V, Vᶜ, hV.1.isOpen, hV.1.compl.isOpen, hV.2.1, notMem_subset hV.2.2 hx.2,
      (union_compl_self V).sup

中文:
定理 totallySeparatedSpace_of_t0_of_basis_clopen
  结论: [T0空间 X]
  证明: by
  constructor
  rintro x - y - hxy
  choose U hU using exists_isOpen_xor_mem hxy
  obtain ⟨hU₀, hU₁⟩ := hU
  rcases hU₁ with hx | hy
  · choose V hV using h.isOpen_iff.mp hU₀ x hx.1
    exact ⟨V, Vᶜ, hV.1.isOpen, hV.1.compl.isOpen, hV.2.1, notMem_subset hV.2.2 hx.2,
      (union_compl_self V).sup

Depends on / 依赖: compl.isOpen, disjoint_compl_le, disjoint_compl_right, exists_isOpen_xor_mem, h.isOpen_iff.mp, isOpen, isOpen_iff, notMem_subset, superset, union_comm, union_compl_self
-/
theorem totallySeparatedSpace_of_t0_of_basis_clopen [T0Space X]
    (h : IsTopologicalBasis { s : Set X | IsClopen s }) : TotallySeparatedSpace X := by
  constructor
  rintro x - y - hxy
  choose U hU using exists_isOpen_xor_mem hxy
  obtain ⟨hU₀, hU₁⟩ := hU
  rcases hU₁ with hx | hy
  · choose V hV using h.isOpen_iff.mp hU₀ x hx.1
    exact ⟨V, Vᶜ, hV.1.isOpen, hV.1.compl.isOpen, hV.2.1, notMem_subset hV.2.2 hx.2,
      (union_compl_self V).superset, disjoint_compl_right⟩
  · choose V hV using h.isOpen_iff.mp hU₀ y hy.1
    exact ⟨Vᶜ, V, hV.1.compl.isOpen, hV.1.isOpen, notMem_subset hV.2.2 hy.2, hV.2.1,
      (union_comm _ _ ▸ union_compl_self V).superset, disjoint_compl_left⟩

variable [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]

/--
theorem `nhds_basis_clopen` / 定理 `nhds_basis_clopen`

English:
theorem nhds_basis_clopen
  given: (x : X)
  statement: (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsClopen s) id
  proof: ⟨fun U => by
    constructor
    · have hx : connectedComponent x = {x} :=
        totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x
      rw [connectedComponent_eq_iInter_isClopen] at hx
      intro hU
      let N := { s // IsClopen s ∧ x in s }
      rsuffices ⟨⟨s, hs, hs'⟩, hs''⟩

中文:
定理 nhds_basis_clopen
  条件: (x : X)
  结论: (𝓝 x).有基 (fun s : 集合 X => x in s ∧ IsClopen s) id
  证明: ⟨fun U => by
    constructor
    · have hx : connectedComponent x = {x} :=
        totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x
      rw [connectedComponent_eq_iInter_isClopen] at hx
      intro hU
      let N := { s // IsClopen s ∧ x in s }
      rsuffices ⟨⟨s, hs, hs'⟩, hs''⟩

Depends on / 依赖: Directed, GE.ge, IsClopen, IsClosed, Nonempty, connectedComponent, connectedComponent_eq_iInter_isClopen, isClopen_univ, mem_univ, property, rsuffices, s.property, s.val, subseteq, totallyDisconnectedSpace_iff_connectedComponent_singleton, totallyDisconnectedSpace_iff_connectedComponent_singleton.mp
-/
theorem nhds_basis_clopen (x : X) : (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsClopen s) id :=
  ⟨fun U => by
    constructor
    · have hx : connectedComponent x = {x} :=
        totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x
      rw [connectedComponent_eq_iInter_isClopen] at hx
      intro hU
      let N := { s // IsClopen s ∧ x in s }
      rsuffices ⟨⟨s, hs, hs'⟩, hs''⟩ : exists s : N, s.val subseteq U
      · exact ⟨s, ⟨hs', hs⟩, hs''⟩
      have : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
      have hNcl : forall s : N, IsClosed s.val := fun s => s.property.1.1
      have hdir : Directed GE.ge fun s : N => s.val := by
        rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
        exact ⟨⟨s inter t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left, inter_subset_right⟩
      have h_nhds : forall y in ⋂ s : N, s.val, U in 𝓝 y := fun y y_in => by
        rw [hx]; rw [mem_singleton_iff] at y_in
        rwa [y_in]
      exact exists_subset_nhds_of_compactSpace hdir hNcl h_nhds
    · rintro ⟨V, ⟨hxV, -, V_op⟩, hUV : V subseteq U⟩
      rw [mem_nhds_iff]
      exact ⟨V, hUV, V_op, hxV⟩⟩

/--
theorem `isTopologicalBasis_isClopen` / 定理 `isTopologicalBasis_isClopen`

English:
theorem isTopologicalBasis_isClopen
  statement: IsTopologicalBasis { s : Set X | IsClopen s }
  proof: by
  apply isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U in 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V subseteq U⟩
  use V
  tauto

中文:
定理 isTopologicalBasis_isClopen
  结论: 是TopologicalBasis { s : 集合 X | IsClopen s }
  证明: by
  apply isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U in 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V subseteq U⟩
  use V
  tauto

Depends on / 依赖: IsClopen, IsOpen, IsOpen.mem_nhds, U_op, isTopologicalBasis_of_isOpen_of_nhds, mem_iff, mem_iff.mp, mem_nhds, nhds_basis_clopen, subseteq
-/
theorem isTopologicalBasis_isClopen : IsTopologicalBasis { s : Set X | IsClopen s } := by
  apply isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U in 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V subseteq U⟩
  use V
  tauto

/--
theorem `compact_exists_isClopen_in_isOpen` / 定理 `compact_exists_isClopen_in_isOpen`

English:
theorem compact_exists_isClopen_in_isOpen
  given: {x : X} {U : Set X} (is_open : IsOpen U) (memU : x in U)
  proof: isTopologicalBasis_isClopen.mem_nhds_iff.1 (is_open.mem_nhds memU)

中文:
定理 compact_存在_isClopen_in_isOpen
  条件: {x : X} {U : 集合 X} (is_open : 是开集 U) (memU : x in U)
  证明: isTopologicalBasis_isClopen.mem_nhds_iff.1 (is_open.mem_nhds memU)

Depends on / 依赖: isTopologicalBasis_isClopen, isTopologicalBasis_isClopen.mem_nhds_iff, is_open, is_open.mem_nhds, mem_nhds, mem_nhds_iff
-/
theorem compact_exists_isClopen_in_isOpen {x : X} {U : Set X} (is_open : IsOpen U) (memU : x in U) :
    exists V : Set X, IsClopen V ∧ x in V ∧ V subseteq U :=
  isTopologicalBasis_isClopen.mem_nhds_iff.1 (is_open.mem_nhds memU)

end Profinite

section LocallyCompact

variable {H : Type*} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]

/--
theorem `loc_compact_Haus_tot_disc_of_zero_dim` / 定理 `loc_compact_Haus_tot_disc_of_zero_dim`

English:
theorem loc_compact_Haus_tot_disc_of_zero_dim
  given: [TotallyDisconnectedSpace H]
  proof: by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) fun x U memU hU => ?_
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  let u : Set s := ((↑) : s -> H) ⁻¹' interior s
  have u_open_in_s : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  lift x to s using 

中文:
定理 loc_compact_Haus_tot_disc_of_zero_dim
  条件: [全不连通空间 H]
  证明: by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) fun x U memU hU => ?_
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  let u : Set s := ((↑) : s -> H) ⁻¹' interior s
  have u_open_in_s : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  lift x to s using 

Depends on / 依赖: CompactSpace, IsClopen, IsOpen, V_sub, VisClopen, compact_exists_isClopen_in_isOpen, continuous_subtype_val, exists_compact_subset, interior, interior_subset, isCompact_iff_compactSpace, isOpen_interior, isOpen_interior.preimage, isTopologicalBasis_of_isOpen_of_nhds, preimage, u_open_in_s
-/
theorem loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] :
    IsTopologicalBasis { s : Set H | IsClopen s } := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.2) fun x U memU hU => ?_
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  let u : Set s := ((↑) : s -> H) ⁻¹' interior s
  have u_open_in_s : IsOpen u := isOpen_interior.preimage continuous_subtype_val
  lift x to s using interior_subset xs
  have : CompactSpace s := isCompact_iff_compactSpace.1 comp
  obtain ⟨V : Set s, VisClopen, Vx, V_sub⟩ := compact_exists_isClopen_in_isOpen u_open_in_s xs
  have VisClopen' : IsClopen (((↑) : s -> H) '' V) := by
    refine ⟨comp.isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.1 VisClopen.1,
      ?_⟩
    let v : Set u := ((↑) : u -> s) ⁻¹' V
    have : ((↑) : u -> H) = ((↑) : s -> H) ∘ ((↑) : u -> s) := rfl
    have f0 : IsEmbedding ((↑) : u -> H) := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    have f1 : IsOpenEmbedding ((↑) : u -> H) := by
      refine ⟨f0, ?_⟩
      · have : Set.range ((↑) : u -> H) = interior s := by
          rw [this]; rw [Set.range_comp]; rw [Subtype.range_coe]; rw [Subtype.image_preimage_coe]
          apply Set.inter_eq_self_of_subset_right interior_subset
        rw [this]
        apply isOpen_interior
    have f2 : IsOpen v := VisClopen.2.preimage continuous_subtype_val
    have f3 : ((↑) : s -> H) '' V = ((↑) : u -> H) '' v := by
      rw [this]; rw [image_comp]; rw [Subtype.image_preimage_coe]; rw [inter_eq_self_of_subset_right V_sub]
    rw [f3]
    apply f1.isOpenMap v f2
  use (↑) '' V, VisClopen', by simp [Vx], Subset.trans (by simp) sU

/--
theorem `loc_compact_t2_tot_disc_iff_tot_sep` / 定理 `loc_compact_t2_tot_disc_iff_tot_sep`

English:
theorem loc_compact_t2_tot_disc_iff_tot_sep
  proof: by
  constructor
  · intro h
    exact totallySeparatedSpace_of_t0_of_basis_clopen loc_compact_Haus_tot_disc_of_zero_dim
  apply TotallySeparatedSpace.totallyDisconnectedSpace

中文:
定理 loc_compact_t2_tot_disc_iff_tot_sep
  证明: by
  constructor
  · intro h
    exact totallySeparatedSpace_of_t0_of_basis_clopen loc_compact_Haus_tot_disc_of_zero_dim
  apply TotallySeparatedSpace.totallyDisconnectedSpace

Depends on / 依赖: TotallySeparatedSpace, TotallySeparatedSpace.totallyDisconnectedSpace, loc_compact_Haus_tot_disc_of_zero_dim, totallyDisconnectedSpace, totallySeparatedSpace_of_t0_of_basis_clopen
-/
theorem loc_compact_t2_tot_disc_iff_tot_sep :
    TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H := by
  constructor
  · intro h
    exact totallySeparatedSpace_of_t0_of_basis_clopen loc_compact_Haus_tot_disc_of_zero_dim
  apply TotallySeparatedSpace.totallyDisconnectedSpace

/-- A totally disconnected compact Hausdorff space is totally separated. -/
instance (priority := 100) [TotallyDisconnectedSpace H] : TotallySeparatedSpace H :=
  loc_compact_t2_tot_disc_iff_tot_sep.mp inferInstance

/--
lemma `exists_clopen_of_closed_subset_open` / 引理 `exists_clopen_of_closed_subset_open`

English:
lemma exists_clopen_of_closed_subset_open
  statement: {X : Type*}
  proof: by
  -- every `z ∈ Z` has clopen neighborhood `V z ⊆ U`
  choose V hV using fun (z : Z) => compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the `V z` cover `Z`
  have V_cover : Z subseteq ⋃ z, V z := fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- choose a finite subcover
  cho

中文:
引理 存在_clopen_of_closed_subset_open
  结论: {X : 类型}
  证明: by
  -- every `z ∈ Z` has clopen neighborhood `V z ⊆ U`
  choose V hV using fun (z : Z) => compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the `V z` cover `Z`
  have V_cover : Z subseteq ⋃ z, V z := fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- choose a finite subcover
  cho
-/
lemma exists_clopen_of_closed_subset_open {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {Z U : Set X} (hZ : IsClosed Z) (hU : IsOpen U) (hZU : Z subseteq U) :
    exists C : Set X, IsClopen C ∧ Z subseteq C ∧ C subseteq U := by
  -- every `z ∈ Z` has clopen neighborhood `V z ⊆ U`
  choose V hV using fun (z : Z) => compact_exists_isClopen_in_isOpen hU (hZU z.property)
  -- the `V z` cover `Z`
  have V_cover : Z subseteq ⋃ z, V z := fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, (hV ⟨z, hz⟩).2.1⟩
  -- choose a finite subcover
  choose I hI using hZ.isCompact.elim_finite_subcover V (fun z => (hV z).1.isOpen) V_cover
  -- the union of this finite subcover does the job
  exact ⟨⋃ (i in I), V i, I.finite_toSet.isClopen_biUnion (fun i _ => (hV i).1), hI, by simp_all⟩

/--
lemma `exists_clopen_partition_of_clopen_cover` / 引理 `exists_clopen_partition_of_clopen_cover`

English:
lemma exists_clopen_partition_of_clopen_cover
  proof: by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := IH (Z := Z ∘ e) (D := D ∘ e)
      (fun i => Z_closed (e i)) (fun i => D_clopen (e i))
      (fun i => Z_subset_D (e i)) (by simpa [← e.injective.injOn.pairwiseDisjoint_image])
    re

中文:
引理 存在_clopen_partition_of_clopen_cover
  证明: by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := IH (Z := Z ∘ e) (D := D ∘ e)
      (fun i => Z_closed (e i)) (fun i => D_clopen (e i))
      (fun i => Z_subset_D (e i)) (by simpa [← e.injective.injOn.pairwiseDisjoint_image])
    re

Depends on / 依赖: D_clopen, Finite, Finite.induction_empty_option, Function, Function.comp_apply, Z_closed, Z_subset_D, comp_apply, e.injective.injOn.pairwiseDisjoint_image, e.symm, e.symm.injective.injOn.pairwiseDisjoint_image, iUnion_s, induction_empty_option, injective, of_equiv, pairwiseDisjoint_image
-/
lemma exists_clopen_partition_of_clopen_cover
    {X I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [Finite I] {Z D : I -> Set X}
    (Z_closed : forall i, IsClosed (Z i)) (D_clopen : forall i, IsClopen (D i))
    (Z_subset_D : forall i, Z i subseteq D i) (Z_disj : univ.PairwiseDisjoint Z) :
    exists C : I -> Set X, (forall i, IsClopen (C i)) ∧ (forall i, Z i subseteq C i) ∧ (forall i, C i subseteq D i) ∧
    (⋃ i, D i) subseteq (⋃ i, C i) ∧ (univ.PairwiseDisjoint C) := by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    obtain ⟨C, h1, h2, h3, h4, h5⟩ := IH (Z := Z ∘ e) (D := D ∘ e)
      (fun i => Z_closed (e i)) (fun i => D_clopen (e i))
      (fun i => Z_subset_D (e i)) (by simpa [← e.injective.injOn.pairwiseDisjoint_image])
    refine ⟨C ∘ e.symm, fun i => h1 (e.symm i), fun i => by simpa using h2 (e.symm i),
      fun i => by simpa using h3 (e.symm i), ?_,
      by simpa [← e.symm.injective.injOn.pairwiseDisjoint_image]⟩
    simp only [Function.comp_apply, iUnion_subset_iff] at h4
    simpa [e.symm.surjective.iUnion_comp C] using fun i => h4 (e.symm i)
  | h_empty => exact ⟨fun _ => univ, by simp, by simp, by simp, by simp, fun i => PEmpty.elim i⟩
  | @h_option I _ IH =>
    -- let `Z'` be the restriction of `Z` along `some : I → Option I`
    let Z' : I -> Set X := fun i => Z (some i)
    have Z'_closed (i : I) : IsClosed (Z (some i)) := Z_closed (some i)
    have Z'_disj : univ.PairwiseDisjoint (Z ∘ some) := by
      rw [← (Option.some_injective _).injOn.pairwiseDisjoint_image]
      exact PairwiseDisjoint.subset Z_disj (by simp)
    -- find `Z none ⊆ V ⊆ D none \ ⋃ Z'` using `exists_clopen_of_closed_subset_open`
    let U : Set X := D none \ ⋃ i, Z (some i)
    have U_open : IsOpen U := IsOpen.sdiff (D_clopen none).2
      (isClosed_iUnion_of_finite (fun i => Z_closed (some i)))
    have Z0_subset_U : Z none subseteq U := by
      rw [subset_sdiff]
      simpa using ⟨Z_subset_D none, fun i => (by apply Z_disj; all_goals simp)⟩
    obtain ⟨V, V_clopen, Z0_subset_V, V_subset_U⟩ :=
      exists_clopen_of_closed_subset_open (Z_closed none) U_open Z0_subset_U
    have V_subset_D0 : V subseteq D none := subset_trans V_subset_U sdiff_subset
    -- choose `Z' i ⊆ C' i ⊆ D' i = D i.succ \ V` using the inductive hypothesis
    let D' : I -> Set X := fun i => D (some i) \ V
    have D'_clopen (i : I) : IsClopen (D' i) := (D_clopen (some i)).diff V_clopen
    have Z'_subset_D' (i : I) : Z' i subseteq D' i := by
      rw [subset_sdiff]
      refine ⟨by grind, Disjoint.mono_right V_subset_U ?_⟩
      exact Disjoint.mono_left (subset_iUnion_of_subset i fun _ h => h) (by grind)
    obtain ⟨C', C'_clopen, Z'_subset_C', C'_subset_D', C'_cover_D', C'_disj⟩ :=
      IH Z'_closed D'_clopen Z'_subset_D' Z'_disj
    -- now choose `C0 = D none \ ⋃ C' i`
    let C0 : Set X := D none \ ⋃ i, C' i
    have : IsClopen C0 := (D_clopen none).diff (isClopen_iUnion_of_finite C'_clopen)
    have : Z none subseteq C0 := by
      simp only [C0, subset_sdiff]
      exact ⟨by grind, Disjoint.mono_left Z0_subset_V (by simp; grind)⟩
    -- patch together to define `C none := C0`, `C (some i) := C' i`
    -- and verify the needed properties
    let C : Option I -> Set X := fun i => Option.casesOn i C0 C'
    refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try rintro (_ | i); all_goals grind
    · intro x hx
      rw [mem_iUnion] at hx ⊢
      by_cases hx0 : x in C0; { exact ⟨none, hx0⟩ }
      by_cases hxD : x in D none
      · have hxC' : x in ⋃ i, C' i := by grind
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxC'
        exact ⟨some i, hi⟩
      · obtain ⟨none | j, hi⟩ := hx; {grind}
        have hxD' : x in ⋃ i, D' i := mem_iUnion.mpr ⟨j, by grind⟩
obtain ⟨k, hk⟩ := mem_iUnion.mp C'_cover_D' hxD'
        exact ⟨some k, hk⟩
    · rw [Set.pairwiseDisjoint_iff]
      rintro (_ | i) _ (_ | j) _
      · simp
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_right (subset_iUnion C' j) disjoint_sdiff_left
      · simpa [C, C0, Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] using
          Disjoint.mono_left (subset_iUnion C' i) disjoint_sdiff_right
      · simpa using (Set.pairwiseDisjoint_iff.mp C'_disj) (by trivial) (by trivial)

end LocallyCompact
