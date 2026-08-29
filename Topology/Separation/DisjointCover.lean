/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Disjointed
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.OpenCover

/-!
# Disjoint covers of profinite spaces

We prove various results about covering profinite spaces by disjoint clopens, including

* `TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`: any open cover of a
  profinite space can be refined to a finite cover by pairwise disjoint nonempty clopens.

* `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal`: if `f : X → V` is continuous
  with `X` profinite, and `S` is a neighbourhood of the diagonal in `V × V`, then `f` can be
  `S`-approximated by a function factoring through `Fin n` for some `n`.
-/

public section

open Set TopologicalSpace

open scoped Function Finset Topology

namespace TopologicalSpace.IsOpenCover

variable {ι X : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X] {U : ι -> Opens X}

/--
lemma `exists_finite_clopen_cover` / 引理 `exists_finite_clopen_cover`

English:
lemma exists_finite_clopen_cover
  given: (hU : IsOpenCover U)
  statement: exists (n : Nat) (V : Fin n -> Clopens X),
  proof: by
  -- Choose an index `r x` for each point in `X` such that `∀ x, x ∈ U (r x)`.
  choose r hr using hU.exists_mem
  -- Choose a clopen neighbourhood `V x` of each `x` contained in `U (r x)`.
  choose V hV hVx hVU using fun x => compact_exists_isClopen_in_isOpen (U _).isOpen (hr x)
  -- Apply compa

中文:
引理 exists_finite_clopen_cover
  条件: (hU : IsOpenCover U)
  结论: 存在 (n : 自然数) (V : Fin n -> Clopens X),
  证明: by
  -- Choose an index `r x` for each point in `X` such that `∀ x, x ∈ U (r x)`.
  choose r hr using hU.exists_mem
  -- Choose a clopen neighbourhood `V x` of each `x` contained in `U (r x)`.
  choose V hV hVx hVU using fun x => compact_exists_isClopen_in_isOpen (U _).isOpen (hr x)
  -- Apply compa
-/
lemma exists_finite_clopen_cover (hU : IsOpenCover U) : exists (n : Nat) (V : Fin n -> Clopens X),
    (forall j, exists i, (V j : Set X) subseteq U i) ∧ univ subseteq ⋃ j, (V j : Set X) := by
  -- Choose an index `r x` for each point in `X` such that `∀ x, x ∈ U (r x)`.
  choose r hr using hU.exists_mem
  -- Choose a clopen neighbourhood `V x` of each `x` contained in `U (r x)`.
  choose V hV hVx hVU using fun x => compact_exists_isClopen_in_isOpen (U _).isOpen (hr x)
  -- Apply compactness to extract a finite subset of the `V`s which covers `X`.
  obtain ⟨t, ht⟩ : exists t, univ subseteq ⋃ i in t, V i :=
    isCompact_univ.elim_finite_subcover V (fun x => (hV x).2) (fun x _ => mem_iUnion.mpr ⟨x, hVx x⟩)
  -- Biject it noncanonically with `Fin n` for some `n`.
  refine ⟨_, fun j => ⟨_, hV (t.equivFin.symm j)⟩, fun j => ⟨_, hVU _⟩, fun x hx => ?_⟩
  obtain ⟨m, hm, hm'⟩ := mem_iUnion₂.mp (ht hx)
  exact Set.mem_iUnion_of_mem (t.equivFin ⟨m, hm⟩) (by simpa)

/--
lemma `exists_finite_nonempty_disjoint_clopen_cover` / 引理 `exists_finite_nonempty_disjoint_clopen_cover`

English:
lemma exists_finite_nonempty_disjoint_clopen_cover
  given: (hU : IsOpenCover U)
  proof: by
  classical
  obtain ⟨n, V, hVle, hVun⟩ := hU.exists_finite_clopen_cover
  obtain ⟨W, hWle, hWun, hWd⟩ := Fintype.exists_disjointed_le V
  simp only [← SetLike.coe_set_eq, Clopens.coe_finset_sup, Finset.mem_univ, iUnion_true] at hWun
  let t : Finset (Fin n) := {j | W j != ⊥}
  refine ⟨#t, fun k 

中文:
引理 exists_finite_nonempty_disjoint_clopen_cover
  条件: (hU : IsOpenCover U)
  证明: by
  classical
  obtain ⟨n, V, hVle, hVun⟩ := hU.exists_finite_clopen_cover
  obtain ⟨W, hWle, hWun, hWd⟩ := Fintype.exists_disjointed_le V
  simp only [← SetLike.coe_set_eq, Clopens.coe_finset_sup, Finset.mem_univ, iUnion_true] at hWun
  let t : Finset (Fin n) := {j | W j != ⊥}
  refine ⟨#t, fun k 

Depends on / 依赖: Clopens, Clopens.coe_finset_sup, Finset, Finset.mem_filter.mp, Finset.mem_univ, Fintype, Fintype.exists_disjointed_le, SetLike, SetLike.coe_set_eq, classical, coe_finset_sup, coe_set_eq, equivFin, exists_disjointed_le, exists_finite_clopen_cover, hU.exists_finite_clopen_cover, iUnion_true, mem_filter, mem_univ, subset_trans
-/
lemma exists_finite_nonempty_disjoint_clopen_cover (hU : IsOpenCover U) :
    exists (n : Nat) (W : Fin n -> Clopens X), (forall j, W j != ⊥ ∧ exists i, (W j : Set X) subseteq U i)
    ∧ (univ : Set X) subseteq ⋃ j, ↑(W j) ∧ Pairwise (Disjoint on W) := by
  classical
  obtain ⟨n, V, hVle, hVun⟩ := hU.exists_finite_clopen_cover
  obtain ⟨W, hWle, hWun, hWd⟩ := Fintype.exists_disjointed_le V
  simp only [← SetLike.coe_set_eq, Clopens.coe_finset_sup, Finset.mem_univ, iUnion_true] at hWun
  let t : Finset (Fin n) := {j | W j != ⊥}
  refine ⟨#t, fun k => W (t.equivFin.symm k), fun k => ⟨?_, ?_⟩, fun x hx => ?_, ?_⟩
  · exact (Finset.mem_filter.mp (t.equivFin.symm k).2).2
  · exact match hVle (t.equivFin.symm k) with | ⟨i, hi⟩ => ⟨i, subset_trans (hWle _) hi⟩
· obtain ⟨j, hj⟩ := mem_iUnion.mp (hWun ▸ hVun) hx
    have : W j != ⊥ := by simpa [← SetLike.coe_ne_coe, ← Set.nonempty_iff_ne_empty] using ⟨x, hj⟩
    exact mem_iUnion.mpr ⟨t.equivFin ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩⟩, by simpa⟩
· exact hWd.comp_of_injective Subtype.val_injective.comp t.equivFin.symm.injective

end TopologicalSpace.IsOpenCover

namespace TopologicalSpace
variable {X : Type*} [TopologicalSpace X] {S : Set (X × X)}

/--
lemma `exists_open_prod_subset_of_mem_nhds_diagonal` / 引理 `exists_open_prod_subset_of_mem_nhds_diagonal`

English:
lemma exists_open_prod_subset_of_mem_nhds_diagonal
  given: (hS : S in nhdsSet (diagonal X)) (x : X)
  proof: by
  have : S in 𝓝 (x, x) := mem_nhdsSet_iff_forall.mp hS _ rfl
  obtain ⟨u, v, huo, hux, hvo, hvx, H⟩ := by rwa [mem_nhds_prod_iff'] at this
  exact ⟨_, huo.inter hvo, ⟨hux, hvx⟩, fun p hp => H ⟨hp.1.1, hp.2.2⟩⟩

中文:
引理 exists_open_prod_subset_of_mem_nhds_diagonal
  条件: (hS : S in nhdsSet (diagonal X)) (x : X)
  证明: by
  have : S in 𝓝 (x, x) := mem_nhdsSet_iff_forall.mp hS _ rfl
  obtain ⟨u, v, huo, hux, hvo, hvx, H⟩ := by rwa [mem_nhds_prod_iff'] at this
  exact ⟨_, huo.inter hvo, ⟨hux, hvx⟩, fun p hp => H ⟨hp.1.1, hp.2.2⟩⟩

Depends on / 依赖: huo.inter, mem_nhdsSet_iff_forall, mem_nhdsSet_iff_forall.mp, mem_nhds_prod_iff
-/
lemma exists_open_prod_subset_of_mem_nhds_diagonal (hS : S in nhdsSet (diagonal X)) (x : X) :
    exists U : Set X, IsOpen U ∧ x in U ∧ U ×ˢ U subseteq S := by
  have : S in 𝓝 (x, x) := mem_nhdsSet_iff_forall.mp hS _ rfl
  obtain ⟨u, v, huo, hux, hvo, hvx, H⟩ := by rwa [mem_nhds_prod_iff'] at this
  exact ⟨_, huo.inter hvo, ⟨hux, hvx⟩, fun p hp => H ⟨hp.1.1, hp.2.2⟩⟩

variable [CompactSpace X]

/--
lemma `exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact` / 引理 `exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact`

English:
lemma exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact
  proof: by
  choose U hUo hUx hUp using exists_open_prod_subset_of_mem_nhds_diagonal hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hUo (fun x _ => mem_iUnion.mpr ⟨_, hUx x⟩)
  refine ⟨t, fun i => ⟨_, hUo i⟩, .of_sets _ ?_, (hUp ·)⟩
  simpa [iUnion_subtype, ← univ_subset_iff] using ht

中文:
引理 exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact
  证明: by
  choose U hUo hUx hUp using exists_open_prod_subset_of_mem_nhds_diagonal hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hUo (fun x _ => mem_iUnion.mpr ⟨_, hUx x⟩)
  refine ⟨t, fun i => ⟨_, hUo i⟩, .of_sets _ ?_, (hUp ·)⟩
  simpa [iUnion_subtype, ← univ_subset_iff] using ht

Depends on / 依赖: elim_finite_subcover, exists_open_prod_subset_of_mem_nhds_diagonal, iUnion_subtype, isCompact_univ, isCompact_univ.elim_finite_subcover, mem_iUnion, mem_iUnion.mpr, of_sets, univ_subset_iff
-/
lemma exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact
    (hS : S in nhdsSet (diagonal X)) :
    exists (t : Finset X) (U : t -> Opens X), IsOpenCover U ∧ forall i, (U i : Set X) ×ˢ U i subseteq S := by
  choose U hUo hUx hUp using exists_open_prod_subset_of_mem_nhds_diagonal hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hUo (fun x _ => mem_iUnion.mpr ⟨_, hUx x⟩)
  refine ⟨t, fun i => ⟨_, hUo i⟩, .of_sets _ ?_, (hUp ·)⟩
  simpa [iUnion_subtype, ← univ_subset_iff] using ht

variable [TotallyDisconnectedSpace X] [T2Space X]

/--
lemma `exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite` / 引理 `exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite`

English:
lemma exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite
  proof: by
  obtain ⟨t, U, hUc, hUS⟩ := exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact hS
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hUc.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, fun j => (hW₁ j).1, fun j y hy z hz => ?_, hW₂, hW₃⟩
 

中文:
引理 exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite
  证明: by
  obtain ⟨t, U, hUc, hUS⟩ := exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact hS
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hUc.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, fun j => (hW₁ j).1, fun j y hy z hz => ?_, hW₂, hW₃⟩
 
-/
private lemma exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite
    (hS : S in nhdsSet (diagonal X)) :
    exists (n : Nat) (D : Fin n -> Clopens X), (forall i, D i != ⊥) ∧ (forall i, forall y in D i, forall z in D i, (y, z) in S)
    ∧ (univ : Set X) subseteq ⋃ i, D i ∧ Pairwise (Disjoint on D) := by
  obtain ⟨t, U, hUc, hUS⟩ := exists_finite_open_cover_prod_subset_of_mem_nhds_diagonal_of_compact hS
  -- Now refine it to a disjoint covering.
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hUc.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, fun j => (hW₁ j).1, fun j y hy z hz => ?_, hW₂, hW₃⟩
  exact match (hW₁ j).2 with | ⟨i, hi⟩ => hUS i ⟨hi hy, hi hz⟩

end TopologicalSpace

namespace ContinuousMap

variable {X V : Type*} [TopologicalSpace X] [TopologicalSpace V] [TotallyDisconnectedSpace X]
  [T2Space X] [CompactSpace X] {S : Set (V × V)} (f : C(X, V))

/--
lemma `exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal` / 引理 `exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal`

English:
lemma exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal
  given: (hS : S in nhdsSet (diagonal V))
  proof: by
  have : (f.prodMap f) ⁻¹' S in nhdsSet (diagonal X) := by
    rw [mem_nhdsSet_iff_forall] at hS ⊢
    rintro ⟨x, y⟩ (rfl : x = y)
    exact (map_continuous _).continuousAt.preimage_mem_nhds (hS _ rfl)
  exact exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite this

中文:
引理 exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal
  条件: (hS : S in nhdsSet (diagonal V))
  证明: by
  have : (f.prodMap f) ⁻¹' S in nhdsSet (diagonal X) := by
    rw [mem_nhdsSet_iff_forall] at hS ⊢
    rintro ⟨x, y⟩ (rfl : x = y)
    exact (map_continuous _).continuousAt.preimage_mem_nhds (hS _ rfl)
  exact exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite this

Depends on / 依赖: continuousAt, continuousAt.preimage_mem_nhds, diagonal, exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite, f.prodMap, map_continuous, mem_nhdsSet_iff_forall, nhdsSet, preimage_mem_nhds, prodMap
-/
lemma exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal (hS : S in nhdsSet (diagonal V)) :
    exists (n : Nat) (D : Fin n -> Clopens X), (forall i, D i != ⊥) ∧ (forall i, forall y in D i, forall z in D i, (f y, f z) in S)
    ∧ (univ : Set X) subseteq ⋃ i, D i ∧ Pairwise (Disjoint on D) := by
  have : (f.prodMap f) ⁻¹' S in nhdsSet (diagonal X) := by
    rw [mem_nhdsSet_iff_forall] at hS ⊢
    rintro ⟨x, y⟩ (rfl : x = y)
    exact (map_continuous _).continuousAt.preimage_mem_nhds (hS _ rfl)
  exact exists_finite_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal_of_profinite this

/--
lemma `exists_finite_approximation_of_mem_nhds_diagonal` / 引理 `exists_finite_approximation_of_mem_nhds_diagonal`

English:
lemma exists_finite_approximation_of_mem_nhds_diagonal
  given: (hS : S in nhdsSet (diagonal V))
  proof: by
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal f hS
  have h_uniq (x) : exists! i, x in E i := by
    refine match mem_iUnion.mp (hEuniv <| mem_univ x) with
      | ⟨i, hi⟩ => ⟨i, hi, fun j hj => hEdis.eq ?_⟩
    simpa [← Clopens.coe_di

中文:
引理 exists_finite_approximation_of_mem_nhds_diagonal
  条件: (hS : S in nhdsSet (diagonal V))
  证明: by
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal f hS
  have h_uniq (x) : exists! i, x in E i := by
    refine match mem_iUnion.mp (hEuniv <| mem_univ x) with
      | ⟨i, hi⟩ => ⟨i, hi, fun j hj => hEdis.eq ?_⟩
    simpa [← Clopens.coe_di

Depends on / 依赖: Clopens, Clopens.coe_disjoint, SetLike, SetLike.coe_set_eq, coe_disjoint, coe_set_eq, exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal, hEdis.eq, hEuniv, h_ex, h_uniq, mem_iUnion, mem_iUnion.mp, mem_univ, nonempty_iff_ne, not_disjoint_iff, unique
-/
lemma exists_finite_approximation_of_mem_nhds_diagonal (hS : S in nhdsSet (diagonal V)) :
    exists (n : Nat) (g : X -> Fin n) (h : Fin n -> V), Continuous g ∧ forall x, (f x, h (g x)) in S := by
  obtain ⟨n, E, hEne, hES, hEuniv, hEdis⟩ :=
    exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal f hS
  have h_uniq (x) : exists! i, x in E i := by
    refine match mem_iUnion.mp (hEuniv <| mem_univ x) with
      | ⟨i, hi⟩ => ⟨i, hi, fun j hj => hEdis.eq ?_⟩
    simpa [← Clopens.coe_disjoint, not_disjoint_iff] using! ⟨x, hj, hi⟩
  choose g hg hg' using h_uniq -- for each `x`, `g x` is the unique `i` such that `x ∈ E i`
  have h_ex (i) : exists x, x in E i := by
    simpa [← SetLike.coe_set_eq, ← nonempty_iff_ne_empty] using! hEne i
  choose r hr using h_ex -- for each `i`, choose an `r i ∈ E i`
  refine ⟨n, g, f ∘ r, continuous_discrete_rng.mpr fun j => ?_, fun x => (hES _) _ (hg _) _ (hr _)⟩
  convert! (E j).isOpen
  exact Set.ext fun x => ⟨fun hj => hj ▸ hg x, fun hx => (hg' _ _ hx).symm⟩

/--
If `f` is a continuous map from a profinite space to a topological space with a commutative monoid
structure, then we can approximate `f` by finite products of indicator functions of clopen sets.

(Note no compatibility is assumed between the monoid structure on `V` and the topology.)
-/
@[to_additive /-- If `f` is a continuous map from a profinite space to a topological space with a
commutative additive monoid structure, then we can approximate `f` by finite sums of indicator
functions of clopen sets.

(Note no compatibility is assumed between the monoid structure on `V` and the topology.) -/]
/--
lemma `exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal` / 引理 `exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal`

English:
lemma exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal
  statement: [CommMonoid V]
  proof: by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_finite_approximation_of_mem_nhds_diagonal f hS
  refine ⟨n, fun i => ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x => ?_⟩
  convert! hgh x
  exact (Fintype.prod_eq_single _ fun i hi => mulIndicator_of_notMem hi.symm _).trans
    (mulIndicator_of_mem rfl 

中文:
引理 exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal
  结论: [CommMonoid V]
  证明: by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_finite_approximation_of_mem_nhds_diagonal f hS
  refine ⟨n, fun i => ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x => ?_⟩
  convert! hgh x
  exact (Fintype.prod_eq_single _ fun i hi => mulIndicator_of_notMem hi.symm _).trans
    (mulIndicator_of_mem rfl 

Depends on / 依赖: Fintype, Fintype.prod_eq_single, convert, exists_finite_approximation_of_mem_nhds_diagonal, hi.symm, isClopen_discrete, mulIndicator_of_mem, mulIndicator_of_notMem, preimage, prod_eq_single
-/
lemma exists_finite_sum_const_mulIndicator_approximation_of_mem_nhds_diagonal [CommMonoid V]
    (hS : S in nhdsSet (diagonal V)) :
    exists (n : Nat) (U : Fin n -> Clopens X) (v : Fin n -> V),
    forall x, (f x, ∏ n, mulIndicator (U n) (fun _ => v n) x) in S := by
  obtain ⟨n, g, h, hg, hgh⟩ := exists_finite_approximation_of_mem_nhds_diagonal f hS
  refine ⟨n, fun i => ⟨_, (isClopen_discrete {i}).preimage hg⟩, h, fun x => ?_⟩
  convert! hgh x
  exact (Fintype.prod_eq_single _ fun i hi => mulIndicator_of_notMem hi.symm _).trans
    (mulIndicator_of_mem rfl _)

end ContinuousMap
