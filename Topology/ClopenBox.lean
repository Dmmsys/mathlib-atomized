/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Sets.Closeds

/-!
# Clopen subsets in Cartesian products

In general, a clopen subset in a Cartesian product of topological spaces
cannot be written as a union of "clopen boxes",
i.e. products of clopen subsets of the components (see [buzyakovaClopenBox] for counterexamples).

However, when one of the factors is compact, a clopen subset can be written as such a union.
Our argument in `TopologicalSpace.Clopens.exists_prod_subset`
follows the one given in [buzyakovaClopenBox].

We deduce that in a product of compact spaces, a clopen subset is a finite union of clopen boxes,
and use that to prove that the property of having countably many clopens is preserved by taking
Cartesian products of compact spaces (this is relevant to the theory of light profinite sets).

## References

- [buzyakovaClopenBox]: *On clopen sets in Cartesian products*, 2001.
- [engelking1989]: *General Topology*, 1989.

-/

public section

open Function Set Filter TopologicalSpace
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]

namespace TopologicalSpace.Clopens

/--
theorem `exists_prod_subset` / 定理 `exists_prod_subset`

English:
theorem exists_prod_subset
  given: (W : Clopens (X × Y)) {a : X × Y} (h : a in W)
  proof: by
  have hp : Continuous (fun y : Y => (a.1, y)) := .prodMk_right _
  let V : Set Y := {y | (a.1, y) in W}
  have hV : IsCompact V := (W.2.1.preimage hp).isCompact
  let U : Set X := {x | MapsTo (Prod.mk x) V W}
  have hUV : U ×ˢ V subseteq W := fun ⟨_, _⟩ hw => hw.1 hw.2
  exact ⟨⟨U, (ContinuousMap.isClopen_setOfPred_mapsTo hV W.2).preimage
    (ContinuousMap.id (X × Y)).curry.2⟩, by simp [U, V, MapsTo], ⟨V, W.2.preimage hp⟩, h, hUV⟩

中文:
定理 存在_prod_subset
  条件: (W : Clopens (X × Y)) {a : X × Y} (h : a in W)
  证明: by
  have hp : Continuous (fun y : Y => (a.1, y)) := .prodMk_right _
  let V : Set Y := {y | (a.1, y) in W}
  have hV : IsCompact V := (W.2.1.preimage hp).isCompact
  let U : Set X := {x | MapsTo (Prod.mk x) V W}
  have hUV : U ×ˢ V subseteq W := fun ⟨_, _⟩ hw => hw.1 hw.2
  exact ⟨⟨U, (ContinuousMap.isClopen_setOfPred_mapsTo hV W.2).preimage
    (ContinuousMap.id (X × Y)).curry.2⟩, by simp [U, V, MapsTo], ⟨V, W.2.preimage hp⟩, h, hUV⟩

Depends on / 依赖: Continuous, ContinuousMap, ContinuousMap.id, ContinuousMap.isClopen_setOfPred_mapsTo, IsCompact, MapsTo, Prod.mk, isClopen_setOfPred_mapsTo, isCompact, preimage, prodMk_right, subseteq
-/
theorem exists_prod_subset (W : Clopens (X × Y)) {a : X × Y} (h : a in W) :
    exists U : Clopens X, a.1 in U ∧ exists V : Clopens Y, a.2 in V ∧ U ×ˢ V <= W := by
  have hp : Continuous (fun y : Y => (a.1, y)) := .prodMk_right _
  let V : Set Y := {y | (a.1, y) in W}
  have hV : IsCompact V := (W.2.1.preimage hp).isCompact
  let U : Set X := {x | MapsTo (Prod.mk x) V W}
  have hUV : U ×ˢ V subseteq W := fun ⟨_, _⟩ hw => hw.1 hw.2
  exact ⟨⟨U, (ContinuousMap.isClopen_setOfPred_mapsTo hV W.2).preimage
    (ContinuousMap.id (X × Y)).curry.2⟩, by simp [U, V, MapsTo], ⟨V, W.2.preimage hp⟩, h, hUV⟩

variable [CompactSpace X]

/--
theorem `exists_finset_eq_sup_prod` / 定理 `exists_finset_eq_sup_prod`

English:
theorem exists_finset_eq_sup_prod
  given: (W : Clopens (X × Y))
  proof: by
  choose! U hxU V hxV hUV using fun x => W.exists_prod_subset (a := x)
  rcases W.2.1.isCompact.elim_nhds_subcover (fun x => U x ×ˢ V x) (fun x hx =>
    (U x ×ˢ V x).2.isOpen.mem_nhds ⟨hxU x hx, hxV x hx⟩) with ⟨I, hIW, hWI⟩
  classical
  use I.image fun x => (U x, V x)
  rw [Finset.sup_image]
  refine le_antisymm (fun x hx => ?_) (Finset.sup_le fun x hx => ?_)
  · rcases Set.mem_iUnion₂.1 (hWI hx) with ⟨i, hi, hxi⟩
    exact SetLike.le_def.1 (Finset.le_sup hi) hxi
· exact hUV _ hIW _ hx

中文:
定理 存在_finset_eq_sup_prod
  条件: (W : Clopens (X × Y))
  证明: by
  choose! U hxU V hxV hUV using fun x => W.exists_prod_subset (a := x)
  rcases W.2.1.isCompact.elim_nhds_subcover (fun x => U x ×ˢ V x) (fun x hx =>
    (U x ×ˢ V x).2.isOpen.mem_nhds ⟨hxU x hx, hxV x hx⟩) with ⟨I, hIW, hWI⟩
  classical
  use I.image fun x => (U x, V x)
  rw [Finset.sup_image]
  refine le_antisymm (fun x hx => ?_) (Finset.sup_le fun x hx => ?_)
  · rcases Set.mem_iUnion₂.1 (hWI hx) with ⟨i, hi, hxi⟩
    exact SetLike.le_def.1 (Finset.le_sup hi) hxi
· exact hUV _ hIW _ hx

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_image, Finset.sup_le, I.image, Set.mem_iUnion, SetLike, SetLike.le_def, W.exists_prod_subset, classical, elim_nhds_subcover, exists_prod_subset, isCompact, isCompact.elim_nhds_subcover, isOpen, isOpen.mem_nhds, le_antisymm, le_def, le_sup, mem_nhds
-/
theorem exists_finset_eq_sup_prod (W : Clopens (X × Y)) :
    exists (I : Finset (Clopens X × Clopens Y)), W = I.sup fun i => i.1 ×ˢ i.2 := by
  choose! U hxU V hxV hUV using fun x => W.exists_prod_subset (a := x)
  rcases W.2.1.isCompact.elim_nhds_subcover (fun x => U x ×ˢ V x) (fun x hx =>
    (U x ×ˢ V x).2.isOpen.mem_nhds ⟨hxU x hx, hxV x hx⟩) with ⟨I, hIW, hWI⟩
  classical
  use I.image fun x => (U x, V x)
  rw [Finset.sup_image]
  refine le_antisymm (fun x hx => ?_) (Finset.sup_le fun x hx => ?_)
  · rcases Set.mem_iUnion₂.1 (hWI hx) with ⟨i, hi, hxi⟩
    exact SetLike.le_def.1 (Finset.le_sup hi) hxi
· exact hUV _ hIW _ hx

/--
lemma `surjective_finset_sup_prod` / 引理 `surjective_finset_sup_prod`

English:
lemma surjective_finset_sup_prod
  proof: fun W =>
  let ⟨I, hI⟩ := W.exists_finset_eq_sup_prod; ⟨I, hI.symm⟩

中文:
引理 surjective_finset_sup_prod
  证明: fun W =>
  let ⟨I, hI⟩ := W.exists_finset_eq_sup_prod; ⟨I, hI.symm⟩
-/
lemma surjective_finset_sup_prod :
    Surjective fun I : Finset (Clopens X × Clopens Y) => I.sup fun i => i.1 ×ˢ i.2 := fun W =>
  let ⟨I, hI⟩ := W.exists_finset_eq_sup_prod; ⟨I, hI.symm⟩

/--
Instance `countable_prod` / 实例 `countable_prod`

English:
instance countable_prod
  signature: [Countable (Clopens X)]
  body: surjective_finset_sup_prod.countable

中文:
实例 countable_prod
  签名: [可数 (Clopens X)]
  定义体: surjective_finset_sup_prod.countable

Depends on / 依赖: countable, surjective_finset_sup_prod, surjective_finset_sup_prod.countable
-/
instance countable_prod [Countable (Clopens X)]
    [Countable (Clopens Y)] : Countable (Clopens (X × Y)) :=
  surjective_finset_sup_prod.countable

/--
Instance `finite_prod` / 实例 `finite_prod`

English:
instance finite_prod
  signature: [Finite (Clopens X)] [Finite (Clopens Y)]
  body: by
  cases nonempty_fintype (Clopens X)
  cases nonempty_fintype (Clopens Y)
  exact .of_surjective _ surjective_finset_sup_prod

中文:
实例 finite_prod
  签名: [有限 (Clopens X)] [有限 (Clopens Y)]
  定义体: by
  cases nonempty_fintype (Clopens X)
  cases nonempty_fintype (Clopens Y)
  exact .of_surjective _ surjective_finset_sup_prod

Depends on / 依赖: Clopens, nonempty_fintype, of_surjective, surjective_finset_sup_prod
-/
instance finite_prod [Finite (Clopens X)] [Finite (Clopens Y)] :
    Finite (Clopens (X × Y)) := by
  cases nonempty_fintype (Clopens X)
  cases nonempty_fintype (Clopens Y)
  exact .of_surjective _ surjective_finset_sup_prod

/--
lemma `countable_iff_secondCountable` / 引理 `countable_iff_secondCountable`

English:
lemma countable_iff_secondCountable
  statement: [T2Space X]
  proof: by
  refine ⟨fun h => ⟨{s : Set X | IsClopen s}, ?_, ?_⟩, fun h => ?_⟩
  · let f : {s : Set X | IsClopen s} -> Clopens X := fun s => ⟨s.1, s.2⟩
.countable exact Injective.of_eq_imp_le (f := f) (·.le)
  · apply IsTopologicalBasis.eq_generateFrom
    exact loc_compact_Haus_tot_disc_of_zero_dim
  · have : forall (s : Clopens X), exists (t : Finset (countableBasis X)), s.1 = (SetLike.coe t).sUnion :=
      fun s => eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
        (isBasis_countableBasis X) s.1 s.2.1.isCompact s.2.2
    let f : Clopens X -> Finset (countableBasis X) := fun s => (this s).choose
    have hf : f.Injective := by
      intro s t (h : Exists.choose _ = Exists.choose _)
      ext1; change s.carrier = t.carrier
      rw [(this s).choose_spec]; rw [(this t).choose_spec]; rw [h]
    exact hf.countable

中文:
引理 countable_iff_secondCountable
  结论: [T2空间 X]
  证明: by
  refine ⟨fun h => ⟨{s : Set X | IsClopen s}, ?_, ?_⟩, fun h => ?_⟩
  · let f : {s : Set X | IsClopen s} -> Clopens X := fun s => ⟨s.1, s.2⟩
.countable exact Injective.of_eq_imp_le (f := f) (·.le)
  · apply IsTopologicalBasis.eq_generateFrom
    exact loc_compact_Haus_tot_disc_of_zero_dim
  · have : forall (s : Clopens X), exists (t : Finset (countableBasis X)), s.1 = (SetLike.coe t).sUnion :=
      fun s => eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
        (isBasis_countableBasis X) s.1 s.2.1.isCompact s.2.2
    let f : Clopens X -> Finset (countableBasis X) := fun s => (this s).choose
    have hf : f.Injective := by
      intro s t (h : Exists.choose _ = Exists.choose _)
      ext1; change s.carrier = t.carrier
      rw [(this s).choose_spec]; rw [(this t).choose_spec]; rw [h]
    exact hf.countable

Depends on / 依赖: Clopens, Finset, Injective, Injective.of_eq_imp_le, IsClopen, IsTopologicalBasis, IsTopologicalBasis.eq_generateFrom, SetLike, SetLike.coe, countable, countableBasis, eq_generateFrom, eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open, isBasis_countableBasis, isCompa, loc_compact_Haus_tot_disc_of_zero_dim, of_eq_imp_le, sUnion
-/
lemma countable_iff_secondCountable [T2Space X]
    [TotallyDisconnectedSpace X] : Countable (Clopens X) ↔ SecondCountableTopology X := by
  refine ⟨fun h => ⟨{s : Set X | IsClopen s}, ?_, ?_⟩, fun h => ?_⟩
  · let f : {s : Set X | IsClopen s} -> Clopens X := fun s => ⟨s.1, s.2⟩
.countable exact Injective.of_eq_imp_le (f := f) (·.le)
  · apply IsTopologicalBasis.eq_generateFrom
    exact loc_compact_Haus_tot_disc_of_zero_dim
  · have : forall (s : Clopens X), exists (t : Finset (countableBasis X)), s.1 = (SetLike.coe t).sUnion :=
      fun s => eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
        (isBasis_countableBasis X) s.1 s.2.1.isCompact s.2.2
    let f : Clopens X -> Finset (countableBasis X) := fun s => (this s).choose
    have hf : f.Injective := by
      intro s t (h : Exists.choose _ = Exists.choose _)
      ext1; change s.carrier = t.carrier
      rw [(this s).choose_spec]; rw [(this t).choose_spec]; rw [h]
    exact hf.countable

end TopologicalSpace.Clopens
