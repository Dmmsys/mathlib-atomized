/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.Metrizable.Basic

/-!
# Sequences in topological spaces

In this file we prove theorems about relations
between closure/compactness/continuity etc. and their sequential counterparts.

## Main definitions

The following notions are defined in `Topology/Defs/Sequences`.
We build theory about these definitions here, so we remind the definitions.

### Set operation
* `seqClosure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `IsSeqClosed s`: predicate saying that a set is sequentially closed, i.e., `seqClosure s ⊆ s`;
* `SeqContinuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `IsSeqCompact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `FrechetUrysohnSpace X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `SequentialSpace X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `SeqCompactSpace X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Main results

* `seqClosure_subset_closure`: closure of a set includes its sequential closure;
* `IsClosed.isSeqClosed`: a closed set is sequentially closed;
* `IsSeqClosed.seqClosure_eq`: sequential closure of a sequentially closed set `s` is equal
  to `s`;
* `seqClosure_eq_closure`: in a Fréchet-Urysohn space, the sequential closure of a set is equal to
  its closure;
* `tendsto_nhds_iff_seq_tendsto`, `FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`: a topological
  space is a Fréchet-Urysohn space if and only if sequential convergence implies convergence;
* `FirstCountableTopology.frechetUrysohnSpace`: every topological space with
  first countable topology is a Fréchet-Urysohn space;
* `FrechetUrysohnSpace.to_sequentialSpace`: every Fréchet-Urysohn space is a sequential space;
* `IsSeqCompact.isCompact`: a sequentially compact set in a uniform space with countably
  generated uniformity is compact.

## Tags

sequentially closed, sequentially compact, sequential space
-/

public section


open Bornology Filter Function Set TopologicalSpace Topology
open scoped Uniformity

variable {X Y : Type*}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/

section TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

/--
theorem `subset_seqClosure` / 定理 `subset_seqClosure`

English:
theorem subset_seqClosure
  given: {s : Set X}
  statement: s subseteq seqClosure s
  proof: fun p hp =>
  ⟨const Nat p, fun _ => hp, tendsto_const_nhds⟩

中文:
定理 subset_seqClosure
  条件: {s : Set X}
  结论: s subseteq seqClosure s
  证明: fun p hp =>
  ⟨const Nat p, fun _ => hp, tendsto_const_nhds⟩
-/
theorem subset_seqClosure {s : Set X} : s subseteq seqClosure s := fun p hp =>
  ⟨const Nat p, fun _ => hp, tendsto_const_nhds⟩

/--
theorem `seqClosure_subset_closure` / 定理 `seqClosure_subset_closure`

English:
theorem seqClosure_subset_closure
  given: {s : Set X}
  statement: seqClosure s subseteq closure s
  proof: fun _p ⟨_x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)

中文:
定理 seqClosure_subset_closure
  条件: {s : Set X}
  结论: seqClosure s subseteq closure s
  证明: fun _p ⟨_x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)
-/
theorem seqClosure_subset_closure {s : Set X} : seqClosure s subseteq closure s := fun _p ⟨_x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)

/--
theorem `IsSeqClosed.seqClosure_eq` / 定理 `IsSeqClosed.seqClosure_eq`

English:
theorem IsSeqClosed.seqClosure_eq
  given: {s : Set X} (hs : IsSeqClosed s)
  statement: seqClosure s = s
  proof: Subset.antisymm (fun _p ⟨_x, hx, hp⟩ => hs hx hp) subset_seqClosure

中文:
定理 IsSeqClosed.seqClosure_eq
  条件: {s : Set X} (hs : IsSeqClosed s)
  结论: seqClosure s = s
  证明: Subset.antisymm (fun _p ⟨_x, hx, hp⟩ => hs hx hp) subset_seqClosure

Depends on / 依赖: Subset, Subset.antisymm, antisymm, subset_seqClosure
-/
theorem IsSeqClosed.seqClosure_eq {s : Set X} (hs : IsSeqClosed s) : seqClosure s = s :=
  Subset.antisymm (fun _p ⟨_x, hx, hp⟩ => hs hx hp) subset_seqClosure

/--
theorem `isSeqClosed_of_seqClosure_eq` / 定理 `isSeqClosed_of_seqClosure_eq`

English:
theorem isSeqClosed_of_seqClosure_eq
  given: {s : Set X} (hs : seqClosure s = s)
  statement: IsSeqClosed s
  proof: fun x _p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩

中文:
定理 isSeqClosed_of_seqClosure_eq
  条件: {s : Set X} (hs : seqClosure s = s)
  结论: IsSeqClosed s
  证明: fun x _p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩
-/
theorem isSeqClosed_of_seqClosure_eq {s : Set X} (hs : seqClosure s = s) : IsSeqClosed s :=
  fun x _p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩

/--
theorem `isSeqClosed_iff` / 定理 `isSeqClosed_iff`

English:
theorem isSeqClosed_iff
  given: {s : Set X}
  statement: IsSeqClosed s ↔ seqClosure s = s
  proof: ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩

中文:
定理 isSeqClosed_iff
  条件: {s : Set X}
  结论: IsSeqClosed s ↔ seqClosure s = s
  证明: ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩

Depends on / 依赖: IsSeqClosed, IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq, seqClosure_eq
-/
theorem isSeqClosed_iff {s : Set X} : IsSeqClosed s ↔ seqClosure s = s :=
  ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩

/--
theorem `IsClosed.isSeqClosed` / 定理 `IsClosed.isSeqClosed`

English:
theorem IsClosed.isSeqClosed
  given: {s : Set X} (hc : IsClosed s)
  statement: IsSeqClosed s
  proof: fun _u _x hu hx => hc.mem_of_tendsto hx (Eventually.of_forall hu)

中文:
定理 IsClosed.isSeqClosed
  条件: {s : Set X} (hc : IsClosed s)
  结论: IsSeqClosed s
  证明: fun _u _x hu hx => hc.mem_of_tendsto hx (Eventually.of_forall hu)
-/
protected theorem IsClosed.isSeqClosed {s : Set X} (hc : IsClosed s) : IsSeqClosed s :=
  fun _u _x hu hx => hc.mem_of_tendsto hx (Eventually.of_forall hu)

/--
theorem `seqClosure_eq_closure` / 定理 `seqClosure_eq_closure`

English:
theorem seqClosure_eq_closure
  given: [FrechetUrysohnSpace X] (s : Set X)
  statement: seqClosure s = closure s
  proof: seqClosure_subset_closure.antisymm FrechetUrysohnSpace.closure_subset_seqClosure s

中文:
定理 seqClosure_eq_closure
  条件: [FrechetUrysohnSpace X] (s : Set X)
  结论: seqClosure s = closure s
  证明: seqClosure_subset_closure.antisymm FrechetUrysohnSpace.closure_subset_seqClosure s

Depends on / 依赖: FrechetUrysohnSpace, FrechetUrysohnSpace.closure_subset_seqClosure, antisymm, closure_subset_seqClosure, seqClosure_subset_closure, seqClosure_subset_closure.antisymm
-/
theorem seqClosure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : seqClosure s = closure s :=
seqClosure_subset_closure.antisymm FrechetUrysohnSpace.closure_subset_seqClosure s

/--
theorem `mem_closure_iff_seq_limit` / 定理 `mem_closure_iff_seq_limit`

English:
theorem mem_closure_iff_seq_limit
  given: [FrechetUrysohnSpace X] {s : Set X} {a : X}
  proof: by
  rw [← seqClosure_eq_closure]
  rfl

中文:
定理 mem_closure_iff_seq_limit
  条件: [FrechetUrysohnSpace X] {s : Set X} {a : X}
  证明: by
  rw [← seqClosure_eq_closure]
  rfl

Depends on / 依赖: seqClosure_eq_closure
-/
theorem mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a in closure s ↔ exists x : Nat -> X, (forall n : Nat, x n in s) ∧ Tendsto x atTop (𝓝 a) := by
  rw [← seqClosure_eq_closure]
  rfl

/--
theorem `tendsto_nhds_iff_seq_tendsto` / 定理 `tendsto_nhds_iff_seq_tendsto`

English:
theorem tendsto_nhds_iff_seq_tendsto
  given: [FrechetUrysohnSpace X] {f : X -> Y} {a : X} {b : Y}
  proof: by
  refine
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 ?_⟩
  rintro s ⟨hbs, hsc⟩
  refine ⟨closure (f ⁻¹' s), ⟨mt ?_ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩

中文:
定理 tendsto_nhds_iff_seq_tendsto
  条件: [FrechetUrysohnSpace X] {f : X -> Y} {a : X} {b : Y}
  证明: by
  refine
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 ?_⟩
  rintro s ⟨hbs, hsc⟩
  refine ⟨closure (f ⁻¹' s), ⟨mt ?_ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩

Depends on / 依赖: Eventually, Eventually.of_forall, closure, hf.comp, hsc.mem_of_tendsto, isClosed_closure, mem_of_tendsto, nhds_basis_closeds, of_forall, seqClosure_eq_closure, subset_closure, tendsto_iff
-/
theorem tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X -> Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ forall u : Nat -> X, Tendsto u atTop (𝓝 a) -> Tendsto (f ∘ u) atTop (𝓝 b) := by
  refine
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 ?_⟩
  rintro s ⟨hbs, hsc⟩
  refine ⟨closure (f ⁻¹' s), ⟨mt ?_ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩
  exact hsc.mem_of_tendsto (h u hu) (Eventually.of_forall hus)

/--
theorem `FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto` / 定理 `FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`

English:
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
  proof: by
  refine ⟨fun s x hcx => ?_⟩
  by_cases hx : x in s
  · exact subset_seqClosure hx
  · obtain ⟨u, hux, hus⟩ : exists u : Nat -> X, Tendsto u atTop (𝓝 x) ∧ existsᶠ x in atTop, u x in s := by
      simpa only [ContinuousAt, hx, tendsto_nhds_true, (· ∘ ·), ← not_frequently, exists_prop,
        ← me

中文:
定理 FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
  证明: by
  refine ⟨fun s x hcx => ?_⟩
  by_cases hx : x in s
  · exact subset_seqClosure hx
  · obtain ⟨u, hux, hus⟩ : exists u : Nat -> X, Tendsto u atTop (𝓝 x) ∧ existsᶠ x in atTop, u x in s := by
      simpa only [ContinuousAt, hx, tendsto_nhds_true, (· ∘ ·), ← not_frequently, exists_prop,
        ← me

Depends on / 依赖: ContinuousAt, Tendsto, _mono.tendst, exists_prop, extraction_of_frequently_atTop, hux.comp, imp_false, mem_closure_iff_frequently, not_false_eq_true, not_forall, not_frequently, not_not, not_true_eq_false, subset_seqClosure, tendst, tendsto_nhds_true
-/
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
    (h : forall (f : X -> Prop) (a : X),
      (forall u : Nat -> X, Tendsto u atTop (𝓝 a) -> Tendsto (f ∘ u) atTop (𝓝 (f a))) -> ContinuousAt f a) :
    FrechetUrysohnSpace X := by
  refine ⟨fun s x hcx => ?_⟩
  by_cases hx : x in s
  · exact subset_seqClosure hx
  · obtain ⟨u, hux, hus⟩ : exists u : Nat -> X, Tendsto u atTop (𝓝 x) ∧ existsᶠ x in atTop, u x in s := by
      simpa only [ContinuousAt, hx, tendsto_nhds_true, (· ∘ ·), ← not_frequently, exists_prop,
        ← mem_closure_iff_frequently, hcx, imp_false, not_forall, not_not, not_false_eq_true,
        not_true_eq_false] using h (· ∉ s) x
    rcases extraction_of_frequently_atTop hus with ⟨φ, φ_mono, hφ⟩
    exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_atTop⟩

-- see Note [lower instance priority]
/-- Every first-countable space is a Fréchet-Urysohn space. -/
instance (priority := 100) FirstCountableTopology.frechetUrysohnSpace
    [FirstCountableTopology X] : FrechetUrysohnSpace X :=
  FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto fun _ _ => tendsto_iff_seq_tendsto.2

-- see Note [lower instance priority]
/-- Every Fréchet-Urysohn space is a sequential space. -/
instance (priority := 100) FrechetUrysohnSpace.to_sequentialSpace [FrechetUrysohnSpace X] :
    SequentialSpace X :=
  ⟨fun s hs => by rw [← closure_eq_iff_isClosed, ← seqClosure_eq_closure, hs.seqClosure_eq]⟩

/--
theorem `Topology.IsInducing.frechetUrysohnSpace` / 定理 `Topology.IsInducing.frechetUrysohnSpace`

English:
theorem Topology.IsInducing.frechetUrysohnSpace
  statement: [FrechetUrysohnSpace Y] {f : X -> Y}
  proof: by
  refine ⟨fun s x hx => ?_⟩
  rw [hf.closure_eq_preimage_closure_image]; rw [mem_preimage]; rw [mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hus, hu⟩
  choose v hv hvu using hus
  refine ⟨v, hv, ?_⟩
  simpa only [hf.tendsto_nhds_iff, Function.comp_def, hvu]

中文:
定理 Topology.IsInducing.frechetUrysohnSpace
  结论: [FrechetUrysohnSpace Y] {f : X -> Y}
  证明: by
  refine ⟨fun s x hx => ?_⟩
  rw [hf.closure_eq_preimage_closure_image]; rw [mem_preimage]; rw [mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hus, hu⟩
  choose v hv hvu using hus
  refine ⟨v, hv, ?_⟩
  simpa only [hf.tendsto_nhds_iff, Function.comp_def, hvu]

Depends on / 依赖: Function, Function.comp_def, closure_eq_preimage_closure_image, comp_def, hf.closure_eq_preimage_closure_image, hf.tendsto_nhds_iff, mem_closure_iff_seq_limit, mem_preimage, tendsto_nhds_iff
-/
theorem Topology.IsInducing.frechetUrysohnSpace [FrechetUrysohnSpace Y] {f : X -> Y}
    (hf : IsInducing f) : FrechetUrysohnSpace X := by
  refine ⟨fun s x hx => ?_⟩
  rw [hf.closure_eq_preimage_closure_image]; rw [mem_preimage]; rw [mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hus, hu⟩
  choose v hv hvu using hus
  refine ⟨v, hv, ?_⟩
  simpa only [hf.tendsto_nhds_iff, Function.comp_def, hvu]

/--
Instance `Subtype.instFrechetUrysohnSpace` / 实例 `Subtype.instFrechetUrysohnSpace`

English:
instance Subtype.instFrechetUrysohnSpace
  signature: [FrechetUrysohnSpace X] {p : X -> Prop}
  body: IsInducing.subtypeVal.frechetUrysohnSpace

中文:
实例 Subtype.instFrechetUrysohnSpace
  签名: [FrechetUrysohnSpace X] {p : X -> 命题}
  定义体: IsInducing.subtypeVal.frechetUrysohnSpace

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.frechetUrysohnSpace, frechetUrysohnSpace, subtypeVal
-/
instance Subtype.instFrechetUrysohnSpace [FrechetUrysohnSpace X] {p : X -> Prop} :
    FrechetUrysohnSpace (Subtype p) :=
  IsInducing.subtypeVal.frechetUrysohnSpace

/--
theorem `isSeqClosed_iff_isClosed` / 定理 `isSeqClosed_iff_isClosed`

English:
theorem isSeqClosed_iff_isClosed
  given: [SequentialSpace X] {M : Set X}
  statement: IsSeqClosed M ↔ IsClosed M
  proof: ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩

中文:
定理 isSeqClosed_iff_isClosed
  条件: [SequentialSpace X] {M : Set X}
  结论: IsSeqClosed M ↔ IsClosed M
  证明: ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩

Depends on / 依赖: IsClosed, IsClosed.isSeqClosed, IsSeqClosed, IsSeqClosed.isClosed, isClosed, isSeqClosed
-/
theorem isSeqClosed_iff_isClosed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔ IsClosed M :=
  ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩

/--
lemma `isClosed_iUnion_closure_singleton_of_not_tendsto` / 引理 `isClosed_iUnion_closure_singleton_of_not_tendsto`

English:
lemma isClosed_iUnion_closure_singleton_of_not_tendsto
  statement: {x : Nat -> X} [SequentialSpace X]
  proof: by
  refine IsSeqClosed.isClosed fun y l hy hy' => ?_
  by_cases! hm : exists m, existsᶠ n in atTop, y n in closure {x m}
  · obtain ⟨m, pm⟩ := hm
    exact subset_iUnion _ m (isClosed_closure.mem_of_frequently_of_tendsto pm hy')
  · have (j : Nat) : existsᶠ k in atTop, exists n >= j, y n in closure

中文:
引理 isClosed_iUnion_closure_singleton_of_not_tendsto
  结论: {x : 自然数 -> X} [SequentialSpace X]
  证明: by
  refine IsSeqClosed.isClosed fun y l hy hy' => ?_
  by_cases! hm : exists m, existsᶠ n in atTop, y n in closure {x m}
  · obtain ⟨m, pm⟩ := hm
    exact subset_iUnion _ m (isClosed_closure.mem_of_frequently_of_tendsto pm hy')
  · have (j : Nat) : existsᶠ k in atTop, exists n >= j, y n in closure

Depends on / 依赖: Filter, Filter.eventually_all_finite, Finite, IsSeqClosed, IsSeqClosed.isClosed, closure, eventually_all_finite, eventually_atTop, frequently_atTop, isClosed, isClosed_closure, isClosed_closure.mem_of_frequently_of_tendsto, mem_Iic, mem_of_frequently_of_tendsto, subset_iUnion
-/
lemma isClosed_iUnion_closure_singleton_of_not_tendsto {x : Nat -> X} [SequentialSpace X]
    (hx : forall (l : X) (φ : Nat -> Nat), StrictMono φ -> ¬Tendsto (x ∘ φ) atTop (𝓝 l)) :
    IsClosed (⋃ i, closure {x i}) := by
  refine IsSeqClosed.isClosed fun y l hy hy' => ?_
  by_cases! hm : exists m, existsᶠ n in atTop, y n in closure {x m}
  · obtain ⟨m, pm⟩ := hm
    exact subset_iUnion _ m (isClosed_closure.mem_of_frequently_of_tendsto pm hy')
  · have (j : Nat) : existsᶠ k in atTop, exists n >= j, y n in closure {x k} := by
      refine frequently_atTop.2 fun a => ?_
      have := (Filter.eventually_all_finite (by simp : (Iic a).Finite)).2 fun i hi => hm i
      simp only [mem_Iic, eventually_atTop] at this
      obtain ⟨c, hc⟩ := this
      obtain ⟨b, hb⟩ := mem_iUnion.1 (hy (c + j))
      refine ⟨b, ?_, c + j, j.le_add_left c, hb⟩
      by_contra! hab
      simp_all [hc (c + j) (c.le_add_right j) b hab.le]
    obtain ⟨φ, hφ⟩ := extraction_forall_of_frequently this
    choose ψ hψ1 hψ2 using hφ.2
    have : Tendsto ψ atTop atTop := tendsto_atTop_mono hψ1 tendsto_id
    refine (hx l φ hφ.1 (Tendsto.specializes (hy'.comp this) (fun n => ?_))).elim
    exact specializes_iff_mem_closure.2 (hψ2 n)

/--
lemma `isClosed_range_of_not_tendsto` / 引理 `isClosed_range_of_not_tendsto`

English:
lemma isClosed_range_of_not_tendsto
  statement: {x : Nat -> X} [SequentialSpace X] [T1Space X]
  proof: by
  simpa using isClosed_iUnion_closure_singleton_of_not_tendsto hx

中文:
引理 isClosed_range_of_not_tendsto
  结论: {x : 自然数 -> X} [SequentialSpace X] [T1Space X]
  证明: by
  simpa using isClosed_iUnion_closure_singleton_of_not_tendsto hx

Depends on / 依赖: isClosed_iUnion_closure_singleton_of_not_tendsto
-/
lemma isClosed_range_of_not_tendsto {x : Nat -> X} [SequentialSpace X] [T1Space X]
    (hx : forall (l : X) (φ : Nat -> Nat), StrictMono φ -> ¬Tendsto (x ∘ φ) atTop (𝓝 l)) :
    IsClosed (range x) := by
  simpa using isClosed_iUnion_closure_singleton_of_not_tendsto hx

/--
theorem `IsSeqClosed.preimage` / 定理 `IsSeqClosed.preimage`

English:
theorem IsSeqClosed.preimage
  given: {f : X -> Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f)
  proof: fun _x _p hx hp => hs hx (hf hp)

中文:
定理 IsSeqClosed.preimage
  条件: {f : X -> Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f)
  证明: fun _x _p hx hp => hs hx (hf hp)
-/
theorem IsSeqClosed.preimage {f : X -> Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f) :
    IsSeqClosed (f ⁻¹' s) := fun _x _p hx hp => hs hx (hf hp)

-- A continuous function is sequentially continuous.
/--
theorem `Continuous.seqContinuous` / 定理 `Continuous.seqContinuous`

English:
theorem Continuous.seqContinuous
  given: {f : X -> Y} (hf : Continuous f)
  statement: SeqContinuous f
  proof: fun _x p hx => (hf.tendsto p).comp hx

中文:
定理 Continuous.seqContinuous
  条件: {f : X -> Y} (hf : Continuous f)
  结论: SeqContinuous f
  证明: fun _x p hx => (hf.tendsto p).comp hx
-/
protected theorem Continuous.seqContinuous {f : X -> Y} (hf : Continuous f) : SeqContinuous f :=
  fun _x p hx => (hf.tendsto p).comp hx

/--
theorem `SeqContinuous.continuous` / 定理 `SeqContinuous.continuous`

English:
theorem SeqContinuous.continuous
  given: [SequentialSpace X] {f : X -> Y} (hf : SeqContinuous f)
  proof: continuous_iff_isClosed.mpr fun _s hs => (hs.isSeqClosed.preimage hf).isClosed

中文:
定理 SeqContinuous.continuous
  条件: [SequentialSpace X] {f : X -> Y} (hf : SeqContinuous f)
  证明: continuous_iff_isClosed.mpr fun _s hs => (hs.isSeqClosed.preimage hf).isClosed
-/
protected theorem SeqContinuous.continuous [SequentialSpace X] {f : X -> Y} (hf : SeqContinuous f) :
    Continuous f :=
  continuous_iff_isClosed.mpr fun _s hs => (hs.isSeqClosed.preimage hf).isClosed

/--
theorem `continuous_iff_seqContinuous` / 定理 `continuous_iff_seqContinuous`

English:
theorem continuous_iff_seqContinuous
  given: [SequentialSpace X] {f : X -> Y}
  proof: ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩

中文:
定理 continuous_iff_seqContinuous
  条件: [SequentialSpace X] {f : X -> Y}
  证明: ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩

Depends on / 依赖: Continuous, Continuous.seqContinuous, SeqContinuous, SeqContinuous.continuous, continuous, seqContinuous
-/
theorem continuous_iff_seqContinuous [SequentialSpace X] {f : X -> Y} :
    Continuous f ↔ SeqContinuous f :=
  ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩

/--
theorem `SequentialSpace.coinduced` / 定理 `SequentialSpace.coinduced`

English:
theorem SequentialSpace.coinduced
  given: [SequentialSpace X] {Y} (f : X -> Y)
  proof: letI : TopologicalSpace Y := .coinduced f ‹_›
  ⟨fun _ hs => isClosed_coinduced.2 (hs.preimage continuous_coinduced_rng.seqContinuous).isClosed⟩

中文:
定理 SequentialSpace.coinduced
  条件: [SequentialSpace X] {Y} (f : X -> Y)
  证明: letI : TopologicalSpace Y := .coinduced f ‹_›
  ⟨fun _ hs => isClosed_coinduced.2 (hs.preimage continuous_coinduced_rng.seqContinuous).isClosed⟩

Depends on / 依赖: TopologicalSpace, coinduced, continuous_coinduced_rng, continuous_coinduced_rng.seqContinuous, hs.preimage, isClosed, isClosed_coinduced, preimage, seqContinuous
-/
theorem SequentialSpace.coinduced [SequentialSpace X] {Y} (f : X -> Y) :
    @SequentialSpace Y (.coinduced f ‹_›) :=
  letI : TopologicalSpace Y := .coinduced f ‹_›
  ⟨fun _ hs => isClosed_coinduced.2 (hs.preimage continuous_coinduced_rng.seqContinuous).isClosed⟩

/--
theorem `SequentialSpace.iSup` / 定理 `SequentialSpace.iSup`

English:
theorem SequentialSpace.iSup
  statement: {X} {ι : Sort*} {t : ι -> TopologicalSpace X}
  proof: by
  let : TopologicalSpace X := ⨆ i, t i
  refine ⟨fun s hs => isClosed_iSup_iff.2 fun i => ?_⟩
  let := t i
exact IsSeqClosed.isClosed fun u x hus hux => hs hus hux.mono_right nhds_mono le_iSup _ _

中文:
定理 SequentialSpace.iSup
  结论: {X} {ι : Sort*} {t : ι -> TopologicalSpace X}
  证明: by
  let : TopologicalSpace X := ⨆ i, t i
  refine ⟨fun s hs => isClosed_iSup_iff.2 fun i => ?_⟩
  let := t i
exact IsSeqClosed.isClosed fun u x hus hux => hs hus hux.mono_right nhds_mono le_iSup _ _
-/
protected theorem SequentialSpace.iSup {X} {ι : Sort*} {t : ι -> TopologicalSpace X}
    (h : forall i, @SequentialSpace X (t i)) : @SequentialSpace X (⨆ i, t i) := by
  let : TopologicalSpace X := ⨆ i, t i
  refine ⟨fun s hs => isClosed_iSup_iff.2 fun i => ?_⟩
  let := t i
exact IsSeqClosed.isClosed fun u x hus hux => hs hus hux.mono_right nhds_mono le_iSup _ _

/--
theorem `SequentialSpace.sup` / 定理 `SequentialSpace.sup`

English:
theorem SequentialSpace.sup
  statement: {X} {t₁ t₂ : TopologicalSpace X}
  proof: by
  rw [sup_eq_iSup]
exact .iSup Bool.forall_bool.2 ⟨h₂, h₁⟩

中文:
定理 SequentialSpace.sup
  结论: {X} {t₁ t₂ : TopologicalSpace X}
  证明: by
  rw [sup_eq_iSup]
exact .iSup Bool.forall_bool.2 ⟨h₂, h₁⟩
-/
protected theorem SequentialSpace.sup {X} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @SequentialSpace X t₁) (h₂ : @SequentialSpace X t₂) :
    @SequentialSpace X (t₁ ⊔ t₂) := by
  rw [sup_eq_iSup]
exact .iSup Bool.forall_bool.2 ⟨h₂, h₁⟩

/--
lemma `Topology.IsQuotientMap.sequentialSpace` / 引理 `Topology.IsQuotientMap.sequentialSpace`

English:
lemma Topology.IsQuotientMap.sequentialSpace
  statement: [SequentialSpace X] {f : X -> Y}
  proof: hf.isCoinducing.eq_coinduced.symm ▸ .coinduced f

中文:
引理 Topology.IsQuotientMap.sequentialSpace
  结论: [SequentialSpace X] {f : X -> Y}
  证明: hf.isCoinducing.eq_coinduced.symm ▸ .coinduced f

Depends on / 依赖: coinduced, eq_coinduced, hf.isCoinducing.eq_coinduced.symm, isCoinducing
-/
lemma Topology.IsQuotientMap.sequentialSpace [SequentialSpace X] {f : X -> Y}
    (hf : IsQuotientMap f) : SequentialSpace Y := hf.isCoinducing.eq_coinduced.symm ▸ .coinduced f

/--
Instance `Quotient.instSequentialSpace` / 实例 `Quotient.instSequentialSpace`

English:
instance Quotient.instSequentialSpace
  signature: [SequentialSpace X] {s : Setoid X}
  body: isQuotientMap_quot_mk.sequentialSpace

中文:
实例 Quotient.instSequentialSpace
  签名: [SequentialSpace X] {s : Setoid X}
  定义体: isQuotientMap_quot_mk.sequentialSpace

Depends on / 依赖: isQuotientMap_quot_mk, isQuotientMap_quot_mk.sequentialSpace, sequentialSpace
-/
instance Quotient.instSequentialSpace [SequentialSpace X] {s : Setoid X} :
    SequentialSpace (Quotient s) :=
  isQuotientMap_quot_mk.sequentialSpace

/--
Instance `Sum.instSequentialSpace` / 实例 `Sum.instSequentialSpace`

English:
instance Sum.instSequentialSpace
  signature: [SequentialSpace X] [SequentialSpace Y]
  body: .sup (.coinduced Sum.inl) (.coinduced Sum.inr)

中文:
实例 Sum.instSequentialSpace
  签名: [SequentialSpace X] [SequentialSpace Y]
  定义体: .sup (.coinduced Sum.inl) (.coinduced Sum.inr)

Depends on / 依赖: Sum.inl, Sum.inr, coinduced
-/
instance Sum.instSequentialSpace [SequentialSpace X] [SequentialSpace Y] :
    SequentialSpace (X oplus Y) :=
  .sup (.coinduced Sum.inl) (.coinduced Sum.inr)

/--
Instance `Sigma.instSequentialSpace` / 实例 `Sigma.instSequentialSpace`

English:
instance Sigma.instSequentialSpace
  signature: {ι : Type*} {X : ι -> Type*}
  body: .iSup fun _ => .coinduced _

中文:
实例 Sigma.instSequentialSpace
  签名: {ι : 类型} {X : ι -> 类型}
  定义体: .iSup fun _ => .coinduced _

Depends on / 依赖: coinduced
-/
instance Sigma.instSequentialSpace {ι : Type*} {X : ι -> Type*}
    [forall i, TopologicalSpace (X i)] [forall i, SequentialSpace (X i)] : SequentialSpace (Σ i, X i) :=
  .iSup fun _ => .coinduced _

end TopologicalSpace

section SeqCompact

open TopologicalSpace FirstCountableTopology

variable [TopologicalSpace X]

/--
theorem `IsSeqCompact.subseq_of_frequently_in` / 定理 `IsSeqCompact.subseq_of_frequently_in`

English:
theorem IsSeqCompact.subseq_of_frequently_in
  statement: {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X}
  proof: let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

中文:
定理 IsSeqCompact.subseq_of_frequently_in
  结论: {s : Set X} (hs : IsSeqCompact s) {x : 自然数 -> X}
  证明: let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

Depends on / 依赖: a_in, extraction_of_frequently_atTop
-/
theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X}
    (hx : existsᶠ n in atTop, x n in s) :
    exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

/--
theorem `SeqCompactSpace.tendsto_subseq` / 定理 `SeqCompactSpace.tendsto_subseq`

English:
theorem SeqCompactSpace.tendsto_subseq
  given: [SeqCompactSpace X] (x : Nat -> X)
  proof: let ⟨a, _, φ, mono, h⟩ := isSeqCompact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

中文:
定理 SeqCompactSpace.tendsto_subseq
  条件: [SeqCompactSpace X] (x : 自然数 -> X)
  证明: let ⟨a, _, φ, mono, h⟩ := isSeqCompact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

Depends on / 依赖: isSeqCompact_univ, mem_univ
-/
theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : Nat -> X) :
    exists (a : X) (φ : Nat -> Nat), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨a, _, φ, mono, h⟩ := isSeqCompact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

section FirstCountableTopology

variable [FirstCountableTopology X]

open FirstCountableTopology

/--
theorem `IsCompact.isSeqCompact` / 定理 `IsCompact.isSeqCompact`

English:
theorem IsCompact.isSeqCompact
  given: {s : Set X} (hs : IsCompact s)
  statement: IsSeqCompact s
  proof: fun _x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (Eventually.of_forall x_in))
  ⟨a, a_in, MapClusterPt.tendsto_subseq ha⟩

中文:
定理 IsCompact.isSeqCompact
  条件: {s : Set X} (hs : IsCompact s)
  结论: IsSeqCompact s
  证明: fun _x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (Eventually.of_forall x_in))
  ⟨a, a_in, MapClusterPt.tendsto_subseq ha⟩
-/
protected theorem IsCompact.isSeqCompact {s : Set X} (hs : IsCompact s) : IsSeqCompact s :=
  fun _x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (Eventually.of_forall x_in))
  ⟨a, a_in, MapClusterPt.tendsto_subseq ha⟩

/--
theorem `IsCompact.tendsto_subseq'` / 定理 `IsCompact.tendsto_subseq'`

English:
theorem IsCompact.tendsto_subseq'
  statement: {s : Set X} {x : Nat -> X} (hs : IsCompact s)
  proof: hs.isSeqCompact.subseq_of_frequently_in hx

中文:
定理 IsCompact.tendsto_subseq'
  结论: {s : Set X} {x : 自然数 -> X} (hs : IsCompact s)
  证明: hs.isSeqCompact.subseq_of_frequently_in hx

Depends on / 依赖: hs.isSeqCompact.subseq_of_frequently_in, isSeqCompact, subseq_of_frequently_in
-/
theorem IsCompact.tendsto_subseq' {s : Set X} {x : Nat -> X} (hs : IsCompact s)
    (hx : existsᶠ n in atTop, x n in s) :
    exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact.subseq_of_frequently_in hx

/--
theorem `IsCompact.tendsto_subseq` / 定理 `IsCompact.tendsto_subseq`

English:
theorem IsCompact.tendsto_subseq
  given: {s : Set X} {x : Nat -> X} (hs : IsCompact s) (hx : forall n, x n in s)
  proof: hs.isSeqCompact hx

中文:
定理 IsCompact.tendsto_subseq
  条件: {s : Set X} {x : 自然数 -> X} (hs : IsCompact s) (hx : 对任意 n, x n in s)
  证明: hs.isSeqCompact hx

Depends on / 依赖: hs.isSeqCompact, isSeqCompact
-/
theorem IsCompact.tendsto_subseq {s : Set X} {x : Nat -> X} (hs : IsCompact s) (hx : forall n, x n in s) :
    exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact hx

-- see Note [lower instance priority]
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] :
    SeqCompactSpace X :=
  ⟨isCompact_univ.isSeqCompact⟩

/--
theorem `CompactSpace.tendsto_subseq` / 定理 `CompactSpace.tendsto_subseq`

English:
theorem CompactSpace.tendsto_subseq
  given: [CompactSpace X] (x : Nat -> X)
  proof: SeqCompactSpace.tendsto_subseq x

中文:
定理 CompactSpace.tendsto_subseq
  条件: [CompactSpace X] (x : 自然数 -> X)
  证明: SeqCompactSpace.tendsto_subseq x

Depends on / 依赖: SeqCompactSpace, SeqCompactSpace.tendsto_subseq, tendsto_subseq
-/
theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : Nat -> X) :
    exists (a : _) (φ : Nat -> Nat), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  SeqCompactSpace.tendsto_subseq x

end FirstCountableTopology

section Image

variable [TopologicalSpace Y] {f : X -> Y}

/--
theorem `IsSeqCompact.image` / 定理 `IsSeqCompact.image`

English:
theorem IsSeqCompact.image
  given: (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K)
  proof: by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using ys_in_fK
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨f a, mem_image_of_mem f a_in_K, phi, phi_mono, ?_⟩
  exact (f_cont xs_phi_lim).congr fun x => fxs_eq_ys (phi x)

中文:
定理 IsSeqCompact.image
  条件: (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K)
  证明: by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using ys_in_fK
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨f a, mem_image_of_mem f a_in_K, phi, phi_mono, ?_⟩
  exact (f_cont xs_phi_lim).congr fun x => fxs_eq_ys (phi x)

Depends on / 依赖: K_cpt, a_in_K, f_cont, fxs_eq_ys, mem_image_of_mem, phi_mono, xs_in_K, xs_phi_lim, ys_in_fK
-/
theorem IsSeqCompact.image (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
    IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using ys_in_fK
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨f a, mem_image_of_mem f a_in_K, phi, phi_mono, ?_⟩
  exact (f_cont xs_phi_lim).congr fun x => fxs_eq_ys (phi x)

/--
theorem `IsSeqCompact.range` / 定理 `IsSeqCompact.range`

English:
theorem IsSeqCompact.range
  given: [SeqCompactSpace X] (f_cont : SeqContinuous f)
  proof: by
  simpa using isSeqCompact_univ.image f_cont

中文:
定理 IsSeqCompact.range
  条件: [SeqCompactSpace X] (f_cont : SeqContinuous f)
  证明: by
  simpa using isSeqCompact_univ.image f_cont

Depends on / 依赖: f_cont, isSeqCompact_univ, isSeqCompact_univ.image
-/
theorem IsSeqCompact.range [SeqCompactSpace X] (f_cont : SeqContinuous f) :
    IsSeqCompact (Set.range f) := by
  simpa using isSeqCompact_univ.image f_cont

end Image

end SeqCompact

section UniformSpaceSeqCompact

open uniformity

open UniformSpace Prod

variable [UniformSpace X] {s : Set X}

/--
theorem `IsSeqCompact.exists_tendsto_of_frequently_mem` / 定理 `IsSeqCompact.exists_tendsto_of_frequently_mem`

English:
theorem IsSeqCompact.exists_tendsto_of_frequently_mem
  statement: (hs : IsSeqCompact s) {u : Nat -> X}
  proof: let ⟨x, hxs, _φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩

中文:
定理 IsSeqCompact.exists_tendsto_of_frequently_mem
  结论: (hs : IsSeqCompact s) {u : 自然数 -> X}
  证明: let ⟨x, hxs, _φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩

Depends on / 依赖: _mono.tendsto_atTop, hs.subseq_of_frequently_in, subseq_of_frequently_in, tendsto_atTop, tendsto_nhds_of_cauchySeq_of_subseq
-/
theorem IsSeqCompact.exists_tendsto_of_frequently_mem (hs : IsSeqCompact s) {u : Nat -> X}
    (hu : existsᶠ n in atTop, u n in s) (huc : CauchySeq u) : exists x in s, Tendsto u atTop (𝓝 x) :=
  let ⟨x, hxs, _φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩

/--
theorem `IsSeqCompact.exists_tendsto` / 定理 `IsSeqCompact.exists_tendsto`

English:
theorem IsSeqCompact.exists_tendsto
  statement: (hs : IsSeqCompact s) {u : Nat -> X} (hu : forall n, u n in s)
  proof: hs.exists_tendsto_of_frequently_mem (Frequently.of_forall hu) huc

中文:
定理 IsSeqCompact.exists_tendsto
  结论: (hs : IsSeqCompact s) {u : 自然数 -> X} (hu : 对任意 n, u n in s)
  证明: hs.exists_tendsto_of_frequently_mem (Frequently.of_forall hu) huc

Depends on / 依赖: Frequently, Frequently.of_forall, exists_tendsto_of_frequently_mem, hs.exists_tendsto_of_frequently_mem, of_forall
-/
theorem IsSeqCompact.exists_tendsto (hs : IsSeqCompact s) {u : Nat -> X} (hu : forall n, u n in s)
    (huc : CauchySeq u) : exists x in s, Tendsto u atTop (𝓝 x) :=
  hs.exists_tendsto_of_frequently_mem (Frequently.of_forall hu) huc

/--
theorem `IsSeqCompact.totallyBounded` / 定理 `IsSeqCompact.totallyBounded`

English:
theorem IsSeqCompact.totallyBounded
  given: (h : IsSeqCompact s)
  statement: TotallyBounded s
  proof: by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : exists u : Nat -> X, (forall n, u n in s) ∧ forall n m, m < n -> u m ∉ ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and]

中文:
定理 IsSeqCompact.totallyBounded
  条件: (h : IsSeqCompact s)
  结论: TotallyBounded s
  证明: by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : exists u : Nat -> X, (forall n, u n in s) ∧ forall n m, m < n -> u m ∉ ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and]
-/
protected theorem IsSeqCompact.totallyBounded (h : IsSeqCompact s) : TotallyBounded s := by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : exists u : Nat -> X, (forall n, u n in s) ∧ forall n m, m < n -> u m ∉ ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
  refine ⟨u, u_in, fun x _ φ hφ huφ => ?_⟩
  obtain ⟨N, hN⟩ : exists N, forall p q, p >= N -> q >= N -> (u (φ p), u (φ q)) in V :=
    huφ.cauchySeq.mem_entourage V_in
  exact hu (φ <| N + 1) (φ N) (hφ <| Nat.lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)

variable [IsCountablyGenerated (𝓤 X)]

/--
theorem `IsSeqCompact.isComplete` / 定理 `IsSeqCompact.isComplete`

English:
theorem IsSeqCompact.isComplete
  given: (hs : IsSeqCompact s)
  statement: IsComplete s
  proof: fun l hl hls => by
  have := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : forall n, W n subseteq V n := fun n ⟨x, y⟩ hx =>
@hWV n (x, y) ⟨x, refl_mem_uniformity hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩

中文:
定理 IsSeqCompact.isComplete
  条件: (hs : IsSeqCompact s)
  结论: IsComplete s
  证明: fun l hl hls => by
  have := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : forall n, W n subseteq V n := fun n ⟨x, y⟩ hx =>
@hWV n (x, y) ⟨x, refl_mem_uniformity hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩
-/
protected theorem IsSeqCompact.isComplete (hs : IsSeqCompact s) : IsComplete s := fun l hl hls => by
  have := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : forall n, W n subseteq V n := fun n ⟨x, y⟩ hx =>
@hWV n (x, y) ⟨x, refl_mem_uniformity hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩ :
      exists t : Nat -> Set X, Antitone t ∧ (forall n, t n in l) ∧ (forall n, t n ×ˢ t n subseteq W n) ∧ forall n, t n subseteq s := by
    have : forall n, exists t in l, t ×ˢ t subseteq W n ∧ t subseteq s := by
      rw [le_principal_iff] at hls
      have : forall n, W n inter s ×ˢ s in l ×ˢ l := fun n => inter_mem (hl.2 (hW n)) (prod_mem_prod hls hls)
      simpa only [l.basis_sets.prod_self.mem_iff, true_imp_iff, subset_inter_iff,
        prod_self_subset_prod_self, and_assoc] using! this
    choose t htl htW hts using this
    have : forall n : Nat, ⋂ k <= n, t k subseteq t n := fun n => by apply iInter₂_subset; rfl
    exact ⟨fun n => ⋂ k <= n, t k, fun m n h =>
      biInter_subset_biInter_left fun k (hk : k <= m) => hk.trans h, fun n =>
      (biInter_mem (finite_le_nat n)).2 fun k _ => htl k, fun n =>
      (prod_mono (this n) (this n)).trans (htW n), fun n => (this n).trans (hts n)⟩
  choose u hu using fun n => Filter.nonempty_of_mem (htl n)
  have huc : CauchySeq u := hV.toHasBasis.cauchySeq_iff.2 fun N _ =>
⟨N, fun m hm n hn => hWV' _ @htW N (_, _) ⟨ht_anti hm (hu _), ht_anti hn (hu _)⟩⟩
  rcases hs.exists_tendsto (fun n => hts n (hu n)) huc with ⟨x, hxs, hx⟩
  refine ⟨x, hxs, (nhds_basis_uniformity' hV.toHasBasis).ge_iff.2 fun N _ => ?_⟩
  obtain ⟨n, hNn, hn⟩ : exists n, N <= n ∧ u n in ball x (W N) :=
    ((eventually_ge_atTop N).and (hx <| ball_mem_nhds x (hW N))).exists
  refine mem_of_superset (htl n) fun y hy => hWV N ⟨u n, hn, htW N ?_⟩
  exact ⟨ht_anti hNn (hu n), ht_anti hNn hy⟩

end UniformSpaceSeqCompact

section MetrizableSpaceSeqCompact

variable [TopologicalSpace X] [PseudoMetrizableSpace X] {s : Set X}

/--
theorem `IsSeqCompact.isCompact` / 定理 `IsSeqCompact.isCompact`

English:
theorem IsSeqCompact.isCompact
  given: (hs : IsSeqCompact s)
  statement: IsCompact s
  proof: letI := pseudoMetrizableSpaceUniformity X
  haveI := pseudoMetrizableSpaceUniformity_countably_generated X
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.totallyBounded, hs.isComplete⟩

中文:
定理 IsSeqCompact.isCompact
  条件: (hs : IsSeqCompact s)
  结论: IsCompact s
  证明: letI := pseudoMetrizableSpaceUniformity X
  haveI := pseudoMetrizableSpaceUniformity_countably_generated X
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.totallyBounded, hs.isComplete⟩
-/
protected theorem IsSeqCompact.isCompact (hs : IsSeqCompact s) : IsCompact s :=
  letI := pseudoMetrizableSpaceUniformity X
  haveI := pseudoMetrizableSpaceUniformity_countably_generated X
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.totallyBounded, hs.isComplete⟩

/--
theorem `isCompact_iff_isSeqCompact` / 定理 `isCompact_iff_isSeqCompact`

English:
theorem isCompact_iff_isSeqCompact
  statement: IsCompact s ↔ IsSeqCompact s
  proof: ⟨fun H => H.isSeqCompact, fun H => H.isCompact⟩

中文:
定理 isCompact_iff_isSeqCompact
  结论: IsCompact s ↔ IsSeqCompact s
  证明: ⟨fun H => H.isSeqCompact, fun H => H.isCompact⟩

Depends on / 依赖: H.isCompact, H.isSeqCompact, isCompact, isSeqCompact
-/
theorem isCompact_iff_isSeqCompact : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.isSeqCompact, fun H => H.isCompact⟩

/--
theorem `compactSpace_iff_seqCompactSpace` / 定理 `compactSpace_iff_seqCompactSpace`

English:
theorem compactSpace_iff_seqCompactSpace
  statement: CompactSpace X ↔ SeqCompactSpace X
  proof: by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, isCompact_iff_isSeqCompact]

中文:
定理 compactSpace_iff_seqCompactSpace
  结论: CompactSpace X ↔ SeqCompactSpace X
  证明: by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, isCompact_iff_isSeqCompact]

Depends on / 依赖: isCompact_iff_isSeqCompact, isCompact_univ_iff, seqCompactSpace_iff
-/
theorem compactSpace_iff_seqCompactSpace : CompactSpace X ↔ SeqCompactSpace X := by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, isCompact_iff_isSeqCompact]

end MetrizableSpaceSeqCompact
