/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.MetricSpace.PiNat

/-!
# (Topological) Schemes and their induced maps

In topology, and especially descriptive set theory, one often constructs functions `(ℕ → β) → α`,
where α is some topological space and β is a discrete space, as an appropriate limit of some map
`List β → Set α`. We call the latter type of map a "`β`-scheme on `α`".

This file develops the basic, abstract theory of these schemes and the functions they induce.

## Main Definitions

* `CantorScheme.inducedMap A` : The aforementioned "limit" of a scheme `A : List β → Set α`.
  This is a partial function from `ℕ → β` to `a`,
  implemented here as an object of type `Σ s : Set (ℕ → β), s → α`.
  That is, `(inducedMap A).1` is the domain and `(inducedMap A).2` is the function.

## Implementation Notes

We consider end-appending to be the fundamental way to build lists (say on `β`) inductively,
as this interacts better with the topology on `ℕ → β`.
As a result, functions like `List.get?` or `Stream'.take` do not have their intended meaning
in this file. See instead `PiNat.res`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

scheme, cantor scheme, lusin scheme, approximation.

-/

@[expose] public section

namespace CantorScheme

open List Function Filter Set PiNat Topology

variable {β α : Type*} (A : List β -> Set α)

/--
Definition of `inducedMap` / `inducedMap` 的定义

English:
definition inducedMap
  signature: : Σ s : Set (Nat -> β), s -> α
  body: ⟨{x | Set.Nonempty (⋂ n : Nat, A (res x n))}, fun x => x.property.some⟩

中文:
定义 inducedMap
  签名: : Σ s : 集合 (自然数 -> β), s -> α
  定义体: ⟨{x | Set.Nonempty (⋂ n : Nat, A (res x n))}, fun x => x.property.some⟩

Depends on / 依赖: Nonempty, Set.Nonempty, property, x.property.some
-/
noncomputable def inducedMap : Σ s : Set (Nat -> β), s -> α :=
  ⟨{x | Set.Nonempty (⋂ n : Nat, A (res x n))}, fun x => x.property.some⟩

section Topology

/--
Definition of `Antitone` / `Antitone` 的定义

English:
definition Antitone
  signature: : Prop
  body: forall l : List β, forall a : β, A (a :: l) subseteq A l

中文:
定义 递减
  签名: : 命题
  定义体: forall l : List β, forall a : β, A (a :: l) subseteq A l
-/
protected def Antitone : Prop :=
  forall l : List β, forall a : β, A (a :: l) subseteq A l

/--
Definition of `ClosureAntitone` / `ClosureAntitone` 的定义

English:
definition ClosureAntitone
  signature: [TopologicalSpace α]
  body: forall l : List β, forall a : β, closure (A (a :: l)) subseteq A l

中文:
定义 ClosureAntitone
  签名: [拓扑空间 α]
  定义体: forall l : List β, forall a : β, closure (A (a :: l)) subseteq A l

Depends on / 依赖: closure, subseteq
-/
def ClosureAntitone [TopologicalSpace α] : Prop :=
  forall l : List β, forall a : β, closure (A (a :: l)) subseteq A l

/--
Definition of `Disjoint` / `Disjoint` 的定义

English:
definition Disjoint
  signature: : Prop
  body: forall l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))

中文:
定义 Disjoint
  签名: : 命题
  定义体: forall l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))
-/
protected def Disjoint : Prop :=
  forall l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))

variable {A}

/--
theorem `map_mem` / 定理 `map_mem`

English:
theorem map_mem
  given: (x : (inducedMap A).1) (n : Nat)
  statement: (inducedMap A).2 x in A (res x n)
  proof: by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n

中文:
定理 map_mem
  条件: (x : (inducedMap A).1) (n : 自然数)
  结论: (inducedMap A).2 x in A (res x n)
  证明: by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n

Depends on / 依赖: mem_iInter, property, some_mem, x.property.some_mem
-/
theorem map_mem (x : (inducedMap A).1) (n : Nat) : (inducedMap A).2 x in A (res x n) := by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n

/--
theorem `ClosureAntitone.antitone` / 定理 `ClosureAntitone.antitone`

English:
theorem ClosureAntitone.antitone
  given: [TopologicalSpace α] (hA : ClosureAntitone A)
  proof: fun l a => subset_closure.trans (hA l a)

中文:
定理 ClosureAntitone.antitone
  条件: [拓扑空间 α] (hA : ClosureAntitone A)
  证明: fun l a => subset_closure.trans (hA l a)
-/
protected theorem ClosureAntitone.antitone [TopologicalSpace α] (hA : ClosureAntitone A) :
    CantorScheme.Antitone A := fun l a => subset_closure.trans (hA l a)

/--
theorem `Antitone.closureAntitone` / 定理 `Antitone.closureAntitone`

English:
theorem Antitone.closureAntitone
  statement: [TopologicalSpace α] (hanti : CantorScheme.Antitone A)
  proof: fun _ _ =>
  (hclosed _).closure_eq.subset.trans (hanti _ _)

中文:
定理 递减.closureAntitone
  结论: [拓扑空间 α] (hanti : CantorScheme.递减 A)
  证明: fun _ _ =>
  (hclosed _).closure_eq.subset.trans (hanti _ _)
-/
protected theorem Antitone.closureAntitone [TopologicalSpace α] (hanti : CantorScheme.Antitone A)
    (hclosed : forall l, IsClosed (A l)) : ClosureAntitone A := fun _ _ =>
  (hclosed _).closure_eq.subset.trans (hanti _ _)

/--
theorem `Disjoint.map_injective` / 定理 `Disjoint.map_injective`

English:
theorem Disjoint.map_injective
  given: (hA : CantorScheme.Disjoint A)
  statement: Injective (inducedMap A).2
  proof: by
  rintro x y hxy
  ext1
  apply res_injective
  ext n : 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [res_succ, cons.injEq]
    refine ⟨?_, ih⟩
    contrapose hA
    simp only [CantorScheme.Disjoint, _root_.Pairwise, Ne, not_forall, exists_prop]
    refine ⟨res x n, _, _, 

中文:
定理 Disjoint.map_injective
  条件: (hA : CantorScheme.Disjoint A)
  结论: 单射 (inducedMap A).2
  证明: by
  rintro x y hxy
  ext1
  apply res_injective
  ext n : 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [res_succ, cons.injEq]
    refine ⟨?_, ih⟩
    contrapose hA
    simp only [CantorScheme.Disjoint, _root_.Pairwise, Ne, not_forall, exists_prop]
    refine ⟨res x n, _, _, 

Depends on / 依赖: CantorScheme, CantorScheme.Disjoint, Disjoint, Pairwise, _root_, _root_.Pairwise, cons.injEq, contrapose, exists_prop, inducedMap, map_mem, not_disjoint_iff, not_forall, res_injective, res_succ
-/
theorem Disjoint.map_injective (hA : CantorScheme.Disjoint A) : Injective (inducedMap A).2 := by
  rintro x y hxy
  ext1
  apply res_injective
  ext n : 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [res_succ, cons.injEq]
    refine ⟨?_, ih⟩
    contrapose hA
    simp only [CantorScheme.Disjoint, _root_.Pairwise, Ne, not_forall, exists_prop]
    refine ⟨res x n, _, _, hA, ?_⟩
    rw [not_disjoint_iff]
    refine ⟨(inducedMap A).2 x, ?_, ?_⟩
    · rw [← res_succ]
      apply map_mem
    rw [hxy]; rw [ih]; rw [← res_succ]
    apply map_mem

end Topology

section Metric

variable [PseudoMetricSpace α]

/--
Definition of `VanishingDiam` / `VanishingDiam` 的定义

English:
definition VanishingDiam
  signature: : Prop
  body: forall x : Nat -> β, Tendsto (fun n : Nat => Metric.ediam (A (res x n))) atTop (𝓝 0)

中文:
定义 VanishingDiam
  签名: : 命题
  定义体: forall x : Nat -> β, Tendsto (fun n : Nat => Metric.ediam (A (res x n))) atTop (𝓝 0)

Depends on / 依赖: Metric, Metric.ediam, Tendsto
-/
def VanishingDiam : Prop :=
  forall x : Nat -> β, Tendsto (fun n : Nat => Metric.ediam (A (res x n))) atTop (𝓝 0)

variable {A}

/--
theorem `VanishingDiam.dist_lt` / 定理 `VanishingDiam.dist_lt`

English:
theorem VanishingDiam.dist_lt
  given: (hA : VanishingDiam A) (ε : Real) (ε_pos : 0 < ε) (x : Nat -> β)
  proof: by
  specialize hA x
  rw [ENNReal.tendsto_atTop_zero] at hA
  obtain ⟨n, hn⟩ := hA (ENNReal.ofReal (ε / 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]; linarith)
  use n
  intro y hy z hz
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos]; rw [← edist_dist]
  apply lt_of_le_of_lt (Metric.edist_le_e

中文:
定理 VanishingDiam.dist_lt
  条件: (hA : VanishingDiam A) (ε : 实数) (ε_pos : 0 < ε) (x : 自然数 -> β)
  证明: by
  specialize hA x
  rw [ENNReal.tendsto_atTop_zero] at hA
  obtain ⟨n, hn⟩ := hA (ENNReal.ofReal (ε / 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]; linarith)
  use n
  intro y hy z hz
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos]; rw [← edist_dist]
  apply lt_of_le_of_lt (Metric.edist_le_e

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_lt_ofReal_iff, ENNReal.ofReal_pos, ENNReal.tendsto_atTop_zero, Metric, Metric.edist_le_ediam_of_mem, edist_dist, edist_le_ediam_of_mem, gt_iff_lt, le_refl, lt_of_le_of_lt, ofReal, ofReal_lt_ofReal_iff, ofReal_pos, specialize, tendsto_atTop_zero
-/
theorem VanishingDiam.dist_lt (hA : VanishingDiam A) (ε : Real) (ε_pos : 0 < ε) (x : Nat -> β) :
    exists n : Nat, forall (y) (_ : y in A (res x n)) (z) (_ : z in A (res x n)), dist y z < ε := by
  specialize hA x
  rw [ENNReal.tendsto_atTop_zero] at hA
  obtain ⟨n, hn⟩ := hA (ENNReal.ofReal (ε / 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]; linarith)
  use n
  intro y hy z hz
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos]; rw [← edist_dist]
  apply lt_of_le_of_lt (Metric.edist_le_ediam_of_mem hy hz)
  apply lt_of_le_of_lt (hn _ (le_refl _))
  rw [ENNReal.ofReal_lt_ofReal_iff ε_pos]
  linarith

/--
theorem `VanishingDiam.map_continuous` / 定理 `VanishingDiam.map_continuous`

English:
theorem VanishingDiam.map_continuous
  statement: [TopologicalSpace β] [DiscreteTopology β]
  proof: by
  rw [Metric.continuous_iff']
  rintro x ε ε_pos
  obtain ⟨n, hn⟩ := hA.dist_lt _ ε_pos x
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x.1 n, ?_, ?_, by simp⟩
  · rintro y hyx
    rw [mem_preimage]; rw [Subtype.coe_mk]; rw [cylinder_eq_res]; rw [mem_ofPred] at hyx
    apply hn
    

中文:
定理 VanishingDiam.map_continuous
  结论: [拓扑空间 β] [离散拓扑 β]
  证明: by
  rw [Metric.continuous_iff']
  rintro x ε ε_pos
  obtain ⟨n, hn⟩ := hA.dist_lt _ ε_pos x
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x.1 n, ?_, ?_, by simp⟩
  · rintro y hyx
    rw [mem_preimage]; rw [Subtype.coe_mk]; rw [cylinder_eq_res]; rw [mem_ofPred] at hyx
    apply hn
    

Depends on / 依赖: Metric, Metric.continuous_iff, Subtype, Subtype.coe_mk, _root_, _root_.eventually_nhds_iff, coe_mk, continuous_iff, continuous_subtype_val, continuous_subtype_val.isOpen_preimage, cylinder, cylinder_eq_res, dist_lt, eventually_nhds_iff, hA.dist_lt, isOpen_cylinder, isOpen_preimage, map_mem, mem_ofPred, mem_preimage
-/
theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 := by
  rw [Metric.continuous_iff']
  rintro x ε ε_pos
  obtain ⟨n, hn⟩ := hA.dist_lt _ ε_pos x
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x.1 n, ?_, ?_, by simp⟩
  · rintro y hyx
    rw [mem_preimage]; rw [Subtype.coe_mk]; rw [cylinder_eq_res]; rw [mem_ofPred] at hyx
    apply hn
    · rw [← hyx]
      apply map_mem
    apply map_mem
  apply continuous_subtype_val.isOpen_preimage
  apply isOpen_cylinder

/--
theorem `ClosureAntitone.map_of_vanishingDiam` / 定理 `ClosureAntitone.map_of_vanishingDiam`

English:
theorem ClosureAntitone.map_of_vanishingDiam
  statement: [CompleteSpace α] (hdiam : VanishingDiam A)
  proof: by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : forall n m : Nat, n <= m -> u m in A (res x n) := by
    have : Antitone fun n : Nat => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n

中文:
定理 ClosureAntitone.map_of_vanishingDiam
  结论: [完备空间 α] (hdiam : VanishingDiam A)
  证明: by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : forall n m : Nat, n <= m -> u m in A (res x n) := by
    have : Antitone fun n : Nat => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n

Depends on / 依赖: Antitone, CauchySeq, Metric, Metric.cauchySeq_iff, antitone, antitone_nat_of_succ_le, cauchySeq_iff, cauchySeq_tends, dist_lt, eq_univ_iff_forall, hanti.antitone, hdiam.dist_lt, hnonempty
-/
theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : forall l, (A l).Nonempty) : (inducedMap A).1 = univ := by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : forall n m : Nat, n <= m -> u m in A (res x n) := by
    have : Antitone fun n : Nat => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    obtain ⟨n, hn⟩ := hdiam.dist_lt _ ε_pos x
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  use y
  rw [mem_iInter]
  intro n
  apply hanti _ (x n)
  apply mem_closure_of_tendsto hy
  rw [eventually_atTop]
  exact ⟨n.succ, umem _⟩

end Metric

end CantorScheme
