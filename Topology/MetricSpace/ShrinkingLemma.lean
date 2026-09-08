/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking lemma in a proper metric space

In this file we prove a few versions of the shrinking lemma for coverings by balls in a proper
(pseudo) metric space.

## Tags

shrinking lemma, metric space
-/

public section


universe u v

open Set Metric

open Topology

variable {α : Type u} {ι : Type v} [MetricSpace α] [ProperSpace α] {c : ι → α}
variable {s : Set α}

/-- **Shrinking lemma** for coverings by open balls in a proper metric space. A point-finite open
cover of a closed subset of a proper metric space by open balls can be shrunk to a new cover by
open balls so that each of the new balls has strictly smaller radius than the old one. This version
assumes that `fun x ↦ ball (c i) (r i)` is a locally finite covering and provides a covering
indexed by the same type. -/
/-
**exists_subset_iUnion_ball_radius_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_iUnion_ball_radius_lt {r : ι -> Real} (hs : IsClosed s) (uf 
: forall x in s, { i | x in ball (c i) (r i) }.Finite) (us : s subseteq ⋃ i, bal
l (c i) (r i)) : exists r' : ι -> Real, (s subseteq ⋃ i, ball (c i) (r' i)) ∧ fo
rall i, r' i < r i
参数：hs : IsClosed s；uf : forall x in s, { i | x in ball (c i) (r i) }.Finite；us :
 s subseteq ⋃ i, ball (c i) (r i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closed_subset`：exists_subset_iUnion_closed_subset (
hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in u
 i }.Finite) (us : s sub…
· 使用定理 `NormalSpace.of_paracompactSpace_r1Space`：∀ {X : Type v} [inst : Topologi
calSpace X] [R1Space X] [ParacompactSpace X], NormalSpace X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Metric.instParacompactSpace`：∀ {α : Type u_1} [inst : PseudoEMetricSpace
 α], ParacompactSpace α
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `exists_lt_subset_ball`：exists_lt_subset_ball (hs : IsClosed s) (h : s su
bseteq ball x r) : exists r' < r, s subseteq ball x r'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
**Shrinking lemma** for coverings by open balls in a proper metric space. A poin
t-finite open
cover of a closed subset of a proper metric space by open balls can be shrunk to
 a new cover by
open balls so that each of the new balls has strictly smaller radius than the ol
d one. This version
assumes that `fun x ↦ ball (c i) (r i)` is a locally finite covering and provide
s a covering
indexed by the same type.
-/
theorem exists_subset_iUnion_ball_radius_lt {r : ι → ℝ} (hs : IsClosed s)
    (uf : ∀ x ∈ s, { i | x ∈ ball (c i) (r i) }.Finite) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
    ∃ r' : ι → ℝ, (s ⊆ ⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i < r i := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_lt_subset_ball (hvc i) (hcv i)
  choose r' hlt hsub using this
  exact ⟨r', hsv.trans <| iUnion_mono <| hsub, hlt⟩

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a proper metric space by open balls can be shrunk to a new cover by open balls so that each of
the new balls has strictly smaller radius than the old one. -/
/-
**exists_iUnion_ball_eq_radius_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_iUnion_ball_eq_radius_lt {r : ι -> Real} (uf : forall x, { i | x in
 ball (c i) (r i) }.Finite) (uU : ⋃ i, ball (c i) (r i) = univ) : exists r' : ι 
-> Real, ⋃ i, ball (c i) (r' i) = univ ∧ forall i, r' i < r i
参数：uf : forall x, { i | x in ball (c i) (r i) }.Finite；uU : ⋃ i, ball (c i) (r i
) = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_ball_radius_lt`：exists_subset_iUnion_ball_radius_lt
 {r : ι -> Real} (hs : IsClosed s) (uf : forall x in s, { i | x in ball (c i) (r
 i) }.Finite) (us : s sub…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
Shrinking lemma for coverings by open balls in a proper metric space. A point-fi
nite open cover
of a proper metric space by open balls can be shrunk to a new cover by open ball
s so that each of
the new balls has strictly smaller radius than the old one.
-/
theorem exists_iUnion_ball_eq_radius_lt {r : ι → ℝ} (uf : ∀ x, { i | x ∈ ball (c i) (r i) }.Finite)
    (uU : ⋃ i, ball (c i) (r i) = univ) :
    ∃ r' : ι → ℝ, ⋃ i, ball (c i) (r' i) = univ ∧ ∀ i, r' i < r i :=
  let ⟨r', hU, hv⟩ := exists_subset_iUnion_ball_radius_lt isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a closed subset of a proper metric space by nonempty open balls can be shrunk to a new cover by
nonempty open balls so that each of the new balls has strictly smaller radius than the old one. -/
/-
**exists_subset_iUnion_ball_radius_pos_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_iUnion_ball_radius_pos_lt {r : ι -> Real} (hr : forall i, 0 
< r i) (hs : IsClosed s) (uf : forall x in s, { i | x in ball (c i) (r i) }.Fini
te) (us : s subseteq ⋃ i, ball (c i) (r i)) : exists r' : ι -> Real, (s subseteq
 ⋃ i, ball (c i) (r' i)) ∧ forall i, r' i in Ioo 0 (r i)
参数：hr : forall i, 0 < r i；hs : IsClosed s；uf : forall x in s, { i | x in ball (c
 i) (r i) }.Finite；us : s subseteq ⋃ i, ball (c i) (r i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closed_subset`：exists_subset_iUnion_closed_subset (
hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in u
 i }.Finite) (us : s sub…
· 使用定理 `NormalSpace.of_paracompactSpace_r1Space`：∀ {X : Type v} [inst : Topologi
calSpace X] [R1Space X] [ParacompactSpace X], NormalSpace X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Metric.instParacompactSpace`：∀ {α : Type u_1} [inst : PseudoEMetricSpace
 α], ParacompactSpace α
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `exists_pos_lt_subset_ball`：exists_pos_lt_subset_ball (hr : 0 < r) (hs : 
IsClosed s) (h : s subseteq ball x r) : exists r' in Ioo 0 r, s subseteq ball x 
r'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Shrinking lemma for coverings by open balls in a proper metric space. A point-fi
nite open cover
of a closed subset of a proper metric space by nonempty open balls can be shrunk
 to a new cover by
nonempty open balls so that each of the new balls has strictly smaller radius th
an the old one.
-/
theorem exists_subset_iUnion_ball_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hs : IsClosed s)
    (uf : ∀ x ∈ s, { i | x ∈ ball (c i) (r i) }.Finite) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
    ∃ r' : ι → ℝ, (s ⊆ ⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i ∈ Ioo 0 (r i) := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i)
  choose r' hlt hsub using this
  exact ⟨r', hsv.trans <| iUnion_mono hsub, hlt⟩

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a proper metric space by nonempty open balls can be shrunk to a new cover by nonempty open balls
so that each of the new balls has strictly smaller radius than the old one. -/
/-
**exists_iUnion_ball_eq_radius_pos_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_iUnion_ball_eq_radius_pos_lt {r : ι -> Real} (hr : forall i, 0 < r 
i) (uf : forall x, { i | x in ball (c i) (r i) }.Finite) (uU : ⋃ i, ball (c i) (
r i) = univ) : exists r' : ι -> Real, ⋃ i, ball (c i) (r' i) = univ ∧ forall i, 
r' i in Ioo 0 (r i)
参数：hr : forall i, 0 < r i；uf : forall x, { i | x in ball (c i) (r i) }.Finite；uU
 : ⋃ i, ball (c i) (r i) = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_ball_radius_pos_lt`：exists_subset_iUnion_ball_radiu
s_pos_lt {r : ι -> Real} (hr : forall i, 0 < r i) (hs : IsClosed s) (uf : forall
 x in s, { i | x in ball (c i…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
Shrinking lemma for coverings by open balls in a proper metric space. A point-fi
nite open cover
of a proper metric space by nonempty open balls can be shrunk to a new cover by 
nonempty open balls
so that each of the new balls has strictly smaller radius than the old one.
-/
theorem exists_iUnion_ball_eq_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (uf : ∀ x, { i | x ∈ ball (c i) (r i) }.Finite) (uU : ⋃ i, ball (c i) (r i) = univ) :
    ∃ r' : ι → ℝ, ⋃ i, ball (c i) (r' i) = univ ∧ ∀ i, r' i ∈ Ioo 0 (r i) :=
  let ⟨r', hU, hv⟩ :=
    exists_subset_iUnion_ball_radius_pos_lt hr isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

/-- Let `R : α → ℝ` be a (possibly discontinuous) function on a proper metric space.
Let `s` be a closed set in `α` such that `R` is positive on `s`. Then there exists a collection of
pairs of balls `Metric.ball (c i) (r i)`, `Metric.ball (c i) (r' i)` such that

* all centers belong to `s`;
* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `Metric.ball (c i) (r' i)` is locally finite;
* the balls `Metric.ball (c i) (r i)` cover `s`.

This is a simple corollary of `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`
and `exists_subset_iUnion_ball_radius_pos_lt`. -/
/-
**exists_locallyFinite_subset_iUnion_ball_radius_lt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：exists_locallyFinite_subset_iUnion_ball_radius_lt (hs : IsClosed s) {R : α
 -> Real} (hR : forall x in s, 0 < R x) : exists (ι : Type u) (c : ι -> α) (r r'
 : ι -> Real), (forall i, c i in s ∧ 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧ (L
ocallyFinite fun i => ball (c i) (r' i)) ∧ s subseteq ⋃ i, ball (c i) (r i)
参数：hs : IsClosed s；hR : forall x in s, 0 < R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_lt`：uniformity_basis_dist_lt {R : Real} (hR
 : 0 < R) : (𝓤 α).HasBasis (fun r : Real => 0 < r ∧ r < R) fun r => { p : α × α 
| dist p.1 p.2 < r }
· 使用定理 `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`：refinement_
of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X] [
SigmaCompactSpace X] [T2Space X] {ι : X -> Type u…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `sigmaCompactSpace_of_locallyCompact_secondCountable`：∀ {X : Type u_1} [i
nst : TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X], S
igmaCompactSpace X
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `MetricSpace.instT0Space`：∀ {γ : Type w} [inst : MetricSpace γ], T0Space 
γ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `exists_subset_iUnion_ball_radius_pos_lt`：exists_subset_iUnion_ball_radiu
s_pos_lt {r : ι -> Real} (hr : forall i, 0 < r i) (hs : IsClosed s) (uf : forall
 x in s, { i | x in ball (c i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LocallyFinite.point_finite`：point_finite (hf : LocallyFinite f) (x : X) 
: { b | x in f b }.Finite

--- 原说明 ---
Let `R : α → ℝ` be a (possibly discontinuous) function on a proper metric space.
Let `s` be a closed set in `α` such that `R` is positive on `s`. Then there exis
ts a collection of
pairs of balls `Metric.ball (c i) (r i)`, `Metric.ball (c i) (r' i)` such that

* all centers belong to `s`;
* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `Metric.ball (c i) (r' i)` is locally finite;
* the balls `Metric.ball (c i) (r i)` cover `s`.

This is a simple corollary of `refinement_of_locallyCompact_sigmaCompact_of_nhds
_basis_set`
and `exists_subset_iUnion_ball_radius_pos_lt`.
-/
theorem exists_locallyFinite_subset_iUnion_ball_radius_lt (hs : IsClosed s) {R : α → ℝ}
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
      (∀ i, c i ∈ s ∧ 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ s ⊆ ⋃ i, ball (c i) (r i) := by
  have : ∀ x ∈ s, (𝓝 x).HasBasis (fun r : ℝ => 0 < r ∧ r < R x) fun r => ball x r := fun x hx =>
    nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs this with
    ⟨ι, c, r', hr', hsub', hfin⟩
  rcases exists_subset_iUnion_ball_radius_pos_lt (fun i => (hr' i).2.1) hs
      (fun x _ => hfin.point_finite x) hsub' with
    ⟨r, hsub, hlt⟩
  exact ⟨ι, c, r, r', fun i => ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩

/-- Let `R : α → ℝ` be a (possibly discontinuous) positive function on a proper metric space. Then
there exists a collection of pairs of balls `Metric.ball (c i) (r i)`, `Metric.ball (c i) (r' i)`
such that

* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `Metric.ball (c i) (r' i)` is locally finite;
* the balls `Metric.ball (c i) (r i)` cover the whole space.

This is a simple corollary of `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`
and `exists_iUnion_ball_eq_radius_pos_lt` or `exists_locallyFinite_subset_iUnion_ball_radius_lt`. -/
/-
**exists_locallyFinite_iUnion_eq_ball_radius_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_locallyFinite_iUnion_eq_ball_radius_lt {R : α -> Real} (hR : forall
 x, 0 < R x) : exists (ι : Type u) (c : ι -> α) (r r' : ι -> Real), (forall i, 0
 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧ (LocallyFinite fun i => ball (c i) (r' i
)) ∧ ⋃ i, ball (c i) (r i) = univ
参数：hR : forall x, 0 < R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_locallyFinite_subset_iUnion_ball_radius_lt`：exists_locallyFinite_
subset_iUnion_ball_radius_lt (hs : IsClosed s) {R : α -> Real} (hR : forall x in
 s, 0 < R x) : exists (ι : Type u) (c :…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
Let `R : α → ℝ` be a (possibly discontinuous) positive function on a proper metr
ic space. Then
there exists a collection of pairs of balls `Metric.ball (c i) (r i)`, `Metric.b
all (c i) (r' i)`
such that

* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `Metric.ball (c i) (r' i)` is locally finite;
* the balls `Metric.ball (c i) (r i)` cover the whole space.

This is a simple corollary of `refinement_of_locallyCompact_sigmaCompact_of_nhds
_basis`
and `exists_iUnion_ball_eq_radius_pos_lt` or `exists_locallyFinite_subset_iUnion
_ball_radius_lt`.
-/
theorem exists_locallyFinite_iUnion_eq_ball_radius_lt {R : α → ℝ} (hR : ∀ x, 0 < R x) :
    ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
      (∀ i, 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ ⋃ i, ball (c i) (r i) = univ :=
  let ⟨ι, c, r, r', hlt, hfin, hsub⟩ :=
    exists_locallyFinite_subset_iUnion_ball_radius_lt isClosed_univ fun x _ => hR x
  ⟨ι, c, r, r', fun i => (hlt i).2, hfin, univ_subset_iff.1 hsub⟩
