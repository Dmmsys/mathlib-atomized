/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Anatole Dedecker
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Linear topologies on modules and rings

Let `M` be a (left) module over a ring `R`. Following
[Stacks: Definition 15.36.1](https://stacks.math.columbia.edu/tag/07E8), we say that a
topology on `M` is *`R`-linear* if it is invariant by translations and admits a basis of
neighborhoods of 0 consisting of (left) `R`-submodules.

If `M` is an `(R, R')`-bimodule, we show that a topology is both `R`-linear and `R'`-linear
if and only if there exists a basis of neighborhoods of 0 consisting of `(R, R')`-subbimodules.

In particular, we say that a topology on the ring `R` is *linear* if it is linear if
it is linear when `R` is viewed as an `(R, Rᵐᵒᵖ)`-bimodule. By the previous results,
this means that there exists a basis of neighborhoods of 0 consisting of two-sided ideals,
hence our definition agrees with [N. Bourbaki, *Algebra II*, chapter 4, §2, n° 3][bourbaki1981].

## Main definitions and statements

* `IsLinearTopology R M`: the topology on `M` is `R`-linear, meaning that there exists a basis
  of neighborhoods of 0 consisting of `R`-submodules. Note that we don't impose that the topology
  is invariant by translation, so you'll often want to add `ContinuousConstVAdd M M` to get
  something meaningful. To express that the topology of a ring `R` is linear, use
  `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`.
* `IsLinearTopology.mk_of_hasBasis`: a convenient constructor for `IsLinearTopology`.
  See also `IsLinearTopology.mk_of_hasBasis'`.
* The discrete topology on `M` is `R`-linear (declared as an `instance`).
* `IsLinearTopology.hasBasis_subbimodule`: assume that `M` is an `(R, R')`-bimodule,
  and that its topology is both `R`-linear and `R'`-linear. Then there exists a basis of
  neighborhoods of 0 made of `(R, R')`-subbimodules. Note that this is not trivial, since the bases
  witnessing `R`-linearity and `R'`-linearity may have nothing to do with each other
* `IsLinearTopology.tendsto_smul_zero`: assume that the topology on `M` is linear.
  For `m : ι → M` such that `m i` tends to 0, `r i • m i` still tends to 0 for any `r : ι → R`.

* `IsLinearTopology.hasBasis_twoSidedIdeal`: if the ring `R` is linearly topologized,
  in the sense that we have both `IsLinearTopology R R` and `IsLinearTopology Rᵐᵒᵖ R`,
  then there exists a basis of neighborhoods of 0 consisting of two-sided ideals.
* Conversely, to prove `IsLinearTopology R R` and `IsLinearTopology Rᵐᵒᵖ R`
  from a basis of two-sided ideals, use `IsLinearTopology.mk_of_hasBasis'` twice.
* `IsLinearTopology.tendsto_mul_zero_of_left`: assume that the topology on `R` is (right-)linear.
  For `f, g : ι → R` such that `f i` tends to `0`, `f i * g i` still tends to `0`.
* `IsLinearTopology.tendsto_mul_zero_of_right`: assume that the topology on `R` is (left-)linear.
  For `f, g : ι → R` such that `g i` tends to `0`, `f i * g i` still tends to `0`
* If `R` is a commutative ring and its topology is left-linear, it is automatically
  right-linear (declared as a low-priority instance).

## Notes on the implementation

* Some statements assume `ContinuousAdd M` where `ContinuousConstVAdd M M`
  (invariance by translation) would be enough. In fact, in presence of `IsLinearTopology R M`,
  invariance by translation implies that `M` is a topological additive group on which `R` acts
  by homeomorphisms. Similarly, `IsLinearTopology R R` and `ContinuousConstVAdd R R` imply that
  `R` is a topological ring. All of this will follow from https://github.com/leanprover-community/mathlib4/issues/18437.

  Nevertheless, we don't plan on adding those facts as instances: one should use directly
  results from https://github.com/leanprover-community/mathlib4/issues/18437 to get `IsTopologicalAddGroup` and `IsTopologicalRing` instances.

* The main constructor for `IsLinearTopology`, `IsLinearTopology.mk_of_hasBasis`
  is formulated in terms of the subobject classes `AddSubmonoidClass` and `SMulMemClass`
  to allow for more complicated types than `Submodule R M` or `Ideal R`. Unfortunately, the scalar
  ring in `SMulMemClass` is an `outParam`, which means that Lean only considers one base ring for
  a given subobject type. For example, Lean will *never* find `SMulMemClass (TwoSidedIdeal R) R R`
  because it prioritizes the (later-defined) instance of `SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R`.

  This makes `IsLinearTopology.mk_of_hasBasis` un-applicable to `TwoSidedIdeal` (and probably other
  types), thus we provide `IsLinearTopology.mk_of_hasBasis'` as an alternative not relying on
  typeclass inference.
-/

public section

open scoped Topology
open Filter

namespace IsLinearTopology

section Module

variable {R R' M : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M] [Module R' M]
  [SMulCommClass R R' M] [TopologicalSpace M]

variable (R M) in
/--
Definition of `_root_.IsLinearTopology` / `_root_.IsLinearTopology` 的定义

English:
class _root_.IsLinearTopology
  parameters: where
  axioms and operations (1):
    - hasBasis_submodule' : (𝓝 (0 : M)).HasBasis (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun N : Submodule R M => (N : Set M))

中文:
类 _root_.是线性拓扑
  参数: where
  公理与运算 (1 个):
    - hasBasis_submodule' : (𝓝 (0 : M)).有基 (fun N : 子模 R M => (N : 集合 M) in 𝓝 0) (fun N : 子模 R M => (N : 集合 M))
-/
class _root_.IsLinearTopology where
  hasBasis_submodule' : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun N : Submodule R M => (N : Set M))

variable (R) in
/--
lemma `hasBasis_submodule` / 引理 `hasBasis_submodule`

English:
lemma hasBasis_submodule
  given: [IsLinearTopology R M]
  statement: (𝓝 (0 : M)).HasBasis
  proof: IsLinearTopology.hasBasis_submodule'

中文:
引理 hasBasis_submodule
  条件: [是线性拓扑 R M]
  结论: (𝓝 (0 : M)).有基
  证明: IsLinearTopology.hasBasis_submodule'

Depends on / 依赖: IsLinearTopology, IsLinearTopology.hasBasis_submodule, hasBasis_submodule
-/
lemma hasBasis_submodule [IsLinearTopology R M] : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun N : Submodule R M => (N : Set M)) :=
  IsLinearTopology.hasBasis_submodule'

variable (R) in
/--
lemma `hasBasis_open_submodule` / 引理 `hasBasis_open_submodule`

English:
lemma hasBasis_open_submodule
  given: [ContinuousAdd M] [IsLinearTopology R M]
  proof: .congr hasBasis_submodule R
    (fun N => ⟨N.toAddSubgroup.isOpen_of_mem_nhds, fun hN => hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ => rfl)

中文:
引理 hasBasis_open_submodule
  条件: [连续加法 M] [是线性拓扑 R M]
  证明: .congr hasBasis_submodule R
    (fun N => ⟨N.toAddSubgroup.isOpen_of_mem_nhds, fun hN => hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ => rfl)

Depends on / 依赖: N.toAddSubgroup.isOpen_of_mem_nhds, hN.mem_nhds, hasBasis_submodule, isOpen_of_mem_nhds, mem_nhds, toAddSubgroup, zero_mem
-/
lemma hasBasis_open_submodule [ContinuousAdd M] [IsLinearTopology R M] :
    (𝓝 (0 : M)).HasBasis
      (fun N : Submodule R M => IsOpen (N : Set M)) (fun N : Submodule R M => (N : Set M)) :=
.congr hasBasis_submodule R
    (fun N => ⟨N.toAddSubgroup.isOpen_of_mem_nhds, fun hN => hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ => rfl)

variable (R) in
/--
lemma `mk_of_hasBasis'` / 引理 `mk_of_hasBasis'`

English:
lemma mk_of_hasBasis'
  statement: {ι : Sort*} {S : Type*} [SetLike S M]
  proof: h.to_hasBasis
    (fun i hi => ⟨
      { carrier := s i,
        add_mem' := add_mem,
        zero_mem' := zero_mem _,
        smul_mem' := hsmul _},
      h.mem_of_mem hi, subset_rfl⟩)
    (fun _ => h.mem_iff.mp)

中文:
引理 mk_of_hasBasis'
  结论: {ι : 类型层*} {S : 类型} [集合状 S M]
  证明: h.to_hasBasis
    (fun i hi => ⟨
      { carrier := s i,
        add_mem' := add_mem,
        zero_mem' := zero_mem _,
        smul_mem' := hsmul _},
      h.mem_of_mem hi, subset_rfl⟩)
    (fun _ => h.mem_iff.mp)

Depends on / 依赖: h.to_hasBasis, to_hasBasis
-/
lemma mk_of_hasBasis' {ι : Sort*} {S : Type*} [SetLike S M]
    [AddSubmonoidClass S M]
    {p : ι -> Prop} {s : ι -> S}
    (h : (𝓝 0).HasBasis p (fun i => (s i : Set M)))
    (hsmul : forall s : S, forall r : R, forall m in s, r • m in s) :
    IsLinearTopology R M where
  hasBasis_submodule' := h.to_hasBasis
    (fun i hi => ⟨
      { carrier := s i,
        add_mem' := add_mem,
        zero_mem' := zero_mem _,
        smul_mem' := hsmul _},
      h.mem_of_mem hi, subset_rfl⟩)
    (fun _ => h.mem_iff.mp)

variable (R) in
/--
lemma `mk_of_hasBasis` / 引理 `mk_of_hasBasis`

English:
lemma mk_of_hasBasis
  statement: {ι : Sort*} {S : Type*} [SetLike S M]
  proof: mk_of_hasBasis' R h fun _ => SMulMemClass.smul_mem

中文:
引理 mk_of_hasBasis
  结论: {ι : 类型层*} {S : 类型} [集合状 S M]
  证明: mk_of_hasBasis' R h fun _ => SMulMemClass.smul_mem

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, mk_of_hasBasis, smul_mem
-/
lemma mk_of_hasBasis {ι : Sort*} {S : Type*} [SetLike S M]
    [SMulMemClass S R M] [AddSubmonoidClass S M]
    {p : ι -> Prop} {s : ι -> S}
    (h : (𝓝 0).HasBasis p (fun i => (s i : Set M))) :
    IsLinearTopology R M :=
  mk_of_hasBasis' R h fun _ => SMulMemClass.smul_mem

/--
theorem `_root_.isLinearTopology_iff_hasBasis_submodule` / 定理 `_root_.isLinearTopology_iff_hasBasis_submodule`

English:
theorem _root_.isLinearTopology_iff_hasBasis_submodule
  proof: ⟨fun _ => hasBasis_submodule R, fun h => .mk_of_hasBasis R h⟩

中文:
定理 _root_.isLinearTopology_iff_hasBasis_submodule
  证明: ⟨fun _ => hasBasis_submodule R, fun h => .mk_of_hasBasis R h⟩

Depends on / 依赖: hasBasis_submodule, mk_of_hasBasis
-/
theorem _root_.isLinearTopology_iff_hasBasis_submodule :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M => (N : Set M) in 𝓝 0) (fun N : Submodule R M => (N : Set M)) :=
  ⟨fun _ => hasBasis_submodule R, fun h => .mk_of_hasBasis R h⟩

/--
theorem `_root_.isLinearTopology_iff_hasBasis_open_submodule` / 定理 `_root_.isLinearTopology_iff_hasBasis_open_submodule`

English:
theorem _root_.isLinearTopology_iff_hasBasis_open_submodule
  given: [ContinuousAdd M]
  proof: ⟨fun _ => hasBasis_open_submodule R, fun h => .mk_of_hasBasis R h⟩

中文:
定理 _root_.isLinearTopology_iff_hasBasis_open_submodule
  条件: [连续加法 M]
  证明: ⟨fun _ => hasBasis_open_submodule R, fun h => .mk_of_hasBasis R h⟩

Depends on / 依赖: hasBasis_open_submodule, mk_of_hasBasis
-/
theorem _root_.isLinearTopology_iff_hasBasis_open_submodule [ContinuousAdd M] :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M => IsOpen (N : Set M)) (fun N : Submodule R M => (N : Set M)) :=
  ⟨fun _ => hasBasis_open_submodule R, fun h => .mk_of_hasBasis R h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: M] : IsLinearTopology R M
  body: have : HasBasis (𝓝 0 : Filter M) (fun _ => True) (fun (_ : Unit) => (⊥ : Submodule R M)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  mk_of_hasBasis R this

中文:
实例 [离散拓扑
  签名: M] : 是线性拓扑 R M
  定义体: have : HasBasis (𝓝 0 : Filter M) (fun _ => True) (fun (_ : Unit) => (⊥ : Submodule R M)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  mk_of_hasBasis R this

Depends on / 依赖: Filter, HasBasis, Submodule, hasBasis_pure, mk_of_hasBasis, nhds_discrete
-/
instance [DiscreteTopology M] : IsLinearTopology R M :=
  have : HasBasis (𝓝 0 : Filter M) (fun _ => True) (fun (_ : Unit) => (⊥ : Submodule R M)) := by
    rw [nhds_discrete]
    exact hasBasis_pure _
  mk_of_hasBasis R this

variable (R R') in
open Set Pointwise in
/--
lemma `hasBasis_subbimodule` / 引理 `hasBasis_subbimodule`

English:
lemma hasBasis_subbimodule
  given: [IsLinearTopology R M] [IsLinearTopology R' M]
  proof: by
  -- Start from a neighborhood `V`. It contains some open sub-`R`-module `I`.
.to_hasBasis (fun I hI => ?_) refine IsLinearTopology.hasBasis_submodule R
    (fun I hI => ⟨{I with smul_mem' := fun r x hx => hI.2.1 r x hx}, hI.1, subset_rfl⟩)
  -- `I` itself is a neighborhood of zero, so it contain

中文:
引理 hasBasis_subbimodule
  条件: [是线性拓扑 R M] [是线性拓扑 R' M]
  证明: by
  -- Start from a neighborhood `V`. It contains some open sub-`R`-module `I`.
.to_hasBasis (fun I hI => ?_) refine IsLinearTopology.hasBasis_submodule R
    (fun I hI => ⟨{I with smul_mem' := fun r x hx => hI.2.1 r x hx}, hI.1, subset_rfl⟩)
  -- `I` itself is a neighborhood of zero, so it contain
-/
lemma hasBasis_subbimodule [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M => (I : Set M) in 𝓝 0 ∧
        (forall r : R, forall x in I, r • x in I) ∧ (forall r' : R', forall x in I, r' • x in I))
      (fun I : AddSubgroup M => (I : Set M)) := by
  -- Start from a neighborhood `V`. It contains some open sub-`R`-module `I`.
.to_hasBasis (fun I hI => ?_) refine IsLinearTopology.hasBasis_submodule R
    (fun I hI => ⟨{I with smul_mem' := fun r x hx => hI.2.1 r x hx}, hI.1, subset_rfl⟩)
  -- `I` itself is a neighborhood of zero, so it contains some open sub-`R'`-module `J`.
  rcases (hasBasis_submodule R').mem_iff.mp hI with ⟨J, hJ, J_sub_I⟩
  set uR : Set R := univ -- Convenient to avoid type ascriptions
  set uR' : Set R' := univ
  have hRR : uR * uR subseteq uR := subset_univ _
  have hRI : uR • (I : Set M) subseteq I := smul_subset_iff.mpr fun x _ i hi => I.smul_mem x hi
  have hR'J : uR' • (J : Set M) subseteq J := smul_subset_iff.mpr fun x _ j hj => J.smul_mem x hj
  have hRJ : uR • (J : Set M) subseteq I := subset_trans (smul_subset_smul_left J_sub_I) hRI
  -- Note that, on top of the obvious `R • I ⊆ I` and `R' • J ⊆ J`, we have `R • J ⊆ R • I ⊆ I`.
  -- Now set `S := J ∪ (R • J)`. We have:
  -- 1. `R • S = (R • J) ∪ (R • R • J) ⊆ R • J ⊆ S`.
  -- 2. `R' • S = (R' • J) ∪ (R' • R • J) ⊆ J ∪ (R • R' • J) ⊆ J ∪ (R • J) = S`.
  -- Hence the subgroup `A` generated by `S` is a sub-`(R, R')`-bimodule,
  -- which we claim is open and contained in `I`.
  -- Indeed, we have `J ⊆ S ⊆ I`, hence `J ⊆ A ⊆ I`, and `J` is open by hypothesis.
  set S : Set M := J union uR • J
  have S_sub_I : S subseteq I := union_subset J_sub_I hRJ
  have hRS : uR • S subseteq S := calc
    uR • S = uR • (J : Set M) union (uR * uR) • (J : Set M) := by simp_rw [S, smul_union, mul_smul]
    _ subseteq uR • (J : Set M) union uR • (J : Set M) := by gcongr
    _ = uR • (J : Set M) := union_self _
    _ subseteq S := subset_union_right
  have hR'S : uR' • S subseteq S := calc
    uR' • S = uR' • (J : Set M) union uR • uR' • (J : Set M) := by simp_rw [S, smul_union, smul_comm]
    _ subseteq J union uR • J := by gcongr
    _ = S := rfl
  set A : AddSubgroup M := .closure S
  have hRA : forall r : R, forall i in A, r • i in A := fun r i hi => by
    refine AddSubgroup.closure_induction (fun x hx => ?base) ?zero (fun x y _ _ hx hy => ?add)
      (fun x _ hx => ?neg) hi
case base => exact AddSubgroup.subset_closure hRS Set.smul_mem_smul trivial hx
    case zero => simp_rw [smul_zero]; exact zero_mem _
    case add => simp_rw [smul_add]; exact add_mem hx hy
    case neg => simp_rw [smul_neg]; exact neg_mem hx
  have hR'A : forall r' : R', forall i in A, r' • i in A := fun r' i hi => by
    refine AddSubgroup.closure_induction (fun x hx => ?base) ?zero (fun x y _ _ hx hy => ?add)
      (fun x _ hx => ?neg) hi
case base => exact AddSubgroup.subset_closure hR'S Set.smul_mem_smul trivial hx
    case zero => simp_rw [smul_zero]; exact zero_mem _
    case add => simp_rw [smul_add]; exact add_mem hx hy
    case neg => simp_rw [smul_neg]; exact neg_mem hx
  have A_sub_I : (A : Set M) subseteq I := I.toAddSubgroup.closure_le.mpr S_sub_I
  have J_sub_A : (J : Set M) subseteq A := subset_trans subset_union_left AddSubgroup.subset_closure
  exact ⟨A, ⟨mem_of_superset hJ J_sub_A, hRA, hR'A⟩, A_sub_I⟩

variable (R R') in
open Set Pointwise in
/--
lemma `hasBasis_open_subbimodule` / 引理 `hasBasis_open_subbimodule`

English:
lemma hasBasis_open_subbimodule
  given: [ContinuousAdd M] [IsLinearTopology R M] [IsLinearTopology R' M]
  proof: .congr hasBasis_subbimodule R R'
    (fun N => and_congr_left' ⟨N.isOpen_of_mem_nhds, fun hN => hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ => rfl)

中文:
引理 hasBasis_open_subbimodule
  条件: [连续加法 M] [是线性拓扑 R M] [是线性拓扑 R' M]
  证明: .congr hasBasis_subbimodule R R'
    (fun N => and_congr_left' ⟨N.isOpen_of_mem_nhds, fun hN => hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ => rfl)

Depends on / 依赖: N.isOpen_of_mem_nhds, and_congr_left, hN.mem_nhds, hasBasis_subbimodule, isOpen_of_mem_nhds, mem_nhds, zero_mem
-/
lemma hasBasis_open_subbimodule [ContinuousAdd M] [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M => IsOpen (I : Set M) ∧
        (forall r : R, forall x in I, r • x in I) ∧ (forall r' : R', forall x in I, r' • x in I))
      (fun I : AddSubgroup M => (I : Set M)) :=
.congr hasBasis_subbimodule R R'
    (fun N => and_congr_left' ⟨N.isOpen_of_mem_nhds, fun hN => hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ => rfl)

-- Even though `R` can be recovered from `a`, the nature of this lemma means that `a` will
-- often be left for Lean to infer, so making `R` explicit is useful in practice.
variable (R) in
/--
theorem `tendsto_smul_zero` / 定理 `tendsto_smul_zero`

English:
theorem tendsto_smul_zero
  statement: [IsLinearTopology R M] {ι : Type*} {f : Filter ι}
  proof: by
  rw [hasBasis_submodule R |>.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.smul_mem _ ai_mem

中文:
定理 tendsto_smul_zero
  结论: [是线性拓扑 R M] {ι : 类型} {f : 滤子 ι}
  证明: by
  rw [hasBasis_submodule R |>.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.smul_mem _ ai_mem

Depends on / 依赖: I.smul_mem, ai_mem, filter_upwards, hasBasis_submodule, smul_mem, tendsto_right_iff
-/
theorem tendsto_smul_zero [IsLinearTopology R M] {ι : Type*} {f : Filter ι}
    (a : ι -> R) (m : ι -> M) (ha : Tendsto m f (𝓝 0)) :
    Tendsto (a • m) f (𝓝 0) := by
  rw [hasBasis_submodule R |>.tendsto_right_iff] at ha ⊢
  intro I hI
  filter_upwards [ha I hI] with i ai_mem
  exact I.smul_mem _ ai_mem

variable (R) in
/--
theorem `_root_.IsCentralScalar.isLinearTopology_iff` / 定理 `_root_.IsCentralScalar.isLinearTopology_iff`

English:
theorem _root_.IsCentralScalar.isLinearTopology_iff
  given: [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  proof: by
  constructor <;> intro H
  · exact mk_of_hasBasis' R (IsLinearTopology.hasBasis_submodule Rᵐᵒᵖ)
      fun S r m hm => op_smul_eq_smul r m ▸ S.smul_mem _ hm
  · exact mk_of_hasBasis' Rᵐᵒᵖ (IsLinearTopology.hasBasis_submodule R)
      fun S r m hm => unop_smul_eq_smul r m ▸ S.smul_mem _ hm

中文:
定理 _root_.中心标量.isLinearTopology_iff
  条件: [模 Rᵐᵒᵖ M] [中心标量 R M]
  证明: by
  constructor <;> intro H
  · exact mk_of_hasBasis' R (IsLinearTopology.hasBasis_submodule Rᵐᵒᵖ)
      fun S r m hm => op_smul_eq_smul r m ▸ S.smul_mem _ hm
  · exact mk_of_hasBasis' Rᵐᵒᵖ (IsLinearTopology.hasBasis_submodule R)
      fun S r m hm => unop_smul_eq_smul r m ▸ S.smul_mem _ hm

Depends on / 依赖: IsLinearTopology, IsLinearTopology.hasBasis_submodule, S.smul_mem, hasBasis_submodule, mk_of_hasBasis, op_smul_eq_smul, smul_mem, unop_smul_eq_smul
-/
theorem _root_.IsCentralScalar.isLinearTopology_iff [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsLinearTopology Rᵐᵒᵖ M ↔ IsLinearTopology R M := by
  constructor <;> intro H
  · exact mk_of_hasBasis' R (IsLinearTopology.hasBasis_submodule Rᵐᵒᵖ)
      fun S r m hm => op_smul_eq_smul r m ▸ S.smul_mem _ hm
  · exact mk_of_hasBasis' Rᵐᵒᵖ (IsLinearTopology.hasBasis_submodule R)
      fun S r m hm => unop_smul_eq_smul r m ▸ S.smul_mem _ hm

end Module

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

/--
theorem `hasBasis_ideal` / 定理 `hasBasis_ideal`

English:
theorem hasBasis_ideal
  given: [IsLinearTopology R R]
  proof: hasBasis_submodule R

中文:
定理 hasBasis_ideal
  条件: [是线性拓扑 R R]
  证明: hasBasis_submodule R

Depends on / 依赖: hasBasis_submodule
-/
theorem hasBasis_ideal [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R => (I : Set R) in 𝓝 0) (fun I : Ideal R => (I : Set R)) :=
  hasBasis_submodule R

/--
theorem `hasBasis_open_ideal` / 定理 `hasBasis_open_ideal`

English:
theorem hasBasis_open_ideal
  given: [ContinuousAdd R] [IsLinearTopology R R]
  proof: hasBasis_open_submodule R

中文:
定理 hasBasis_open_ideal
  条件: [连续加法 R] [是线性拓扑 R R]
  证明: hasBasis_open_submodule R

Depends on / 依赖: hasBasis_open_submodule
-/
theorem hasBasis_open_ideal [ContinuousAdd R] [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R => IsOpen (I : Set R)) (fun I : Ideal R => (I : Set R)) :=
  hasBasis_open_submodule R

/--
theorem `_root_.isLinearTopology_iff_hasBasis_ideal` / 定理 `_root_.isLinearTopology_iff_hasBasis_ideal`

English:
theorem _root_.isLinearTopology_iff_hasBasis_ideal
  proof: isLinearTopology_iff_hasBasis_submodule

中文:
定理 _root_.isLinearTopology_iff_hasBasis_ideal
  证明: isLinearTopology_iff_hasBasis_submodule

Depends on / 依赖: isLinearTopology_iff_hasBasis_submodule
-/
theorem _root_.isLinearTopology_iff_hasBasis_ideal :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R => (I : Set R) in 𝓝 0) (fun I : Ideal R => (I : Set R)) :=
  isLinearTopology_iff_hasBasis_submodule

/--
theorem `_root_.isLinearTopology_iff_hasBasis_open_ideal` / 定理 `_root_.isLinearTopology_iff_hasBasis_open_ideal`

English:
theorem _root_.isLinearTopology_iff_hasBasis_open_ideal
  given: [IsTopologicalRing R]
  proof: isLinearTopology_iff_hasBasis_open_submodule

中文:
定理 _root_.isLinearTopology_iff_hasBasis_open_ideal
  条件: [是拓扑环 R]
  证明: isLinearTopology_iff_hasBasis_open_submodule

Depends on / 依赖: isLinearTopology_iff_hasBasis_open_submodule
-/
theorem _root_.isLinearTopology_iff_hasBasis_open_ideal [IsTopologicalRing R] :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R => IsOpen (I : Set R)) (fun I : Ideal R => (I : Set R)) :=
  isLinearTopology_iff_hasBasis_open_submodule

/--
theorem `hasBasis_right_ideal` / 定理 `hasBasis_right_ideal`

English:
theorem hasBasis_right_ideal
  given: [IsLinearTopology Rᵐᵒᵖ R]
  proof: hasBasis_submodule Rᵐᵒᵖ

中文:
定理 hasBasis_right_ideal
  条件: [是线性拓扑 Rᵐᵒᵖ R]
  证明: hasBasis_submodule Rᵐᵒᵖ

Depends on / 依赖: hasBasis_submodule
-/
theorem hasBasis_right_ideal [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 0).HasBasis (fun I : Submodule Rᵐᵒᵖ R => (I : Set R) in 𝓝 0) (fun I => (I : Set R)) :=
  hasBasis_submodule Rᵐᵒᵖ

set_option backward.isDefEq.respectTransparency false in
open Set Pointwise in
/--
lemma `hasBasis_twoSidedIdeal` / 引理 `hasBasis_twoSidedIdeal`

English:
lemma hasBasis_twoSidedIdeal
  given: [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]
  proof: .to_hasBasis hasBasis_subbimodule R Rᵐᵒᵖ
    (fun I ⟨hI, hRI, hRI'⟩ => ⟨.mk' I (zero_mem _) add_mem neg_mem (hRI _ _) (hRI' _ _),
      by simpa using hI, by simp⟩)
    (fun I hI => ⟨I.asIdeal.toAddSubgroup,
      ⟨hI, I.mul_mem_left, fun r x hx => I.mul_mem_right x (r.unop) hx⟩, subset_rfl⟩)

中文:
引理 hasBasis_twoSidedIdeal
  条件: [是线性拓扑 R R] [是线性拓扑 Rᵐᵒᵖ R]
  证明: .to_hasBasis hasBasis_subbimodule R Rᵐᵒᵖ
    (fun I ⟨hI, hRI, hRI'⟩ => ⟨.mk' I (zero_mem _) add_mem neg_mem (hRI _ _) (hRI' _ _),
      by simpa using hI, by simp⟩)
    (fun I hI => ⟨I.asIdeal.toAddSubgroup,
      ⟨hI, I.mul_mem_left, fun r x hx => I.mul_mem_right x (r.unop) hx⟩, subset_rfl⟩)

Depends on / 依赖: I.asIdeal.toAddSubgroup, I.mul_mem_left, I.mul_mem_right, add_mem, asIdeal, hasBasis_subbimodule, mul_mem_left, mul_mem_right, neg_mem, r.unop, subset_rfl, toAddSubgroup, to_hasBasis, zero_mem
-/
lemma hasBasis_twoSidedIdeal [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis (fun I : TwoSidedIdeal R => (I : Set R) in 𝓝 0)
      (fun I : TwoSidedIdeal R => (I : Set R)) :=
.to_hasBasis hasBasis_subbimodule R Rᵐᵒᵖ
    (fun I ⟨hI, hRI, hRI'⟩ => ⟨.mk' I (zero_mem _) add_mem neg_mem (hRI _ _) (hRI' _ _),
      by simpa using hI, by simp⟩)
    (fun I hI => ⟨I.asIdeal.toAddSubgroup,
      ⟨hI, I.mul_mem_left, fun r x hx => I.mul_mem_right x (r.unop) hx⟩, subset_rfl⟩)

/--
lemma `hasBasis_open_twoSidedIdeal` / 引理 `hasBasis_open_twoSidedIdeal`

English:
lemma hasBasis_open_twoSidedIdeal
  statement: [ContinuousAdd R]
  proof: hasBasis_twoSidedIdeal.congr
    (fun I => ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI => hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ => rfl)

中文:
引理 hasBasis_open_twoSidedIdeal
  结论: [连续加法 R]
  证明: hasBasis_twoSidedIdeal.congr
    (fun I => ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI => hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ => rfl)

Depends on / 依赖: I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, asIdeal, hI.mem_nhds, hasBasis_twoSidedIdeal, hasBasis_twoSidedIdeal.congr, isOpen_of_mem_nhds, mem_nhds, toAddSubgroup, zero_mem
-/
lemma hasBasis_open_twoSidedIdeal [ContinuousAdd R]
    [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis
      (fun I : TwoSidedIdeal R => IsOpen (I : Set R)) (fun I : TwoSidedIdeal R => (I : Set R)) :=
  hasBasis_twoSidedIdeal.congr
    (fun I => ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI => hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ => rfl)

/--
theorem `_root_.isLinearTopology_iff_hasBasis_twoSidedIdeal` / 定理 `_root_.isLinearTopology_iff_hasBasis_twoSidedIdeal`

English:
theorem _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal
  proof: ⟨fun ⟨_, _⟩ => hasBasis_twoSidedIdeal, fun h =>
    ⟨.mk_of_hasBasis' R h fun I r x hx => I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx => I.mul_mem_right x r.unop hx⟩⟩

中文:
定理 _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal
  证明: ⟨fun ⟨_, _⟩ => hasBasis_twoSidedIdeal, fun h =>
    ⟨.mk_of_hasBasis' R h fun I r x hx => I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx => I.mul_mem_right x r.unop hx⟩⟩

Depends on / 依赖: I.mul_mem_left, I.mul_mem_right, hasBasis_twoSidedIdeal, mk_of_hasBasis, mul_mem_left, mul_mem_right, r.unop
-/
theorem _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔
      (𝓝 0).HasBasis
        (fun I : TwoSidedIdeal R => (I : Set R) in 𝓝 0) (fun I : TwoSidedIdeal R => (I : Set R)) :=
  ⟨fun ⟨_, _⟩ => hasBasis_twoSidedIdeal, fun h =>
    ⟨.mk_of_hasBasis' R h fun I r x hx => I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx => I.mul_mem_right x r.unop hx⟩⟩

/--
theorem `_root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal` / 定理 `_root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal`

English:
theorem _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal
  given: [ContinuousAdd R]
  proof: ⟨fun ⟨_, _⟩ => hasBasis_open_twoSidedIdeal, fun h =>
    ⟨.mk_of_hasBasis' R h fun I r x hx => I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx => I.mul_mem_right x r.unop hx⟩⟩

中文:
定理 _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal
  条件: [连续加法 R]
  证明: ⟨fun ⟨_, _⟩ => hasBasis_open_twoSidedIdeal, fun h =>
    ⟨.mk_of_hasBasis' R h fun I r x hx => I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx => I.mul_mem_right x r.unop hx⟩⟩

Depends on / 依赖: I.mul_mem_left, I.mul_mem_right, hasBasis_open_twoSidedIdeal, mk_of_hasBasis, mul_mem_left, mul_mem_right, r.unop
-/
theorem _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal [ContinuousAdd R] :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal R => IsOpen (I : Set R)) (fun I : TwoSidedIdeal R => (I : Set R)) :=
  ⟨fun ⟨_, _⟩ => hasBasis_open_twoSidedIdeal, fun h =>
    ⟨.mk_of_hasBasis' R h fun I r x hx => I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx => I.mul_mem_right x r.unop hx⟩⟩

/--
theorem `tendsto_mul_zero_of_left` / 定理 `tendsto_mul_zero_of_left`

English:
theorem tendsto_mul_zero_of_left
  statement: [IsLinearTopology Rᵐᵒᵖ R] {ι : Type*} {f : Filter ι}
  proof: tendsto_smul_zero (R := Rᵐᵒᵖ) _ _ ha

中文:
定理 tendsto_mul_zero_of_left
  结论: [是线性拓扑 Rᵐᵒᵖ R] {ι : 类型} {f : 滤子 ι}
  证明: tendsto_smul_zero (R := Rᵐᵒᵖ) _ _ ha

Depends on / 依赖: tendsto_smul_zero
-/
theorem tendsto_mul_zero_of_left [IsLinearTopology Rᵐᵒᵖ R] {ι : Type*} {f : Filter ι}
    (a b : ι -> R) (ha : Tendsto a f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) :=
  tendsto_smul_zero (R := Rᵐᵒᵖ) _ _ ha

/--
theorem `tendsto_mul_zero_of_right` / 定理 `tendsto_mul_zero_of_right`

English:
theorem tendsto_mul_zero_of_right
  statement: [IsLinearTopology R R] {ι : Type*} {f : Filter ι}
  proof: tendsto_smul_zero (R := R) _ _ hb

中文:
定理 tendsto_mul_zero_of_right
  结论: [是线性拓扑 R R] {ι : 类型} {f : 滤子 ι}
  证明: tendsto_smul_zero (R := R) _ _ hb

Depends on / 依赖: tendsto_smul_zero
-/
theorem tendsto_mul_zero_of_right [IsLinearTopology R R] {ι : Type*} {f : Filter ι}
    (a b : ι -> R) (hb : Tendsto b f (𝓝 0)) :
    Tendsto (a * b) f (𝓝 0) :=
  tendsto_smul_zero (R := R) _ _ hb

end Ring

section CommRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R]

/-- If `R` is commutative and left-linearly topologized, it is also right-linearly topologized. -/
instance (priority := 100) [IsLinearTopology R R] :
    IsLinearTopology Rᵐᵒᵖ R := by
  rwa [IsCentralScalar.isLinearTopology_iff]

end CommRing

end IsLinearTopology
