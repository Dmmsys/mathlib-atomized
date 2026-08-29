/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth algebras have Noetherian models

In this file, we show if `S` is a smooth `R`-algebra, there exists a `ℤ`-subalgebra of finite type
`R₀` and a smooth `R₀`-algebra `S₀` such that `S ≃ₐ R ⊗[R₀] S₀`.

The analogous result for etale algebras is also provided.
-/

universe u

open TensorProduct MvPolynomial

namespace Algebra.Smooth

variable {R : Type*} [CommRing R]
variable {A : Type u} {B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra A B]

variable (A B) in
/--
Definition of `DescentAux` / `DescentAux` 的定义

English:
structure DescentAux
  parameters: where
  axioms and operations (11):
    - vars : Type
    - rels : Type
    - P : Presentation A B vars rels
    - σ : B ->ₐ[A] MvPolynomial vars A ⧸ P.ker ^ 2
    - h : vars -> MvPolynomial vars A
    - p : rels -> MvPolynomial rels (MvPolynomial vars A)
    - hphom : forall (j : rels), (p j).IsHomogeneous 2
    - hp : forall (j : rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
    - q : vars -> MvPolynomial rels P.Ring
    - hqhom : forall (i : vars), (q i).IsHomogeneous 1
    - hq : forall (i : vars), (eval P.relation) (q i) = h i - X i

中文:
结构 DescentAux
  参数: where
  公理与运算 (11 个):
    - vars : 类型
    - rels : 类型
    - P : 呈现 A B vars rels
    - σ : B ->ₐ[A] 多元多项式 vars A ⧸ P.ker ^ 2
    - h : vars -> 多元多项式 vars A
    - p : rels -> 多元多项式 rels (多元多项式 vars A)
    - hphom : 对任意 (j : rels), (p j).IsHomogeneous 2
    - hp : 对任意 (j : rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
    - q : vars -> 多元多项式 rels P.环
    - hqhom : 对任意 (i : vars), (q i).IsHomogeneous 1
    - hq : 对任意 (i : vars), (eval P.relation) (q i) = h i - X i
-/
structure DescentAux where
  vars : Type
  rels : Type
  P : Presentation A B vars rels
  σ : B ->ₐ[A] MvPolynomial vars A ⧸ P.ker ^ 2
  h : vars -> MvPolynomial vars A
  p : rels -> MvPolynomial rels (MvPolynomial vars A)
  hphom : forall (j : rels), (p j).IsHomogeneous 2
  hp : forall (j : rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
  q : vars -> MvPolynomial rels P.Ring
  hqhom : forall (i : vars), (q i).IsHomogeneous 1
  hq : forall (i : vars), (eval P.relation) (q i) = h i - X i

namespace DescentAux

variable (D : DescentAux A B)

variable (R)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `subalgebra` / `subalgebra` 的定义

English:
definition subalgebra
  signature: (D : DescentAux A B)
  body: Algebra.adjoin R
    (D.P.coeffs union
      ((⋃ i, (D.h i).coeffs) union
       (⋃ i, ⋃ x in (D.q i).coeffs, x.coeffs) union
       (⋃ i, ⋃ x in (D.p i).coeffs, x.coeffs)) : Set A)

中文:
定义 subalgebra
  签名: (D : DescentAux A B)
  定义体: Algebra.adjoin R
    (D.P.coeffs union
      ((⋃ i, (D.h i).coeffs) union
       (⋃ i, ⋃ x in (D.q i).coeffs, x.coeffs) union
       (⋃ i, ⋃ x in (D.p i).coeffs, x.coeffs)) : Set A)

Depends on / 依赖: Algebra, Algebra.adjoin, D.P.coeffs, adjoin, coeffs, x.coeffs
-/
noncomputable def subalgebra (D : DescentAux A B) : Subalgebra R A :=
  Algebra.adjoin R
    (D.P.coeffs union
      ((⋃ i, (D.h i).coeffs) union
       (⋃ i, ⋃ x in (D.q i).coeffs, x.coeffs) union
       (⋃ i, ⋃ x in (D.p i).coeffs, x.coeffs)) : Set A)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (D.subalgebra R)
  body: inferInstanceAs CommRing (Algebra.adjoin _ _)

中文:
实例 :
  签名: 交换环 (D.subalgebra R)
  定义体: inferInstanceAs CommRing (Algebra.adjoin _ _)

Depends on / 依赖: Algebra, Algebra.adjoin, CommRing, adjoin
-/
noncomputable instance : CommRing (D.subalgebra R) :=
inferInstanceAs CommRing (Algebra.adjoin _ _)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `algebra₀` / 实例 `algebra₀`

English:
instance algebra₀
  signature: : Algebra R (D.subalgebra R)
  body: inferInstanceAs Algebra R (Algebra.adjoin _ _)

中文:
实例 algebra₀
  签名: : 代数 R (D.subalgebra R)
  定义体: inferInstanceAs Algebra R (Algebra.adjoin _ _)

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin
-/
noncomputable instance algebra₀ : Algebra R (D.subalgebra R) :=
inferInstanceAs Algebra R (Algebra.adjoin _ _)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `algebra₁` / 实例 `algebra₁`

English:
instance algebra₁
  signature: : Algebra (D.subalgebra R) A
  body: inferInstanceAs Algebra (Algebra.adjoin _ _) A

中文:
实例 algebra₁
  签名: : 代数 (D.subalgebra R) A
  定义体: inferInstanceAs Algebra (Algebra.adjoin _ _) A

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin
-/
noncomputable instance algebra₁ : Algebra (D.subalgebra R) A :=
inferInstanceAs Algebra (Algebra.adjoin _ _) A

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `algebra₂` / 实例 `algebra₂`

English:
instance algebra₂
  signature: : Algebra (D.subalgebra R) B
  body: inferInstanceAs Algebra (Algebra.adjoin _ _) B

中文:
实例 algebra₂
  签名: : 代数 (D.subalgebra R) B
  定义体: inferInstanceAs Algebra (Algebra.adjoin _ _) B

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin
-/
noncomputable instance algebra₂ : Algebra (D.subalgebra R) B :=
inferInstanceAs Algebra (Algebra.adjoin _ _) B

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower (D.subalgebra R) A B
  body: inferInstanceAs IsScalarTower (Algebra.adjoin _ _) _ _

中文:
实例 :
  签名: 标量塔 (D.subalgebra R) A B
  定义体: inferInstanceAs IsScalarTower (Algebra.adjoin _ _) _ _

Depends on / 依赖: Algebra, Algebra.adjoin, IsScalarTower, adjoin
-/
instance : IsScalarTower (D.subalgebra R) A B :=
inferInstanceAs IsScalarTower (Algebra.adjoin _ _) _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul (D.subalgebra R) A
  body: inferInstanceAs FaithfulSMul (Algebra.adjoin _ _) _

中文:
实例 :
  签名: 忠实标量乘法 (D.subalgebra R) A
  定义体: inferInstanceAs FaithfulSMul (Algebra.adjoin _ _) _

Depends on / 依赖: Algebra, Algebra.adjoin, FaithfulSMul, adjoin
-/
instance : FaithfulSMul (D.subalgebra R) A := inferInstanceAs FaithfulSMul (Algebra.adjoin _ _) _

/--
lemma `fg_subalgebra` / 引理 `fg_subalgebra`

English:
lemma fg_subalgebra
  given: [Finite D.vars] [Finite D.rels]
  statement: (D.subalgebra R).FG
  proof: by
  refine Subalgebra.fg_def.mpr ⟨_, ?_, rfl⟩
  refine .union ?_ (.union (.union ?_ ?_) ?_)
  · exact Presentation.finite_coeffs
  · refine Set.finite_iUnion fun i => Finset.finite_toSet _
  · refine Set.finite_iUnion fun i => ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi => Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i => ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi => Finset.finite_toSet _)

中文:
引理 fg_subalgebra
  条件: [有限 D.vars] [有限 D.rels]
  结论: (D.subalgebra R).FG
  证明: by
  refine Subalgebra.fg_def.mpr ⟨_, ?_, rfl⟩
  refine .union ?_ (.union (.union ?_ ?_) ?_)
  · exact Presentation.finite_coeffs
  · refine Set.finite_iUnion fun i => Finset.finite_toSet _
  · refine Set.finite_iUnion fun i => ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi => Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i => ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi => Finset.finite_toSet _)

Depends on / 依赖: Finite, Finset, Finset.finite_toSet, Presentation, Presentation.finite_coeffs, Set.Finite.biUnion, Set.finite_iUnion, Subalgebra, Subalgebra.fg_def.mpr, biUnion, fg_def, finite_coeffs, finite_iUnion, finite_toSet
-/
lemma fg_subalgebra [Finite D.vars] [Finite D.rels] : (D.subalgebra R).FG := by
  refine Subalgebra.fg_def.mpr ⟨_, ?_, rfl⟩
  refine .union ?_ (.union (.union ?_ ?_) ?_)
  · exact Presentation.finite_coeffs
  · refine Set.finite_iUnion fun i => Finset.finite_toSet _
  · refine Set.finite_iUnion fun i => ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi => Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i => ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi => Finset.finite_toSet _)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasCoeffs` / 实例 `hasCoeffs`

English:
instance hasCoeffs
  signature: : D.P.HasCoeffs (D.subalgebra R) where
  body: by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
    problem in the new canonicalizer; a minimization would help. The original proof was:
    `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
    rw [Subalgebra.setRange_algebraMap]
    grind [subalgebra, Algebra.subset_adjoin]

中文:
实例 hasCoeffs
  签名: : D.P.有余effs (D.subalgebra R) where
  定义体: by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
    problem in the new canonicalizer; a minimization would help. The original proof was:
    `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
    rw [Subalgebra.setRange_algebraMap]
    grind [subalgebra, Algebra.subset_adjoin]

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Before, Mathlib, Subalgebra, Subalgebra.setRange_algebraMap, adaptation_note, canonicalizer, closed, directed, github, github.com, leanprover, minimization, normalizer, original, problem, replacing, setRange_algebraMap, subalgebra
-/
instance hasCoeffs : D.P.HasCoeffs (D.subalgebra R) where
  coeffs_subset_range := by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
    problem in the new canonicalizer; a minimization would help. The original proof was:
    `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
    rw [Subalgebra.setRange_algebraMap]
    grind [subalgebra, Algebra.subset_adjoin]

set_option quotPrecheck false in
local notation "f₀" =>
  Ideal.Quotient.mkₐ (D.subalgebra R)
    (Ideal.span <| .range <| D.P.relationOfHasCoeffs (D.subalgebra R))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coeffs_h_subset` / 引理 `coeffs_h_subset`

English:
lemma coeffs_h_subset
  given: (i)
  statement: ↑(D.h i).coeffs subseteq Set.range ⇑(algebraMap (D.subalgebra R) A)
  proof: by
  have : ((D.h i).coeffs : Set _) subseteq ⋃ i, ((D.h i).coeffs : Set A) :=
    Set.subset_iUnion_of_subset i subset_rfl
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

中文:
引理 coeffs_h_subset
  条件: (i)
  结论: ↑(D.h i).coeffs subseteq 集合.range ⇑(algebraMap (D.subalgebra R) A)
  证明: by
  have : ((D.h i).coeffs : Set _) subseteq ⋃ i, ((D.h i).coeffs : Set A) :=
    Set.subset_iUnion_of_subset i subset_rfl
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

Depends on / 依赖: Before, Mathlib, Set.subset_iUnion_of_subset, Subalgebra, Subalgebra.setRange_a, adaptation_note, canonicalizer, closed, coeffs, directed, github, github.com, leanprover, minimization, normalizer, original, problem, replacing, setRange_a, subalgebra
-/
lemma coeffs_h_subset (i) : ↑(D.h i).coeffs subseteq Set.range ⇑(algebraMap (D.subalgebra R) A) := by
  have : ((D.h i).coeffs : Set _) subseteq ⋃ i, ((D.h i).coeffs : Set A) :=
    Set.subset_iUnion_of_subset i subset_rfl
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coeffs_p_subset` / 引理 `coeffs_p_subset`

English:
lemma coeffs_p_subset
  given: (i)
  proof: by
  intro p hp
  have : (p.coeffs : Set A) subseteq ⋃ i, ⋃ x in (D.p i).coeffs, ↑x.coeffs :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]; rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

中文:
引理 coeffs_p_subset
  条件: (i)
  证明: by
  intro p hp
  have : (p.coeffs : Set A) subseteq ⋃ i, ⋃ x in (D.p i).coeffs, ↑x.coeffs :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]; rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

Depends on / 依赖: Before, D.subalgebra, D.vars, Mathlib, Set.subset_iUnion, Set.subset_iUnion_of_subset, adaptation_note, algebraMap, canonicalizer, closed, coeffs, directed, github, github.com, leanprover, normalizer, p.coeffs, problem, replacing, subalgebra
-/
lemma coeffs_p_subset (i) :
    ↑(D.p i).coeffs subseteq
      Set.range (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) := by
  intro p hp
  have : (p.coeffs : Set A) subseteq ⋃ i, ⋃ x in (D.p i).coeffs, ↑x.coeffs :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]; rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coeffs_q_subset` / 引理 `coeffs_q_subset`

English:
lemma coeffs_q_subset
  given: (i)
  proof: by
  intro q hq
  have : (q.coeffs : Set A) subseteq ⋃ i, ⋃ x in (D.q i).coeffs, ↑(coeffs x) :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]; rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

中文:
引理 coeffs_q_subset
  条件: (i)
  证明: by
  intro q hq
  have : (q.coeffs : Set A) subseteq ⋃ i, ⋃ x in (D.q i).coeffs, ↑(coeffs x) :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]; rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

Depends on / 依赖: Before, D.subalgebra, D.vars, Mathlib, Set.subset_iUnion, Set.subset_iUnion_of_subset, adaptation_note, algebraMap, canonicalize, canonicalizer, closed, coeffs, directed, github, github.com, leanprover, normalizer, problem, q.coeffs, replacing
-/
lemma coeffs_q_subset (i) :
    ↑(D.q i).coeffs subseteq
      Set.range (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) := by
  intro q hq
  have : (q.coeffs : Set A) subseteq ⋃ i, ⋃ x in (D.q i).coeffs, ↑(coeffs x) :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]; rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_kerSquareLift_comp_eq_id` / 引理 `exists_kerSquareLift_comp_eq_id`

English:
lemma exists_kerSquareLift_comp_eq_id
  proof: by
  choose p hp using fun i => (D.h i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_h_subset R i)
  refine ⟨?_, ?_⟩
  · refine Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval p) ?_
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
    obtain ⟨q, hq⟩ := (D.p i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_p_subset R i)
    refine ⟨q, .of_map hinj ?_, hinj ?_⟩
    · rw [hq]
      exact D.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_relationOfHasCoeffs,
        hq, D.hp, MvPolynomial.map_aeval, hp]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_relationOfHasCoeffs, aeval_def]
  · have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
    rw [← AlgHom.cancel_right hf₀]
    refine MvPolynomial.algHom_ext fun i => ?_
    suffices h : exists p', p'.IsHomogeneous 1 ∧ (eval (D.P.relationOfHasCoeffs (D.subalgebra R))) p' =
        p i - X i by
      -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
      -- Can be fixed after #25138.
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa [Ideal.mem_span_iff_exists_isHomogeneous, hp]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    obtain ⟨t, ht⟩ := (D.q i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_q_subset R i)
    refine ⟨t, .of_map hinj ?_, hinj ?_⟩
    · rw [ht]
      exact D.hqhom i
    · simp [MvPolynomial.map_eval, Function.comp_def,
        Presentation.map_relationOfHasCoeffs, ht, hq, hp]

中文:
引理 存在_kerSquareLift_comp_eq_id
  证明: by
  choose p hp using fun i => (D.h i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_h_subset R i)
  refine ⟨?_, ?_⟩
  · refine Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval p) ?_
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
    obtain ⟨q, hq⟩ := (D.p i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_p_subset R i)
    refine ⟨q, .of_map hinj ?_, hinj ?_⟩
    · rw [hq]
      exact D.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_relationOfHasCoeffs,
        hq, D.hp, MvPolynomial.map_aeval, hp]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_relationOfHasCoeffs, aeval_def]
  · have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
    rw [← AlgHom.cancel_right hf₀]
    refine MvPolynomial.algHom_ext fun i => ?_
    suffices h : exists p', p'.IsHomogeneous 1 ∧ (eval (D.P.relationOfHasCoeffs (D.subalgebra R))) p' =
        p i - X i by
      -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
      -- Can be fixed after #25138.
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa [Ideal.mem_span_iff_exists_isHomogeneous, hp]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    obtain ⟨t, ht⟩ := (D.q i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_q_subset R i)
    refine ⟨t, .of_map hinj ?_, hinj ?_⟩
    · rw [ht]
      exact D.hqhom i
    · simp [MvPolynomial.map_eval, Function.comp_def,
        Presentation.map_relationOfHasCoeffs, ht, hq, hp]

Depends on / 依赖: AlgHom, AlgHom.comap_ker, D.coeffs_h_subset, Ideal.Quotient.lift, Ideal.Quotient.mk, Ideal.coe_comap, Ideal.span_le, Quotient, RingHom, RingHom.ker_coe_toRingHom, RingHom.mem_ker, Set.mem_preimage, Set.range_subset_iff, SetLike, SetLike.le_def, SetLike.mem_coe, coe_comap, coeffs_h_subset, comap_ker, ker_coe_toRingHom
-/
lemma exists_kerSquareLift_comp_eq_id :
    exists (σ₀ : D.P.ModelOfHasCoeffs (D.subalgebra R) ->ₐ[D.subalgebra R]
        MvPolynomial D.vars (D.subalgebra R) ⧸ (RingHom.ker f₀ ^ 2)),
      (AlgHom.kerSquareLift f₀).comp σ₀ =
        .id (D.subalgebra R) (Presentation.ModelOfHasCoeffs (D.subalgebra R)) := by
  choose p hp using fun i => (D.h i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_h_subset R i)
  refine ⟨?_, ?_⟩
  · refine Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval p) ?_
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [Ideal.Quotient.mkₐ_ker]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
    obtain ⟨q, hq⟩ := (D.p i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_p_subset R i)
    refine ⟨q, .of_map hinj ?_, hinj ?_⟩
    · rw [hq]
      exact D.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_relationOfHasCoeffs,
        hq, D.hp, MvPolynomial.map_aeval, hp]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_relationOfHasCoeffs, aeval_def]
  · have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
    rw [← AlgHom.cancel_right hf₀]
    refine MvPolynomial.algHom_ext fun i => ?_
    suffices h : exists p', p'.IsHomogeneous 1 ∧ (eval (D.P.relationOfHasCoeffs (D.subalgebra R))) p' =
        p i - X i by
      -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
      -- Can be fixed after #25138.
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa [Ideal.mem_span_iff_exists_isHomogeneous, hp]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    obtain ⟨t, ht⟩ := (D.q i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_q_subset R i)
    refine ⟨t, .of_map hinj ?_, hinj ?_⟩
    · rw [ht]
      exact D.hqhom i
    · simp [MvPolynomial.map_eval, Function.comp_def,
        Presentation.map_relationOfHasCoeffs, ht, hq, hp]

end DescentAux

variable (R A B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Let `A` be an `R`-algebra. If `B` is a smooth `A`-algebra, there exists an
`R`-subalgebra of finite type `A₀` of `A` and a smooth `A₀`-algebra `B₀` such that
`B ≃ₐ A ⊗[A₀] B₀`.
See `Algebra.Smooth.exists_finiteType` for a version in terms of `Function.Injective`.
-/
public theorem exists_subalgebra_fg [Smooth A B] :
    exists (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Smooth A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A otimes[A₀] B₀) := by
  let P := Presentation.ofFinitePresentation A B
  let f : P.Ring ->ₐ[A] B := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  obtain ⟨(σ : B ->ₐ[A] MvPolynomial _ A ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (FormallySmooth.iff_split_surjection f P.algebraMap_surjective).mp inferInstance
  have (i : _) := Ideal.Quotient.mk_surjective (σ <| P.val i)
  choose h hh using this
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = σ.comp (aeval P.val) :=
    algHom_ext (by simp [hh])
  have (j : _) : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (P.relation j)) = 0 := by
    suffices ho : σ (aeval P.val (P.relation j)) = 0 by
      convert! ho
      exact congr($hdiag _)
    simp
  simp_rw [Ideal.Quotient.eq_zero_iff_mem, hkerf,
    Ideal.mem_span_pow_iff_exists_isHomogeneous] at this
  choose p homog hp using this
  have hsig (i : _) : f (h i) = P.val i := by
    rw [← AlgHom.kerSquareLift_mk]
    -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
    -- Can be fixed after #25138.
    exact hh i ▸ congr($hsig (P.val i))
  have (i : Fin (Presentation.ofFinitePresentationVars A B)) :
      h i - X i in Ideal.span (.range P.relation) := by
    simpa [P.span_range_relation_eq_ker, sub_eq_zero, f] using hsig i
  simp_rw [Ideal.mem_span_iff_exists_isHomogeneous] at this
  choose q hqhom hq using this
  let D : DescentAux A B :=
    { vars := _, rels := _, P := P, σ := σ, p := p, h := h, hphom := homog, hp := hp,
      q := q, hqhom := hqhom, hq := hq }
  have : P.HasCoeffs (D.subalgebra R) := D.hasCoeffs R
  obtain ⟨σ₀, hσ₀⟩ := D.exists_kerSquareLift_comp_eq_id R
  exact ⟨D.subalgebra R, P.ModelOfHasCoeffs (D.subalgebra R), inferInstance, inferInstance,
    D.fg_subalgebra R, ⟨.of_split _ σ₀ hσ₀, inferInstance⟩,
    ⟨(P.tensorModelOfHasCoeffsEquiv (D.subalgebra R)).symm⟩⟩

@[deprecated exists_subalgebra_fg (since := "2026-01-07")]
public theorem exists_subalgebra_finiteType [Smooth A B] :
    exists (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      FiniteType R A₀ ∧ Smooth A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A otimes[A₀] B₀) := by
  obtain ⟨A₀, B₀, _, _, h0, h1, h2⟩ := exists_subalgebra_fg R A B
  exact ⟨A₀, B₀, inferInstance, inferInstance, (Subalgebra.fg_iff_finiteType A₀).mp h0, h1, h2⟩

/--
Let `A` be an `R`-algebra. If `B` is a smooth `A`-algebra, there exists an
`R`-algebra of finite type `A₀` and a smooth `A₀`-algebra `B₀` such that `B ≃ₐ A ⊗[A₀] B₀`
with `A₀ → A` injective.
See `Algebra.Smooth.exists_subalgebra_fg` for a version in terms of `Subalgebra`.
-/
@[stacks 00TP]
public theorem exists_finiteType [Smooth A B] :
    exists (A₀ : Type u) (B₀ : Type u) (_ : CommRing A₀) (_ : CommRing B₀)
      (_ : Algebra R A₀) (_ : Algebra A₀ A) (_ : Algebra A₀ B₀),
      Function.Injective (algebraMap A₀ A) ∧ FiniteType R A₀ ∧ Smooth A₀ B₀ ∧
      Nonempty (B ≃ₐ[A] A otimes[A₀] B₀) := by
  obtain ⟨A₀, B₀, _, _, hA₀, _, _⟩ := exists_subalgebra_fg R A B
  use A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val_injective, ⟨A₀.fg_top.mpr hA₀⟩, inferInstance

public theorem _root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg
    (n : Nat) [IsStandardSmoothOfRelativeDimension n A B] :
    exists (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ IsStandardSmoothOfRelativeDimension n A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A otimes[A₀] B₀) := by
  obtain ⟨ι, σ, _, _, P, hP⟩ := IsStandardSmoothOfRelativeDimension.out (n := n) (R := A) (S := B)
  let A₀ := Algebra.adjoin R P.coeffs
  have : P.HasCoeffs A₀ := ⟨by simp [A₀]⟩
  exact ⟨A₀, (P.ModelOfHasCoeffs A₀:), inferInstance, inferInstance,
    ⟨P.finite_coeffs.toFinset, by simp [A₀]⟩, ⟨_, _, _, inferInstance,
      P.ofHasCoeffs A₀, hP⟩, ⟨(P.tensorModelOfHasCoeffsEquiv A₀).symm⟩⟩

/--
Let `A` be an `R`-algebra. If `B` is an etale `A`-algebra, there exists an
`R`-subalgebra of finite type `A₀` of `A` and an etale `A₀`-algebra `B₀` such that
`B ≃ₐ A ⊗[A₀] B₀`.
-/
@[stacks 00U2 "(8)"]
public theorem _root_.Algebra.Etale.exists_subalgebra_fg [Etale A B] :
    exists (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A otimes[A₀] B₀) := by
  simp only [Etale.iff_isStandardSmoothOfRelativeDimension_zero] at *
  exact IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg ..

end Algebra.Smooth
