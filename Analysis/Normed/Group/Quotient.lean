/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Quotients of seminormed groups

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M`, we provide a
`SeminormedAddCommGroup`, the group quotient `M ⧸ S`.
If `S` is closed, we provide `NormedAddCommGroup (M ⧸ S)` (regardless of whether `M` itself is
separated). The two main properties of these structures are the underlying topology is the quotient
topology and the projection is a normed group homomorphism which is norm non-increasing
(better, it has operator norm exactly one unless `S` is dense in `M`). The corresponding
universal property is that every normed group hom defined on `M` which vanishes on `S` descends
to a normed group hom defined on `M ⧸ S`.

This file also introduces a predicate `IsQuotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.

In addition, this file also provides normed structures for quotients of modules by submodules, and
of (commutative) rings by ideals. The `SeminormedAddCommGroup` and `NormedAddCommGroup`
instances described above are transferred directly, but we also define instances of `NormedSpace`,
`SeminormedCommRing`, `NormedCommRing` and `NormedAlgebra` under appropriate type class
assumptions on the original space. Moreover, while `QuotientAddGroup.completeSpace_right` works
out-of-the-box for quotients of `NormedAddCommGroup`s by `AddSubgroup`s, we need to transfer
this instance in `Submodule.Quotient.completeSpace` so that it applies to these other quotients.

## Main definitions


We use `M` and `N` to denote seminormed groups and `S : AddSubgroup M`.
All the following definitions are in the `AddSubgroup` namespace. Hence we can access
`AddSubgroup.normedMk S` as `S.normedMk`.

* `seminormedAddCommGroupQuotient` : The seminormed group structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedAddCommGroupQuotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedMk S` : the normed group hom from `M` to `M ⧸ S`.

* `lift S f hf`: implements the universal property of `M ⧸ S`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : NormedAddGroupHom (M ⧸ S) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `IsQuotient.norm_lift`: Provided `f : normed_hom M N` satisfies `IsQuotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M` we define a norm on `M ⧸ S` by
`‖x‖ = sInf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `M ⧸ S` is automatically a topological space (as any quotient of a topological space),
one needs to be careful while defining the `SeminormedAddCommGroup` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhds_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ‖x‖ < ε}` for positive `ε`.

Once this mathematical point is settled, we have two topologies that are propositionally equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `SeminormedAddCommGroup` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `IsTopologicalAddGroup.rightUniformSpace`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/

@[expose] public section


noncomputable section

open Metric Set Topology NNReal

namespace QuotientGroup
variable {M : Type*} [SeminormedCommGroup M] {S T : Subgroup M} {x : M ⧸ S} {m : M} {r ε : Real}

@[to_additive add_norm_aux]
/--
lemma `norm_aux` / 引理 `norm_aux`

English:
lemma norm_aux
  given: (x : M ⧸ S)
  statement: {m : M | (m : M ⧸ S) = x}.Nonempty
  proof: Quot.exists_rep x

中文:
引理 norm_aux
  条件: (x : M ⧸ S)
  结论: {m : M | (m : M ⧸ S) = x}.非空
  证明: Quot.exists_rep x
-/
private lemma norm_aux (x : M ⧸ S) : {m : M | (m : M ⧸ S) = x}.Nonempty := Quot.exists_rep x

/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x * M`. -/
@[to_additive
/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x + S`. -/]
/--
Definition of `groupSeminorm` / `groupSeminorm` 的定义

English:
definition groupSeminorm
  signature: : GroupSeminorm (M ⧸ S) where
  body: infDist 1 {m : M | (m : M ⧸ S) = x}
  map_one' := infDist_zero_of_mem (by simp)
  mul_le' x y := by
    simp only [infDist_eq_iInf]
    have := (norm_aux x).to_subtype
    have := (norm_aux y).to_subtype
    refine le_ciInf_add_ciInf ?_
    rintro ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ciInf_le_of_le ⟨0, fora

中文:
定义 groupSeminorm
  签名: : 群半范数 (M ⧸ S) where
  定义体: infDist 1 {m : M | (m : M ⧸ S) = x}
  map_one' := infDist_zero_of_mem (by simp)
  mul_le' x y := by
    simp only [infDist_eq_iInf]
    have := (norm_aux x).to_subtype
    have := (norm_aux y).to_subtype
    refine le_ciInf_add_ciInf ?_
    rintro ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ciInf_le_of_le ⟨0, fora

Depends on / 依赖: infDist
-/
noncomputable def groupSeminorm : GroupSeminorm (M ⧸ S) where
  toFun x := infDist 1 {m : M | (m : M ⧸ S) = x}
  map_one' := infDist_zero_of_mem (by simp)
  mul_le' x y := by
    simp only [infDist_eq_iInf]
    have := (norm_aux x).to_subtype
    have := (norm_aux y).to_subtype
    refine le_ciInf_add_ciInf ?_
    rintro ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ciInf_le_of_le ⟨0, forall_mem_range.2 fun _ => dist_nonneg⟩ ⟨a * b, rfl⟩ ?_
    simpa using norm_mul_le' _ _
  inv' x := eq_of_forall_le_iff fun r => by
    simp only [le_infDist (norm_aux _)]
    exact (Equiv.inv _).forall_congr (by simp [← inv_eq_iff_eq_inv])

/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x * S`. -/
@[to_additive
/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x + S`. -/]
/--
Instance `instNorm` / 实例 `instNorm`

English:
instance instNorm
  signature: : Norm (M ⧸ S) where norm
  body: groupSeminorm

@[to_additive]

中文:
实例 instNorm
  签名: : 范数 (M ⧸ S) where norm
  定义体: groupSeminorm

@[to_additive]

Depends on / 依赖: groupSeminorm
-/
noncomputable instance instNorm : Norm (M ⧸ S) where norm := groupSeminorm

@[to_additive]
/--
lemma `norm_eq_groupSeminorm` / 引理 `norm_eq_groupSeminorm`

English:
lemma norm_eq_groupSeminorm
  given: (x : M ⧸ S)
  statement: ‖x‖ = groupSeminorm x
  proof: rfl

@[to_additive]

中文:
引理 norm_eq_groupSeminorm
  条件: (x : M ⧸ S)
  结论: ‖x‖ = groupSeminorm x
  证明: rfl

@[to_additive]
-/
lemma norm_eq_groupSeminorm (x : M ⧸ S) : ‖x‖ = groupSeminorm x := rfl

@[to_additive]
/--
lemma `norm_eq_infDist` / 引理 `norm_eq_infDist`

English:
lemma norm_eq_infDist
  given: (x : M ⧸ S)
  statement: ‖x‖ = infDist 1 {m : M | (m : M ⧸ S) = x}
  proof: rfl

@[to_additive]

中文:
引理 norm_eq_infDist
  条件: (x : M ⧸ S)
  结论: ‖x‖ = infDist 1 {m : M | (m : M ⧸ S) = x}
  证明: rfl

@[to_additive]
-/
lemma norm_eq_infDist (x : M ⧸ S) : ‖x‖ = infDist 1 {m : M | (m : M ⧸ S) = x} := rfl

@[to_additive]
/--
lemma `le_norm_iff` / 引理 `le_norm_iff`

English:
lemma le_norm_iff
  statement: r <= ‖x‖ ↔ forall m : M, ↑m = x -> r <= ‖m‖
  proof: by
  simp [norm_eq_infDist, le_infDist (norm_aux _)]

@[to_additive]

中文:
引理 le_norm_iff
  结论: r <= ‖x‖ ↔ 对任意 m : M, ↑m = x -> r <= ‖m‖
  证明: by
  simp [norm_eq_infDist, le_infDist (norm_aux _)]

@[to_additive]

Depends on / 依赖: le_infDist, norm_aux, norm_eq_infDist
-/
lemma le_norm_iff : r <= ‖x‖ ↔ forall m : M, ↑m = x -> r <= ‖m‖ := by
  simp [norm_eq_infDist, le_infDist (norm_aux _)]

@[to_additive]
/--
lemma `norm_lt_iff` / 引理 `norm_lt_iff`

English:
lemma norm_lt_iff
  statement: ‖x‖ < r ↔ exists m : M, ↑m = x ∧ ‖m‖ < r
  proof: by
  simp [norm_eq_infDist, infDist_lt_iff (norm_aux _)]

@[to_additive]

中文:
引理 norm_lt_iff
  结论: ‖x‖ < r ↔ 存在 m : M, ↑m = x ∧ ‖m‖ < r
  证明: by
  simp [norm_eq_infDist, infDist_lt_iff (norm_aux _)]

@[to_additive]

Depends on / 依赖: infDist_lt_iff, norm_aux, norm_eq_infDist
-/
lemma norm_lt_iff : ‖x‖ < r ↔ exists m : M, ↑m = x ∧ ‖m‖ < r := by
  simp [norm_eq_infDist, infDist_lt_iff (norm_aux _)]

@[to_additive]
/--
lemma `nhds_one_hasBasis` / 引理 `nhds_one_hasBasis`

English:
lemma nhds_one_hasBasis
  statement: (𝓝 (1 : M ⧸ S)).HasBasis (fun ε => 0 < ε) fun ε => {x | ‖x‖ < ε}
  proof: by
  have : forall ε : Real, mk '' ball (1 : M) ε = {x : M ⧸ S | ‖x‖ < ε} := by
refine fun ε => Set.ext forall_mk.2 fun x => ?_
    rw [ball_one_eq]; rw [mem_ofPred_eq]; rw [norm_lt_iff]; rw [mem_image]
    exact exists_congr fun _ => and_comm
  rw [← mk_one]; rw [nhds_eq]; rw [← funext this]
  exac

中文:
引理 nhds_one_hasBasis
  结论: (𝓝 (1 : M ⧸ S)).有基 (fun ε => 0 < ε) fun ε => {x | ‖x‖ < ε}
  证明: by
  have : forall ε : Real, mk '' ball (1 : M) ε = {x : M ⧸ S | ‖x‖ < ε} := by
refine fun ε => Set.ext forall_mk.2 fun x => ?_
    rw [ball_one_eq]; rw [mem_ofPred_eq]; rw [norm_lt_iff]; rw [mem_image]
    exact exists_congr fun _ => and_comm
  rw [← mk_one]; rw [nhds_eq]; rw [← funext this]
  exac

Depends on / 依赖: Metric, Metric.nhds_basis_ball, Set.ext, and_comm, ball_one_eq, exists_congr, forall_mk, mem_image, mem_ofPred_eq, mk_one, nhds_basis_ball, nhds_eq, norm_lt_iff
-/
lemma nhds_one_hasBasis : (𝓝 (1 : M ⧸ S)).HasBasis (fun ε => 0 < ε) fun ε => {x | ‖x‖ < ε} := by
  have : forall ε : Real, mk '' ball (1 : M) ε = {x : M ⧸ S | ‖x‖ < ε} := by
refine fun ε => Set.ext forall_mk.2 fun x => ?_
    rw [ball_one_eq]; rw [mem_ofPred_eq]; rw [norm_lt_iff]; rw [mem_image]
    exact exists_congr fun _ => and_comm
  rw [← mk_one]; rw [nhds_eq]; rw [← funext this]
  exact .map _ Metric.nhds_basis_ball

/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/
@[to_additive
/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/]
/--
lemma `norm_mk` / 引理 `norm_mk`

English:
lemma norm_mk
  given: (x : M)
  statement: ‖(x : M ⧸ S)‖ = infDist x S
  proof: by
  rw [norm_eq_infDist]; rw [← infDist_image (IsometryEquiv.divLeft x).isometry]; rw [← IsometryEquiv.preimage_symm]
  simp

中文:
引理 norm_mk
  条件: (x : M)
  结论: ‖(x : M ⧸ S)‖ = infDist x S
  证明: by
  rw [norm_eq_infDist]; rw [← infDist_image (IsometryEquiv.divLeft x).isometry]; rw [← IsometryEquiv.preimage_symm]
  simp

Depends on / 依赖: IsometryEquiv, IsometryEquiv.divLeft, IsometryEquiv.preimage_symm, divLeft, infDist_image, isometry, norm_eq_infDist, preimage_symm
-/
lemma norm_mk (x : M) : ‖(x : M ⧸ S)‖ = infDist x S := by
  rw [norm_eq_infDist]; rw [← infDist_image (IsometryEquiv.divLeft x).isometry]; rw [← IsometryEquiv.preimage_symm]
  simp

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
@[to_additive
/-- The norm of the projection is smaller or equal to the norm of the original element. -/]
/--
lemma `norm_mk_le_norm` / 引理 `norm_mk_le_norm`

English:
lemma norm_mk_le_norm
  statement: ‖(m : M ⧸ S)‖ <= ‖m‖
  proof: (infDist_le_dist_of_mem (by simp)).trans_eq (dist_one_left _)

中文:
引理 norm_mk_le_norm
  结论: ‖(m : M ⧸ S)‖ <= ‖m‖
  证明: (infDist_le_dist_of_mem (by simp)).trans_eq (dist_one_left _)

Depends on / 依赖: dist_one_left, infDist_le_dist_of_mem, trans_eq
-/
lemma norm_mk_le_norm : ‖(m : M ⧸ S)‖ <= ‖m‖ :=
  (infDist_le_dist_of_mem (by simp)).trans_eq (dist_one_left _)

/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
@[to_additive /-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m`
belongs to the closure of `S`. -/]
/--
lemma `norm_mk_eq_zero_iff_mem_closure` / 引理 `norm_mk_eq_zero_iff_mem_closure`

English:
lemma norm_mk_eq_zero_iff_mem_closure
  statement: ‖(m : M ⧸ S)‖ = 0 ↔ m in closure (S : Set M)
  proof: by
  rw [norm_mk]; rw [← mem_closure_iff_infDist_zero]
  exact ⟨1, S.one_mem⟩

中文:
引理 norm_mk_eq_zero_iff_mem_closure
  结论: ‖(m : M ⧸ S)‖ = 0 ↔ m in closure (S : 集合 M)
  证明: by
  rw [norm_mk]; rw [← mem_closure_iff_infDist_zero]
  exact ⟨1, S.one_mem⟩

Depends on / 依赖: S.one_mem, mem_closure_iff_infDist_zero, norm_mk, one_mem
-/
lemma norm_mk_eq_zero_iff_mem_closure : ‖(m : M ⧸ S)‖ = 0 ↔ m in closure (S : Set M) := by
  rw [norm_mk]; rw [← mem_closure_iff_infDist_zero]
  exact ⟨1, S.one_mem⟩

/-- The norm of the image of `m : M` in the quotient by a closed subgroup `S` is zero if and only if
`m ∈ S`. -/
@[to_additive /-- The norm of the image of `m : M` in the quotient by a closed subgroup `S` is zero
if and only if `m ∈ S`. -/]
/--
lemma `norm_mk_eq_zero` / 引理 `norm_mk_eq_zero`

English:
lemma norm_mk_eq_zero
  given: [hS : IsClosed (S : Set M)]
  statement: ‖(m : M ⧸ S)‖ = 0 ↔ m in S
  proof: by
  rw [norm_mk_eq_zero_iff_mem_closure]; rw [hS.closure_eq]; rw [SetLike.mem_coe]

中文:
引理 norm_mk_eq_zero
  条件: [hS : 是闭集 (S : 集合 M)]
  结论: ‖(m : M ⧸ S)‖ = 0 ↔ m in S
  证明: by
  rw [norm_mk_eq_zero_iff_mem_closure]; rw [hS.closure_eq]; rw [SetLike.mem_coe]

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_eq, hS.closure_eq, mem_coe, norm_mk_eq_zero_iff_mem_closure
-/
lemma norm_mk_eq_zero [hS : IsClosed (S : Set M)] : ‖(m : M ⧸ S)‖ = 0 ↔ m in S := by
  rw [norm_mk_eq_zero_iff_mem_closure]; rw [hS.closure_eq]; rw [SetLike.mem_coe]

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/
@[to_additive /-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/]
/--
lemma `exists_norm_mk_lt` / 引理 `exists_norm_mk_lt`

English:
lemma exists_norm_mk_lt
  given: (x : M ⧸ S) (hε : 0 < ε)
  statement: exists m : M, m = x ∧ ‖m‖ < ‖x‖ + ε
  proof: norm_lt_iff.1 lt_add_of_pos_right _ hε

中文:
引理 存在_norm_mk_lt
  条件: (x : M ⧸ S) (hε : 0 < ε)
  结论: 存在 m : M, m = x ∧ ‖m‖ < ‖x‖ + ε
  证明: norm_lt_iff.1 lt_add_of_pos_right _ hε

Depends on / 依赖: lt_add_of_pos_right, norm_lt_iff
-/
lemma exists_norm_mk_lt (x : M ⧸ S) (hε : 0 < ε) : exists m : M, m = x ∧ ‖m‖ < ‖x‖ + ε :=
norm_lt_iff.1 lt_add_of_pos_right _ hε

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m * s‖ < ‖mk' S m‖ + ε`. -/
@[to_additive
/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m + s‖ < ‖mk' S m‖ + ε`. -/]
/--
lemma `exists_norm_mul_lt` / 引理 `exists_norm_mul_lt`

English:
lemma exists_norm_mul_lt
  given: (S : Subgroup M) (m : M) {ε : Real} (hε : 0 < ε)
  proof: by
  obtain ⟨n : M, hn, hn'⟩ := exists_norm_mk_lt (QuotientGroup.mk' S m) hε
  exact ⟨m⁻¹ * n, by simpa [eq_comm, QuotientGroup.eq] using hn, by simpa⟩

中文:
引理 存在_norm_mul_lt
  条件: (S : 子群 M) (m : M) {ε : 实数} (hε : 0 < ε)
  证明: by
  obtain ⟨n : M, hn, hn'⟩ := exists_norm_mk_lt (QuotientGroup.mk' S m) hε
  exact ⟨m⁻¹ * n, by simpa [eq_comm, QuotientGroup.eq] using hn, by simpa⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, QuotientGroup.mk, eq_comm, exists_norm_mk_lt
-/
lemma exists_norm_mul_lt (S : Subgroup M) (m : M) {ε : Real} (hε : 0 < ε) :
    exists s in S, ‖m * s‖ < ‖mk' S m‖ + ε := by
  obtain ⟨n : M, hn, hn'⟩ := exists_norm_mk_lt (QuotientGroup.mk' S m) hε
  exact ⟨m⁻¹ * n, by simpa [eq_comm, QuotientGroup.eq] using hn, by simpa⟩

variable (S) in
/-- The seminormed group structure on the quotient by a subgroup. -/
@[to_additive /-- The seminormed group structure on the quotient by an additive subgroup. -/]
/--
Instance `instSeminormedCommGroup` / 实例 `instSeminormedCommGroup`

English:
instance instSeminormedCommGroup
  signature: : SeminormedCommGroup (M ⧸ S) where
  body: IsTopologicalGroup.leftUniformSpace (M ⧸ S)
  __ := groupSeminorm.toSeminormedCommGroup
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_one_left]; rw [(nhds_one_hasBasis.comap _).eq_biInf]
    simp only [dist, preimage_ofPred_eq, norm_eq_groupSeminorm]

中文:
实例 instSeminormedCommGroup
  签名: : SeminormedComm群 (M ⧸ S) where
  定义体: IsTopologicalGroup.leftUniformSpace (M ⧸ S)
  __ := groupSeminorm.toSeminormedCommGroup
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_one_left]; rw [(nhds_one_hasBasis.comap _).eq_biInf]
    simp only [dist, preimage_ofPred_eq, norm_eq_groupSeminorm]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.leftUniformSpace, leftUniformSpace
-/
noncomputable instance instSeminormedCommGroup : SeminormedCommGroup (M ⧸ S) where
  toUniformSpace := IsTopologicalGroup.leftUniformSpace (M ⧸ S)
  __ := groupSeminorm.toSeminormedCommGroup
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_one_left]; rw [(nhds_one_hasBasis.comap _).eq_biInf]
    simp only [dist, preimage_ofPred_eq, norm_eq_groupSeminorm]

variable (S) in
/-- The quotient in the category of normed groups. -/
@[to_additive /-- The quotient in the category of normed groups. -/]
/--
Instance `instNormedCommGroup` / 实例 `instNormedCommGroup`

English:
instance instNormedCommGroup
  signature: [hS : IsClosed (S : Set M)]
  body: MetricSpace.ofT0PseudoMetricSpace _

中文:
实例 instNormedCommGroup
  签名: [hS : 是闭集 (S : 集合 M)]
  定义体: MetricSpace.ofT0PseudoMetricSpace _

Depends on / 依赖: MetricSpace, MetricSpace.ofT0PseudoMetricSpace, ofT0PseudoMetricSpace
-/
noncomputable instance instNormedCommGroup [hS : IsClosed (S : Set M)] :
    NormedCommGroup (M ⧸ S) where
  __ := MetricSpace.ofT0PseudoMetricSpace _

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example :
    (instTopologicalSpaceQuotient : TopologicalSpace <| M ⧸ S) =
      (instSeminormedCommGroup S).toUniformSpace.toTopologicalSpace := rfl

example [IsClosed (S : Set M)] :
    (instSeminormedCommGroup S) = NormedCommGroup.toSeminormedCommGroup := rfl

/-- An isometric version of `Subgroup.quotientEquivOfEq`. -/
@[to_additive /-- An isometric version of `AddSubgroup.quotientEquivOfEq`. -/]
/--
Definition of `_root_.Subgroup.quotientIsometryEquivOfEq` / `_root_.Subgroup.quotientIsometryEquivOfEq` 的定义

English:
definition _root_.Subgroup.quotientIsometryEquivOfEq
  signature: (h : S = T)
  body: Subgroup.quotientEquivOfEq h
  isometry_toFun := by subst h; rintro ⟨_⟩ ⟨_⟩; rfl

中文:
定义 _root_.子群.quotientIsometryEquivOfEq
  签名: (h : S = T)
  定义体: Subgroup.quotientEquivOfEq h
  isometry_toFun := by subst h; rintro ⟨_⟩ ⟨_⟩; rfl

Depends on / 依赖: Subgroup, Subgroup.quotientEquivOfEq, quotientEquivOfEq
-/
def _root_.Subgroup.quotientIsometryEquivOfEq (h : S = T) : M ⧸ S ≃ᵢ M ⧸ T where
  __ := Subgroup.quotientEquivOfEq h
  isometry_toFun := by subst h; rintro ⟨_⟩ ⟨_⟩; rfl

/-- An isometric version of `QuotientGroup.quotientBot`. -/
@[to_additive /-- An isometric version of `QuotientAddGroup.quotientBot`. -/]
/--
Definition of `quotientBotIsometryEquiv` / `quotientBotIsometryEquiv` 的定义

English:
definition quotientBotIsometryEquiv
  signature: : M ⧸ (⊥ : Subgroup M) ≃ᵢ M where
  body: quotientBot
  isometry_toFun : Isometry quotientBot := by
    rw [MonoidHomClass.isometry_iff_norm]
    rintro ⟨x⟩
    change ‖x‖ = ‖QuotientGroup.mk x‖
    simp [norm_mk]

中文:
定义 quotientBotIsometryEquiv
  签名: : M ⧸ (⊥ : 子群 M) ≃ᵢ M where
  定义体: quotientBot
  isometry_toFun : Isometry quotientBot := by
    rw [MonoidHomClass.isometry_iff_norm]
    rintro ⟨x⟩
    change ‖x‖ = ‖QuotientGroup.mk x‖
    simp [norm_mk]

Depends on / 依赖: quotientBot
-/
def quotientBotIsometryEquiv : M ⧸ (⊥ : Subgroup M) ≃ᵢ M where
  __ := quotientBot
  isometry_toFun : Isometry quotientBot := by
    rw [MonoidHomClass.isometry_iff_norm]
    rintro ⟨x⟩
    change ‖x‖ = ‖QuotientGroup.mk x‖
    simp [norm_mk]

/-- An isometric version of `QuotientGroup.quotientQuotientEquivQuotient`. -/
@[to_additive /-- An isometric version of `QuotientAddGroup.quotientQuotientEquivQuotient`. -/]
/--
Definition of `quotientQuotientIsometryEquivQuotient` / `quotientQuotientIsometryEquivQuotient` 的定义

English:
definition quotientQuotientIsometryEquivQuotient
  signature: (h : S <= T)
  body: quotientQuotientEquivQuotient S T h
  isometry_toFun : Isometry (quotientQuotientEquivQuotient S T h) := by
    rw [MonoidHomClass.isometry_iff_norm]
    refine fun x => eq_of_forall_le_iff fun r => ?_
    simp only [le_norm_iff]
    exact ⟨
fun h₁ y h₂ z h₃ => h₁ z by subst_vars; rfl,
      fun h₁ 

中文:
定义 quotientQuotientIsometryEquivQuotient
  签名: (h : S <= T)
  定义体: quotientQuotientEquivQuotient S T h
  isometry_toFun : Isometry (quotientQuotientEquivQuotient S T h) := by
    rw [MonoidHomClass.isometry_iff_norm]
    refine fun x => eq_of_forall_le_iff fun r => ?_
    simp only [le_norm_iff]
    exact ⟨
fun h₁ y h₂ z h₃ => h₁ z by subst_vars; rfl,
      fun h₁ 

Depends on / 依赖: quotientQuotientEquivQuotient
-/
def quotientQuotientIsometryEquivQuotient (h : S <= T) : (M ⧸ S) ⧸ T.map (mk' S) ≃ᵢ M ⧸ T where
  __ := quotientQuotientEquivQuotient S T h
  isometry_toFun : Isometry (quotientQuotientEquivQuotient S T h) := by
    rw [MonoidHomClass.isometry_iff_norm]
    refine fun x => eq_of_forall_le_iff fun r => ?_
    simp only [le_norm_iff]
    exact ⟨
fun h₁ y h₂ z h₃ => h₁ z by subst_vars; rfl,
      fun h₁ y h₂ => h₁ y ((quotientQuotientEquivQuotient S T h).injective h₂) y rfl⟩

end QuotientGroup

open QuotientAddGroup Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/--
theorem `quotient_norm_mk_eq` / 定理 `quotient_norm_mk_eq`

English:
theorem quotient_norm_mk_eq
  given: (S : AddSubgroup M) (m : M)
  proof: by
  rw [mk'_apply]; rw [norm_mk]; rw [sInf_image']; rw [← infDist_image isometry_neg]; rw [image_neg_eq_neg]; rw [neg_coe_set (H := S)]; rw [infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]

中文:
定理 quotient_norm_mk_eq
  条件: (S : 加法子群 M) (m : M)
  证明: by
  rw [mk'_apply]; rw [norm_mk]; rw [sInf_image']; rw [← infDist_image isometry_neg]; rw [image_neg_eq_neg]; rw [neg_coe_set (H := S)]; rw [infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]

Depends on / 依赖: _apply, add_comm, dist_eq_norm, image_neg_eq_neg, infDist_eq_iInf, infDist_image, isometry_neg, neg_coe_set, norm_mk, sInf_image, sub_neg_eq_add
-/
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = sInf ((‖m + ·‖) '' S) := by
  rw [mk'_apply]; rw [norm_mk]; rw [sInf_image']; rw [← infDist_image isometry_neg]; rw [image_neg_eq_neg]; rw [neg_coe_set (H := S)]; rw [infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]

/--
theorem `quotient_norm_add_le` / 定理 `quotient_norm_add_le`

English:
theorem quotient_norm_add_le
  given: (S : AddSubgroup M) (x y : M ⧸ S)
  statement: ‖x + y‖ <= ‖x‖ + ‖y‖
  proof: norm_add_le x y

中文:
定理 quotient_norm_add_le
  条件: (S : 加法子群 M) (x y : M ⧸ S)
  结论: ‖x + y‖ <= ‖x‖ + ‖y‖
  证明: norm_add_le x y

Depends on / 依赖: norm_add_le
-/
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ <= ‖x‖ + ‖y‖ :=
  norm_add_le x y

namespace AddSubgroup

open NormedAddGroupHom

/--
Definition of `normedMk` / `normedMk` 的定义

English:
definition normedMk
  signature: (S : AddSubgroup M)
  body: QuotientAddGroup.mk' S
  bound' := ⟨1, fun m => by simpa [one_mul] using norm_mk_le_norm⟩

中文:
定义 normedMk
  签名: (S : 加法子群 M)
  定义体: QuotientAddGroup.mk' S
  bound' := ⟨1, fun m => by simpa [one_mul] using norm_mk_le_norm⟩

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.mk
-/
noncomputable def normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) where
  __ := QuotientAddGroup.mk' S
  bound' := ⟨1, fun m => by simpa [one_mul] using norm_mk_le_norm⟩

/-- `S.normedMk` agrees with `QuotientAddGroup.mk' S`. -/
@[simp]
/--
theorem `normedMk.apply` / 定理 `normedMk.apply`

English:
theorem normedMk.apply
  given: (S : AddSubgroup M) (m : M)
  statement: normedMk S m = QuotientAddGroup.mk' S m
  proof: rfl

中文:
定理 normedMk.apply
  条件: (S : 加法子群 M) (m : M)
  结论: normedMk S m = QuotientAddGroup.mk' S m
  证明: rfl
-/
theorem normedMk.apply (S : AddSubgroup M) (m : M) : normedMk S m = QuotientAddGroup.mk' S m :=
  rfl

/--
theorem `surjective_normedMk` / 定理 `surjective_normedMk`

English:
theorem surjective_normedMk
  given: (S : AddSubgroup M)
  statement: Function.Surjective (normedMk S)
  proof: Quot.mk_surjective

中文:
定理 surjective_normedMk
  条件: (S : 加法子群 M)
  结论: 函数.满射 (normedMk S)
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S) :=
  Quot.mk_surjective

/--
theorem `ker_normedMk` / 定理 `ker_normedMk`

English:
theorem ker_normedMk
  given: (S : AddSubgroup M)
  statement: S.normedMk.ker = S
  proof: QuotientAddGroup.ker_mk' _

中文:
定理 ker_normedMk
  条件: (S : 加法子群 M)
  结论: S.normedMk.ker = S
  证明: QuotientAddGroup.ker_mk' _

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.ker_mk, ker_mk
-/
theorem ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S :=
  QuotientAddGroup.ker_mk' _

/--
theorem `norm_normedMk_le` / 定理 `norm_normedMk_le`

English:
theorem norm_normedMk_le
  given: (S : AddSubgroup M)
  statement: ‖S.normedMk‖ <= 1
  proof: NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [norm_mk_le_norm]

中文:
定理 norm_normedMk_le
  条件: (S : 加法子群 M)
  结论: ‖S.normedMk‖ <= 1
  证明: NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [norm_mk_le_norm]

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.opNorm_le_bound, norm_mk_le_norm, opNorm_le_bound, zero_le_one
-/
theorem norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ <= 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [norm_mk_le_norm]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `_root_.QuotientAddGroup.norm_lift_apply_le` / 定理 `_root_.QuotientAddGroup.norm_lift_apply_le`

English:
theorem _root_.QuotientAddGroup.norm_lift_apply_le
  statement: {S : AddSubgroup M} (f : NormedAddGroupHom M N)
  proof: by
  cases (norm_nonneg f).eq_or_lt' with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt]; rw [← lt_div_iff₀' h]; rw [norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff₀' h).1 hx).not_ge (le_opNorm f x)

中文:
定理 _root_.QuotientAddGroup.norm_lift_apply_le
  结论: {S : 加法子群 M} (f : 赋范加群态射 M N)
  证明: by
  cases (norm_nonneg f).eq_or_lt' with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt]; rw [← lt_div_iff₀' h]; rw [norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff₀' h).1 hx).not_ge (le_opNorm f x)

Depends on / 依赖: eq_or_lt, le_opNorm, mk_surjective, norm_lt_iff, norm_nonneg, not_ge, not_lt
-/
theorem _root_.QuotientAddGroup.norm_lift_apply_le {S : AddSubgroup M} (f : NormedAddGroupHom M N)
    (hf : forall x in S, f x = 0) (x : M ⧸ S) : ‖lift S f.toAddMonoidHom hf x‖ <= ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_lt' with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt]; rw [← lt_div_iff₀' h]; rw [norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff₀' h).1 hx).not_ge (le_opNorm f x)

/--
theorem `norm_normedMk` / 定理 `norm_normedMk`

English:
theorem norm_normedMk
  given: (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) != univ)
  proof: by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : exists x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx => ?_
exact (norm_nonneg _).lt_of_ne' mt norm_mk_eq_zero_iff_mem_closure.1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le

中文:
定理 norm_normedMk
  条件: (S : 加法子群 M) (h : (S.topologicalClosure : 集合 M) != univ)
  证明: by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : exists x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx => ?_
exact (norm_nonneg _).lt_of_ne' mt norm_mk_eq_zero_iff_mem_closure.1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le

Depends on / 依赖: S.normedMk, Set.nonempty_compl, eq_zero_iff, le_antisymm, le_mul_iff_one_le_left, lt_of_ne, nonempty_compl, norm_lift_apply_le, norm_mk_eq_zero_iff_mem_closure, norm_nonneg, norm_normedMk_le, normedMk
-/
theorem norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) != univ) :
    ‖S.normedMk‖ = 1 := by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : exists x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx => ?_
exact (norm_nonneg _).lt_of_ne' mt norm_mk_eq_zero_iff_mem_closure.1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le S.normedMk (fun x => (eq_zero_iff x).2) x

/--
theorem `norm_trivial_quotient_mk` / 定理 `norm_trivial_quotient_mk`

English:
theorem norm_trivial_quotient_mk
  statement: (S : AddSubgroup M)
  proof: by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
  have hker : x in S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk]; rw [← SetLike.mem_coe]; rw [h]
    trivial
  rw [ker_normedMk] at hker
  simp [norm_mk_eq_zero_iff_mem_closure.mpr hker]

中文:
定理 norm_trivial_quotient_mk
  结论: (S : 加法子群 M)
  证明: by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
  have hker : x in S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk]; rw [← SetLike.mem_coe]; rw [h]
    trivial
  rw [ker_normedMk] at hker
  simp [norm_mk_eq_zero_iff_mem_closure.mpr hker]

Depends on / 依赖: S.ker_normedMk, S.normedMk.ker.topologicalClosure, SetLike, SetLike.mem_coe, ker_normedMk, le_antisymm, le_rfl, mem_coe, norm_mk_eq_zero_iff_mem_closure, norm_mk_eq_zero_iff_mem_closure.mpr, norm_nonneg, normedMk, opNorm_le_bound, topologicalClosure
-/
theorem norm_trivial_quotient_mk (S : AddSubgroup M)
    (h : (S.topologicalClosure : Set M) = Set.univ) : ‖S.normedMk‖ = 0 := by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
  have hker : x in S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk]; rw [← SetLike.mem_coe]; rw [h]
    trivial
  rw [ker_normedMk] at hker
  simp [norm_mk_eq_zero_iff_mem_closure.mpr hker]

end AddSubgroup

namespace NormedAddGroupHom

/--
Definition of `IsQuotient` / `IsQuotient` 的定义

English:
structure IsQuotient
  parameters: (f : NormedAddGroupHom M N)
  axioms and operations (2):
    - surjective : Function.Surjective f
    - norm : forall x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)

中文:
结构 是商
  参数: (f : 赋范加群态射 M N)
  公理与运算 (2 个):
    - surjective : 函数.满射 f
    - norm : 对任意 x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)
-/
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : forall x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
  body: { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }

中文:
定义 lift
  签名: {N : 类型} [SeminormedAddComm群 N] (S : 加法子群 M)
  定义体: { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.lift, f.toAddMonoidHom, norm_lift_apply_le, toAddMonoidHom
-/
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }

/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
  proof: rfl

中文:
定理 lift_mk
  结论: {N : 类型} [SeminormedAddComm群 N] (S : 加法子群 M)
  证明: rfl
-/
theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) (m : M) :
    lift S f hf (S.normedMk m) = f m :=
  rfl

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
  proof: by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl

中文:
定理 lift_unique
  结论: {N : 类型} [SeminormedAddComm群 N] (S : 加法子群 M)
  证明: by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl

Depends on / 依赖: AddSubgroup, AddSubgroup.surjective_normedMk, S.normedMk, g.comp, normedMk, surjective_normedMk
-/
theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) (g : NormedAddGroupHom (M ⧸ S) N)
    (h : g.comp S.normedMk = f) : g = lift S f hf := by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl

/--
theorem `isQuotientQuotient` / 定理 `isQuotientQuotient`

English:
theorem isQuotientQuotient
  given: (S : AddSubgroup M)
  statement: IsQuotient S.normedMk
  proof: ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩

中文:
定理 isQuotientQuotient
  条件: (S : 加法子群 M)
  结论: 是商 S.normedMk
  证明: ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩

Depends on / 依赖: S.ker_normedMk, S.surjective_normedMk, ker_normedMk, quotient_norm_mk_eq, surjective_normedMk
-/
theorem isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk :=
  ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩

/--
theorem `IsQuotient.norm_lift` / 定理 `IsQuotient.norm_lift`

English:
theorem IsQuotient.norm_lift
  statement: {f : NormedAddGroupHom M N} (hquot : IsQuotient f) {ε : Real} (hε : 0 < ε)
  proof: by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty := by
    rw [Set.image_nonempty]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_sInf_add_pos nonemp hε
    with ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < sInf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact

中文:
定理 是商.norm_lift
  结论: {f : 赋范加群态射 M N} (hquot : 是商 f) {ε : 实数} (hε : 0 < ε)
  证明: by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty := by
    rw [Set.image_nonempty]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_sInf_add_pos nonemp hε
    with ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < sInf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact

Depends on / 依赖: Nonempty, NormedAddGroupHom, NormedAddGroupHom.mem_ker, Real.lt_sInf_add_pos, Set.image_nonempty, add_zero, f.ker, f.ker.zero_mem, hquot.norm, hquot.surjective, image_nonempty, lt_sInf_add_pos, map_add, mem_ker, nonemp, surjective, zero_mem
-/
theorem IsQuotient.norm_lift {f : NormedAddGroupHom M N} (hquot : IsQuotient f) {ε : Real} (hε : 0 < ε)
    (n : N) : exists m : M, f m = n ∧ ‖m‖ < ‖n‖ + ε := by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty := by
    rw [Set.image_nonempty]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_sInf_add_pos nonemp hε
    with ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < sInf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact ⟨m + x, by rw [map_add, (NormedAddGroupHom.mem_ker f x).mp hx, add_zero], by
    rwa [hquot.norm]⟩

/--
theorem `IsQuotient.norm_le` / 定理 `IsQuotient.norm_le`

English:
theorem IsQuotient.norm_le
  given: {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M)
  proof: by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩

中文:
定理 是商.norm_le
  条件: {f : 赋范加群态射 M N} (hquot : 是商 f) (m : M)
  证明: by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩

Depends on / 依赖: csInf_le, f.ker.zero_mem, hquot.norm, norm_nonneg, zero_mem
-/
theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
    ‖f m‖ <= ‖m‖ := by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩

/--
theorem `norm_lift_le` / 定理 `norm_lift_le`

English:
theorem norm_lift_le
  statement: {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
  proof: opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

中文:
定理 norm_lift_le
  结论: {N : 类型} [SeminormedAddComm群 N] (S : 加法子群 M)
  证明: opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

Depends on / 依赖: norm_lift_apply_le, norm_nonneg, opNorm_le_bound
-/
theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) :
    ‖lift S f hf‖ <= ‖f‖ :=
  opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

-- TODO: deprecate?
/--
theorem `lift_norm_le` / 定理 `lift_norm_le`

English:
theorem lift_norm_le
  statement: {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
  proof: (norm_lift_le S f hf).trans fb

中文:
定理 lift_norm_le
  结论: {N : 类型} [SeminormedAddComm群 N] (S : 加法子群 M)
  证明: (norm_lift_le S f hf).trans fb

Depends on / 依赖: norm_lift_le
-/
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) {c : Real>=0} (fb : ‖f‖ <= c) :
    ‖lift S f hf‖ <= c :=
  (norm_lift_le S f hf).trans fb

/--
theorem `lift_normNoninc` / 定理 `lift_normNoninc`

English:
theorem lift_normNoninc
  statement: {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
  proof: fun x => by
  have fb' : ‖f‖ <= (1 : Real>=0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _

中文:
定理 lift_normNoninc
  结论: {N : 类型} [SeminormedAddComm群 N] (S : 加法子群 M)
  证明: fun x => by
  have fb' : ‖f‖ <= (1 : Real>=0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _

Depends on / 依赖: NormNoninc, NormNoninc.normNoninc_iff_norm_le_one.mp, f.lift_norm_le, le_of_opNorm_le, lift_norm_le, normNoninc_iff_norm_le_one
-/
theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : forall s in S, f s = 0) (fb : f.NormNoninc) :
    (lift S f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ <= (1 : Real>=0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _

end NormedAddGroupHom

/-!
### Submodules and ideals

In what follows, the norm structures created above for quotients of (semi)`NormedAddCommGroup`s
by `AddSubgroup`s are transferred via definitional equality to quotients of modules by submodules,
and of rings by ideals, thereby preserving the definitional equality for the topological group and
uniform structures worked for above. Completeness is also transferred via this definitional
equality.

In addition, instances are constructed for `NormedSpace`, `SeminormedCommRing`,
`NormedCommRing` and `NormedAlgebra` under the appropriate hypotheses. Currently, we do not
have quotients of rings by two-sided ideals, hence the commutativity hypotheses are required.
-/

section Submodule

variable {R : Type*} [Ring R] [Module R M] (S T : Submodule R M)

/--
Instance `Submodule.Quotient.seminormedAddCommGroup` / 实例 `Submodule.Quotient.seminormedAddCommGroup`

English:
instance Submodule.Quotient.seminormedAddCommGroup
  signature: : SeminormedAddCommGroup (M ⧸ S)
  body: inferInstanceAs SeminormedAddCommGroup (M ⧸ S.toAddSubgroup)

中文:
实例 子模.商.seminormedAddCommGroup
  签名: : SeminormedAddComm群 (M ⧸ S)
  定义体: inferInstanceAs SeminormedAddCommGroup (M ⧸ S.toAddSubgroup)

Depends on / 依赖: S.toAddSubgroup, SeminormedAddCommGroup, toAddSubgroup
-/
instance Submodule.Quotient.seminormedAddCommGroup : SeminormedAddCommGroup (M ⧸ S) :=
inferInstanceAs SeminormedAddCommGroup (M ⧸ S.toAddSubgroup)

/--
Instance `Submodule.Quotient.normedAddCommGroup` / 实例 `Submodule.Quotient.normedAddCommGroup`

English:
instance Submodule.Quotient.normedAddCommGroup
  signature: [hS : IsClosed (S : Set M)]
  body: inferInstanceAs NormedAddCommGroup (M ⧸ S.toAddSubgroup)

中文:
实例 子模.商.normedAddCommGroup
  签名: [hS : 是闭集 (S : 集合 M)]
  定义体: inferInstanceAs NormedAddCommGroup (M ⧸ S.toAddSubgroup)

Depends on / 依赖: NormedAddCommGroup, S.toAddSubgroup, toAddSubgroup
-/
instance Submodule.Quotient.normedAddCommGroup [hS : IsClosed (S : Set M)] :
    NormedAddCommGroup (M ⧸ S) :=
inferInstanceAs NormedAddCommGroup (M ⧸ S.toAddSubgroup)

/--
Instance `Submodule.Quotient.completeSpace` / 实例 `Submodule.Quotient.completeSpace`

English:
instance Submodule.Quotient.completeSpace
  signature: [CompleteSpace M]
  body: QuotientAddGroup.completeSpace_left M S.toAddSubgroup

中文:
实例 子模.商.completeSpace
  签名: [完备空间 M]
  定义体: QuotientAddGroup.completeSpace_left M S.toAddSubgroup

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.completeSpace_left, S.toAddSubgroup, completeSpace_left, toAddSubgroup
-/
instance Submodule.Quotient.completeSpace [CompleteSpace M] : CompleteSpace (M ⧸ S) :=
  QuotientAddGroup.completeSpace_left M S.toAddSubgroup

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `Submodule.Quotient.mk m = x`
and `‖m‖ < ‖x‖ + ε`. -/
nonrec theorem Submodule.Quotient.norm_mk_lt {S : Submodule R M} (x : M ⧸ S) {ε : Real} (hε : 0 < ε) :
    exists m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  exists_norm_mk_lt x hε

/--
theorem `Submodule.Quotient.norm_mk_le` / 定理 `Submodule.Quotient.norm_mk_le`

English:
theorem Submodule.Quotient.norm_mk_le
  given: (m : M)
  statement: ‖(Submodule.Quotient.mk m : M ⧸ S)‖ <= ‖m‖
  proof: norm_mk_le_norm

中文:
定理 子模.商.norm_mk_le
  条件: (m : M)
  结论: ‖(子模.商.mk m : M ⧸ S)‖ <= ‖m‖
  证明: norm_mk_le_norm

Depends on / 依赖: norm_mk_le_norm
-/
theorem Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)‖ <= ‖m‖ :=
  norm_mk_le_norm

/--
Instance `Submodule.Quotient.instIsBoundedSMul` / 实例 `Submodule.Quotient.instIsBoundedSMul`

English:
instance Submodule.Quotient.instIsBoundedSMul
  signature: (𝕜 : Type*)
  body: .of_norm_smul_le fun k x =>
    -- this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M ⧸ S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds

中文:
实例 子模.商.instIsBoundedSMul
  签名: (𝕜 : 类型)
  定义体: .of_norm_smul_le fun k x =>
    -- this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M ⧸ S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds

Depends on / 依赖: of_norm_smul_le
-/
instance Submodule.Quotient.instIsBoundedSMul (𝕜 : Type*)
    [SeminormedCommRing 𝕜] [Module 𝕜 M] [IsBoundedSMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] :
    IsBoundedSMul 𝕜 (M ⧸ S) :=
  .of_norm_smul_le fun k x =>
    -- this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M ⧸ S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
        ((@Real.uniformContinuous_const_mul ‖k‖).continuous.tendsto ‖x‖) ε hε
      simp only [mem_ball, dist, abs_sub_lt_iff] at this
      rcases this with ⟨δ, hδ, h⟩
      obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ
      specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le S a]⟩
      calc
        _ <= ‖k‖ * ‖a‖ := (norm_mk_le ..).trans (norm_smul_le k a)
        _ <= _ := (sub_lt_iff_lt_add'.mp h.1).le

/--
Instance `Submodule.Quotient.normedSpace` / 实例 `Submodule.Quotient.normedSpace`

English:
instance Submodule.Quotient.normedSpace
  signature: (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
  body: norm_smul_le

中文:
实例 子模.商.normedSpace
  签名: (𝕜 : 类型) [赋范域 𝕜] [赋范空间 𝕜 M] [标量乘法 𝕜 R]
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance Submodule.Quotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
    [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) where
  norm_smul_le := norm_smul_le

/--
Definition of `Submodule.quotLIEOfEq` / `Submodule.quotLIEOfEq` 的定义

English:
definition Submodule.quotLIEOfEq
  signature: (h : S = T)
  body: Submodule.quotEquivOfEq S T h
  norm_map' := by subst h; rintro ⟨_⟩; rfl

中文:
定义 子模.quotLIEOfEq
  签名: (h : S = T)
  定义体: Submodule.quotEquivOfEq S T h
  norm_map' := by subst h; rintro ⟨_⟩; rfl

Depends on / 依赖: Submodule, Submodule.quotEquivOfEq, quotEquivOfEq
-/
def Submodule.quotLIEOfEq (h : S = T) : M ⧸ S ≃ₗᵢ[R] M ⧸ T where
  __ := Submodule.quotEquivOfEq S T h
  norm_map' := by subst h; rintro ⟨_⟩; rfl

/--
Definition of `Submodule.quotientQuotientLIEQuotient` / `Submodule.quotientQuotientLIEQuotient` 的定义

English:
definition Submodule.quotientQuotientLIEQuotient
  signature: (h : S <= T)
  body: Submodule.quotientQuotientEquivQuotient S T h
  norm_map' :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (QuotientAddGroup.quotientQuotientIsometryEquivQuotient
        ((Submodule.toAddSubgroup_le S T).mpr h)).isometry

中文:
定义 子模.quotientQuotientLIEQuotient
  签名: (h : S <= T)
  定义体: Submodule.quotientQuotientEquivQuotient S T h
  norm_map' :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (QuotientAddGroup.quotientQuotientIsometryEquivQuotient
        ((Submodule.toAddSubgroup_le S T).mpr h)).isometry

Depends on / 依赖: Submodule, Submodule.quotientQuotientEquivQuotient, quotientQuotientEquivQuotient
-/
def Submodule.quotientQuotientLIEQuotient (h : S <= T) : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M ⧸ T where
  __ := Submodule.quotientQuotientEquivQuotient S T h
  norm_map' :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (QuotientAddGroup.quotientQuotientIsometryEquivQuotient
        ((Submodule.toAddSubgroup_le S T).mpr h)).isometry

/--
Definition of `Submodule.quotientQuotientLIEQuotientSup` / `Submodule.quotientQuotientLIEQuotientSup` 的定义

English:
definition Submodule.quotientQuotientLIEQuotientSup
  signature: : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M ⧸ (S ⊔ T)
  body: (quotLIEOfEq _ _ (by simp)).trans (quotientQuotientLIEQuotient _ _ le_sup_left)

中文:
定义 子模.quotientQuotientLIEQuotientSup
  签名: : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M ⧸ (S ⊔ T)
  定义体: (quotLIEOfEq _ _ (by simp)).trans (quotientQuotientLIEQuotient _ _ le_sup_left)

Depends on / 依赖: le_sup_left, quotLIEOfEq, quotientQuotientLIEQuotient
-/
def Submodule.quotientQuotientLIEQuotientSup : (M ⧸ S) ⧸ map S.mkQ T ≃ₗᵢ[R] M ⧸ (S ⊔ T) :=
  (quotLIEOfEq _ _ (by simp)).trans (quotientQuotientLIEQuotient _ _ le_sup_left)

end Submodule

section Ideal

variable {R : Type*} [SeminormedCommRing R] (I : Ideal R)

nonrec theorem Ideal.Quotient.norm_mk_lt {I : Ideal R} (x : R ⧸ I) {ε : Real} (hε : 0 < ε) :
    exists r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  exists_norm_mk_lt x hε

/--
theorem `Ideal.Quotient.norm_mk_le` / 定理 `Ideal.Quotient.norm_mk_le`

English:
theorem Ideal.Quotient.norm_mk_le
  given: (r : R)
  statement: ‖Ideal.Quotient.mk I r‖ <= ‖r‖
  proof: norm_mk_le_norm

中文:
定理 理想.商.norm_mk_le
  条件: (r : R)
  结论: ‖理想.商.mk I r‖ <= ‖r‖
  证明: norm_mk_le_norm

Depends on / 依赖: norm_mk_le_norm
-/
theorem Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ <= ‖r‖ := norm_mk_le_norm

/--
Instance `Ideal.Quotient.semiNormedCommRing` / 实例 `Ideal.Quotient.semiNormedCommRing`

English:
instance Ideal.Quotient.semiNormedCommRing
  signature: : SeminormedCommRing (R ⧸ I) where
  body: dist_eq_norm_neg_add
  mul_comm := _root_.mul_comm
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.

中文:
实例 理想.商.semiNormedCommRing
  签名: : SeminormedComm环 (R ⧸ I) where
  定义体: dist_eq_norm_neg_add
  mul_comm := _root_.mul_comm
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.

Depends on / 依赖: dist_eq_norm_neg_add
-/
instance Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  mul_comm := _root_.mul_comm
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := Ideal.Quotient.norm_mk_lt x h₁,
      Ideal.Quotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I a]⟩
      ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I b]⟩
    calc
      _ <= ‖a‖ * ‖b‖ := (Ideal.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ <= _ := (sub_lt_iff_lt_add'.mp h.1).le

/--
Instance `Ideal.Quotient.normedCommRing` / 实例 `Ideal.Quotient.normedCommRing`

English:
instance Ideal.Quotient.normedCommRing
  signature: [IsClosed (I : Set R)]
  body: { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }

中文:
实例 理想.商.normedCommRing
  签名: [是闭集 (I : 集合 R)]
  定义体: { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }

Depends on / 依赖: Ideal.Quotient.semiNormedCommRing, Quotient, Submodule, Submodule.Quotient.normedAddCommGroup, normedAddCommGroup, semiNormedCommRing
-/
instance Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) :=
  { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }

variable (𝕜 : Type*) [NormedField 𝕜]

/--
Instance `Ideal.Quotient.normedAlgebra` / 实例 `Ideal.Quotient.normedAlgebra`

English:
instance Ideal.Quotient.normedAlgebra
  signature: [NormedAlgebra 𝕜 R]
  body: { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

中文:
实例 理想.商.normedAlgebra
  签名: [赋范代数 𝕜 R]
  定义体: { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

Depends on / 依赖: Ideal.Quotient.algebra, Quotient, Submodule, Submodule.Quotient.normedSpace, algebra, normedSpace
-/
instance Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

end Ideal
