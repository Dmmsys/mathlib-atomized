/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ines Wright, Joachim Breitner
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.GroupTheory.Commutator.Finite

/-!

# Nilpotent groups

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : Subgroup G` then `⁅H, K⁆ : Subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `Subgroup.upperCentralSeries G : ℕ → Subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of characteristic subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `Subgroup.lowerCentralSeries (S : Subgroup G) : ℕ → Subgroup G` : the lower central series of `S`,
     computed in the ambient group `G`. This is the iterated commutator
     `S, ⁅S, S⁆, ⁅⁅S, S⁆, S⁆, …`. The classical lower central series of `G` is the case
     `S = ⊤`.
* `IsNilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `Group.nilpotencyClass` : the length of the upper central series of a nilpotent group.
* `IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop` and
* `IsDescendingCentralSeries (H : ℕ → Subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.
* The `Group.nilpotencyClass` can likewise be obtained from these equivalent
  definitions, see `least_ascending_central_series_length_eq_nilpotencyClass`,
  `least_descending_central_series_length_eq_nilpotencyClass` and
  `lowerCentralSeries_length_eq_nilpotencyClass`.
* If `G` is nilpotent, then so are its subgroups, images, quotients and preimages.
  Binary and finite products of nilpotent groups are nilpotent.
  Infinite products are nilpotent if their nilpotent class is bounded.
  Corresponding lemmas about the `Group.nilpotencyClass` are provided.
* The `Group.nilpotencyClass` of `G ⧸ center G` is given explicitly, and an induction principle
  is derived from that.
* `IsNilpotent.to_isSolvable`: If `G` is nilpotent, it is solvable.


## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upperCentralSeries G`, `(⊤ : Subgroup G).lowerCentralSeries` or
the sequences satisfying `IsAscendingCentralSeries` or `IsDescendingCentralSeries`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/

@[expose] public section


open commutatorElement Subgroup

section WithGroup

variable {G : Type*} [Group G] (N : Subgroup G) [Normal N]

namespace Subgroup

/-- If `N` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ N}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/N`.)
-/
@[to_additive /-- If `N` is a normal additive subgroup of `G`, then the set
`{x : G | ∀ y : G, x + y -x - y ∈ N}` is an additive subgroup of `G`
(because it is the preimage in `G` of the centre of the additive quotient group `G/N`.) -/]
/--
Definition of `upperCentralSeriesStep` / `upperCentralSeriesStep` 的定义

English:
definition upperCentralSeriesStep
  signature: : Subgroup G where
  body: { x : G | forall y : G, ⁅x, y⁆ in N }
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    convert! Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' {x} hx y := by
    specialize hx y⁻¹
    rw [commutatorElement_def]; rw [mul_assoc]; rw [inv_inv] at hx ⊢
    exact Subg

中文:
定义 upperCentralSeriesStep
  签名: : 子群 G where
  定义体: { x : G | forall y : G, ⁅x, y⁆ in N }
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    convert! Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' {x} hx y := by
    specialize hx y⁻¹
    rw [commutatorElement_def]; rw [mul_assoc]; rw [inv_inv] at hx ⊢
    exact Subg
-/
def upperCentralSeriesStep : Subgroup G where
  carrier := { x : G | forall y : G, ⁅x, y⁆ in N }
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    convert! Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' {x} hx y := by
    specialize hx y⁻¹
    rw [commutatorElement_def]; rw [mul_assoc]; rw [inv_inv] at hx ⊢
    exact Subgroup.Normal.mem_comm inferInstance hx

@[to_additive]
/--
theorem `mem_upperCentralSeriesStep` / 定理 `mem_upperCentralSeriesStep`

English:
theorem mem_upperCentralSeriesStep
  given: (x : G)
  proof: Iff.rfl

中文:
定理 mem_upperCentralSeriesStep
  条件: (x : G)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_upperCentralSeriesStep (x : G) :
    x in upperCentralSeriesStep N ↔ forall y, ⁅x, y⁆ in N := Iff.rfl

open QuotientGroup

/-- The proof that `upperCentralSeriesStep N` is the preimage of the centre of `G/N` under
the canonical surjection. -/
@[to_additive /-- The proof that `upperCentralSeriesStep N` is the preimage of the centre of `G/N`\
under the canonical surjection. -/]
/--
theorem `upperCentralSeriesStep_eq_comap_center` / 定理 `upperCentralSeriesStep_eq_comap_center`

English:
theorem upperCentralSeriesStep_eq_comap_center
  proof: by
  ext
  rw [mem_comap]; rw [mem_center_iff]; rw [forall_mk]
  refine forall_congr' fun y => ?_
  rw [coe_mk']; rw [← QuotientGroup.mk_mul]; rw [← QuotientGroup.mk_mul]; rw [eq_comm]; rw [eq_iff_div_mem]; rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [commutatorElement_def]
  simp_rw [mul_assoc]

@[to

中文:
定理 upperCentralSeriesStep_eq_comap_center
  证明: by
  ext
  rw [mem_comap]; rw [mem_center_iff]; rw [forall_mk]
  refine forall_congr' fun y => ?_
  rw [coe_mk']; rw [← QuotientGroup.mk_mul]; rw [← QuotientGroup.mk_mul]; rw [eq_comm]; rw [eq_iff_div_mem]; rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [commutatorElement_def]
  simp_rw [mul_assoc]

@[to

Depends on / 依赖: QuotientGroup, QuotientGroup.mk_mul, coe_mk, commutatorElement_def, div_eq_mul_inv, eq_comm, eq_iff_div_mem, forall_congr, forall_mk, mem_center_iff, mem_comap, mk_mul, mul_assoc, mul_inv_rev, simp_rw
-/
theorem upperCentralSeriesStep_eq_comap_center :
    upperCentralSeriesStep N = Subgroup.comap (mk' N) (center (G ⧸ N)) := by
  ext
  rw [mem_comap]; rw [mem_center_iff]; rw [forall_mk]
  refine forall_congr' fun y => ?_
  rw [coe_mk']; rw [← QuotientGroup.mk_mul]; rw [← QuotientGroup.mk_mul]; rw [eq_comm]; rw [eq_iff_div_mem]; rw [div_eq_mul_inv]; rw [mul_inv_rev]; rw [commutatorElement_def]
  simp_rw [mul_assoc]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [N.Characteristic]
  signature: : Characteristic (upperCentralSeriesStep N)
  body: (upperCentralSeriesStep_eq_comap_center N) ▸ Characteristic.comap_quotient_mk centerCharacteristic

中文:
实例 [N.特征]
  签名: : 特征 (upperCentralSeriesStep N)
  定义体: (upperCentralSeriesStep_eq_comap_center N) ▸ Characteristic.comap_quotient_mk centerCharacteristic

Depends on / 依赖: Characteristic, Characteristic.comap_quotient_mk, centerCharacteristic, comap_quotient_mk, upperCentralSeriesStep_eq_comap_center
-/
instance [N.Characteristic] : Characteristic (upperCentralSeriesStep N) :=
  (upperCentralSeriesStep_eq_comap_center N) ▸ Characteristic.comap_quotient_mk centerCharacteristic

variable (G)

/--
Definition of `upperCentralSeriesAux` / `upperCentralSeriesAux` 的定义

English:
definition upperCentralSeriesAux
  signature: : Nat -> Σ' H : Subgroup G, Characteristic H
  body: upperCentralSeriesAux n
    let _un_characteristic := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩

中文:
定义 upperCentralSeriesAux
  签名: : 自然数 -> Σ' H : 子群 G, 特征 H
  定义体: upperCentralSeriesAux n
    let _un_characteristic := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩

Depends on / 依赖: upperCentralSeriesAux
-/
def upperCentralSeriesAux : Nat -> Σ' H : Subgroup G, Characteristic H
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux n
    let _un_characteristic := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩

/--
Definition of `_root_.AddSubgroup.upperCentralSeriesAux` / `_root_.AddSubgroup.upperCentralSeriesAux` 的定义

English:
definition _root_.AddSubgroup.upperCentralSeriesAux
  signature: (G : Type*) [AddGroup G]
  body: upperCentralSeriesAux G n
    let _un_characteristic := un.2
    ⟨AddSubgroup.upperCentralSeriesStep un.1, inferInstance⟩

中文:
定义 _root_.加法子群.upperCentralSeriesAux
  签名: (G : 类型) [加法群 G]
  定义体: upperCentralSeriesAux G n
    let _un_characteristic := un.2
    ⟨AddSubgroup.upperCentralSeriesStep un.1, inferInstance⟩

Depends on / 依赖: upperCentralSeriesAux
-/
def _root_.AddSubgroup.upperCentralSeriesAux (G : Type*) [AddGroup G] :
    Nat -> Σ' H : AddSubgroup G, H.Characteristic
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux G n
    let _un_characteristic := un.2
    ⟨AddSubgroup.upperCentralSeriesStep un.1, inferInstance⟩

attribute [to_additive existing] upperCentralSeriesAux

/-- `upperCentralSeries G n` is the `n`th term in the upper central series of `G`.

This is the increasing chain of subgroups of `G` that starts with the trivial subgroup `⊥` of `G`
and then continues defining `upperCentralSeries G (n + 1)` to be all the elements of `G`
that, modulo `upperCentralSeries G n`, belong to the center of the quotient
`G ⧸ upperCentralSeries G n`.

In particular, the identities
* `upperCentralSeries G 0 = ⊥` (`upperCentralSeries_zero`);
* `upperCentralSeries G 1 = center G` (`upperCentralSeries_one`);

hold.
-/
@[to_additive
/-- `upperCentralSeries G n` is the `n`th term in the upper central series of `G`.

This is the increasing chain of additive subgroups of `G` that starts with the trivial additive
subgroup `⊥` of `G` and then continues defining `upperCentralSeries G (n + 1)` to be all the
elements of `G` that, modulo `upperCentralSeries G n`, belong to the center of the additive quotient
`G ⧸ upperCentralSeries G n`.

In particular, the identities
* `upperCentralSeries G 0 = ⊥` (`upperCentralSeries_zero`);
* `upperCentralSeries G 1 = center G` (`upperCentralSeries_one`);

hold.
-/]
/--
Definition of `upperCentralSeries` / `upperCentralSeries` 的定义

English:
definition upperCentralSeries
  signature: (n : Nat)
  body: (upperCentralSeriesAux G n).1

@[to_additive]

中文:
定义 upperCentralSeries
  签名: (n : 自然数)
  定义体: (upperCentralSeriesAux G n).1

@[to_additive]

Depends on / 依赖: upperCentralSeriesAux
-/
def upperCentralSeries (n : Nat) : Subgroup G :=
  (upperCentralSeriesAux G n).1

@[to_additive]
instance (n : Nat) : Characteristic (upperCentralSeries G n) :=
  (upperCentralSeriesAux G n).2

@[to_additive (attr := simp)]
/--
theorem `upperCentralSeries_zero` / 定理 `upperCentralSeries_zero`

English:
theorem upperCentralSeries_zero
  statement: upperCentralSeries G 0 = ⊥
  proof: rfl

中文:
定理 upperCentralSeries_zero
  结论: upperCentralSeries G 0 = ⊥
  证明: rfl
-/
theorem upperCentralSeries_zero : upperCentralSeries G 0 = ⊥ := rfl

/--
theorem `upperCentralSeries_one` / 定理 `upperCentralSeries_one`

English:
theorem upperCentralSeries_one
  statement: upperCentralSeries G 1 = center G
  proof: by
  ext
  simp only [upperCentralSeries, upperCentralSeriesAux, upperCentralSeriesStep, mem_bot, mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, mem_center_iff]
  exact forall_congr' fun y => by
    rw [commutatorElement_def]; rw [mul_inv_eq_one]; rw [mul_inv_eq_iff_eq_mul]; r

中文:
定理 upperCentralSeries_one
  结论: upperCentralSeries G 1 = center G
  证明: by
  ext
  simp only [upperCentralSeries, upperCentralSeriesAux, upperCentralSeriesStep, mem_bot, mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, mem_center_iff]
  exact forall_congr' fun y => by
    rw [commutatorElement_def]; rw [mul_inv_eq_one]; rw [mul_inv_eq_iff_eq_mul]; r

Depends on / 依赖: Set.mem_ofPred_eq, Submonoid, Submonoid.mem_mk, Subsemigroup, Subsemigroup.mem_mk, commutatorElement_def, eq_comm, forall_congr, mem_bot, mem_center_iff, mem_mk, mem_ofPred_eq, mul_inv_eq_iff_eq_mul, mul_inv_eq_one, upperCentralSeries, upperCentralSeriesAux, upperCentralSeriesStep
-/
theorem upperCentralSeries_one : upperCentralSeries G 1 = center G := by
  ext
  simp only [upperCentralSeries, upperCentralSeriesAux, upperCentralSeriesStep, mem_bot, mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, mem_center_iff]
  exact forall_congr' fun y => by
    rw [commutatorElement_def]; rw [mul_inv_eq_one]; rw [mul_inv_eq_iff_eq_mul]; rw [eq_comm]

/--
theorem `_root_.AddSubgroup.upperCentralSeries_one` / 定理 `_root_.AddSubgroup.upperCentralSeries_one`

English:
theorem _root_.AddSubgroup.upperCentralSeries_one
  given: (G : Type*) [AddGroup G]
  proof: by
  ext
  simp only [AddSubgroup.upperCentralSeries, AddSubgroup.upperCentralSeriesAux,
    AddSubgroup.upperCentralSeriesStep, AddSubgroup.mem_bot, AddSubgroup.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_center_iff]
  exact forall_congr' fun y => by


中文:
定理 _root_.加法子群.upperCentralSeries_one
  条件: (G : 类型) [加法群 G]
  证明: by
  ext
  simp only [AddSubgroup.upperCentralSeries, AddSubgroup.upperCentralSeriesAux,
    AddSubgroup.upperCentralSeriesStep, AddSubgroup.mem_bot, AddSubgroup.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_center_iff]
  exact forall_congr' fun y => by


Depends on / 依赖: AddSubgroup, AddSubgroup.mem_bot, AddSubgroup.mem_center_iff, AddSubgroup.mem_mk, AddSubgroup.upperCentralSeries, AddSubgroup.upperCentralSeriesAux, AddSubgroup.upperCentralSeriesStep, AddSubmonoid, AddSubmonoid.mem_mk, AddSubsemigroup, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, addCommutatorElement_def, add_neg_eq_iff_eq_add, add_neg_eq_zero, eq_comm, forall_congr, mem_bot, mem_center_iff, mem_mk
-/
theorem _root_.AddSubgroup.upperCentralSeries_one (G : Type*) [AddGroup G] :
    AddSubgroup.upperCentralSeries G 1 = AddSubgroup.center G := by
  ext
  simp only [AddSubgroup.upperCentralSeries, AddSubgroup.upperCentralSeriesAux,
    AddSubgroup.upperCentralSeriesStep, AddSubgroup.mem_bot, AddSubgroup.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_center_iff]
  exact forall_congr' fun y => by
    rw [addCommutatorElement_def]; rw [add_neg_eq_zero]; rw [add_neg_eq_iff_eq_add]; rw [eq_comm]

attribute [to_additive existing (attr := simp) AddSubgroup.upperCentralSeries_one]
  upperCentralSeries_one

variable {G}

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`. -/
@[to_additive /-- The `n+1`st term of the upper central series `H i` has underlying set equal to
the `x` such that `⁅x,G⁆ ⊆ H n`. -/]
/--
theorem `mem_upperCentralSeries_succ_iff` / 定理 `mem_upperCentralSeries_succ_iff`

English:
theorem mem_upperCentralSeries_succ_iff
  given: {n : Nat} {x : G}
  proof: Iff.rfl

中文:
定理 mem_upperCentralSeries_succ_iff
  条件: {n : 自然数} {x : G}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_upperCentralSeries_succ_iff {n : Nat} {x : G} :
    x in upperCentralSeries G (n + 1) ↔ forall y : G, ⁅x, y⁆ in upperCentralSeries G n :=
  Iff.rfl

variable (G) in
@[to_additive]
/--
theorem `commutator_upperCentralSeries_top_le` / 定理 `commutator_upperCentralSeries_top_le`

English:
theorem commutator_upperCentralSeries_top_le
  given: (n : Nat)
  proof: by
.mpr apply closure_le _
  rintro _ ⟨h, hh, g, _, rfl⟩
  exact mem_upperCentralSeries_succ_iff.mp hh g

@[to_additive (attr := simp)]

中文:
定理 commutator_upperCentralSeries_top_le
  条件: (n : 自然数)
  证明: by
.mpr apply closure_le _
  rintro _ ⟨h, hh, g, _, rfl⟩
  exact mem_upperCentralSeries_succ_iff.mp hh g

@[to_additive (attr := simp)]

Depends on / 依赖: closure_le, mem_upperCentralSeries_succ_iff, mem_upperCentralSeries_succ_iff.mp
-/
theorem commutator_upperCentralSeries_top_le (n : Nat) :
    ⁅upperCentralSeries G (n + 1), ⊤⁆ <= upperCentralSeries G n := by
.mpr apply closure_le _
  rintro _ ⟨h, hh, g, _, rfl⟩
  exact mem_upperCentralSeries_succ_iff.mp hh g

@[to_additive (attr := simp)]
/--
lemma `comap_upperCentralSeries` / 引理 `comap_upperCentralSeries`

English:
lemma comap_upperCentralSeries
  given: {H : Type*} [Group H] (e : H ≃* G)

中文:
引理 comap_upperCentralSeries
  条件: {H : 类型} [群 H] (e : H ≃* G)
-/
lemma comap_upperCentralSeries {H : Type*} [Group H] (e : H ≃* G) :
    forall n, (upperCentralSeries G n).comap e = upperCentralSeries H n
  | 0 => by simpa [MonoidHom.ker_eq_bot_iff] using e.injective
  | n + 1 => by
    ext
    simp [mem_upperCentralSeries_succ_iff, ← comap_upperCentralSeries e n,
      ← e.toEquiv.forall_congr_right, commutatorElement_def]

end Subgroup

namespace Group

variable (G) in
-- `IsNilpotent` is already defined in the root namespace (for elements of rings).
-- TODO: Rename it to `IsNilpotentElement`?
/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
@[mk_iff, wikidata Q1755242]
/--
Definition of `IsNilpotent` / `IsNilpotent` 的定义

English:
class IsNilpotent
  parameters: (G : Type*) [Group G]
  axioms and operations (1):
    - nilpotent' : exists n : Nat, upperCentralSeries G n = ⊤

中文:
类 是幂零
  参数: (G : 类型) [群 G]
  公理与运算 (1 个):
    - nilpotent' : 存在 n : 自然数, upperCentralSeries G n = ⊤
-/
class IsNilpotent (G : Type*) [Group G] : Prop where
  nilpotent' : exists n : Nat, upperCentralSeries G n = ⊤

variable (G) in
-- `IsNilpotent` is already defined in the root namespace (for elements of rings).
-- TODO: Rename it to `IsNilpotentElement`?
/-- An additive group `G` is nilpotent if its upper central series is eventually `G`. -/
@[mk_iff]
/--
Definition of `_root_.AddGroup.IsNilpotent` / `_root_.AddGroup.IsNilpotent` 的定义

English:
class _root_.AddGroup.IsNilpotent
  parameters: (G : Type*) [AddGroup G]
  axioms and operations (1):
    - nilpotent' : exists n : Nat, AddSubgroup.upperCentralSeries G n = ⊤

中文:
类 _root_.加法群.是幂零
  参数: (G : 类型) [加法群 G]
  公理与运算 (1 个):
    - nilpotent' : 存在 n : 自然数, 加法子群.upperCentralSeries G n = ⊤
-/
class _root_.AddGroup.IsNilpotent (G : Type*) [AddGroup G] : Prop where
  nilpotent' : exists n : Nat, AddSubgroup.upperCentralSeries G n = ⊤

@[to_additive]
/--
lemma `IsNilpotent.nilpotent` / 引理 `IsNilpotent.nilpotent`

English:
lemma IsNilpotent.nilpotent
  given: (G : Type*) [Group G] [IsNilpotent G]
  proof: Group.IsNilpotent.nilpotent'

@[to_additive]

中文:
引理 是幂零.nilpotent
  条件: (G : 类型) [群 G] [是幂零 G]
  证明: Group.IsNilpotent.nilpotent'

@[to_additive]
-/
lemma IsNilpotent.nilpotent (G : Type*) [Group G] [IsNilpotent G] :
    exists n : Nat, upperCentralSeries G n = ⊤ := Group.IsNilpotent.nilpotent'

@[to_additive]
/--
lemma `isNilpotent_congr` / 引理 `isNilpotent_congr`

English:
lemma isNilpotent_congr
  given: {H : Type*} [Group H] (e : G ≃* H)
  statement: IsNilpotent G ↔ IsNilpotent H
  proof: by
  simp_rw [isNilpotent_iff]
  refine exists_congr fun n => ⟨fun h => ?_, fun h => ?_⟩
  · simp [← Subgroup.comap_top e.symm.toMonoidHom, ← h]
  · simp [← Subgroup.comap_top e.toMonoidHom, ← h]

@[to_additive (attr := simp)]

中文:
引理 isNilpotent_congr
  条件: {H : 类型} [群 H] (e : G ≃* H)
  结论: 是幂零 G ↔ 是幂零 H
  证明: by
  simp_rw [isNilpotent_iff]
  refine exists_congr fun n => ⟨fun h => ?_, fun h => ?_⟩
  · simp [← Subgroup.comap_top e.symm.toMonoidHom, ← h]
  · simp [← Subgroup.comap_top e.toMonoidHom, ← h]

@[to_additive (attr := simp)]

Depends on / 依赖: Subgroup, Subgroup.comap_top, comap_top, e.symm.toMonoidHom, e.toMonoidHom, exists_congr, isNilpotent_iff, simp_rw, toMonoidHom
-/
lemma isNilpotent_congr {H : Type*} [Group H] (e : G ≃* H) : IsNilpotent G ↔ IsNilpotent H := by
  simp_rw [isNilpotent_iff]
  refine exists_congr fun n => ⟨fun h => ?_, fun h => ?_⟩
  · simp [← Subgroup.comap_top e.symm.toMonoidHom, ← h]
  · simp [← Subgroup.comap_top e.toMonoidHom, ← h]

@[to_additive (attr := simp)]
/--
lemma `isNilpotent_top` / 引理 `isNilpotent_top`

English:
lemma isNilpotent_top
  statement: IsNilpotent (⊤ : Subgroup G) ↔ IsNilpotent G
  proof: isNilpotent_congr Subgroup.topEquiv

中文:
引理 isNilpotent_top
  结论: 是幂零 (⊤ : 子群 G) ↔ 是幂零 G
  证明: isNilpotent_congr Subgroup.topEquiv

Depends on / 依赖: Subgroup, Subgroup.topEquiv, isNilpotent_congr, topEquiv
-/
lemma isNilpotent_top : IsNilpotent (⊤ : Subgroup G) ↔ IsNilpotent G :=
  isNilpotent_congr Subgroup.topEquiv

variable (G) in
/-- A group `G` is virtually nilpotent if it has a nilpotent cofinite subgroup `N`. -/
@[to_additive /-- An additive group `G` is virtually nilpotent if it has a nilpotent cofinite
additive subgroup `N`. -/]
/--
Definition of `IsVirtuallyNilpotent` / `IsVirtuallyNilpotent` 的定义

English:
definition IsVirtuallyNilpotent
  signature: : Prop
  body: exists N : Subgroup G, IsNilpotent N ∧ FiniteIndex N

@[to_additive]

中文:
定义 IsVirtuallyNilpotent
  签名: : 命题
  定义体: exists N : Subgroup G, IsNilpotent N ∧ FiniteIndex N

@[to_additive]

Depends on / 依赖: FiniteIndex, IsNilpotent, Subgroup
-/
def IsVirtuallyNilpotent : Prop := exists N : Subgroup G, IsNilpotent N ∧ FiniteIndex N

@[to_additive]
/--
lemma `IsNilpotent.isVirtuallyNilpotent` / 引理 `IsNilpotent.isVirtuallyNilpotent`

English:
lemma IsNilpotent.isVirtuallyNilpotent
  given: (hG : IsNilpotent G)
  statement: IsVirtuallyNilpotent G
  proof: ⟨⊤, by simpa, inferInstance⟩

中文:
引理 是幂零.isVirtuallyNilpotent
  条件: (hG : 是幂零 G)
  结论: IsVirtuallyNilpotent G
  证明: ⟨⊤, by simpa, inferInstance⟩
-/
lemma IsNilpotent.isVirtuallyNilpotent (hG : IsNilpotent G) : IsVirtuallyNilpotent G :=
  ⟨⊤, by simpa, inferInstance⟩

end Group

open Group

namespace Subgroup

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
`⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
@[to_additive /-- A sequence of additive subgroups of `G` is an ascending central series if `H 0` is
trivial and `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. We do not require that `H n = G` for some `n`. -/]
/--
Definition of `IsAscendingCentralSeries` / `IsAscendingCentralSeries` 的定义

English:
definition IsAscendingCentralSeries
  signature: (H : Nat -> Subgroup G)
  body: H 0 = ⊥ ∧ forall (x : G) (n : Nat), x in H (n + 1) -> forall g, ⁅x, g⁆ in H n

中文:
定义 IsAscendingCentralSeries
  签名: (H : 自然数 -> 子群 G)
  定义体: H 0 = ⊥ ∧ forall (x : G) (n : Nat), x in H (n + 1) -> forall g, ⁅x, g⁆ in H n
-/
def IsAscendingCentralSeries (H : Nat -> Subgroup G) : Prop :=
  H 0 = ⊥ ∧ forall (x : G) (n : Nat), x in H (n + 1) -> forall g, ⁅x, g⁆ in H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
`⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not require that `H n = {1}` for some `n`. -/
@[to_additive /-- A sequence of additive subgroups of `G` is a descending central series if `H 0` is
`G` and `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. We do not require that `H n = {1}` for some `n`. -/]
/--
Definition of `IsDescendingCentralSeries` / `IsDescendingCentralSeries` 的定义

English:
definition IsDescendingCentralSeries
  signature: (H : Nat -> Subgroup G)
  body: H 0 = ⊤ ∧ forall (x : G) (n : Nat), x in H n -> forall g, ⁅x, g⁆ in H (n + 1)

中文:
定义 IsDescendingCentralSeries
  签名: (H : 自然数 -> 子群 G)
  定义体: H 0 = ⊤ ∧ forall (x : G) (n : Nat), x in H n -> forall g, ⁅x, g⁆ in H (n + 1)
-/
def IsDescendingCentralSeries (H : Nat -> Subgroup G) :=
  H 0 = ⊤ ∧ forall (x : G) (n : Nat), x in H n -> forall g, ⁅x, g⁆ in H (n + 1)

/-- Any ascending central series for a group is bounded above by the upper central series. -/
@[to_additive /-- Any ascending central series for an additive group is bounded above by the upper
central series. -/]
/--
theorem `ascending_central_series_le_upper` / 定理 `ascending_central_series_le_upper`

English:
theorem ascending_central_series_le_upper
  given: (H : Nat -> Subgroup G) (hH : IsAscendingCentralSeries H)

中文:
定理 ascending_central_series_le_upper
  条件: (H : 自然数 -> 子群 G) (hH : IsAscendingCentralSeries H)
-/
theorem ascending_central_series_le_upper (H : Nat -> Subgroup G) (hH : IsAscendingCentralSeries H) :
    forall n : Nat, H n <= upperCentralSeries G n
  | 0 => hH.1.symm ▸ le_refl ⊥
  | n + 1 => by
    intro x hx
    rw [mem_upperCentralSeries_succ_iff]
    exact fun y => ascending_central_series_le_upper H hH n (hH.2 x n hx y)

variable (G)

/-- The upper central series of a group is an ascending central series. -/
@[to_additive /-- The upper central series of an additive group is an ascending central series. -/]
/--
theorem `upperCentralSeries_isAscendingCentralSeries` / 定理 `upperCentralSeries_isAscendingCentralSeries`

English:
theorem upperCentralSeries_isAscendingCentralSeries
  proof: ⟨rfl, fun _x _n h => h⟩

@[to_additive]

中文:
定理 upperCentralSeries_isAscendingCentralSeries
  证明: ⟨rfl, fun _x _n h => h⟩

@[to_additive]
-/
theorem upperCentralSeries_isAscendingCentralSeries :
    IsAscendingCentralSeries (upperCentralSeries G) :=
  ⟨rfl, fun _x _n h => h⟩

@[to_additive]
/--
theorem `upperCentralSeries_mono` / 定理 `upperCentralSeries_mono`

English:
theorem upperCentralSeries_mono
  statement: Monotone (upperCentralSeries G)
  proof: by
  refine monotone_nat_of_le_succ ?_
  intro n x hx y
  rw [commutatorElement_def]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_assoc y x⁻¹ y⁻¹]
  exact mul_mem hx (Normal.conj_mem inferInstance x⁻¹ (inv_mem hx) y)

中文:
定理 upperCentralSeries_mono
  结论: 递增 (upperCentralSeries G)
  证明: by
  refine monotone_nat_of_le_succ ?_
  intro n x hx y
  rw [commutatorElement_def]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_assoc y x⁻¹ y⁻¹]
  exact mul_mem hx (Normal.conj_mem inferInstance x⁻¹ (inv_mem hx) y)

Depends on / 依赖: Normal, Normal.conj_mem, commutatorElement_def, conj_mem, inv_mem, monotone_nat_of_le_succ, mul_assoc, mul_mem
-/
theorem upperCentralSeries_mono : Monotone (upperCentralSeries G) := by
  refine monotone_nat_of_le_succ ?_
  intro n x hx y
  rw [commutatorElement_def]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_assoc y x⁻¹ y⁻¹]
  exact mul_mem hx (Normal.conj_mem inferInstance x⁻¹ (inv_mem hx) y)

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
finitely many steps. -/
@[to_additive /-- An additive group `G` is nilpotent iff there exists an ascending central series
which reaches `G` in finitely many steps. -/]
/--
theorem `nilpotent_iff_finite_ascending_central_series` / 定理 `nilpotent_iff_finite_ascending_central_series`

English:
theorem nilpotent_iff_finite_ascending_central_series
  proof: by
  constructor
  · rintro ⟨n, nH⟩
    exact ⟨_, _, upperCentralSeries_isAscendingCentralSeries G, nH⟩
  · rintro ⟨n, H, hH, hn⟩
    use n
    rw [eq_top_iff]; rw [← hn]
    exact ascending_central_series_le_upper H hH n

@[to_additive]

中文:
定理 nilpotent_iff_finite_ascending_central_series
  证明: by
  constructor
  · rintro ⟨n, nH⟩
    exact ⟨_, _, upperCentralSeries_isAscendingCentralSeries G, nH⟩
  · rintro ⟨n, H, hH, hn⟩
    use n
    rw [eq_top_iff]; rw [← hn]
    exact ascending_central_series_le_upper H hH n

@[to_additive]

Depends on / 依赖: ascending_central_series_le_upper, eq_top_iff, upperCentralSeries_isAscendingCentralSeries
-/
theorem nilpotent_iff_finite_ascending_central_series :
    IsNilpotent G ↔ exists n : Nat, exists H : Nat -> Subgroup G, IsAscendingCentralSeries H ∧ H n = ⊤ := by
  constructor
  · rintro ⟨n, nH⟩
    exact ⟨_, _, upperCentralSeries_isAscendingCentralSeries G, nH⟩
  · rintro ⟨n, H, hH, hn⟩
    use n
    rw [eq_top_iff]; rw [← hn]
    exact ascending_central_series_le_upper H hH n

@[to_additive]
/--
theorem `is_descending_rev_series_of_is_ascending` / 定理 `is_descending_rev_series_of_is_ascending`

English:
theorem is_descending_rev_series_of_is_ascending
  statement: {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊤)
  proof: by
  obtain ⟨h0, hH⟩ := hasc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp at hx
  by_cases! hm : n <= m
  · rw [tsub_eq_zero_of_le hm, h0, Subgroup.mem_bot] at hx
    subst hx
    rw [commutatorElement_one_left]
    exact Subgroup.one_mem _
  · apply hH
    convert! hx using 1
    rw [tsub_add_eq_add_t

中文:
定理 is_descending_rev_series_of_is_ascending
  结论: {H : 自然数 -> 子群 G} {n : 自然数} (hn : H n = ⊤)
  证明: by
  obtain ⟨h0, hH⟩ := hasc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp at hx
  by_cases! hm : n <= m
  · rw [tsub_eq_zero_of_le hm, h0, Subgroup.mem_bot] at hx
    subst hx
    rw [commutatorElement_one_left]
    exact Subgroup.one_mem _
  · apply hH
    convert! hx using 1
    rw [tsub_add_eq_add_t

Depends on / 依赖: Nat.add_sub_add_right, Nat.succ_eq_add_one, Nat.succ_le_of_lt, Subgroup, Subgroup.mem_bot, Subgroup.one_mem, add_sub_add_right, commutatorElement_one_left, convert, mem_bot, one_mem, succ_eq_add_one, succ_le_of_lt, tsub_add_eq_add_tsub, tsub_eq_zero_of_le
-/
theorem is_descending_rev_series_of_is_ascending {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊤)
    (hasc : IsAscendingCentralSeries H) : IsDescendingCentralSeries fun m : Nat => H (n - m) := by
  obtain ⟨h0, hH⟩ := hasc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp at hx
  by_cases! hm : n <= m
  · rw [tsub_eq_zero_of_le hm, h0, Subgroup.mem_bot] at hx
    subst hx
    rw [commutatorElement_one_left]
    exact Subgroup.one_mem _
  · apply hH
    convert! hx using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm)]; rw [Nat.succ_eq_add_one]; rw [Nat.add_sub_add_right]

@[to_additive]
/--
theorem `is_ascending_rev_series_of_is_descending` / 定理 `is_ascending_rev_series_of_is_descending`

English:
theorem is_ascending_rev_series_of_is_descending
  statement: {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊥)
  proof: by
  obtain ⟨h0, hH⟩ := hdesc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp only at hx ⊢
  by_cases! hm : n <= m
  · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
    rw [hnm]; rw [h0]
    exact mem_top _
  · convert! hH x _ hx g using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm)]; rw [Nat

中文:
定理 is_ascending_rev_series_of_is_descending
  结论: {H : 自然数 -> 子群 G} {n : 自然数} (hn : H n = ⊥)
  证明: by
  obtain ⟨h0, hH⟩ := hdesc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp only at hx ⊢
  by_cases! hm : n <= m
  · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
    rw [hnm]; rw [h0]
    exact mem_top _
  · convert! hH x _ hx g using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm)]; rw [Nat

Depends on / 依赖: Nat.add_sub_add_right, Nat.succ_eq_add_one, Nat.succ_le_of_lt, add_sub_add_right, convert, mem_top, succ_eq_add_one, succ_le_of_lt, tsub_add_eq_add_tsub, tsub_eq_zero_iff_le, tsub_eq_zero_iff_le.mpr
-/
theorem is_ascending_rev_series_of_is_descending {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊥)
    (hdesc : IsDescendingCentralSeries H) : IsAscendingCentralSeries fun m : Nat => H (n - m) := by
  obtain ⟨h0, hH⟩ := hdesc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp only at hx ⊢
  by_cases! hm : n <= m
  · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
    rw [hnm]; rw [h0]
    exact mem_top _
  · convert! hH x _ hx g using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm)]; rw [Nat.succ_eq_add_one]; rw [Nat.add_sub_add_right]

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
trivial group in a finite time. -/
@[to_additive /-- An additive group `G` is nilpotent iff there exists a descending central series
which reaches the trivial group in a finite time. -/]
/--
theorem `nilpotent_iff_finite_descending_central_series` / 定理 `nilpotent_iff_finite_descending_central_series`

English:
theorem nilpotent_iff_finite_descending_central_series
  proof: by
  rw [nilpotent_iff_finite_ascending_central_series]
  constructor
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_as

中文:
定理 nilpotent_iff_finite_descending_central_series
  证明: by
  rw [nilpotent_iff_finite_ascending_central_series]
  constructor
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_as

Depends on / 依赖: is_ascending_rev_series_of_is_descending, is_descending_rev_series_of_is_ascending, nilpotent_iff_finite_ascending_central_series, tsub_self
-/
theorem nilpotent_iff_finite_descending_central_series :
    IsNilpotent G ↔ exists n : Nat, exists H : Nat -> Subgroup G, IsDescendingCentralSeries H ∧ H n = ⊥ := by
  rw [nilpotent_iff_finite_ascending_central_series]
  constructor
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_ascending_rev_series_of_is_descending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1

variable {G}

/--
Definition of `lowerCentralSeries` / `lowerCentralSeries` 的定义

English:
definition lowerCentralSeries
  signature: (S : Subgroup G)

中文:
定义 lowerCentralSeries
  签名: (S : 子群 G)
-/
def lowerCentralSeries (S : Subgroup G) : Nat -> Subgroup G
  | 0 => S
  | n + 1 => ⁅lowerCentralSeries S n, S⁆

/--
Definition of `_root_.AddSubgroup.lowerCentralSeries` / `_root_.AddSubgroup.lowerCentralSeries` 的定义

English:
definition _root_.AddSubgroup.lowerCentralSeries
  signature: {G : Type*} [AddGroup G] (S : AddSubgroup G)

中文:
定义 _root_.加法子群.lowerCentralSeries
  签名: {G : 类型} [加法群 G] (S : 加法子群 G)
-/
def _root_.AddSubgroup.lowerCentralSeries {G : Type*} [AddGroup G] (S : AddSubgroup G) :
    Nat -> AddSubgroup G
  | 0 => S
  | n + 1 => ⁅lowerCentralSeries S n, S⁆

attribute [to_additive existing] lowerCentralSeries

variable (S : Subgroup G)

@[to_additive (attr := simp)]
/--
theorem `lowerCentralSeries_zero` / 定理 `lowerCentralSeries_zero`

English:
theorem lowerCentralSeries_zero
  statement: S.lowerCentralSeries 0 = S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lowerCentralSeries_zero
  结论: S.lowerCentralSeries 0 = S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem lowerCentralSeries_zero : S.lowerCentralSeries 0 = S := rfl

@[to_additive (attr := simp)]
/--
theorem `lowerCentralSeries_succ` / 定理 `lowerCentralSeries_succ`

English:
theorem lowerCentralSeries_succ
  given: (n : Nat)
  proof: rfl

@[to_additive top_lowerCentralSeries_one]

中文:
定理 lowerCentralSeries_succ
  条件: (n : 自然数)
  证明: rfl

@[to_additive top_lowerCentralSeries_one]
-/
theorem lowerCentralSeries_succ (n : Nat) :
    S.lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆ := rfl

@[to_additive top_lowerCentralSeries_one]
/--
theorem `top_lowerCentralSeries_one` / 定理 `top_lowerCentralSeries_one`

English:
theorem top_lowerCentralSeries_one
  statement: (⊤ : Subgroup G).lowerCentralSeries 1 = _root_.commutator G
  proof: rfl

@[deprecated (since := "2026-05-25")]
alias _root_.AddSubgroup.lowerCentralSeries_one := AddSubgroup.top_lowerCentralSeries_one

@[to_additive existing lowerCentralSeries_one, deprecated (since := "2026-05-25")]
alias lowerCentralSeries_one := top_lowerCentralSeries_one

@[to_additive]

中文:
定理 top_lowerCentralSeries_one
  结论: (⊤ : 子群 G).lowerCentralSeries 1 = _root_.commutator G
  证明: rfl

@[deprecated (since := "2026-05-25")]
alias _root_.AddSubgroup.lowerCentralSeries_one := AddSubgroup.top_lowerCentralSeries_one

@[to_additive existing lowerCentralSeries_one, deprecated (since := "2026-05-25")]
alias lowerCentralSeries_one := top_lowerCentralSeries_one

@[to_additive]
-/
theorem top_lowerCentralSeries_one : (⊤ : Subgroup G).lowerCentralSeries 1 = _root_.commutator G :=
  rfl

@[deprecated (since := "2026-05-25")]
alias _root_.AddSubgroup.lowerCentralSeries_one := AddSubgroup.top_lowerCentralSeries_one

@[to_additive existing lowerCentralSeries_one, deprecated (since := "2026-05-25")]
alias lowerCentralSeries_one := top_lowerCentralSeries_one

@[to_additive]
/--
theorem `mem_lowerCentralSeries_succ_iff` / 定理 `mem_lowerCentralSeries_succ_iff`

English:
theorem mem_lowerCentralSeries_succ_iff
  given: (n : Nat) (q : G)
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_lowerCentralSeries_succ_iff
  条件: (n : 自然数) (q : G)
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_lowerCentralSeries_succ_iff (n : Nat) (q : G) :
    q in S.lowerCentralSeries (n + 1) ↔
    q in closure { x | exists p in S.lowerCentralSeries n, exists q in S, ⁅p, q⁆ = x } := Iff.rfl

@[to_additive]
/--
Instance `lowerCentralSeries_characteristic` / 实例 `lowerCentralSeries_characteristic`

English:
instance lowerCentralSeries_characteristic
  signature: [S.Characteristic] (n : Nat)
  body: by
  induction n with
  | zero => simpa
  | succ d _ => rw [lowerCentralSeries_succ]; infer_instance

@[to_additive]

中文:
实例 lowerCentralSeries_characteristic
  签名: [S.特征] (n : 自然数)
  定义体: by
  induction n with
  | zero => simpa
  | succ d _ => rw [lowerCentralSeries_succ]; infer_instance

@[to_additive]

Depends on / 依赖: infer_instance, lowerCentralSeries_succ
-/
instance lowerCentralSeries_characteristic [S.Characteristic] (n : Nat) :
    (S.lowerCentralSeries n).Characteristic := by
  induction n with
  | zero => simpa
  | succ d _ => rw [lowerCentralSeries_succ]; infer_instance

@[to_additive]
/--
theorem `self_le_normalizer_lowerCentralSeries` / 定理 `self_le_normalizer_lowerCentralSeries`

English:
theorem self_le_normalizer_lowerCentralSeries

中文:
定理 self_le_normalizer_lowerCentralSeries
-/
theorem self_le_normalizer_lowerCentralSeries :
    forall n, S <= Subgroup.normalizer (S.lowerCentralSeries n : Set G)
  | 0 => Subgroup.le_normalizer
  | n + 1 => by
    rw [lowerCentralSeries_succ]
    apply normalizer_commutator_ge_right

@[to_additive]
/--
theorem `lowerCentralSeries_antitone` / 定理 `lowerCentralSeries_antitone`

English:
theorem lowerCentralSeries_antitone
  statement: Antitone S.lowerCentralSeries
  proof: by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [lowerCentralSeries_succ]; rw [← le_normalizer_iff_commutator_le_left]
  exact S.self_le_normalizer_lowerCentralSeries n

中文:
定理 lowerCentralSeries_antitone
  结论: 递减 S.lowerCentralSeries
  证明: by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [lowerCentralSeries_succ]; rw [← le_normalizer_iff_commutator_le_left]
  exact S.self_le_normalizer_lowerCentralSeries n

Depends on / 依赖: S.self_le_normalizer_lowerCentralSeries, antitone_nat_of_succ_le, le_normalizer_iff_commutator_le_left, lowerCentralSeries_succ, self_le_normalizer_lowerCentralSeries
-/
theorem lowerCentralSeries_antitone : Antitone S.lowerCentralSeries := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [lowerCentralSeries_succ]; rw [← le_normalizer_iff_commutator_le_left]
  exact S.self_le_normalizer_lowerCentralSeries n

/-- The lower central series of a group is a descending central series. -/
@[to_additive /-- The lower central series of an additive group is a descending central series. -/]
/--
theorem `lowerCentralSeries_isDescendingCentralSeries` / 定理 `lowerCentralSeries_isDescendingCentralSeries`

English:
theorem lowerCentralSeries_isDescendingCentralSeries
  proof: by
  constructor
  · rfl
  intro x n hxn g
  exact commutator_mem_commutator hxn (mem_top g)

中文:
定理 lowerCentralSeries_isDescendingCentralSeries
  证明: by
  constructor
  · rfl
  intro x n hxn g
  exact commutator_mem_commutator hxn (mem_top g)

Depends on / 依赖: commutator_mem_commutator, lowerCentralSeries, mem_top
-/
theorem lowerCentralSeries_isDescendingCentralSeries :
    IsDescendingCentralSeries (G := G) (lowerCentralSeries ⊤) := by
  constructor
  · rfl
  intro x n hxn g
  exact commutator_mem_commutator hxn (mem_top g)

/-- Any descending central series for a group is bounded below by the lower central series. -/
@[to_additive /-- Any descending central series for an additive group is bounded below by the lower
central series. -/]
/--
theorem `descending_central_series_ge_lower` / 定理 `descending_central_series_ge_lower`

English:
theorem descending_central_series_ge_lower
  given: (H : Nat -> Subgroup G) (hH : IsDescendingCentralSeries H)

中文:
定理 descending_central_series_ge_lower
  条件: (H : 自然数 -> 子群 G) (hH : IsDescendingCentralSeries H)
-/
theorem descending_central_series_ge_lower (H : Nat -> Subgroup G) (hH : IsDescendingCentralSeries H) :
    forall n : Nat, lowerCentralSeries ⊤ n <= H n
  | 0 => hH.1.symm ▸ le_refl ⊤
  | n + 1 => commutator_le.mpr fun x hx q _ =>
      hH.2 x n (descending_central_series_ge_lower H hH n hx) q

/-- The lower central series commutes with images under a group homomorphism. -/
@[to_additive]
/--
theorem `map_lowerCentralSeries` / 定理 `map_lowerCentralSeries`

English:
theorem map_lowerCentralSeries
  given: {K : Type*} [Group K] (f : G ->* K) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [lowerCentralSeries_succ]; rw [lowerCentralSeries_succ]; rw [Subgroup.map_commutator]; rw [hd]

中文:
定理 map_lowerCentralSeries
  条件: {K : 类型} [群 K] (f : G ->* K) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [lowerCentralSeries_succ]; rw [lowerCentralSeries_succ]; rw [Subgroup.map_commutator]; rw [hd]

Depends on / 依赖: Subgroup, Subgroup.map_commutator, lowerCentralSeries_succ, map_commutator
-/
theorem map_lowerCentralSeries {K : Type*} [Group K] (f : G ->* K) (n : Nat) :
    (S.lowerCentralSeries n).map f = (S.map f).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [lowerCentralSeries_succ]; rw [lowerCentralSeries_succ]; rw [Subgroup.map_commutator]; rw [hd]

/-- The lower central series of `H : Subgroup G` computed in the ambient group `G` coincides with
the lower central series of `H` viewed as its own group, mapped back to `G`. -/
@[to_additive (attr := simp)]
/--
theorem `top_subtype_lowerCentralSeries` / 定理 `top_subtype_lowerCentralSeries`

English:
theorem top_subtype_lowerCentralSeries
  given: (H : Subgroup G) (n : Nat)
  proof: by
  rw [map_lowerCentralSeries]; rw [← MonoidHom.range_eq_map]; rw [subtype_range]

中文:
定理 top_subtype_lowerCentralSeries
  条件: (H : 子群 G) (n : 自然数)
  证明: by
  rw [map_lowerCentralSeries]; rw [← MonoidHom.range_eq_map]; rw [subtype_range]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, map_lowerCentralSeries, range_eq_map, subtype_range
-/
theorem top_subtype_lowerCentralSeries (H : Subgroup G) (n : Nat) :
    (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCentralSeries n := by
  rw [map_lowerCentralSeries]; rw [← MonoidHom.range_eq_map]; rw [subtype_range]

/-- A subgroup is nilpotent iff its lower central series (computed in the ambient group) eventually
vanishes. -/
@[to_additive /-- An additive subgroup is nilpotent iff its lower central series eventually
vanishes. -/]
/--
theorem `isNilpotent_iff_lowerCentralSeries` / 定理 `isNilpotent_iff_lowerCentralSeries`

English:
theorem isNilpotent_iff_lowerCentralSeries
  proof: by
  rw [nilpotent_iff_finite_descending_central_series]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, ?_⟩
    have h1 := descending_central_series_ge_lower H hH n
    rw [hn]; rw [le_bot_iff] at h1
    rw [← top_subtype_lowerCentralSeries]; rw [h1]; rw [Subgroup.map_bot]
  · rintro ⟨n,

中文:
定理 isNilpotent_iff_lowerCentralSeries
  证明: by
  rw [nilpotent_iff_finite_descending_central_series]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, ?_⟩
    have h1 := descending_central_series_ge_lower H hH n
    rw [hn]; rw [le_bot_iff] at h1
    rw [← top_subtype_lowerCentralSeries]; rw [h1]; rw [Subgroup.map_bot]
  · rintro ⟨n,

Depends on / 依赖: Subgroup, Subgroup.map_bot, descending_central_series_ge_lower, le_bot_iff, lowerCentralSeries, lowerCentralSeries_isDescendingCentralSeries, map_bot, map_subtype_inj, nilpotent_iff_finite_descending_central_series, top_subtype_lowerCentralSeries
-/
theorem isNilpotent_iff_lowerCentralSeries :
    Group.IsNilpotent S ↔ exists n, S.lowerCentralSeries n = ⊥ := by
  rw [nilpotent_iff_finite_descending_central_series]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, ?_⟩
    have h1 := descending_central_series_ge_lower H hH n
    rw [hn]; rw [le_bot_iff] at h1
    rw [← top_subtype_lowerCentralSeries]; rw [h1]; rw [Subgroup.map_bot]
  · rintro ⟨n, hn⟩
    refine ⟨n, lowerCentralSeries ⊤, lowerCentralSeries_isDescendingCentralSeries, ?_⟩
    rwa [← map_subtype_inj, map_bot, top_subtype_lowerCentralSeries]

/-- A group is nilpotent if and only if its lower central series eventually reaches
the trivial subgroup. -/
@[to_additive /-- An additive group is nilpotent if and only if its lower central series eventually
reaches the trivial additive subgroup. -/]
/--
theorem `nilpotent_iff_lowerCentralSeries` / 定理 `nilpotent_iff_lowerCentralSeries`

English:
theorem nilpotent_iff_lowerCentralSeries
  proof: Group.isNilpotent_top.symm.trans (isNilpotent_iff_lowerCentralSeries ⊤)

中文:
定理 nilpotent_iff_lowerCentralSeries
  证明: Group.isNilpotent_top.symm.trans (isNilpotent_iff_lowerCentralSeries ⊤)

Depends on / 依赖: Group.isNilpotent_top.symm.trans, isNilpotent_iff_lowerCentralSeries, isNilpotent_top
-/
theorem nilpotent_iff_lowerCentralSeries :
    IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥ :=
  Group.isNilpotent_top.symm.trans (isNilpotent_iff_lowerCentralSeries ⊤)

end Subgroup

section Classical

variable (G) in
open scoped Classical in
/-- The nilpotency class of a nilpotent group is the smallest natural `n` such that
the `n`-th term of the upper central series is `G`. If `G` is not nilpotent then the nilpotency
class takes the junk value 0. -/
@[to_additive /-- The nilpotency class of a nilpotent additive group is the smallest natural `n`
such that the `n`-th term of the upper central series is `G`. If `G` is not nilpotent then the
nilpotency class takes the junk value 0. -/]
/--
Definition of `Group.nilpotencyClass` / `Group.nilpotencyClass` 的定义

English:
definition Group.nilpotencyClass
  signature: : Nat
  body: if hG : IsNilpotent G then Nat.find hG.nilpotent else 0

@[to_additive]

中文:
定义 群.nilpotencyClass
  签名: : 自然数
  定义体: if hG : IsNilpotent G then Nat.find hG.nilpotent else 0

@[to_additive]

Depends on / 依赖: IsNilpotent, Nat.find, hG.nilpotent, nilpotent
-/
noncomputable def Group.nilpotencyClass : Nat :=
  if hG : IsNilpotent G then Nat.find hG.nilpotent else 0

@[to_additive]
/--
theorem `Group.nilpotencyClass_of_not_nilpotent` / 定理 `Group.nilpotencyClass_of_not_nilpotent`

English:
theorem Group.nilpotencyClass_of_not_nilpotent
  given: (hG : ¬ IsNilpotent G)
  proof: dif_neg hG

中文:
定理 群.nilpotencyClass_of_not_nilpotent
  条件: (hG : ¬ 是幂零 G)
  证明: dif_neg hG

Depends on / 依赖: dif_neg
-/
theorem Group.nilpotencyClass_of_not_nilpotent (hG : ¬ IsNilpotent G) :
    Group.nilpotencyClass G = 0 :=
  dif_neg hG

variable [hG : IsNilpotent G]

open scoped Classical in
@[to_additive]
/--
theorem `Group.nilpotencyClass_def` / 定理 `Group.nilpotencyClass_def`

English:
theorem Group.nilpotencyClass_def
  proof: dif_pos hG

中文:
定理 群.nilpotencyClass_def
  证明: dif_pos hG

Depends on / 依赖: dif_pos
-/
theorem Group.nilpotencyClass_def :
    Group.nilpotencyClass G = Nat.find (IsNilpotent.nilpotent G) :=
  dif_pos hG

namespace Subgroup

@[to_additive (attr := simp)]
/--
theorem `upperCentralSeries_nilpotencyClass` / 定理 `upperCentralSeries_nilpotencyClass`

English:
theorem upperCentralSeries_nilpotencyClass
  proof: by
  classical
  rw [nilpotencyClass_def]; rw [Nat.find_spec (IsNilpotent.nilpotent G)]

@[to_additive]

中文:
定理 upperCentralSeries_nilpotencyClass
  证明: by
  classical
  rw [nilpotencyClass_def]; rw [Nat.find_spec (IsNilpotent.nilpotent G)]

@[to_additive]

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, Nat.find_spec, classical, find_spec, nilpotencyClass_def, nilpotent
-/
theorem upperCentralSeries_nilpotencyClass :
    upperCentralSeries G (Group.nilpotencyClass G) = ⊤ := by
  classical
  rw [nilpotencyClass_def]; rw [Nat.find_spec (IsNilpotent.nilpotent G)]

@[to_additive]
/--
theorem `upperCentralSeries_eq_top_iff_nilpotencyClass_le` / 定理 `upperCentralSeries_eq_top_iff_nilpotencyClass_le`

English:
theorem upperCentralSeries_eq_top_iff_nilpotencyClass_le
  given: {n : Nat}
  proof: by
  classical
  constructor
  · intro h
    rw [nilpotencyClass_def]
    exact Nat.find_le h
  · intro h
    rw [eq_top_iff]; rw [← upperCentralSeries_nilpotencyClass]
    exact upperCentralSeries_mono _ h

中文:
定理 upperCentralSeries_eq_top_iff_nilpotencyClass_le
  条件: {n : 自然数}
  证明: by
  classical
  constructor
  · intro h
    rw [nilpotencyClass_def]
    exact Nat.find_le h
  · intro h
    rw [eq_top_iff]; rw [← upperCentralSeries_nilpotencyClass]
    exact upperCentralSeries_mono _ h

Depends on / 依赖: Nat.find_le, classical, eq_top_iff, find_le, nilpotencyClass_def, upperCentralSeries_mono, upperCentralSeries_nilpotencyClass
-/
theorem upperCentralSeries_eq_top_iff_nilpotencyClass_le {n : Nat} :
    upperCentralSeries G n = ⊤ ↔ Group.nilpotencyClass G <= n := by
  classical
  constructor
  · intro h
    rw [nilpotencyClass_def]
    exact Nat.find_le h
  · intro h
    rw [eq_top_iff]; rw [← upperCentralSeries_nilpotencyClass]
    exact upperCentralSeries_mono _ h

open scoped Classical in
/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an ascending
central series reaches `G` in its `n`-th term. -/
@[to_additive /-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an
ascending central series reaches `G` in its `n`-th term. -/]
/--
theorem `least_ascending_central_series_length_eq_nilpotencyClass` / 定理 `least_ascending_central_series_length_eq_nilpotencyClass`

English:
theorem least_ascending_central_series_length_eq_nilpotencyClass
  proof: by
  rw [nilpotencyClass_def]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · intro n hn
    exact ⟨upperCentralSeries G, upperCentralSeries_isAscendingCentralSeries G, hn⟩
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← top_le_iff]; rw [← hn]
    exact ascending_central_series_le_upper H hH n

中文:
定理 least_ascending_central_series_length_eq_nilpotencyClass
  证明: by
  rw [nilpotencyClass_def]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · intro n hn
    exact ⟨upperCentralSeries G, upperCentralSeries_isAscendingCentralSeries G, hn⟩
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← top_le_iff]; rw [← hn]
    exact ascending_central_series_le_upper H hH n

Depends on / 依赖: Nat.find_mono, ascending_central_series_le_upper, find_mono, le_antisymm, nilpotencyClass_def, top_le_iff, upperCentralSeries, upperCentralSeries_isAscendingCentralSeries
-/
theorem least_ascending_central_series_length_eq_nilpotencyClass :
    Nat.find ((nilpotent_iff_finite_ascending_central_series G).mp hG) =
    Group.nilpotencyClass G := by
  rw [nilpotencyClass_def]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · intro n hn
    exact ⟨upperCentralSeries G, upperCentralSeries_isAscendingCentralSeries G, hn⟩
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← top_le_iff]; rw [← hn]
    exact ascending_central_series_le_upper H hH n

open scoped Classical in
/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the descending
central series reaches `⊥` in its `n`-th term. -/
@[to_additive /-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the
descending central series reaches `⊥` in its `n`-th term. -/]
/--
theorem `least_descending_central_series_length_eq_nilpotencyClass` / 定理 `least_descending_central_series_length_eq_nilpotencyClass`

English:
theorem least_descending_central_series_length_eq_nilpotencyClass
  proof: by
  rw [← least_ascending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro

中文:
定理 least_descending_central_series_length_eq_nilpotencyClass
  证明: by
  rw [← least_ascending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro

Depends on / 依赖: Nat.find_mono, find_mono, is_ascending_rev_series_of_is_descending, is_descending_rev_series_of_is_ascending, le_antisymm, least_ascending_central_series_length_eq_nilpotencyClass, tsub_self
-/
theorem least_descending_central_series_length_eq_nilpotencyClass :
    Nat.find ((nilpotent_iff_finite_descending_central_series G).mp hG) =
    Group.nilpotencyClass G := by
  rw [← least_ascending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_ascending_rev_series_of_is_descending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1

open scoped Classical in
/-- The nilpotency class of a nilpotent `G` is equal to the length of the lower central series. -/
@[to_additive /-- The nilpotency class of a nilpotent `G` is equal to the length of the lower
central series. -/]
/--
theorem `lowerCentralSeries_length_eq_nilpotencyClass` / 定理 `lowerCentralSeries_length_eq_nilpotencyClass`

English:
theorem lowerCentralSeries_length_eq_nilpotencyClass
  proof: by
  rw [← least_descending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← le_bot_iff]; rw [← hn]
    exact descending_central_series_ge_lower H hH n
  · rintro n h
    exact ⟨lowerCentralSeries ⊤, ⟨lowerCentr

中文:
定理 lowerCentralSeries_length_eq_nilpotencyClass
  证明: by
  rw [← least_descending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← le_bot_iff]; rw [← hn]
    exact descending_central_series_ge_lower H hH n
  · rintro n h
    exact ⟨lowerCentralSeries ⊤, ⟨lowerCentr

Depends on / 依赖: Nat.find_mono, descending_central_series_ge_lower, find_mono, le_antisymm, le_bot_iff, least_descending_central_series_length_eq_nilpotencyClass, lowerCentralSeries, lowerCentralSeries_isDescendingCentralSeries
-/
theorem lowerCentralSeries_length_eq_nilpotencyClass :
    Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) = Group.nilpotencyClass (G := G) := by
  rw [← least_descending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← le_bot_iff]; rw [← hn]
    exact descending_central_series_ge_lower H hH n
  · rintro n h
    exact ⟨lowerCentralSeries ⊤, ⟨lowerCentralSeries_isDescendingCentralSeries, h⟩⟩

@[to_additive (attr := simp)]
/--
theorem `lowerCentralSeries_nilpotencyClass` / 定理 `lowerCentralSeries_nilpotencyClass`

English:
theorem lowerCentralSeries_nilpotencyClass
  proof: by
  classical
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  exact Nat.find_spec (nilpotent_iff_lowerCentralSeries.mp hG)

@[to_additive]

中文:
定理 lowerCentralSeries_nilpotencyClass
  证明: by
  classical
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  exact Nat.find_spec (nilpotent_iff_lowerCentralSeries.mp hG)

@[to_additive]

Depends on / 依赖: Nat.find_spec, classical, find_spec, lowerCentralSeries_length_eq_nilpotencyClass, nilpotent_iff_lowerCentralSeries, nilpotent_iff_lowerCentralSeries.mp
-/
theorem lowerCentralSeries_nilpotencyClass :
    lowerCentralSeries (⊤ : Subgroup G) (Group.nilpotencyClass G) = ⊥ := by
  classical
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  exact Nat.find_spec (nilpotent_iff_lowerCentralSeries.mp hG)

@[to_additive]
/--
theorem `lowerCentralSeries_eq_bot_iff_nilpotencyClass_le` / 定理 `lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`

English:
theorem lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
  given: {n : Nat}
  proof: by
  classical
  constructor
  · intro h
    rw [← lowerCentralSeries_length_eq_nilpotencyClass]
    exact Nat.find_le h
  · intro h
    rw [eq_bot_iff]; rw [← lowerCentralSeries_nilpotencyClass]
    exact lowerCentralSeries_antitone _ h

omit [IsNilpotent G] in
@[to_additive]

中文:
定理 lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
  条件: {n : 自然数}
  证明: by
  classical
  constructor
  · intro h
    rw [← lowerCentralSeries_length_eq_nilpotencyClass]
    exact Nat.find_le h
  · intro h
    rw [eq_bot_iff]; rw [← lowerCentralSeries_nilpotencyClass]
    exact lowerCentralSeries_antitone _ h

omit [IsNilpotent G] in
@[to_additive]

Depends on / 依赖: Nat.find_le, classical, eq_bot_iff, find_le, lowerCentralSeries_antitone, lowerCentralSeries_length_eq_nilpotencyClass, lowerCentralSeries_nilpotencyClass
-/
theorem lowerCentralSeries_eq_bot_iff_nilpotencyClass_le {n : Nat} :
    lowerCentralSeries (⊤ : Subgroup G) n = ⊥ ↔ Group.nilpotencyClass G <= n := by
  classical
  constructor
  · intro h
    rw [← lowerCentralSeries_length_eq_nilpotencyClass]
    exact Nat.find_le h
  · intro h
    rw [eq_bot_iff]; rw [← lowerCentralSeries_nilpotencyClass]
    exact lowerCentralSeries_antitone _ h

omit [IsNilpotent G] in
@[to_additive]
/--
theorem `lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top` / 定理 `lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top`

English:
theorem lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top
  given: {n : Nat}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsNilpotent G := nilpotent_iff_lowerCentralSeries.mpr ⟨n, h⟩
    rwa [upperCentralSeries_eq_top_iff_nilpotencyClass_le,
      ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  · have : IsNilpotent G := ⟨n, h⟩
    rwa [lowerCentralSeries_eq_bot_if

中文:
定理 lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top
  条件: {n : 自然数}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsNilpotent G := nilpotent_iff_lowerCentralSeries.mpr ⟨n, h⟩
    rwa [upperCentralSeries_eq_top_iff_nilpotencyClass_le,
      ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  · have : IsNilpotent G := ⟨n, h⟩
    rwa [lowerCentralSeries_eq_bot_if

Depends on / 依赖: IsNilpotent, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, nilpotent_iff_lowerCentralSeries, nilpotent_iff_lowerCentralSeries.mpr, upperCentralSeries, upperCentralSeries_eq_top_iff_nilpotencyClass_le
-/
theorem lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top {n : Nat} :
    lowerCentralSeries (G := G) ⊤ n = ⊥ ↔ upperCentralSeries G n = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsNilpotent G := nilpotent_iff_lowerCentralSeries.mpr ⟨n, h⟩
    rwa [upperCentralSeries_eq_top_iff_nilpotencyClass_le,
      ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  · have : IsNilpotent G := ⟨n, h⟩
    rwa [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
      ← upperCentralSeries_eq_top_iff_nilpotencyClass_le]

end Subgroup

end Classical

namespace Subgroup

@[to_additive]
/--
theorem `lowerCentralSeries_le_self` / 定理 `lowerCentralSeries_le_self`

English:
theorem lowerCentralSeries_le_self
  given: (S : Subgroup G) (n : Nat)
  proof: by
  simpa using S.lowerCentralSeries_antitone (Nat.zero_le n)

@[to_additive]

中文:
定理 lowerCentralSeries_le_self
  条件: (S : 子群 G) (n : 自然数)
  证明: by
  simpa using S.lowerCentralSeries_antitone (Nat.zero_le n)

@[to_additive]

Depends on / 依赖: Nat.zero_le, S.lowerCentralSeries_antitone, lowerCentralSeries_antitone, zero_le
-/
theorem lowerCentralSeries_le_self (S : Subgroup G) (n : Nat) :
    S.lowerCentralSeries n <= S := by
  simpa using S.lowerCentralSeries_antitone (Nat.zero_le n)

@[to_additive]
/--
theorem `lowerCentralSeries_mono` / 定理 `lowerCentralSeries_mono`

English:
theorem lowerCentralSeries_mono
  given: (n : Nat)
  proof: by
  induction n with
  | zero => intro S T h; simpa
  | succ d hd => intro S T h; simp only [lowerCentralSeries_succ]; exact commutator_mono (hd h) h

@[to_additive (attr := deprecated "Use `top_subtype_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-27"))]

中文:
定理 lowerCentralSeries_mono
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => intro S T h; simpa
  | succ d hd => intro S T h; simp only [lowerCentralSeries_succ]; exact commutator_mono (hd h) h

@[to_additive (attr := deprecated "Use `top_subtype_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-27"))]

Depends on / 依赖: commutator_mono, lowerCentralSeries_succ
-/
theorem lowerCentralSeries_mono (n : Nat) :
    Monotone (fun S : Subgroup G => S.lowerCentralSeries n) := by
  induction n with
  | zero => intro S T h; simpa
  | succ d hd => intro S T h; simp only [lowerCentralSeries_succ]; exact commutator_mono (hd h) h

@[to_additive (attr := deprecated "Use `top_subtype_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-27"))]
/--
theorem `lowerCentralSeries_map_subtype_le` / 定理 `lowerCentralSeries_map_subtype_le`

English:
theorem lowerCentralSeries_map_subtype_le
  given: (H : Subgroup G) (n : Nat)
  proof: by
  rw [top_subtype_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive (attr := deprecated "Use `map_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-28"))]

中文:
定理 lowerCentralSeries_map_subtype_le
  条件: (H : 子群 G) (n : 自然数)
  证明: by
  rw [top_subtype_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive (attr := deprecated "Use `map_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-28"))]

Depends on / 依赖: le_top, lowerCentralSeries_mono, top_subtype_lowerCentralSeries
-/
theorem lowerCentralSeries_map_subtype_le (H : Subgroup G) (n : Nat) :
    ((⊤ : Subgroup H).lowerCentralSeries n).map H.subtype <= lowerCentralSeries ⊤ n := by
  rw [top_subtype_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive (attr := deprecated "Use `map_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-28"))]
/--
theorem `lowerCentralSeries.map` / 定理 `lowerCentralSeries.map`

English:
theorem lowerCentralSeries.map
  given: {K : Type*} [Group K] (f : G ->* K) (n : Nat)
  proof: by
  rw [map_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive]

中文:
定理 lowerCentralSeries.map
  条件: {K : 类型} [群 K] (f : G ->* K) (n : 自然数)
  证明: by
  rw [map_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive]

Depends on / 依赖: le_top, lowerCentralSeries_mono, map_lowerCentralSeries
-/
theorem lowerCentralSeries.map {K : Type*} [Group K] (f : G ->* K) (n : Nat) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f <= (⊤ : Subgroup K).lowerCentralSeries n := by
  rw [map_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive]
/--
Instance `lowerCentralSeries_normal` / 实例 `lowerCentralSeries_normal`

English:
instance lowerCentralSeries_normal
  signature: (S : Subgroup G) [S.Normal] (n : Nat)
  body: by
  induction n with
  | zero => simpa
  | succ n _ => rw [lowerCentralSeries_succ]; infer_instance

中文:
实例 lowerCentralSeries_normal
  签名: (S : 子群 G) [S.正规] (n : 自然数)
  定义体: by
  induction n with
  | zero => simpa
  | succ n _ => rw [lowerCentralSeries_succ]; infer_instance

Depends on / 依赖: infer_instance, lowerCentralSeries_succ
-/
instance lowerCentralSeries_normal (S : Subgroup G) [S.Normal] (n : Nat) :
    (S.lowerCentralSeries n).Normal := by
  induction n with
  | zero => simpa
  | succ n _ => rw [lowerCentralSeries_succ]; infer_instance

/-- A subgroup of a nilpotent group is nilpotent. -/
@[to_additive /-- An additive subgroup of a nilpotent group is nilpotent. -/]
/--
Instance `isNilpotent` / 实例 `isNilpotent`

English:
instance isNilpotent
  signature: (H : Subgroup G) [hG : IsNilpotent G]
  body: by
  rw [nilpotent_iff_lowerCentralSeries] at *
  rcases hG with ⟨n, hG⟩
  refine ⟨n, ?_⟩
  rw [← map_subtype_inj]; rw [map_bot]; rw [top_subtype_lowerCentralSeries]; rw [eq_bot_iff]; rw [← hG]
  exact H.lowerCentralSeries_mono n le_top

中文:
实例 isNilpotent
  签名: (H : 子群 G) [hG : 是幂零 G]
  定义体: by
  rw [nilpotent_iff_lowerCentralSeries] at *
  rcases hG with ⟨n, hG⟩
  refine ⟨n, ?_⟩
  rw [← map_subtype_inj]; rw [map_bot]; rw [top_subtype_lowerCentralSeries]; rw [eq_bot_iff]; rw [← hG]
  exact H.lowerCentralSeries_mono n le_top

Depends on / 依赖: H.lowerCentralSeries_mono, eq_bot_iff, le_top, lowerCentralSeries_mono, map_bot, map_subtype_inj, nilpotent_iff_lowerCentralSeries, top_subtype_lowerCentralSeries
-/
instance isNilpotent (H : Subgroup G) [hG : IsNilpotent G] : IsNilpotent H := by
  rw [nilpotent_iff_lowerCentralSeries] at *
  rcases hG with ⟨n, hG⟩
  refine ⟨n, ?_⟩
  rw [← map_subtype_inj]; rw [map_bot]; rw [top_subtype_lowerCentralSeries]; rw [eq_bot_iff]; rw [← hG]
  exact H.lowerCentralSeries_mono n le_top

/-- The nilpotency class of a subgroup is less or equal to the nilpotency class of the group. -/
@[to_additive /-- The nilpotency class of an additive subgroup is less or equal to the nilpotency
/--
Definition of `of` / `of` 的定义

English:
class of
  parameters: the additive group. -/]
  (no additional axioms)

中文:
类 of
  参数: the additive group. -/]
  (无附加公理)
-/
class of the additive group. -/]
/--
theorem `nilpotencyClass_le` / 定理 `nilpotencyClass_le`

English:
theorem nilpotencyClass_le
  given: (H : Subgroup G) [hG : IsNilpotent G]
  proof: by
  repeat rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_mono
  intro n hG
  rw [← map_subtype_inj]; rw [map_bot]; rw [top_subtype_lowerCentralSeries]; rw [eq_bot_iff]; rw [← hG]
  exact H.lowerCentralSeries_mono n le_top

@[to_additive]

中文:
定理 nilpotencyClass_le
  条件: (H : 子群 G) [hG : 是幂零 G]
  证明: by
  repeat rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_mono
  intro n hG
  rw [← map_subtype_inj]; rw [map_bot]; rw [top_subtype_lowerCentralSeries]; rw [eq_bot_iff]; rw [← hG]
  exact H.lowerCentralSeries_mono n le_top

@[to_additive]

Depends on / 依赖: H.lowerCentralSeries_mono, Nat.find_mono, classical, eq_bot_iff, find_mono, le_top, lowerCentralSeries_length_eq_nilpotencyClass, lowerCentralSeries_mono, map_bot, map_subtype_inj, repeat, top_subtype_lowerCentralSeries
-/
theorem nilpotencyClass_le (H : Subgroup G) [hG : IsNilpotent G] :
    Group.nilpotencyClass H <= Group.nilpotencyClass G := by
  repeat rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_mono
  intro n hG
  rw [← map_subtype_inj]; rw [map_bot]; rw [top_subtype_lowerCentralSeries]; rw [eq_bot_iff]; rw [← hG]
  exact H.lowerCentralSeries_mono n le_top

@[to_additive]
/--
theorem `isNilpotent_of_lowerCentralSeries_eq_bot` / 定理 `isNilpotent_of_lowerCentralSeries_eq_bot`

English:
theorem isNilpotent_of_lowerCentralSeries_eq_bot
  statement: {S : Subgroup G} {n : Nat}
  proof: (isNilpotent_iff_lowerCentralSeries S).mpr ⟨n, h⟩

@[to_additive]

中文:
定理 isNilpotent_of_lowerCentralSeries_eq_bot
  结论: {S : 子群 G} {n : 自然数}
  证明: (isNilpotent_iff_lowerCentralSeries S).mpr ⟨n, h⟩

@[to_additive]

Depends on / 依赖: isNilpotent_iff_lowerCentralSeries
-/
theorem isNilpotent_of_lowerCentralSeries_eq_bot {S : Subgroup G} {n : Nat}
    (h : S.lowerCentralSeries n = ⊥) : Group.IsNilpotent S :=
  (isNilpotent_iff_lowerCentralSeries S).mpr ⟨n, h⟩

@[to_additive]
/--
theorem `lowerCentralSeries_eq_bot_of_nilpotencyClass_le` / 定理 `lowerCentralSeries_eq_bot_of_nilpotencyClass_le`

English:
theorem lowerCentralSeries_eq_bot_of_nilpotencyClass_le
  statement: {S : Subgroup G}
  proof: by
  rw [← top_subtype_lowerCentralSeries]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hn]; rw [map_bot]

@[to_additive]

中文:
定理 lowerCentralSeries_eq_bot_of_nilpotencyClass_le
  结论: {S : 子群 G}
  证明: by
  rw [← top_subtype_lowerCentralSeries]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hn]; rw [map_bot]

@[to_additive]

Depends on / 依赖: lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr, map_bot, top_subtype_lowerCentralSeries
-/
theorem lowerCentralSeries_eq_bot_of_nilpotencyClass_le {S : Subgroup G}
    [Group.IsNilpotent S] {n : Nat} (hn : Group.nilpotencyClass S <= n) :
    S.lowerCentralSeries n = ⊥ := by
  rw [← top_subtype_lowerCentralSeries]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hn]; rw [map_bot]

@[to_additive]
instance (priority := 100) _root_.Group.isNilpotent_of_subsingleton [Subsingleton G] :
    IsNilpotent G :=
  nilpotent_iff_lowerCentralSeries.2 ⟨0, Subsingleton.elim ⊤ ⊥⟩

@[to_additive]
/--
theorem `upperCentralSeries.map` / 定理 `upperCentralSeries.map`

English:
theorem upperCentralSeries.map
  statement: {H : Type*} [Group H] {f : G ->* H} (h : Function.Surjective f)
  proof: by
  induction n with
  | zero => simp
  | succ d hd =>
    rintro _ ⟨x, hx : x in upperCentralSeries G d.succ, rfl⟩ y'
    rcases h y' with ⟨y, rfl⟩
    simpa using! hd (mem_map_of_mem f (hx y))

@[to_additive]

中文:
定理 upperCentralSeries.map
  结论: {H : 类型} [群 H] {f : G ->* H} (h : 函数.满射 f)
  证明: by
  induction n with
  | zero => simp
  | succ d hd =>
    rintro _ ⟨x, hx : x in upperCentralSeries G d.succ, rfl⟩ y'
    rcases h y' with ⟨y, rfl⟩
    simpa using! hd (mem_map_of_mem f (hx y))

@[to_additive]

Depends on / 依赖: d.succ, mem_map_of_mem, upperCentralSeries
-/
theorem upperCentralSeries.map {H : Type*} [Group H] {f : G ->* H} (h : Function.Surjective f)
    (n : Nat) : Subgroup.map f (upperCentralSeries G n) <= upperCentralSeries H n := by
  induction n with
  | zero => simp
  | succ d hd =>
    rintro _ ⟨x, hx : x in upperCentralSeries G d.succ, rfl⟩ y'
    rcases h y' with ⟨y, rfl⟩
    simpa using! hd (mem_map_of_mem f (hx y))

@[to_additive]
/--
theorem `lowerCentralSeries_succ_eq_bot` / 定理 `lowerCentralSeries_succ_eq_bot`

English:
theorem lowerCentralSeries_succ_eq_bot
  statement: (S : Subgroup G) {n : Nat}
  proof: by
  rw [lowerCentralSeries_succ]; rw [commutator_def]; rw [closure_eq_bot_iff]; rw [Set.subset_singleton_iff]
  rintro x ⟨y, hy1, z, _, rfl⟩
  rw [commutatorElement_def]; rw [mul_assoc]; rw [← mul_inv_rev]; rw [mul_inv_eq_one]; rw [eq_comm]
  exact mem_center_iff.mp (h hy1) z

中文:
定理 lowerCentralSeries_succ_eq_bot
  结论: (S : 子群 G) {n : 自然数}
  证明: by
  rw [lowerCentralSeries_succ]; rw [commutator_def]; rw [closure_eq_bot_iff]; rw [Set.subset_singleton_iff]
  rintro x ⟨y, hy1, z, _, rfl⟩
  rw [commutatorElement_def]; rw [mul_assoc]; rw [← mul_inv_rev]; rw [mul_inv_eq_one]; rw [eq_comm]
  exact mem_center_iff.mp (h hy1) z

Depends on / 依赖: Set.subset_singleton_iff, closure_eq_bot_iff, commutatorElement_def, commutator_def, eq_comm, lowerCentralSeries_succ, mem_center_iff, mem_center_iff.mp, mul_assoc, mul_inv_eq_one, mul_inv_rev, subset_singleton_iff
-/
theorem lowerCentralSeries_succ_eq_bot (S : Subgroup G) {n : Nat}
    (h : S.lowerCentralSeries n <= center G) :
    S.lowerCentralSeries (n + 1) = ⊥ := by
  rw [lowerCentralSeries_succ]; rw [commutator_def]; rw [closure_eq_bot_iff]; rw [Set.subset_singleton_iff]
  rintro x ⟨y, hy1, z, _, rfl⟩
  rw [commutatorElement_def]; rw [mul_assoc]; rw [← mul_inv_rev]; rw [mul_inv_eq_one]; rw [eq_comm]
  exact mem_center_iff.mp (h hy1) z

/-- The preimage of a nilpotent group is nilpotent if the kernel of the homomorphism is contained
in the center. -/
@[to_additive /-- The preimage of a nilpotent additive group is nilpotent if the kernel of the
homomorphism is contained in the center. -/]
/--
theorem `isNilpotent_of_ker_le_center` / 定理 `isNilpotent_of_ker_le_center`

English:
theorem isNilpotent_of_ker_le_center
  statement: {H : Type*} [Group H] (f : G ->* H) (hf1 : f.ker <= center G)
  proof: by
  rw [nilpotent_iff_lowerCentralSeries]
  rcases nilpotent_iff_lowerCentralSeries.mp ‹_› with ⟨n, hn⟩
  refine ⟨n + 1, lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)⟩
  rw [map_lowerCentralSeries]; rw [← le_bot_iff]
  exact hn ▸ Subgroup.lowerCentralSeries

中文:
定理 isNilpotent_of_ker_le_center
  结论: {H : 类型} [群 H] (f : G ->* H) (hf1 : f.ker <= center G)
  证明: by
  rw [nilpotent_iff_lowerCentralSeries]
  rcases nilpotent_iff_lowerCentralSeries.mp ‹_› with ⟨n, hn⟩
  refine ⟨n + 1, lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)⟩
  rw [map_lowerCentralSeries]; rw [← le_bot_iff]
  exact hn ▸ Subgroup.lowerCentralSeries

Depends on / 依赖: Subgroup, Subgroup.lowerCentralSeries_mono, Subgroup.map_eq_bot_iff, le_bot_iff, le_top, le_trans, lowerCentralSeries_mono, lowerCentralSeries_succ_eq_bot, map_eq_bot_iff, map_lowerCentralSeries, nilpotent_iff_lowerCentralSeries, nilpotent_iff_lowerCentralSeries.mp
-/
theorem isNilpotent_of_ker_le_center {H : Type*} [Group H] (f : G ->* H) (hf1 : f.ker <= center G)
    [IsNilpotent H] : IsNilpotent G := by
  rw [nilpotent_iff_lowerCentralSeries]
  rcases nilpotent_iff_lowerCentralSeries.mp ‹_› with ⟨n, hn⟩
  refine ⟨n + 1, lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)⟩
  rw [map_lowerCentralSeries]; rw [← le_bot_iff]
  exact hn ▸ Subgroup.lowerCentralSeries_mono n le_top

end Subgroup

namespace Group

@[to_additive]
/--
theorem `nilpotencyClass_le_of_ker_le_center` / 定理 `nilpotencyClass_le_of_ker_le_center`

English:
theorem nilpotencyClass_le_of_ker_le_center
  statement: {H : Type*} [Group H] (f : G ->* H)
  proof: by
  have : IsNilpotent G := isNilpotent_of_ker_le_center f hf1
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_min'
  refine lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)
  rw [map_lowerCentralSeries]; rw [← le_bot_iff]; rw 

中文:
定理 nilpotencyClass_le_of_ker_le_center
  结论: {H : 类型} [群 H] (f : G ->* H)
  证明: by
  have : IsNilpotent G := isNilpotent_of_ker_le_center f hf1
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_min'
  refine lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)
  rw [map_lowerCentralSeries]; rw [← le_bot_iff]; rw 

Depends on / 依赖: IsNilpotent, Nat.find_min, Subgroup, Subgroup.lowerCentralSeries_mono, Subgroup.map_eq_bot_iff, classical, find_min, isNilpotent_of_ker_le_center, le_bot_iff, le_top, le_trans, lowerCentralSeries_length_eq_nilpotencyClass, lowerCentralSeries_mono, lowerCentralSeries_nilpotencyClass, lowerCentralSeries_succ_eq_bot, map_eq_bot_iff, map_lowerCentralSeries
-/
theorem nilpotencyClass_le_of_ker_le_center {H : Type*} [Group H] (f : G ->* H)
    (hf1 : f.ker <= center G) [IsNilpotent H] :
    Group.nilpotencyClass G <= Group.nilpotencyClass H + 1 := by
  have : IsNilpotent G := isNilpotent_of_ker_le_center f hf1
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_min'
  refine lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)
  rw [map_lowerCentralSeries]; rw [← le_bot_iff]; rw [← lowerCentralSeries_nilpotencyClass (G := H)]
  exact Subgroup.lowerCentralSeries_mono _ le_top

/-- The range of a surjective homomorphism from a nilpotent group is nilpotent. -/
@[to_additive /-- The range of a surjective homomorphism from a nilpotent additive group is
nilpotent. -/]
/--
theorem `nilpotent_of_surjective` / 定理 `nilpotent_of_surjective`

English:
theorem nilpotent_of_surjective
  statement: {G' : Type*} [Group G'] [h : IsNilpotent G] (f : G ->* G')
  proof: by
  rcases h with ⟨n, hn⟩
  use n
  apply eq_top_iff.mpr
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ <= upperCentralSeries G' n := upperCentralSeries.map hf 

中文:
定理 nilpotent_of_surjective
  结论: {G' : 类型} [群 G'] [h : 是幂零 G] (f : G ->* G')
  证明: by
  rcases h with ⟨n, hn⟩
  use n
  apply eq_top_iff.mpr
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ <= upperCentralSeries G' n := upperCentralSeries.map hf 

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, Subgroup, Subgroup.map, eq_top_iff, eq_top_iff.mpr, f.range, f.range_eq_top_of_surjective, range_eq_map, range_eq_top_of_surjective, upperCentralSeries, upperCentralSeries.map
-/
theorem nilpotent_of_surjective {G' : Type*} [Group G'] [h : IsNilpotent G] (f : G ->* G')
    (hf : Function.Surjective f) : IsNilpotent G' := by
  rcases h with ⟨n, hn⟩
  use n
  apply eq_top_iff.mpr
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ <= upperCentralSeries G' n := upperCentralSeries.map hf n

/-- The nilpotency class of the range of a surjective homomorphism from a
nilpotent group is less or equal the nilpotency class of the domain. -/
@[to_additive /-- The nilpotency class of the range of a surjective homomorphism from a
nilpotent additive group is less or equal the nilpotency class of the domain. -/]
/--
theorem `nilpotencyClass_le_of_surjective` / 定理 `nilpotencyClass_le_of_surjective`

English:
theorem nilpotencyClass_le_of_surjective
  statement: {G' : Type*} [Group G'] (f : G ->* G')
  proof: by
  have := nilpotent_of_surjective _ hf
  rw [nilpotencyClass_def]; rw [nilpotencyClass_def]
  classical apply Nat.find_mono
  intro n hn
  rw [eq_top_iff]
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (

中文:
定理 nilpotencyClass_le_of_surjective
  结论: {G' : 类型} [群 G'] (f : G ->* G')
  证明: by
  have := nilpotent_of_surjective _ hf
  rw [nilpotencyClass_def]; rw [nilpotencyClass_def]
  classical apply Nat.find_mono
  intro n hn
  rw [eq_top_iff]
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, Nat.find_mono, Subgroup, Subgroup.map, classical, eq_top_iff, f.range, f.range_eq_top_of_surjective, find_mono, nilpotencyClass_def, nilpotent_of_surjective, range_eq_map, range_eq_top_of_surjective, upperCentralSeries, upperCentralSeries.map
-/
theorem nilpotencyClass_le_of_surjective {G' : Type*} [Group G'] (f : G ->* G')
    (hf : Function.Surjective f) [h : IsNilpotent G] :
    Group.nilpotencyClass G' <= Group.nilpotencyClass G := by
  have := nilpotent_of_surjective _ hf
  rw [nilpotencyClass_def]; rw [nilpotencyClass_def]
  classical apply Nat.find_mono
  intro n hn
  rw [eq_top_iff]
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ <= upperCentralSeries G' n := upperCentralSeries.map hf n

/-- Nilpotency respects isomorphisms. -/
@[to_additive /-- Nilpotency respects isomorphisms. -/]
/--
theorem `nilpotent_of_mulEquiv` / 定理 `nilpotent_of_mulEquiv`

English:
theorem nilpotent_of_mulEquiv
  given: {G' : Type*} [Group G'] [_h : IsNilpotent G] (f : G ≃* G')
  proof: nilpotent_of_surjective f.toMonoidHom (MulEquiv.surjective f)

中文:
定理 nilpotent_of_mulEquiv
  条件: {G' : 类型} [群 G'] [_h : 是幂零 G] (f : G ≃* G')
  证明: nilpotent_of_surjective f.toMonoidHom (MulEquiv.surjective f)

Depends on / 依赖: MulEquiv, MulEquiv.surjective, f.toMonoidHom, nilpotent_of_surjective, surjective, toMonoidHom
-/
theorem nilpotent_of_mulEquiv {G' : Type*} [Group G'] [_h : IsNilpotent G] (f : G ≃* G') :
    IsNilpotent G' :=
  nilpotent_of_surjective f.toMonoidHom (MulEquiv.surjective f)

/-- A quotient of a nilpotent group is nilpotent. -/
@[to_additive /-- A quotient of a nilpotent group is nilpotent. -/]
/--
Instance `nilpotent_quotient_of_nilpotent` / 实例 `nilpotent_quotient_of_nilpotent`

English:
instance nilpotent_quotient_of_nilpotent
  signature: (H : Subgroup G) [H.Normal] [_h : IsNilpotent G]
  body: nilpotent_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

中文:
实例 nilpotent_quotient_of_nilpotent
  签名: (H : 子群 G) [H.正规] [_h : 是幂零 G]
  定义体: nilpotent_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, QuotientGroup.mk_surjective, mk_surjective, nilpotent_of_surjective
-/
instance nilpotent_quotient_of_nilpotent (H : Subgroup G) [H.Normal] [_h : IsNilpotent G] :
    IsNilpotent (G ⧸ H) :=
  nilpotent_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

/-- The nilpotency class of a quotient of `G` is less or equal the nilpotency class of `G`. -/
@[to_additive /-- The nilpotency class of a quotient of `G` is less or equal the nilpotency class
of `G`. -/]
/--
theorem `nilpotencyClass_quotient_le` / 定理 `nilpotencyClass_quotient_le`

English:
theorem nilpotencyClass_quotient_le
  given: (H : Subgroup G) [H.Normal] [_h : IsNilpotent G]
  proof: nilpotencyClass_le_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

中文:
定理 nilpotencyClass_quotient_le
  条件: (H : 子群 G) [H.正规] [_h : 是幂零 G]
  证明: nilpotencyClass_le_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, QuotientGroup.mk_surjective, mk_surjective, nilpotencyClass_le_of_surjective
-/
theorem nilpotencyClass_quotient_le (H : Subgroup G) [H.Normal] [_h : IsNilpotent G] :
    Group.nilpotencyClass (G ⧸ H) <= Group.nilpotencyClass G :=
  nilpotencyClass_le_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

end Group

open QuotientGroup

namespace Subgroup

-- This technical lemma helps with rewriting the subgroup, which occurs in indices
@[to_additive]
/--
theorem `comap_center_subst` / 定理 `comap_center_subst`

English:
theorem comap_center_subst
  given: {H₁ H₂ : Subgroup G} [Normal H₁] [Normal H₂] (h : H₁ = H₂)
  proof: by subst h; rfl

@[to_additive]

中文:
定理 comap_center_subst
  条件: {H₁ H₂ : 子群 G} [正规 H₁] [正规 H₂] (h : H₁ = H₂)
  证明: by subst h; rfl

@[to_additive]
-/
private theorem comap_center_subst {H₁ H₂ : Subgroup G} [Normal H₁] [Normal H₂] (h : H₁ = H₂) :
    comap (mk' H₁) (center (G ⧸ H₁)) = comap (mk' H₂) (center (G ⧸ H₂)) := by subst h; rfl

@[to_additive]
/--
theorem `comap_upperCentralSeries_quotient_center` / 定理 `comap_upperCentralSeries_quotient_center`

English:
theorem comap_upperCentralSeries_quotient_center
  given: (n : Nat)
  proof: by
  induction n with
  | zero =>
    simp only [upperCentralSeries_zero, MonoidHom.comap_bot, ker_mk',
      (upperCentralSeries_one G).symm]
  | succ n ih =>
    let Hn := upperCentralSeries (G ⧸ center G) n
    calc
      comap (mk' (center G)) (upperCentralSeriesStep Hn) =
          comap (mk' (

中文:
定理 comap_upperCentralSeries_quotient_center
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero =>
    simp only [upperCentralSeries_zero, MonoidHom.comap_bot, ker_mk',
      (upperCentralSeries_one G).symm]
  | succ n ih =>
    let Hn := upperCentralSeries (G ⧸ center G) n
    calc
      comap (mk' (center G)) (upperCentralSeriesStep Hn) =
          comap (mk' (

Depends on / 依赖: MonoidHom, MonoidHom.comap_bot, QuotientGroup, QuotientGroup.comap_comap_center, center, comap_bot, comap_comap_center, ker_mk, upperCentralSeries, upperCentralSeriesStep, upperCentralSeriesStep_eq_comap_center, upperCentralSeries_one, upperCentralSeries_zero
-/
theorem comap_upperCentralSeries_quotient_center (n : Nat) :
    comap (mk' (center G)) (upperCentralSeries (G ⧸ center G) n) = upperCentralSeries G n.succ := by
  induction n with
  | zero =>
    simp only [upperCentralSeries_zero, MonoidHom.comap_bot, ker_mk',
      (upperCentralSeries_one G).symm]
  | succ n ih =>
    let Hn := upperCentralSeries (G ⧸ center G) n
    calc
      comap (mk' (center G)) (upperCentralSeriesStep Hn) =
          comap (mk' (center G)) (comap (mk' Hn) (center ((G ⧸ center G) ⧸ Hn))) := by
        rw [upperCentralSeriesStep_eq_comap_center]
      _ = comap (mk' (comap (mk' (center G)) Hn)) (center (G ⧸ comap (mk' (center G)) Hn)) :=
        QuotientGroup.comap_comap_center
      _ = comap (mk' (upperCentralSeries G n.succ)) (center (G ⧸ upperCentralSeries G n.succ)) :=
        (comap_center_subst ih)
      _ = upperCentralSeriesStep (upperCentralSeries G n.succ) :=
        symm (upperCentralSeriesStep_eq_comap_center _)

end Subgroup

namespace Group

@[to_additive]
/--
theorem `nilpotencyClass_zero_iff_subsingleton` / 定理 `nilpotencyClass_zero_iff_subsingleton`

English:
theorem nilpotencyClass_zero_iff_subsingleton
  given: [IsNilpotent G]
  proof: by
  classical
  rw [Group.nilpotencyClass_def]; rw [Nat.find_eq_zero]; rw [upperCentralSeries_zero]; rw [subsingleton_iff_bot_eq_top]; rw [Subgroup.subsingleton_iff]

中文:
定理 nilpotencyClass_zero_iff_subsingleton
  条件: [是幂零 G]
  证明: by
  classical
  rw [Group.nilpotencyClass_def]; rw [Nat.find_eq_zero]; rw [upperCentralSeries_zero]; rw [subsingleton_iff_bot_eq_top]; rw [Subgroup.subsingleton_iff]

Depends on / 依赖: Group.nilpotencyClass_def, Nat.find_eq_zero, Subgroup, Subgroup.subsingleton_iff, classical, find_eq_zero, nilpotencyClass_def, subsingleton_iff, subsingleton_iff_bot_eq_top, upperCentralSeries_zero
-/
theorem nilpotencyClass_zero_iff_subsingleton [IsNilpotent G] :
    Group.nilpotencyClass G = 0 ↔ Subsingleton G := by
  classical
  rw [Group.nilpotencyClass_def]; rw [Nat.find_eq_zero]; rw [upperCentralSeries_zero]; rw [subsingleton_iff_bot_eq_top]; rw [Subgroup.subsingleton_iff]

/-- If the quotient by `center G` is nilpotent, then so is G. -/
@[to_additive /-- If the quotient by `center G` is nilpotent, then so is G. -/]
/--
theorem `of_quotient_center_nilpotent` / 定理 `of_quotient_center_nilpotent`

English:
theorem of_quotient_center_nilpotent
  given: (h : IsNilpotent (G ⧸ center G))
  statement: IsNilpotent G
  proof: by
  obtain ⟨n, hn⟩ := h.nilpotent
  use n.succ
  simp [← comap_upperCentralSeries_quotient_center, hn]

中文:
定理 of_quotient_center_nilpotent
  条件: (h : 是幂零 (G ⧸ center G))
  结论: 是幂零 G
  证明: by
  obtain ⟨n, hn⟩ := h.nilpotent
  use n.succ
  simp [← comap_upperCentralSeries_quotient_center, hn]

Depends on / 依赖: comap_upperCentralSeries_quotient_center, h.nilpotent, n.succ, nilpotent
-/
theorem of_quotient_center_nilpotent (h : IsNilpotent (G ⧸ center G)) : IsNilpotent G := by
  obtain ⟨n, hn⟩ := h.nilpotent
  use n.succ
  simp [← comap_upperCentralSeries_quotient_center, hn]

/-- Quotienting the `center G` reduces the nilpotency class by 1. -/
@[to_additive /-- Quotienting the `center G` reduces the nilpotency class by 1. -/]
/--
theorem `nilpotencyClass_quotient_center` / 定理 `nilpotencyClass_quotient_center`

English:
theorem nilpotencyClass_quotient_center
  proof: by
  by_cases hH : IsNilpotent G; swap
  · rw [nilpotencyClass_of_not_nilpotent hH, zero_tsub, nilpotencyClass_of_not_nilpotent]
    exact mt of_quotient_center_nilpotent hH
  generalize hn : Group.nilpotencyClass G = n
  rcases n with (rfl | n)
  · simp only [nilpotencyClass_zero_iff_subsingleton, 

中文:
定理 nilpotencyClass_quotient_center
  证明: by
  by_cases hH : IsNilpotent G; swap
  · rw [nilpotencyClass_of_not_nilpotent hH, zero_tsub, nilpotencyClass_of_not_nilpotent]
    exact mt of_quotient_center_nilpotent hH
  generalize hn : Group.nilpotencyClass G = n
  rcases n with (rfl | n)
  · simp only [nilpotencyClass_zero_iff_subsingleton, 

Depends on / 依赖: Group.nilpotencyClass, IsNilpotent, Quotient, Quotient.instSubsingletonQuotient, center, generalize, instSubsingletonQuotient, le_antisymm, leftRel, nilpotencyClass, nilpotencyClass_of_not_nilpotent, nilpotencyClass_zero_iff_subsingleton, of_quotient_center_nilpotent, upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_eq_top_iff_nilpotencyClass_le.m, zero_tsub
-/
theorem nilpotencyClass_quotient_center :
    Group.nilpotencyClass (G ⧸ center G) = Group.nilpotencyClass G - 1 := by
  by_cases hH : IsNilpotent G; swap
  · rw [nilpotencyClass_of_not_nilpotent hH, zero_tsub, nilpotencyClass_of_not_nilpotent]
    exact mt of_quotient_center_nilpotent hH
  generalize hn : Group.nilpotencyClass G = n
  rcases n with (rfl | n)
  · simp only [nilpotencyClass_zero_iff_subsingleton, zero_tsub] at *
    exact Quotient.instSubsingletonQuotient (leftRel (center G))
  · suffices Group.nilpotencyClass (G ⧸ center G) = n by simpa
    apply le_antisymm
    · apply upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp
      apply comap_injective (f := (mk' (center G))) Quot.mk_surjective
      rw [comap_upperCentralSeries_quotient_center]; rw [comap_top]; rw [Nat.succ_eq_add_one]; rw [← hn]
      exact upperCentralSeries_nilpotencyClass
    · apply le_of_add_le_add_right
      calc
        n + 1 = Group.nilpotencyClass G := hn.symm
        _ <= Group.nilpotencyClass (G ⧸ center G) + 1 :=
          nilpotencyClass_le_of_ker_le_center _ (le_of_eq (ker_mk' _))

/-- The nilpotency class of a non-trivial group is one more than its quotient by the center -/
@[to_additive /-- The nilpotency class of a non-trivial additive group is one more than its quotient
by the center -/]
/--
theorem `nilpotencyClass_eq_quotient_center_plus_one` / 定理 `nilpotencyClass_eq_quotient_center_plus_one`

English:
theorem nilpotencyClass_eq_quotient_center_plus_one
  given: [hH : IsNilpotent G] [Nontrivial G]
  proof: by
  rw [nilpotencyClass_quotient_center]
  rcases h : Group.nilpotencyClass G with ⟨⟩
  · exfalso
    rw [nilpotencyClass_zero_iff_subsingleton] at h
    apply false_of_nontrivial_of_subsingleton G
  · simp

中文:
定理 nilpotencyClass_eq_quotient_center_plus_one
  条件: [hH : 是幂零 G] [非平凡 G]
  证明: by
  rw [nilpotencyClass_quotient_center]
  rcases h : Group.nilpotencyClass G with ⟨⟩
  · exfalso
    rw [nilpotencyClass_zero_iff_subsingleton] at h
    apply false_of_nontrivial_of_subsingleton G
  · simp

Depends on / 依赖: Group.nilpotencyClass, false_of_nontrivial_of_subsingleton, nilpotencyClass, nilpotencyClass_quotient_center, nilpotencyClass_zero_iff_subsingleton
-/
theorem nilpotencyClass_eq_quotient_center_plus_one [hH : IsNilpotent G] [Nontrivial G] :
    Group.nilpotencyClass G = Group.nilpotencyClass (G ⧸ center G) + 1 := by
  rw [nilpotencyClass_quotient_center]
  rcases h : Group.nilpotencyClass G with ⟨⟩
  · exfalso
    rw [nilpotencyClass_zero_iff_subsingleton] at h
    apply false_of_nontrivial_of_subsingleton G
  · simp

/-- A custom induction principle for nilpotent groups. The base case is a trivial group
(`subsingleton G`), and in the induction step, one can assume the hypothesis for
the group quotiented by its center. -/
@[to_additive (attr := elab_as_elim) /-- A custom induction principle for nilpotent additive groups.
The base case is a trivial group (`subsingleton G`), and in the induction step, one can assume the
hypothesis for the additive group quotiented by its center. -/]
/--
theorem `nilpotent_center_quotient_ind` / 定理 `nilpotent_center_quotient_ind`

English:
theorem nilpotent_center_quotient_ind
  statement: {P : forall (G) [Group G] [IsNilpotent G], Prop}
  proof: by
  obtain ⟨n, h⟩ : exists n, Group.nilpotencyClass G = n := ⟨_, rfl⟩
  induction n generalizing G with
  | zero =>
    have := nilpotencyClass_zero_iff_subsingleton.mp h
    exact hbase _
  | succ n ih =>
    have hn : Group.nilpotencyClass (G ⧸ center G) = n := by
      simp [nilpotencyClass_quot

中文:
定理 nilpotent_center_quotient_ind
  结论: {P : 对任意 (G) [群 G] [是幂零 G], 命题}
  证明: by
  obtain ⟨n, h⟩ : exists n, Group.nilpotencyClass G = n := ⟨_, rfl⟩
  induction n generalizing G with
  | zero =>
    have := nilpotencyClass_zero_iff_subsingleton.mp h
    exact hbase _
  | succ n ih =>
    have hn : Group.nilpotencyClass (G ⧸ center G) = n := by
      simp [nilpotencyClass_quot

Depends on / 依赖: Group.nilpotencyClass, center, generalizing, nilpotencyClass, nilpotencyClass_quotient_center, nilpotencyClass_zero_iff_subsingleton, nilpotencyClass_zero_iff_subsingleton.mp
-/
theorem nilpotent_center_quotient_ind {P : forall (G) [Group G] [IsNilpotent G], Prop}
    (G : Type*) [Group G] [IsNilpotent G]
    (hbase : forall (G) [Group G] [Subsingleton G], P G)
    (hstep : forall (G) [Group G] [IsNilpotent G], P (G ⧸ center G) -> P G) : P G := by
  obtain ⟨n, h⟩ : exists n, Group.nilpotencyClass G = n := ⟨_, rfl⟩
  induction n generalizing G with
  | zero =>
    have := nilpotencyClass_zero_iff_subsingleton.mp h
    exact hbase _
  | succ n ih =>
    have hn : Group.nilpotencyClass (G ⧸ center G) = n := by
      simp [nilpotencyClass_quotient_center, h]
    exact hstep _ (ih _ hn)

end Group

-- todo: namespace `derivedSeries` and to_additivize.
/--
theorem `Subgroup.derived_le_lower_central` / 定理 `Subgroup.derived_le_lower_central`

English:
theorem Subgroup.derived_le_lower_central
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ i ih => apply commutator_mono ih; simp

@[to_additive]

中文:
定理 子群.derived_le_lower_central
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ i ih => apply commutator_mono ih; simp

@[to_additive]

Depends on / 依赖: commutator_mono
-/
theorem Subgroup.derived_le_lower_central (n : Nat) :
    derivedSeries G n <= lowerCentralSeries ⊤ n := by
  induction n with
  | zero => simp
  | succ i ih => apply commutator_mono ih; simp

@[to_additive]
/--
theorem `Subgroup.upperCentralSeries_one_eq_top_iff` / 定理 `Subgroup.upperCentralSeries_one_eq_top_iff`

English:
theorem Subgroup.upperCentralSeries_one_eq_top_iff
  proof: by
  rw [upperCentralSeries_one]
  exact Subgroup.center_eq_top_iff

@[to_additive]

中文:
定理 子群.upperCentralSeries_one_eq_top_iff
  证明: by
  rw [upperCentralSeries_one]
  exact Subgroup.center_eq_top_iff

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.center_eq_top_iff, center_eq_top_iff, upperCentralSeries_one
-/
theorem Subgroup.upperCentralSeries_one_eq_top_iff :
    upperCentralSeries G 1 = ⊤ ↔ IsMulCommutative G := by
  rw [upperCentralSeries_one]
  exact Subgroup.center_eq_top_iff

@[to_additive]
/--
theorem `Subgroup.lowerCentralSeries_one_eq_bot_iff` / 定理 `Subgroup.lowerCentralSeries_one_eq_bot_iff`

English:
theorem Subgroup.lowerCentralSeries_one_eq_bot_iff
  proof: by
  rw [lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top]
  exact upperCentralSeries_one_eq_top_iff

@[to_additive]

中文:
定理 子群.lowerCentralSeries_one_eq_bot_iff
  证明: by
  rw [lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top]
  exact upperCentralSeries_one_eq_top_iff

@[to_additive]

Depends on / 依赖: IsMulCommutative, lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top, upperCentralSeries_one_eq_top_iff
-/
theorem Subgroup.lowerCentralSeries_one_eq_bot_iff :
    lowerCentralSeries (G := G) ⊤ 1 = ⊥ ↔ IsMulCommutative G := by
  rw [lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top]
  exact upperCentralSeries_one_eq_top_iff

@[to_additive]
/--
theorem `Group.IsNilpotent.nilpotencyClass_le_one_iff` / 定理 `Group.IsNilpotent.nilpotencyClass_le_one_iff`

English:
theorem Group.IsNilpotent.nilpotencyClass_le_one_iff
  given: [IsNilpotent G]
  proof: by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  exact upperCentralSeries_one_eq_top_iff

中文:
定理 群.是幂零.nilpotencyClass_le_one_iff
  条件: [是幂零 G]
  证明: by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  exact upperCentralSeries_one_eq_top_iff

Depends on / 依赖: upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_one_eq_top_iff
-/
theorem Group.IsNilpotent.nilpotencyClass_le_one_iff [IsNilpotent G] :
    Group.nilpotencyClass G <= 1 ↔ IsMulCommutative G := by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  exact upperCentralSeries_one_eq_top_iff

/-- Abelian groups are nilpotent. -/
@[to_additive /-- Abelian groups are nilpotent. -/]
instance (priority := 100) CommGroup.isNilpotent {G : Type*} [CommGroup G] : IsNilpotent G := by
  use 1
  rw [upperCentralSeries_one]
  apply CommGroup.center_eq_top

/-- Abelian groups have nilpotency class at most one. -/
@[to_additive /-- Abelian groups have nilpotency class at most one. -/]
/--
theorem `CommGroup.nilpotencyClass_le_one` / 定理 `CommGroup.nilpotencyClass_le_one`

English:
theorem CommGroup.nilpotencyClass_le_one
  given: {G : Type*} [CommGroup G]
  proof: by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]; rw [upperCentralSeries_one]
  apply CommGroup.center_eq_top

中文:
定理 交换群.nilpotencyClass_le_one
  条件: {G : 类型} [交换群 G]
  证明: by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]; rw [upperCentralSeries_one]
  apply CommGroup.center_eq_top

Depends on / 依赖: CommGroup, CommGroup.center_eq_top, center_eq_top, upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_one
-/
theorem CommGroup.nilpotencyClass_le_one {G : Type*} [CommGroup G] :
    Group.nilpotencyClass G <= 1 := by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]; rw [upperCentralSeries_one]
  apply CommGroup.center_eq_top

/-- Groups with nilpotency class at most one are abelian. -/
@[to_additive /-- Additive groups with nilpotency class at most one are abelian. -/,
  instance_reducible]
/--
Definition of `commGroupOfNilpotencyClass` / `commGroupOfNilpotencyClass` 的定义

English:
definition commGroupOfNilpotencyClass
  signature: [IsNilpotent G] (h : Group.nilpotencyClass G <= 1)
  body: Group.commGroupOfCenterEqTop by
    rw [← upperCentralSeries_one]
    exact upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h

中文:
定义 commGroupOfNilpotencyClass
  签名: [是幂零 G] (h : 群.nilpotencyClass G <= 1)
  定义体: Group.commGroupOfCenterEqTop by
    rw [← upperCentralSeries_one]
    exact upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h

Depends on / 依赖: Group.commGroupOfCenterEqTop, commGroupOfCenterEqTop, upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr, upperCentralSeries_one
-/
def commGroupOfNilpotencyClass [IsNilpotent G] (h : Group.nilpotencyClass G <= 1) : CommGroup G :=
Group.commGroupOfCenterEqTop by
    rw [← upperCentralSeries_one]
    exact upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h

namespace Subgroup

@[to_additive]
/--
lemma `upperCentralSeries.eq_ge_of_eq_succ` / 引理 `upperCentralSeries.eq_ge_of_eq_succ`

English:
lemma upperCentralSeries.eq_ge_of_eq_succ
  statement: {a b : Nat} (ab : a <= b)
  proof: by
  refine Nat.le_induction rfl ?_ b ab
  grind only [eq_def, upperCentralSeriesAux.eq_def]

中文:
引理 upperCentralSeries.eq_ge_of_eq_succ
  结论: {a b : 自然数} (ab : a <= b)
  证明: by
  refine Nat.le_induction rfl ?_ b ab
  grind only [eq_def, upperCentralSeriesAux.eq_def]

Depends on / 依赖: Nat.le_induction, eq_def, le_induction, upperCentralSeriesAux, upperCentralSeriesAux.eq_def
-/
lemma upperCentralSeries.eq_ge_of_eq_succ {a b : Nat} (ab : a <= b)
    (hn : upperCentralSeries G a = upperCentralSeries G (a + 1)) :
    upperCentralSeries G a = upperCentralSeries G b := by
  refine Nat.le_induction rfl ?_ b ab
  grind only [eq_def, upperCentralSeriesAux.eq_def]

/-- If two different elements of the `upperCentralSeries` of a group `G` are equal, then
they are all equal, starting from the smaller index. -/
@[to_additive /-- If two different elements of the `upperCentralSeries` of an additive group `G`
are equal, then they are all equal, starting from the smaller index. -/]
/--
lemma `upperCentralSeries.eq_ge_of_eq_gt` / 引理 `upperCentralSeries.eq_ge_of_eq_gt`

English:
lemma upperCentralSeries.eq_ge_of_eq_gt
  statement: {a b c : Nat} (ab : a != b) (ac : a <= c)
  proof: by
  wlog ab : a < b
  · grind
  refine eq_ge_of_eq_succ ac (le_antisymm ?_ ?_)
· exact upperCentralSeries_mono _ Nat.le_succ ..
  · rw [hn]
    exact upperCentralSeries_mono _ (by grind)

@[to_additive]

中文:
引理 upperCentralSeries.eq_ge_of_eq_gt
  结论: {a b c : 自然数} (ab : a != b) (ac : a <= c)
  证明: by
  wlog ab : a < b
  · grind
  refine eq_ge_of_eq_succ ac (le_antisymm ?_ ?_)
· exact upperCentralSeries_mono _ Nat.le_succ ..
  · rw [hn]
    exact upperCentralSeries_mono _ (by grind)

@[to_additive]

Depends on / 依赖: Nat.le_succ, eq_ge_of_eq_succ, le_antisymm, le_succ, upperCentralSeries_mono
-/
lemma upperCentralSeries.eq_ge_of_eq_gt {a b c : Nat} (ab : a != b) (ac : a <= c)
    (hn : upperCentralSeries G a = upperCentralSeries G b) :
    upperCentralSeries G a = upperCentralSeries G c := by
  wlog ab : a < b
  · grind
  refine eq_ge_of_eq_succ ac (le_antisymm ?_ ?_)
· exact upperCentralSeries_mono _ Nat.le_succ ..
  · rw [hn]
    exact upperCentralSeries_mono _ (by grind)

@[to_additive]
/--
lemma `upperCentralSeries.eq_top` / 引理 `upperCentralSeries.eq_top`

English:
lemma upperCentralSeries.eq_top
  statement: [IsNilpotent G] {a b : Nat} (ab : a != b)
  proof: by
  grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent,
    upperCentralSeries_eq_top_iff_nilpotencyClass_le, eq_ge_of_eq_gt]

@[to_additive]

中文:
引理 upperCentralSeries.eq_top
  结论: [是幂零 G] {a b : 自然数} (ab : a != b)
  证明: by
  grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent,
    upperCentralSeries_eq_top_iff_nilpotencyClass_le, eq_ge_of_eq_gt]

@[to_additive]

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, eq_ge_of_eq_gt, nilpotent, upperCentralSeries_eq_top_iff_nilpotencyClass_le
-/
lemma upperCentralSeries.eq_top [IsNilpotent G] {a b : Nat} (ab : a != b)
    (hn : upperCentralSeries G a = upperCentralSeries G b) :
    upperCentralSeries G a = ⊤ := by
  grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent,
    upperCentralSeries_eq_top_iff_nilpotencyClass_le, eq_ge_of_eq_gt]

@[to_additive]
/--
lemma `nilpotencyClass_le_of_upperCentralSeries_eq` / 引理 `nilpotencyClass_le_of_upperCentralSeries_eq`

English:
lemma nilpotencyClass_le_of_upperCentralSeries_eq
  statement: {a b : Nat} (ab : a < b)
  proof: by
  by_cases hG : IsNilpotent G
  · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, upperCentralSeries.eq_top,
      upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw [nilpotencyClass_of_not_nilpotent hG]
    apply Nat.zero_le

中文:
引理 nilpotencyClass_le_of_upperCentralSeries_eq
  结论: {a b : 自然数} (ab : a < b)
  证明: by
  by_cases hG : IsNilpotent G
  · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, upperCentralSeries.eq_top,
      upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw [nilpotencyClass_of_not_nilpotent hG]
    apply Nat.zero_le

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, Nat.zero_le, eq_top, nilpotencyClass_of_not_nilpotent, nilpotent, upperCentralSeries, upperCentralSeries.eq_top, upperCentralSeries_eq_top_iff_nilpotencyClass_le, zero_le
-/
lemma nilpotencyClass_le_of_upperCentralSeries_eq {a b : Nat} (ab : a < b)
    (hn : upperCentralSeries G a = upperCentralSeries G b) :
    nilpotencyClass G <= a := by
  by_cases hG : IsNilpotent G
  · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, upperCentralSeries.eq_top,
      upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw [nilpotencyClass_of_not_nilpotent hG]
    apply Nat.zero_le

variable (G) in
@[to_additive]
/--
lemma `upperCentralSeries.StrictMonoOn` / 引理 `upperCentralSeries.StrictMonoOn`

English:
lemma upperCentralSeries.StrictMonoOn
  proof: by
  by_cases hG : IsNilpotent G
  · intros a ha b hb ab
    simp only [Set.mem_Iic] at ha hb
    apply lt_of_le_of_ne
    · exact upperCentralSeries_mono _ ab.le
    · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, eq_top,
        upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw

中文:
引理 upperCentralSeries.StrictMonoOn
  证明: by
  by_cases hG : IsNilpotent G
  · intros a ha b hb ab
    simp only [Set.mem_Iic] at ha hb
    apply lt_of_le_of_ne
    · exact upperCentralSeries_mono _ ab.le
    · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, eq_top,
        upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw

Depends on / 依赖: Iic_bot, IsNilpotent, IsNilpotent.nilpotent, Nat.bot_eq_zero, Set.Iic_bot, Set.mem_Iic, Set.strictMonoOn_singleton, ab.le, bot_eq_zero, eq_top, intros, lt_of_le_of_ne, mem_Iic, nilpotencyClass_of_not_nilpotent, nilpotent, strictMonoOn_singleton, upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_mono
-/
lemma upperCentralSeries.StrictMonoOn :
    StrictMonoOn (upperCentralSeries G) (Set.Iic (nilpotencyClass G)) := by
  by_cases hG : IsNilpotent G
  · intros a ha b hb ab
    simp only [Set.mem_Iic] at ha hb
    apply lt_of_le_of_ne
    · exact upperCentralSeries_mono _ ab.le
    · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, eq_top,
        upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw [nilpotencyClass_of_not_nilpotent hG, ← Nat.bot_eq_zero, Set.Iic_bot]
    apply Set.strictMonoOn_singleton

@[to_additive]
/--
lemma `upperCentralSeries.card_image_eq_of_le_nilpotencyClass` / 引理 `upperCentralSeries.card_image_eq_of_le_nilpotencyClass`

English:
lemma upperCentralSeries.card_image_eq_of_le_nilpotencyClass
  statement: {a : Nat}
  proof: by
  refine Set.ncard_eq_of_bijective (fun _ => upperCentralSeries G ·) ?_ ?_ ?_
  · grind
  · grind
  · intros i j hi hj
    refine (upperCentralSeries.StrictMonoOn G).injOn ?_ ?_ <;> grind

中文:
引理 upperCentralSeries.card_image_eq_of_le_nilpotencyClass
  结论: {a : 自然数}
  证明: by
  refine Set.ncard_eq_of_bijective (fun _ => upperCentralSeries G ·) ?_ ?_ ?_
  · grind
  · grind
  · intros i j hi hj
    refine (upperCentralSeries.StrictMonoOn G).injOn ?_ ?_ <;> grind

Depends on / 依赖: Set.ncard_eq_of_bijective, StrictMonoOn, intros, ncard_eq_of_bijective, upperCentralSeries, upperCentralSeries.StrictMonoOn
-/
lemma upperCentralSeries.card_image_eq_of_le_nilpotencyClass {a : Nat}
    (h2 : a <= nilpotencyClass G) :
    (upperCentralSeries G '' (Set.Iic a)).ncard = a + 1 := by
  refine Set.ncard_eq_of_bijective (fun _ => upperCentralSeries G ·) ?_ ?_ ?_
  · grind
  · grind
  · intros i j hi hj
    refine (upperCentralSeries.StrictMonoOn G).injOn ?_ ?_ <;> grind

end Subgroup

variable (G) in
@[to_additive]
/--
theorem `Group.IsNilpotent.center_ne_bot` / 定理 `Group.IsNilpotent.center_ne_bot`

English:
theorem Group.IsNilpotent.center_ne_bot
  given: [Nontrivial G] [IsNilpotent G]
  statement: center G != ⊥
  proof: .symm by simpa using mt (upperCentralSeries.eq_top zero_ne_one) by simp

中文:
定理 群.是幂零.center_ne_bot
  条件: [非平凡 G] [是幂零 G]
  结论: center G != ⊥
  证明: .symm by simpa using mt (upperCentralSeries.eq_top zero_ne_one) by simp

Depends on / 依赖: eq_top, upperCentralSeries, upperCentralSeries.eq_top, zero_ne_one
-/
theorem Group.IsNilpotent.center_ne_bot [Nontrivial G] [IsNilpotent G] : center G != ⊥ :=
.symm by simpa using mt (upperCentralSeries.eq_top zero_ne_one) by simp

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

@[to_additive]
/--
theorem `Subgroup.lowerCentralSeries_prod` / 定理 `Subgroup.lowerCentralSeries_prod`

English:
theorem Subgroup.lowerCentralSeries_prod
  given: (S₁ : Subgroup G₁) (S₂ : Subgroup G₂) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_prod_prod]

中文:
定理 子群.lowerCentralSeries_prod
  条件: (S₁ : 子群 G₁) (S₂ : 子群 G₂) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_prod_prod]

Depends on / 依赖: commutator_prod_prod, lowerCentralSeries_succ, simp_rw
-/
theorem Subgroup.lowerCentralSeries_prod (S₁ : Subgroup G₁) (S₂ : Subgroup G₂) (n : Nat) :
    (S₁.prod S₂).lowerCentralSeries n =
      (S₁.lowerCentralSeries n).prod (S₂.lowerCentralSeries n) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_prod_prod]

/-- The ⊤-specialization of `lowerCentralSeries_prod`. -/
@[to_additive]
/--
theorem `Subgroup.top_lowerCentralSeries_prod` / 定理 `Subgroup.top_lowerCentralSeries_prod`

English:
theorem Subgroup.top_lowerCentralSeries_prod
  given: (n : Nat)
  proof: by
  rw [← lowerCentralSeries_prod]; rw [top_prod_top]

中文:
定理 子群.top_lowerCentralSeries_prod
  条件: (n : 自然数)
  证明: by
  rw [← lowerCentralSeries_prod]; rw [top_prod_top]

Depends on / 依赖: lowerCentralSeries_prod, top_prod_top
-/
theorem Subgroup.top_lowerCentralSeries_prod (n : Nat) :
    (⊤ : Subgroup (G₁ × G₂)).lowerCentralSeries n =
      ((⊤ : Subgroup G₁).lowerCentralSeries n).prod ((⊤ : Subgroup G₂).lowerCentralSeries n) := by
  rw [← lowerCentralSeries_prod]; rw [top_prod_top]

/-- Products of nilpotent groups are nilpotent. -/
@[to_additive /-- Products of nilpotent groups are nilpotent. -/]
/--
Instance `Group.isNilpotent_prod` / 实例 `Group.isNilpotent_prod`

English:
instance Group.isNilpotent_prod
  signature: [IsNilpotent G₁] [IsNilpotent G₂]
  body: by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂), ?_⟩
  rw [top_lowerCentralSeries_prod]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_left _ _)]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_right 

中文:
实例 群.isNilpotent_prod
  签名: [是幂零 G₁] [是幂零 G₂]
  定义体: by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂), ?_⟩
  rw [top_lowerCentralSeries_prod]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_left _ _)]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_right 

Depends on / 依赖: Group.nilpotencyClass, bot_prod_bot, le_max_left, le_max_right, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr, nilpotencyClass, nilpotent_iff_lowerCentralSeries, top_lowerCentralSeries_prod
-/
instance Group.isNilpotent_prod [IsNilpotent G₁] [IsNilpotent G₂] : IsNilpotent (G₁ × G₂) := by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂), ?_⟩
  rw [top_lowerCentralSeries_prod]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_left _ _)]; rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_right _ _)]; rw [bot_prod_bot]

/-- The nilpotency class of a product is the max of the nilpotency classes of the factors. -/
@[to_additive /-- The nilpotency class of a product is the max of the nilpotency classes of the
factors. -/]
/--
theorem `Group.nilpotencyClass_prod` / 定理 `Group.nilpotencyClass_prod`

English:
theorem Group.nilpotencyClass_prod
  given: [IsNilpotent G₁] [IsNilpotent G₂]
  proof: by
  refine eq_of_forall_ge_iff fun k => ?_
  simp only [max_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_prod, prod_eq_bot_iff]

中文:
定理 群.nilpotencyClass_prod
  条件: [是幂零 G₁] [是幂零 G₂]
  证明: by
  refine eq_of_forall_ge_iff fun k => ?_
  simp only [max_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_prod, prod_eq_bot_iff]

Depends on / 依赖: eq_of_forall_ge_iff, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, max_le_iff, prod_eq_bot_iff, top_lowerCentralSeries_prod
-/
theorem Group.nilpotencyClass_prod [IsNilpotent G₁] [IsNilpotent G₂] :
    Group.nilpotencyClass (G₁ × G₂) =
    max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂) := by
  refine eq_of_forall_ge_iff fun k => ?_
  simp only [max_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_prod, prod_eq_bot_iff]

end Prod

section BoundedPi

-- First the case of infinite products with bounded nilpotency class
variable {η : Type*} {Gs : η -> Type*} [forall i, Group (Gs i)]

@[to_additive]
/--
theorem `Subgroup.lowerCentralSeries_pi_le` / 定理 `Subgroup.lowerCentralSeries_pi_le`

English:
theorem Subgroup.lowerCentralSeries_pi_le
  given: (Ss : forall i, Subgroup (Gs i)) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [lowerCentralSeries_succ]
    grw [commutator_mono ih le_rfl, commutator_pi_pi_le]

中文:
定理 子群.lowerCentralSeries_pi_le
  条件: (Ss : 对任意 i, 子群 (Gs i)) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [lowerCentralSeries_succ]
    grw [commutator_mono ih le_rfl, commutator_pi_pi_le]

Depends on / 依赖: commutator_mono, commutator_pi_pi_le, le_rfl, lowerCentralSeries_succ, simp_rw
-/
theorem Subgroup.lowerCentralSeries_pi_le (Ss : forall i, Subgroup (Gs i)) (n : Nat) :
    (Subgroup.pi Set.univ Ss).lowerCentralSeries n <= Subgroup.pi Set.univ
      fun i => (Ss i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [lowerCentralSeries_succ]
    grw [commutator_mono ih le_rfl, commutator_pi_pi_le]

/-- The ⊤-specialization of `lowerCentralSeries_pi_le`. -/
@[to_additive]
/--
theorem `Subgroup.top_lowerCentralSeries_pi_le` / 定理 `Subgroup.top_lowerCentralSeries_pi_le`

English:
theorem Subgroup.top_lowerCentralSeries_pi_le
  given: (n : Nat)
  proof: by
  rw [← pi_top (I := Set.univ)]
  exact lowerCentralSeries_pi_le _ _

中文:
定理 子群.top_lowerCentralSeries_pi_le
  条件: (n : 自然数)
  证明: by
  rw [← pi_top (I := Set.univ)]
  exact lowerCentralSeries_pi_le _ _

Depends on / 依赖: Set.univ, lowerCentralSeries_pi_le, pi_top
-/
theorem Subgroup.top_lowerCentralSeries_pi_le (n : Nat) :
    (⊤ : Subgroup (forall i, Gs i)).lowerCentralSeries n <= Subgroup.pi Set.univ
      fun i => (⊤ : Subgroup (Gs i)).lowerCentralSeries n := by
  rw [← pi_top (I := Set.univ)]
  exact lowerCentralSeries_pi_le _ _

/-- Products of nilpotent groups are nilpotent if their nilpotency class is bounded. -/
@[to_additive /-- Products of nilpotent additive groups are nilpotent if their nilpotency class is
bounded. -/]
/--
theorem `Group.isNilpotent_pi_of_bounded_class` / 定理 `Group.isNilpotent_pi_of_bounded_class`

English:
theorem Group.isNilpotent_pi_of_bounded_class
  statement: [forall i, IsNilpotent (Gs i)] (n : Nat)
  proof: by
  rw [nilpotent_iff_lowerCentralSeries]
refine ⟨n, eq_bot_iff.mpr (top_lowerCentralSeries_pi_le _).trans ?_⟩
  rw [le_bot_iff]; rw [pi_eq_bot_iff]
  exact fun i => lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (h i)

中文:
定理 群.isNilpotent_pi_of_bounded_class
  结论: [对任意 i, 是幂零 (Gs i)] (n : 自然数)
  证明: by
  rw [nilpotent_iff_lowerCentralSeries]
refine ⟨n, eq_bot_iff.mpr (top_lowerCentralSeries_pi_le _).trans ?_⟩
  rw [le_bot_iff]; rw [pi_eq_bot_iff]
  exact fun i => lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (h i)

Depends on / 依赖: eq_bot_iff, eq_bot_iff.mpr, le_bot_iff, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr, nilpotent_iff_lowerCentralSeries, pi_eq_bot_iff, top_lowerCentralSeries_pi_le
-/
theorem Group.isNilpotent_pi_of_bounded_class [forall i, IsNilpotent (Gs i)] (n : Nat)
    (h : forall i, Group.nilpotencyClass (Gs i) <= n) : IsNilpotent (forall i, Gs i) := by
  rw [nilpotent_iff_lowerCentralSeries]
refine ⟨n, eq_bot_iff.mpr (top_lowerCentralSeries_pi_le _).trans ?_⟩
  rw [le_bot_iff]; rw [pi_eq_bot_iff]
  exact fun i => lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (h i)

end BoundedPi

section FinitePi

-- Now for finite products
variable {η : Type*} {Gs : η -> Type*} [forall i, Group (Gs i)]

@[to_additive]
/--
theorem `Subgroup.lowerCentralSeries_pi_of_finite` / 定理 `Subgroup.lowerCentralSeries_pi_of_finite`

English:
theorem Subgroup.lowerCentralSeries_pi_of_finite
  given: [Finite η] (Ss : forall i, Subgroup (Gs i)) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_pi_pi_of_finite]

中文:
定理 子群.lowerCentralSeries_pi_of_finite
  条件: [有限 η] (Ss : 对任意 i, 子群 (Gs i)) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_pi_pi_of_finite]

Depends on / 依赖: commutator_pi_pi_of_finite, lowerCentralSeries_succ, simp_rw
-/
theorem Subgroup.lowerCentralSeries_pi_of_finite [Finite η] (Ss : forall i, Subgroup (Gs i)) (n : Nat) :
    (Subgroup.pi Set.univ Ss).lowerCentralSeries n = Subgroup.pi Set.univ
      fun i => (Ss i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_pi_pi_of_finite]

/-- The ⊤-specialization of `lowerCentralSeries_pi_of_finite`. -/
@[to_additive]
/--
theorem `Subgroup.top_lowerCentralSeries_pi_of_finite` / 定理 `Subgroup.top_lowerCentralSeries_pi_of_finite`

English:
theorem Subgroup.top_lowerCentralSeries_pi_of_finite
  given: [Finite η] (n : Nat)
  proof: by
  rw [← pi_top (I := Set.univ)]; rw [lowerCentralSeries_pi_of_finite]

中文:
定理 子群.top_lowerCentralSeries_pi_of_finite
  条件: [有限 η] (n : 自然数)
  证明: by
  rw [← pi_top (I := Set.univ)]; rw [lowerCentralSeries_pi_of_finite]

Depends on / 依赖: Set.univ, lowerCentralSeries_pi_of_finite, pi_top
-/
theorem Subgroup.top_lowerCentralSeries_pi_of_finite [Finite η] (n : Nat) :
    (⊤ : Subgroup (forall i, Gs i)).lowerCentralSeries n = Subgroup.pi Set.univ
      fun i => (⊤ : Subgroup (Gs i)).lowerCentralSeries n := by
  rw [← pi_top (I := Set.univ)]; rw [lowerCentralSeries_pi_of_finite]

/-- n-ary products of nilpotent groups are nilpotent. -/
@[to_additive /-- n-ary products of nilpotent groups are nilpotent. -/]
/--
Instance `Group.isNilpotent_pi` / 实例 `Group.isNilpotent_pi`

English:
instance Group.isNilpotent_pi
  signature: [Finite η] [forall i, IsNilpotent (Gs i)]
  body: by
  cases nonempty_fintype η
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨Finset.univ.sup fun i => Group.nilpotencyClass (Gs i), ?_⟩
  rw [top_lowerCentralSeries_pi_of_finite]; rw [pi_eq_bot_iff]
  intro i
  rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  exact Finset.le_sup (f := fun 

中文:
实例 群.isNilpotent_pi
  签名: [有限 η] [对任意 i, 是幂零 (Gs i)]
  定义体: by
  cases nonempty_fintype η
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨Finset.univ.sup fun i => Group.nilpotencyClass (Gs i), ?_⟩
  rw [top_lowerCentralSeries_pi_of_finite]; rw [pi_eq_bot_iff]
  intro i
  rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  exact Finset.le_sup (f := fun 

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_univ, Finset.univ.sup, Group.nilpotencyClass, le_sup, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, mem_univ, nilpotencyClass, nilpotent_iff_lowerCentralSeries, nonempty_fintype, pi_eq_bot_iff, top_lowerCentralSeries_pi_of_finite
-/
instance Group.isNilpotent_pi [Finite η] [forall i, IsNilpotent (Gs i)] : IsNilpotent (forall i, Gs i) := by
  cases nonempty_fintype η
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨Finset.univ.sup fun i => Group.nilpotencyClass (Gs i), ?_⟩
  rw [top_lowerCentralSeries_pi_of_finite]; rw [pi_eq_bot_iff]
  intro i
  rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  exact Finset.le_sup (f := fun i => Group.nilpotencyClass (Gs i)) (Finset.mem_univ i)

/-- The nilpotency class of an n-ary product is the sup of the nilpotency classes of the factors. -/
@[to_additive /-- The nilpotency class of an n-ary product is the sup of the nilpotency classes of
the factors. -/]
/--
theorem `Group.nilpotencyClass_pi` / 定理 `Group.nilpotencyClass_pi`

English:
theorem Group.nilpotencyClass_pi
  given: [Fintype η] [forall i, IsNilpotent (Gs i)]
  proof: by
  apply eq_of_forall_ge_iff
  intro k
  simp only [Finset.sup_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_pi_of_finite, pi_eq_bot_iff, Finset.mem_univ, true_imp_iff]

中文:
定理 群.nilpotencyClass_pi
  条件: [有限类型 η] [对任意 i, 是幂零 (Gs i)]
  证明: by
  apply eq_of_forall_ge_iff
  intro k
  simp only [Finset.sup_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_pi_of_finite, pi_eq_bot_iff, Finset.mem_univ, true_imp_iff]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sup_le_iff, eq_of_forall_ge_iff, lowerCentralSeries_eq_bot_iff_nilpotencyClass_le, mem_univ, pi_eq_bot_iff, sup_le_iff, top_lowerCentralSeries_pi_of_finite, true_imp_iff
-/
theorem Group.nilpotencyClass_pi [Fintype η] [forall i, IsNilpotent (Gs i)] :
    Group.nilpotencyClass (forall i, Gs i) = Finset.univ.sup fun i => Group.nilpotencyClass (Gs i) := by
  apply eq_of_forall_ge_iff
  intro k
  simp only [Finset.sup_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_pi_of_finite, pi_eq_bot_iff, Finset.mem_univ, true_imp_iff]

end FinitePi

/-- A nilpotent subgroup is solvable -/
instance (priority := 100) IsNilpotent.to_isSolvable [h : IsNilpotent G] : Group.IsSolvable G := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.1 h
  use n
  rw [eq_bot_iff]; rw [← hn]
  exact derived_le_lower_central n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSimpleGroup
  signature: G] [IsNilpotent G] : CommGroup G
  body: ⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩

中文:
实例 [是单群
  签名: G] [是幂零 G] : 交换群 G
  定义体: ⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩

Depends on / 依赖: IsSimpleGroup, IsSimpleGroup.comm_iff_isSolvable.mpr, comm_iff_isSolvable
-/
instance [IsSimpleGroup G] [IsNilpotent G] : CommGroup G :=
  ⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSimpleGroup
  signature: G] [IsNilpotent G] : IsCyclic G
  body: inferInstance

中文:
实例 [是单群
  签名: G] [是幂零 G] : 是循环 G
  定义体: inferInstance
-/
instance [IsSimpleGroup G] [IsNilpotent G] : IsCyclic G :=
  inferInstance

namespace Group

/--
lemma `nilpotencyClass_le_one_of_isSimple_of_isNilpotent` / 引理 `nilpotencyClass_le_one_of_isSimple_of_isNilpotent`

English:
lemma nilpotencyClass_le_one_of_isSimple_of_isNilpotent
  given: [IsSimpleGroup G] [IsNilpotent G]
  proof: CommGroup.nilpotencyClass_le_one

中文:
引理 nilpotencyClass_le_one_of_isSimple_of_isNilpotent
  条件: [是单群 G] [是幂零 G]
  证明: CommGroup.nilpotencyClass_le_one

Depends on / 依赖: CommGroup, CommGroup.nilpotencyClass_le_one, nilpotencyClass_le_one
-/
lemma nilpotencyClass_le_one_of_isSimple_of_isNilpotent [IsSimpleGroup G] [IsNilpotent G] :
    nilpotencyClass G <= 1 :=
  CommGroup.nilpotencyClass_le_one

/--
theorem `normalizerCondition_of_isNilpotent` / 定理 `normalizerCondition_of_isNilpotent`

English:
theorem normalizerCondition_of_isNilpotent
  given: [h : IsNilpotent G]
  statement: NormalizerCondition G
  proof: by
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw [normalizerCondition_iff_only_full_group_self_normalizing]
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro G _ _ H _
    exact @Subsingleton.elim _ Unique.instSubsingleton _

中文:
定理 normalizerCondition_of_isNilpotent
  条件: [h : 是幂零 G]
  结论: NormalizerCondition G
  证明: by
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw [normalizerCondition_iff_only_full_group_self_normalizing]
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro G _ _ H _
    exact @Subsingleton.elim _ Unique.instSubsingleton _
-/
theorem normalizerCondition_of_isNilpotent [h : IsNilpotent G] : NormalizerCondition G := by
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw [normalizerCondition_iff_only_full_group_self_normalizing]
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro G _ _ H _
    exact @Subsingleton.elim _ Unique.instSubsingleton _ _
  · intro G _ _ ih H hH
.trans (le_of_eq hH) have hch : center G <= H := Subgroup.center_le_normalizer H
    have hkh : (mk' (center G)).ker <= H := by simpa using hch
    have hsur : Function.Surjective (mk' (center G)) := Quot.mk_surjective
    let H' := H.map (mk' (center G))
    have hH' : normalizer H' = H' := by
      apply comap_injective hsur
      rw [comap_normalizer_eq_of_surjective _ hsur]; rw [comap_map_eq_self hkh]
      exact hH
    apply map_injective_of_ker_le (mk' (center G)) hkh le_top
    exact (ih H' hH').trans (symm (map_top_of_surjective _ hsur))

end Group

end WithGroup

section WithFiniteGroup

open Group Fintype

variable {G : Type*} [hG : Group G]

/--
theorem `IsPGroup.isNilpotent` / 定理 `IsPGroup.isNilpotent`

English:
theorem IsPGroup.isNilpotent
  given: [Finite G] {p : Nat} [hp : Fact (Nat.Prime p)] (h : IsPGroup p G)
  proof: by
  induction G using Finite.induction_subsingleton_or_nontrivial generalizing hG with
  | hbase => infer_instance
  | hstep G ih =>
    have hcq : Nat.card (G ⧸ center G) < Nat.card G := by
      rw [card_eq_card_quotient_mul_card_subgroup (center G)]
      apply lt_mul_of_one_lt_right Nat.card_po

中文:
定理 是p群.isNilpotent
  条件: [有限 G] {p : 自然数} [hp : Fact (自然数.素 p)] (h : 是p群 p G)
  证明: by
  induction G using Finite.induction_subsingleton_or_nontrivial generalizing hG with
  | hbase => infer_instance
  | hstep G ih =>
    have hcq : Nat.card (G ⧸ center G) < Nat.card G := by
      rw [card_eq_card_quotient_mul_card_subgroup (center G)]
      apply lt_mul_of_one_lt_right Nat.card_po

Depends on / 依赖: Finite, Finite.induction_subsingleton_or_nontrivial, IsNilpotent, Nat.card, Nat.card_pos, Subgroup, Subgroup.one_lt_card_iff_ne_bot, bot_lt_center, card_eq_card_quotient_mul_card_subgroup, card_pos, center, generalizing, h.bot_lt_center, h.to_quotient, induction_subsingleton_or_nontrivial, infer_instance, lt_mul_of_one_lt_right, ne_of_gt, of_quotient_center_nilpotent, one_lt_card_iff_ne_bot
-/
theorem IsPGroup.isNilpotent [Finite G] {p : Nat} [hp : Fact (Nat.Prime p)] (h : IsPGroup p G) :
    IsNilpotent G := by
  induction G using Finite.induction_subsingleton_or_nontrivial generalizing hG with
  | hbase => infer_instance
  | hstep G ih =>
    have hcq : Nat.card (G ⧸ center G) < Nat.card G := by
      rw [card_eq_card_quotient_mul_card_subgroup (center G)]
      apply lt_mul_of_one_lt_right Nat.card_pos
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr (ne_of_gt h.bot_lt_center)
    have hnq : IsNilpotent (G ⧸ center G) := ih _ hcq (h.to_quotient (center G))
    exact of_quotient_center_nilpotent hnq

variable [Finite G]

/--
theorem `Group.isNilpotent_of_product_of_sylow_group` / 定理 `Group.isNilpotent_of_product_of_sylow_group`

English:
theorem Group.isNilpotent_of_product_of_sylow_group
  proof: by
  let ps := (Nat.card G).primeFactors
  have : forall (p : ps) (P : Sylow p G), IsNilpotent (↑P : Subgroup G) := by
    intro p P
have : Fact (Nat.Prime ↑p) := Fact.mk Nat.prime_of_mem_primeFactors p.2
    exact P.isPGroup'.isNilpotent
  exact nilpotent_of_mulEquiv e

中文:
定理 群.isNilpotent_of_product_of_sylow_group
  证明: by
  let ps := (Nat.card G).primeFactors
  have : forall (p : ps) (P : Sylow p G), IsNilpotent (↑P : Subgroup G) := by
    intro p P
have : Fact (Nat.Prime ↑p) := Fact.mk Nat.prime_of_mem_primeFactors p.2
    exact P.isPGroup'.isNilpotent
  exact nilpotent_of_mulEquiv e

Depends on / 依赖: Fact.mk, IsNilpotent, Nat.Prime, Nat.card, Nat.prime_of_mem_primeFactors, P.isPGroup, Subgroup, isNilpotent, isPGroup, nilpotent_of_mulEquiv, primeFactors, prime_of_mem_primeFactors
-/
theorem Group.isNilpotent_of_product_of_sylow_group
    (e : (forall p : (Nat.card G).primeFactors, forall P : Sylow p G, (↑P : Subgroup G)) ≃* G) :
    IsNilpotent G := by
  let ps := (Nat.card G).primeFactors
  have : forall (p : ps) (P : Sylow p G), IsNilpotent (↑P : Subgroup G) := by
    intro p P
have : Fact (Nat.Prime ↑p) := Fact.mk Nat.prime_of_mem_primeFactors p.2
    exact P.isPGroup'.isNilpotent
  exact nilpotent_of_mulEquiv e

/--
theorem `Group.isNilpotent_of_finite_tfae` / 定理 `Group.isNilpotent_of_finite_tfae`

English:
theorem Group.isNilpotent_of_finite_tfae
  proof: by
  tfae_have 1 -> 2 := @normalizerCondition_of_isNilpotent _ _
  tfae_have 2 -> 3
  | h, H => NormalizerCondition.normal_of_coatom H h
  tfae_have 3 -> 4
  | h, p, _, P => Sylow.normal_of_all_max_subgroups_normal h _
  tfae_have 4 -> 5
  | h => Nonempty.intro (Sylow.directProductOfNormal fun {p hp

中文:
定理 群.isNilpotent_of_finite_tfae
  证明: by
  tfae_have 1 -> 2 := @normalizerCondition_of_isNilpotent _ _
  tfae_have 2 -> 3
  | h, H => NormalizerCondition.normal_of_coatom H h
  tfae_have 3 -> 4
  | h, p, _, P => Sylow.normal_of_all_max_subgroups_normal h _
  tfae_have 4 -> 5
  | h => Nonempty.intro (Sylow.directProductOfNormal fun {p hp

Depends on / 依赖: Nonempty, Nonempty.intro, NormalizerCondition, NormalizerCondition.normal_of_coatom, Sylow.directProductOfNormal, Sylow.normal_of_all_max_subgroups_normal, directProductOfNormal, isNilpotent_of_product_of_sylow_group, normal_of_all_max_subgroups_normal, normal_of_coatom, normalizerCondition_of_isNilpotent, tfae_finish, tfae_have
-/
theorem Group.isNilpotent_of_finite_tfae :
    List.TFAE
      [IsNilpotent G, NormalizerCondition G, forall H : Subgroup G, IsCoatom H -> H.Normal,
        forall (p : Nat) (_hp : Fact p.Prime) (P : Sylow p G), (↑P : Subgroup G).Normal,
        Nonempty
          ((forall p : (Nat.card G).primeFactors, forall P : Sylow p G, (↑P : Subgroup G)) ≃* G)] := by
  tfae_have 1 -> 2 := @normalizerCondition_of_isNilpotent _ _
  tfae_have 2 -> 3
  | h, H => NormalizerCondition.normal_of_coatom H h
  tfae_have 3 -> 4
  | h, p, _, P => Sylow.normal_of_all_max_subgroups_normal h _
  tfae_have 4 -> 5
  | h => Nonempty.intro (Sylow.directProductOfNormal fun {p hp hP} => h p hp hP)
  tfae_have 5 -> 1
  | ⟨e⟩ => isNilpotent_of_product_of_sylow_group e
  tfae_finish

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNilpotent
  signature: G] {p
  body: .mp ‹_› p ‹_› P isNilpotent_of_finite_tfae.out 0 3 rfl rfl

中文:
实例 [是幂零
  签名: G] {p
  定义体: .mp ‹_› p ‹_› P isNilpotent_of_finite_tfae.out 0 3 rfl rfl

Depends on / 依赖: isNilpotent_of_finite_tfae, isNilpotent_of_finite_tfae.out
-/
instance [IsNilpotent G] {p : Nat} [Fact p.Prime] {P : Sylow p G} : P.Normal :=
.mp ‹_› p ‹_› P isNilpotent_of_finite_tfae.out 0 3 rfl rfl

end WithFiniteGroup

open Group

@[deprecated (since := "2026-03-25")] alias upperCentralSeriesStep := upperCentralSeriesStep
@[deprecated (since := "2026-03-25")] alias mem_upperCentralSeriesStep := mem_upperCentralSeriesStep
@[deprecated (since := "2026-03-25")] alias upperCentralSeriesStep_eq_comap_center :=
  upperCentralSeriesStep_eq_comap_center
@[deprecated (since := "2026-03-25")] alias upperCentralSeriesAux := upperCentralSeriesAux
@[deprecated (since := "2026-03-25")] alias upperCentralSeries := upperCentralSeries
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_zero := upperCentralSeries_zero
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_one := upperCentralSeries_one
@[deprecated (since := "2026-03-25")] alias mem_upperCentralSeries_succ_iff :=
  mem_upperCentralSeries_succ_iff
@[deprecated (since := "2026-03-25")] alias comap_upperCentralSeries := comap_upperCentralSeries
@[deprecated (since := "2026-03-25")] alias IsAscendingCentralSeries := IsAscendingCentralSeries
@[deprecated (since := "2026-03-25")] alias IsDescendingCentralSeries := IsDescendingCentralSeries
@[deprecated (since := "2026-03-25")] alias ascending_central_series_le_upper :=
  ascending_central_series_le_upper
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_isAscendingCentralSeries :=
  upperCentralSeries_isAscendingCentralSeries
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_mono := upperCentralSeries_mono
@[deprecated (since := "2026-03-25")] alias nilpotent_iff_finite_ascending_central_series :=
  nilpotent_iff_finite_ascending_central_series
@[deprecated (since := "2026-03-25")] alias is_descending_rev_series_of_is_ascending :=
  is_descending_rev_series_of_is_ascending
@[deprecated (since := "2026-03-25")] alias is_ascending_rev_series_of_is_descending :=
  is_ascending_rev_series_of_is_descending
@[deprecated (since := "2026-03-25")] alias nilpotent_iff_finite_descending_central_series :=
  nilpotent_iff_finite_descending_central_series
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries := lowerCentralSeries
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_zero := lowerCentralSeries_zero
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_one := top_lowerCentralSeries_one
@[deprecated (since := "2026-03-25")] alias mem_lowerCentralSeries_succ_iff :=
  mem_lowerCentralSeries_succ_iff
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_succ := lowerCentralSeries_succ
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_antitone :=
  lowerCentralSeries_antitone
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_isDescendingCentralSeries :=
  lowerCentralSeries_isDescendingCentralSeries
@[deprecated (since := "2026-03-25")] alias descending_central_series_ge_lower :=
  descending_central_series_ge_lower
@[deprecated (since := "2026-03-25")] alias nilpotent_iff_lowerCentralSeries :=
  nilpotent_iff_lowerCentralSeries
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_nilpotencyClass :=
  upperCentralSeries_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_eq_top_iff_nilpotencyClass_le :=
  upperCentralSeries_eq_top_iff_nilpotencyClass_le
@[deprecated (since := "2026-03-25")]
alias least_ascending_central_series_length_eq_nilpotencyClass :=
  least_ascending_central_series_length_eq_nilpotencyClass
@[deprecated (since := "2026-03-25")]
alias least_descending_central_series_length_eq_nilpotencyClass :=
  least_descending_central_series_length_eq_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_length_eq_nilpotencyClass :=
  lowerCentralSeries_length_eq_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_nilpotencyClass :=
  lowerCentralSeries_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_eq_bot_iff_nilpotencyClass_le :=
  lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_map_subtype_le :=
  lowerCentralSeries_map_subtype_le
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.map := upperCentralSeries.map
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries.map := lowerCentralSeries.map
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_succ_eq_bot :=
  lowerCentralSeries_succ_eq_bot
@[deprecated (since := "2026-03-25")] alias isNilpotent_of_ker_le_center :=
  isNilpotent_of_ker_le_center
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_of_ker_le_center :=
  nilpotencyClass_le_of_ker_le_center
@[deprecated (since := "2026-03-25")] alias nilpotent_of_surjective := nilpotent_of_surjective
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_of_surjective :=
  nilpotencyClass_le_of_surjective
@[deprecated (since := "2026-03-25")] alias nilpotent_of_mulEquiv := nilpotent_of_mulEquiv
@[deprecated (since := "2026-03-25")] alias nilpotent_quotient_of_nilpotent :=
  nilpotent_quotient_of_nilpotent
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_quotient_le :=
  nilpotencyClass_quotient_le
@[deprecated (since := "2026-03-25")] alias comap_upperCentralSeries_quotient_center :=
  comap_upperCentralSeries_quotient_center
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_zero_iff_subsingleton :=
  nilpotencyClass_zero_iff_subsingleton
@[deprecated (since := "2026-03-25")] alias of_quotient_center_nilpotent :=
  of_quotient_center_nilpotent
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_quotient_center :=
  nilpotencyClass_quotient_center
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_eq_quotient_center_plus_one :=
  nilpotencyClass_eq_quotient_center_plus_one
@[deprecated (since := "2026-03-25")] alias nilpotent_center_quotient_ind :=
  nilpotent_center_quotient_ind
@[deprecated (since := "2026-03-25")] alias derived_le_lower_central := derived_le_lower_central
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.eq_ge_of_eq_succ :=
  upperCentralSeries.eq_ge_of_eq_succ
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.eq_ge_of_eq_gt :=
  upperCentralSeries.eq_ge_of_eq_gt
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.eq_top := upperCentralSeries.eq_top
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_of_upperCentralSeries_eq :=
  nilpotencyClass_le_of_upperCentralSeries_eq
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.StrictMonoOn :=
  upperCentralSeries.StrictMonoOn
@[deprecated (since := "2026-03-25")]
alias upperCentralSeries.card_image_eq_of_le_nilpotencyClass :=
  upperCentralSeries.card_image_eq_of_le_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_prod := lowerCentralSeries_prod
@[deprecated (since := "2026-03-25")] alias isNilpotent_prod := isNilpotent_prod
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_prod := nilpotencyClass_prod
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_pi_le := lowerCentralSeries_pi_le
@[deprecated (since := "2026-03-25")] alias isNilpotent_pi_of_bounded_class :=
  isNilpotent_pi_of_bounded_class
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_pi_of_finite :=
  lowerCentralSeries_pi_of_finite
@[deprecated (since := "2026-03-25")] alias isNilpotent_pi := isNilpotent_pi
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_pi := nilpotencyClass_pi
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_one_of_isSimple_of_isNilpotent :=
  nilpotencyClass_le_one_of_isSimple_of_isNilpotent
@[deprecated (since := "2026-03-25")] alias normalizerCondition_of_isNilpotent :=
  normalizerCondition_of_isNilpotent
@[deprecated (since := "2026-03-25")] alias isNilpotent_of_product_of_sylow_group :=
  isNilpotent_of_product_of_sylow_group
@[deprecated (since := "2026-03-25")] alias isNilpotent_of_finite_tfae := isNilpotent_of_finite_tfae
