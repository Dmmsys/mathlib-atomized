/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centralizers in semigroups, as subsemigroups.

## Main definitions

* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

variable {M : Type*} {S T : Set M}
namespace Subsemigroup

section

variable [Semigroup M] (S)

/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive /-- The centralizer of a subset of an additive semigroup. -/]
/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: : Subsemigroup M where
  body: S.centralizer
  mul_mem' := Set.mul_mem_centralizer

@[to_additive (attr := simp, norm_cast)]

中文:
定义 centralizer
  签名: : Subsemigroup M where
  定义体: S.centralizer
  mul_mem' := Set.mul_mem_centralizer

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: S.centralizer, centralizer
-/
def centralizer : Subsemigroup M where
  carrier := S.centralizer
  mul_mem' := Set.mul_mem_centralizer

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_centralizer` / 定理 `coe_centralizer`

English:
theorem coe_centralizer
  statement: ↑(centralizer S) = S.centralizer
  proof: rfl

中文:
定理 coe_centralizer
  结论: ↑(centralizer S) = S.centralizer
  证明: rfl
-/
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl

variable {S}

@[to_additive]
/--
theorem `mem_centralizer_iff` / 定理 `mem_centralizer_iff`

English:
theorem mem_centralizer_iff
  given: {z : M}
  statement: z in centralizer S ↔ forall g in S, g * z = z * g
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_centralizer_iff
  条件: {z : M}
  结论: z in centralizer S ↔ 对任意 g in S, g * z = z * g
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_centralizer_iff {z : M} : z in centralizer S ↔ forall g in S, g * z = z * g :=
  Iff.rfl

@[to_additive]
/--
Instance `decidableMemCentralizer` / 实例 `decidableMemCentralizer`

English:
instance decidableMemCentralizer
  signature: (a) [Decidable <| forall b in S, b * a = a * b]
  body: decidable_of_iff' _ mem_centralizer_iff

@[to_additive]

中文:
实例 decidableMemCentralizer
  签名: (a) [Decidable <| 对任意 b in S, b * a = a * b]
  定义体: decidable_of_iff' _ mem_centralizer_iff

@[to_additive]

Depends on / 依赖: decidable_of_iff, mem_centralizer_iff
-/
instance decidableMemCentralizer (a) [Decidable <| forall b in S, b * a = a * b] :
    Decidable (a in centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff

@[to_additive]
/--
theorem `center_le_centralizer` / 定理 `center_le_centralizer`

English:
theorem center_le_centralizer
  given: (S)
  statement: center M <= centralizer S
  proof: S.center_subset_centralizer

@[to_additive]

中文:
定理 center_le_centralizer
  条件: (S)
  结论: center M <= centralizer S
  证明: S.center_subset_centralizer

@[to_additive]

Depends on / 依赖: S.center_subset_centralizer, center_subset_centralizer
-/
theorem center_le_centralizer (S) : center M <= centralizer S :=
  S.center_subset_centralizer

@[to_additive]
/--
theorem `centralizer_le` / 定理 `centralizer_le`

English:
theorem centralizer_le
  given: (h : S subseteq T)
  statement: centralizer T <= centralizer S
  proof: Set.centralizer_subset h

@[to_additive (attr := simp)]

中文:
定理 centralizer_le
  条件: (h : S subseteq T)
  结论: centralizer T <= centralizer S
  证明: Set.centralizer_subset h

@[to_additive (attr := simp)]

Depends on / 依赖: Set.centralizer_subset, centralizer_subset
-/
theorem centralizer_le (h : S subseteq T) : centralizer T <= centralizer S :=
  Set.centralizer_subset h

@[to_additive (attr := simp)]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  given: {s : Set M}
  statement: centralizer s = ⊤ ↔ s subseteq center M
  proof: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

中文:
定理 centralizer_eq_top_iff_subset
  条件: {s : Set M}
  结论: centralizer s = ⊤ ↔ s subseteq center M
  证明: SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

Depends on / 依赖: Set.centralizer_eq_top_iff_subset, SetLike, SetLike.ext, _iff, _iff.trans, centralizer_eq_top_iff_subset
-/
theorem centralizer_eq_top_iff_subset {s : Set M} : centralizer s = ⊤ ↔ s subseteq center M :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

variable (M)
@[to_additive (attr := simp)]
/--
theorem `centralizer_univ` / 定理 `centralizer_univ`

English:
theorem centralizer_univ
  statement: centralizer Set.univ = center M
  proof: SetLike.ext' (Set.centralizer_univ M)

中文:
定理 centralizer_univ
  结论: centralizer Set.univ = center M
  证明: SetLike.ext' (Set.centralizer_univ M)

Depends on / 依赖: Set.centralizer_univ, SetLike, SetLike.ext, centralizer_univ
-/
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)

variable {M} in
@[to_additive]
/--
lemma `closure_le_centralizer_centralizer` / 引理 `closure_le_centralizer_centralizer`

English:
lemma closure_le_centralizer_centralizer
  given: (s : Set M)
  proof: closure_le.mpr Set.subset_centralizer_centralizer

中文:
引理 closure_le_centralizer_centralizer
  条件: (s : Set M)
  证明: closure_le.mpr Set.subset_centralizer_centralizer

Depends on / 依赖: Set.subset_centralizer_centralizer, closure_le, closure_le.mpr, subset_centralizer_centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set M) :
    closure s <= centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is commutative. -/
@[to_additive
/-- If all the elements of a set `s` commute, then `closure s` is commutative. -/]
/--
theorem `isMulCommutative_closure` / 定理 `isMulCommutative_closure`

English:
theorem isMulCommutative_closure
  given: {s : Set M} (hcomm : forall a in s, forall b in s, a * b = b * a)
  proof: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

中文:
定理 isMulCommutative_closure
  条件: {s : Set M} (hcomm : 对任意 a in s, 对任意 b in s, a * b = b * a)
  证明: have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

Depends on / 依赖: Set.centralizer_centralizer_comm_of_comm, centralizer_centralizer_comm_of_comm, closure_le_centralizer_centralizer, of_setLike_mul_comm
-/
theorem isMulCommutative_closure {s : Set M} (hcomm : forall a in s, forall b in s, a * b = b * a) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ =>
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative semigroup. -/
@[to_additive (attr := deprecated isMulCommutative_closure (since := "2026-03-09"))
/-- If all the elements of a set `s` commute, then `closure s` forms an additive
commutative semigroup. -/]
/--
Definition of `closureCommSemigroupOfComm` / `closureCommSemigroupOfComm` 的定义

English:
abbreviation closureCommSemigroupOfComm
  signature: {s : Set M} (hcomm : forall a in s, forall b in s, a * b = b * a)
  body: haveI := isMulCommutative_closure M hcomm
  inferInstance

@[to_additive]

中文:
缩写 closureCommSemigroupOfComm
  签名: {s : Set M} (hcomm : 对任意 a in s, 对任意 b in s, a * b = b * a)
  定义体: haveI := isMulCommutative_closure M hcomm
  inferInstance

@[to_additive]

Depends on / 依赖: isMulCommutative_closure
-/
abbrev closureCommSemigroupOfComm {s : Set M} (hcomm : forall a in s, forall b in s, a * b = b * a) :
    CommSemigroup (closure s) :=
  haveI := isMulCommutative_closure M hcomm
  inferInstance

@[to_additive]
/--
Instance `instIsMulCommutative_closure` / 实例 `instIsMulCommutative_closure`

English:
instance instIsMulCommutative_closure
  signature: {S : Type*} [SetLike S M] [MulMemClass S M] (s : S)
  body: isMulCommutative_closure _ fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

中文:
实例 instIsMulCommutative_closure
  签名: {S : 类型} [SetLike S M] [MulMemClass S M] (s : S)
  定义体: isMulCommutative_closure _ fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

Depends on / 依赖: isMulCommutative_closure, setLike_mul_comm
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S M] [MulMemClass S M] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set M)) :=
  isMulCommutative_closure _ fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

end

end Subsemigroup
