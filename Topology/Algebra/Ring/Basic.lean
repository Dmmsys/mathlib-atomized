/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.GroupTopology

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `Subring.topologicalClosure`/`Subsemiring.topologicalClosure`: the topological closure of a
  `Subring`/`Subsemiring` is itself a `Sub(semi)ring`.
- The product of two topological (semi)rings is a topological (semi)ring.
- The indexed product of topological (semi)rings is a topological (semi)ring.
-/

@[expose] public section

assert_not_exists Cardinal

open Set Filter TopologicalSpace Function Topology Filter

section IsTopologicalSemiring

variable (R : Type*)

/--
Definition of `IsTopologicalSemiring` / `IsTopologicalSemiring` 的定义

English:
class IsTopologicalSemiring
  parameters: [TopologicalSpace R] [NonUnitalNonAssocSemiring R]
  extends: ContinuousAdd R, ContinuousMul R
  (no additional axioms)

中文:
类 是TopologicalSemiring
  参数: [拓扑空间 R] [非幺非结合半环 R]
  继承: 连续加法 R, 连续乘法 R
  (无附加公理)
-/
class IsTopologicalSemiring [TopologicalSpace R] [NonUnitalNonAssocSemiring R] : Prop
    extends ContinuousAdd R, ContinuousMul R

/--
Definition of `IsTopologicalRing` / `IsTopologicalRing` 的定义

English:
class IsTopologicalRing
  parameters: [TopologicalSpace R] [NonUnitalNonAssocRing R]
  extends: IsTopologicalSemiring R, ContinuousNeg R
  (no additional axioms)

中文:
类 是拓扑环
  参数: [拓扑空间 R] [非幺非结合环 R]
  继承: 是TopologicalSemiring R, 连续取负 R
  (无附加公理)
-/
class IsTopologicalRing [TopologicalSpace R] [NonUnitalNonAssocRing R] : Prop
    extends IsTopologicalSemiring R, ContinuousNeg R

/--
Definition of `IsSemitopologicalSemiring` / `IsSemitopologicalSemiring` 的定义

English:
class IsSemitopologicalSemiring
  parameters: (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocSemiring R]
  extends: ContinuousAdd R, SeparatelyContinuousMul R
  (no additional axioms)

中文:
类 是SemitopologicalSemiring
  参数: (R : 类型) [拓扑空间 R] [非幺非结合半环 R]
  继承: 连续加法 R, SeparatelyContinuousMul R
  (无附加公理)
-/
class IsSemitopologicalSemiring (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocSemiring R]
  extends ContinuousAdd R, SeparatelyContinuousMul R

/--
Definition of `IsSemitopologicalRing` / `IsSemitopologicalRing` 的定义

English:
class IsSemitopologicalRing
  parameters: (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocRing R]
  extends: IsSemitopologicalSemiring R, ContinuousNeg R
  (no additional axioms)

中文:
类 是Semitopological环
  参数: (R : 类型) [拓扑空间 R] [非幺非结合环 R]
  继承: 是SemitopologicalSemiring R, 连续取负 R
  (无附加公理)
-/
class IsSemitopologicalRing (R : Type*) [TopologicalSpace R] [NonUnitalNonAssocRing R]
  extends IsSemitopologicalSemiring R, ContinuousNeg R

variable {R}

/--
theorem `IsSemitopologicalSemiring.continuousNeg_of_mul` / 定理 `IsSemitopologicalSemiring.continuousNeg_of_mul`

English:
theorem IsSemitopologicalSemiring.continuousNeg_of_mul
  statement: [TopologicalSpace R] [NonAssocRing R]
  proof: by simpa using continuous_id.const_mul (-1 : R)

@[deprecated (since := "2026-03-13")] alias IsTopologicalSemiring.continuousNeg_of_mul :=
  IsSemitopologicalSemiring.continuousNeg_of_mul

中文:
定理 是SemitopologicalSemiring.continuousNeg_of_mul
  结论: [拓扑空间 R] [非结合环 R]
  证明: by simpa using continuous_id.const_mul (-1 : R)

@[deprecated (since := "2026-03-13")] alias IsTopologicalSemiring.continuousNeg_of_mul :=
  IsSemitopologicalSemiring.continuousNeg_of_mul

Depends on / 依赖: const_mul, continuous_id, continuous_id.const_mul
-/
theorem IsSemitopologicalSemiring.continuousNeg_of_mul [TopologicalSpace R] [NonAssocRing R]
    [SeparatelyContinuousMul R] : ContinuousNeg R where
  continuous_neg := by simpa using continuous_id.const_mul (-1 : R)

@[deprecated (since := "2026-03-13")] alias IsTopologicalSemiring.continuousNeg_of_mul :=
  IsSemitopologicalSemiring.continuousNeg_of_mul

/--
theorem `IsSemitopologicalSemiring.toIsSemitopologicalRing` / 定理 `IsSemitopologicalSemiring.toIsSemitopologicalRing`

English:
theorem IsSemitopologicalSemiring.toIsSemitopologicalRing
  statement: [TopologicalSpace R] [NonAssocRing R]
  proof: IsSemitopologicalSemiring.continuousNeg_of_mul

中文:
定理 是SemitopologicalSemiring.toIsSemitopologicalRing
  结论: [拓扑空间 R] [非结合环 R]
  证明: IsSemitopologicalSemiring.continuousNeg_of_mul

Depends on / 依赖: IsSemitopologicalSemiring, IsSemitopologicalSemiring.continuousNeg_of_mul, continuousNeg_of_mul
-/
theorem IsSemitopologicalSemiring.toIsSemitopologicalRing [TopologicalSpace R] [NonAssocRing R]
    (_ : IsSemitopologicalSemiring R) : IsSemitopologicalRing R where
  toContinuousNeg := IsSemitopologicalSemiring.continuousNeg_of_mul

/--
theorem `IsTopologicalSemiring.toIsTopologicalRing` / 定理 `IsTopologicalSemiring.toIsTopologicalRing`

English:
theorem IsTopologicalSemiring.toIsTopologicalRing
  statement: [TopologicalSpace R] [NonAssocRing R]
  proof: IsSemitopologicalSemiring.continuousNeg_of_mul

中文:
定理 是TopologicalSemiring.toIsTopologicalRing
  结论: [拓扑空间 R] [非结合环 R]
  证明: IsSemitopologicalSemiring.continuousNeg_of_mul

Depends on / 依赖: IsSemitopologicalSemiring, IsSemitopologicalSemiring.continuousNeg_of_mul, continuousNeg_of_mul
-/
theorem IsTopologicalSemiring.toIsTopologicalRing [TopologicalSpace R] [NonAssocRing R]
    (_ : IsTopologicalSemiring R) : IsTopologicalRing R where
  toContinuousNeg := IsSemitopologicalSemiring.continuousNeg_of_mul

instance (priority := 100) IsTopologicalRing.toIsSemitopologicalRing (R : Type*)
    [TopologicalSpace R] [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsSemitopologicalRing R where

instance (priority := 100) IsTopologicalSemiring.toIsSemitopologicalSemiring (R : Type*)
    [TopologicalSpace R] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsSemitopologicalSemiring R where

-- See note [lower instance priority]
instance (priority := 100) IsSemitopologicalRing.toIsTopologicalAddGroup [NonUnitalNonAssocRing R]
    [TopologicalSpace R] [IsSemitopologicalRing R] : IsTopologicalAddGroup R := ⟨⟩

-- kept just to avoid breaking manual usage of the previous instance
/--
theorem `IsTopologicalRing.to_topologicalAddGroup` / 定理 `IsTopologicalRing.to_topologicalAddGroup`

English:
theorem IsTopologicalRing.to_topologicalAddGroup
  statement: [NonUnitalNonAssocRing R]
  proof: ⟨⟩

中文:
定理 是拓扑环.to_topologicalAddGroup
  结论: [非幺非结合环 R]
  证明: ⟨⟩
-/
theorem IsTopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : IsTopologicalAddGroup R := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [DiscreteTopology R] : IsTopologicalSemiring R := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace R]
    [NonUnitalNonAssocRing R] [DiscreteTopology R] : IsTopologicalRing R := ⟨⟩

section

namespace NonUnitalSubsemiring

variable [TopologicalSpace R] [NonUnitalSemiring R]

/--
Instance `instIsSemitopologicalSemiring` / 实例 `instIsSemitopologicalSemiring`

English:
instance instIsSemitopologicalSemiring
  signature: [IsSemitopologicalSemiring R] (S : NonUnitalSubsemiring R)
  body: { S.toSubsemigroup.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }

中文:
实例 instIsSemitopologicalSemiring
  签名: [是SemitopologicalSemiring R] (S : NonUnital子半环 R)
  定义体: { S.toSubsemigroup.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }

Depends on / 依赖: S.toAddSubmonoid.continuousAdd, S.toSubsemigroup.separatelyContinuousMul, continuousAdd, separatelyContinuousMul, toAddSubmonoid, toSubsemigroup
-/
instance instIsSemitopologicalSemiring [IsSemitopologicalSemiring R] (S : NonUnitalSubsemiring R) :
    IsSemitopologicalSemiring S :=
  { S.toSubsemigroup.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }

/--
Instance `instIsTopologicalSemiring` / 实例 `instIsTopologicalSemiring`

English:
instance instIsTopologicalSemiring
  signature: [IsTopologicalSemiring R] (S : NonUnitalSubsemiring R)
  body: { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

中文:
实例 instIsTopologicalSemiring
  签名: [是TopologicalSemiring R] (S : NonUnital子半环 R)
  定义体: { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

Depends on / 依赖: S.toAddSubmonoid.continuousAdd, S.toSubsemigroup.continuousMul, continuousAdd, continuousMul, toAddSubmonoid, toSubsemigroup
-/
instance instIsTopologicalSemiring [IsTopologicalSemiring R] (S : NonUnitalSubsemiring R) :
    IsTopologicalSemiring S :=
  { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

variable [IsSemitopologicalSemiring R]

/--
Definition of `topologicalClosure` / `topologicalClosure` 的定义

English:
definition topologicalClosure
  signature: (s : NonUnitalSubsemiring R)
  body: { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]

中文:
定义 topologicalClosure
  签名: (s : NonUnital子半环 R)
  定义体: { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]

Depends on / 依赖: _root_, _root_.closure, carrier, closure, s.toAddSubmonoid.topologicalClosure, s.toSubsemigroup.topologicalClosure, toAddSubmonoid, toSubsemigroup, topologicalClosure
-/
def topologicalClosure (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring R :=
  { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]
/--
theorem `topologicalClosure_coe` / 定理 `topologicalClosure_coe`

English:
theorem topologicalClosure_coe
  given: (s : NonUnitalSubsemiring R)
  proof: rfl

中文:
定理 topologicalClosure_coe
  条件: (s : NonUnital子半环 R)
  证明: rfl
-/
theorem topologicalClosure_coe (s : NonUnitalSubsemiring R) :
    (s.topologicalClosure : Set R) = _root_.closure (s : Set R) :=
  rfl

/--
theorem `le_topologicalClosure` / 定理 `le_topologicalClosure`

English:
theorem le_topologicalClosure
  given: (s : NonUnitalSubsemiring R)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

中文:
定理 le_topologicalClosure
  条件: (s : NonUnital子半环 R)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem le_topologicalClosure (s : NonUnitalSubsemiring R) : s <= s.topologicalClosure :=
  _root_.subset_closure

/--
theorem `isClosed_topologicalClosure` / 定理 `isClosed_topologicalClosure`

English:
theorem isClosed_topologicalClosure
  given: (s : NonUnitalSubsemiring R)
  proof: isClosed_closure

中文:
定理 isClosed_topologicalClosure
  条件: (s : NonUnital子半环 R)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem isClosed_topologicalClosure (s : NonUnitalSubsemiring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

/--
theorem `topologicalClosure_minimal` / 定理 `topologicalClosure_minimal`

English:
theorem topologicalClosure_minimal
  statement: (s : NonUnitalSubsemiring R) {t : NonUnitalSubsemiring R}
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 topologicalClosure_minimal
  结论: (s : NonUnital子半环 R) {t : NonUnital子半环 R}
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem topologicalClosure_minimal (s : NonUnitalSubsemiring R) {t : NonUnitalSubsemiring R}
    (h : s <= t) (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `topologicalClosure_mono` / 定理 `topologicalClosure_mono`

English:
theorem topologicalClosure_mono
  given: {s t : NonUnitalSubsemiring R} (h : s <= t)
  proof: _root_.closure_mono h

中文:
定理 topologicalClosure_mono
  条件: {s t : NonUnital子半环 R} (h : s <= t)
  证明: _root_.closure_mono h

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem topologicalClosure_mono {s t : NonUnitalSubsemiring R} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

/--
Definition of `nonUnitalCommSemiringTopologicalClosure` / `nonUnitalCommSemiringTopologicalClosure` 的定义

English:
abbreviation nonUnitalCommSemiringTopologicalClosure
  signature: [T2Space R] (s : NonUnitalSubsemiring R)
  body: { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

中文:
缩写 nonUnitalCommSemiringTopologicalClosure
  签名: [T2空间 R] (s : NonUnital子半环 R)
  定义体: { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

Depends on / 依赖: NonUnitalSubsemiringClass, NonUnitalSubsemiringClass.toNonUnitalSemiring, commSemigroupTopologicalClosure, s.toSubsemigroup.commSemigroupTopologicalClosure, s.topologicalClosure, toNonUnitalSemiring, toSubsemigroup, topologicalClosure
-/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space R] (s : NonUnitalSubsemiring R)
    (hs : forall x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubsemiring

variable [TopologicalSpace R] [Semiring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalSemiring
  signature: R] : IsTopologicalSemiring (ULift R) where

中文:
实例 [是TopologicalSemiring
  签名: R] : 是TopologicalSemiring (类型层提升 R) where
-/
instance [IsTopologicalSemiring R] : IsTopologicalSemiring (ULift R) where

namespace Subsemiring

/--
Instance `semitopologicalSemiring` / 实例 `semitopologicalSemiring`

English:
instance semitopologicalSemiring
  signature: [IsSemitopologicalSemiring R] (S : Subsemiring R)
  body: { S.toSubmonoid.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }

中文:
实例 semitopologicalSemiring
  签名: [是SemitopologicalSemiring R] (S : 子半环 R)
  定义体: { S.toSubmonoid.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }

Depends on / 依赖: S.toAddSubmonoid.continuousAdd, S.toSubmonoid.separatelyContinuousMul, continuousAdd, separatelyContinuousMul, toAddSubmonoid, toSubmonoid
-/
instance semitopologicalSemiring [IsSemitopologicalSemiring R] (S : Subsemiring R) :
    IsSemitopologicalSemiring S :=
  { S.toSubmonoid.separatelyContinuousMul, S.toAddSubmonoid.continuousAdd with }

/--
Instance `topologicalSemiring` / 实例 `topologicalSemiring`

English:
instance topologicalSemiring
  signature: [IsTopologicalSemiring R] (S : Subsemiring R)
  body: { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

中文:
实例 topologicalSemiring
  签名: [是TopologicalSemiring R] (S : 子半环 R)
  定义体: { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

Depends on / 依赖: S.toAddSubmonoid.continuousAdd, S.toSubmonoid.continuousMul, continuousAdd, continuousMul, toAddSubmonoid, toSubmonoid
-/
instance topologicalSemiring [IsTopologicalSemiring R] (S : Subsemiring R) :
    IsTopologicalSemiring S :=
  { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

/--
Instance `continuousSMul` / 实例 `continuousSMul`

English:
instance continuousSMul
  signature: (s : Subsemiring R) (X) [TopologicalSpace X] [MulAction R X]
  body: Submonoid.continuousSMul

中文:
实例 continuousSMul
  签名: (s : 子半环 R) (X) [拓扑空间 X] [乘法作用 R X]
  定义体: Submonoid.continuousSMul

Depends on / 依赖: Submonoid, Submonoid.continuousSMul, continuousSMul
-/
instance continuousSMul (s : Subsemiring R) (X) [TopologicalSpace X] [MulAction R X]
    [ContinuousSMul R X] : ContinuousSMul s X :=
  Submonoid.continuousSMul

end Subsemiring

variable [IsSemitopologicalSemiring R]

/--
Definition of `Subsemiring.topologicalClosure` / `Subsemiring.topologicalClosure` 的定义

English:
definition Subsemiring.topologicalClosure
  signature: (s : Subsemiring R)
  body: { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]

中文:
定义 子半环.topologicalClosure
  签名: (s : 子半环 R)
  定义体: { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]

Depends on / 依赖: _root_, _root_.closure, carrier, closure, s.toAddSubmonoid.topologicalClosure, s.toSubmonoid.topologicalClosure, toAddSubmonoid, toSubmonoid, topologicalClosure
-/
def Subsemiring.topologicalClosure (s : Subsemiring R) : Subsemiring R :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set R) }

@[simp]
/--
theorem `Subsemiring.topologicalClosure_coe` / 定理 `Subsemiring.topologicalClosure_coe`

English:
theorem Subsemiring.topologicalClosure_coe
  given: (s : Subsemiring R)
  proof: rfl

中文:
定理 子半环.topologicalClosure_coe
  条件: (s : 子半环 R)
  证明: rfl
-/
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring R) :
    (s.topologicalClosure : Set R) = _root_.closure (s : Set R) :=
  rfl

/--
theorem `Subsemiring.le_topologicalClosure` / 定理 `Subsemiring.le_topologicalClosure`

English:
theorem Subsemiring.le_topologicalClosure
  given: (s : Subsemiring R)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

中文:
定理 子半环.le_topologicalClosure
  条件: (s : 子半环 R)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem Subsemiring.le_topologicalClosure (s : Subsemiring R) : s <= s.topologicalClosure :=
  _root_.subset_closure

/--
theorem `Subsemiring.isClosed_topologicalClosure` / 定理 `Subsemiring.isClosed_topologicalClosure`

English:
theorem Subsemiring.isClosed_topologicalClosure
  given: (s : Subsemiring R)
  proof: isClosed_closure

中文:
定理 子半环.isClosed_topologicalClosure
  条件: (s : 子半环 R)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

/--
theorem `Subsemiring.topologicalClosure_minimal` / 定理 `Subsemiring.topologicalClosure_minimal`

English:
theorem Subsemiring.topologicalClosure_minimal
  statement: (s : Subsemiring R) {t : Subsemiring R} (h : s <= t)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 子半环.topologicalClosure_minimal
  结论: (s : 子半环 R) {t : 子半环 R} (h : s <= t)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring R) {t : Subsemiring R} (h : s <= t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `Subsemiring.topologicalClosure_mono` / 定理 `Subsemiring.topologicalClosure_mono`

English:
theorem Subsemiring.topologicalClosure_mono
  given: {s t : Subsemiring R} (h : s <= t)
  proof: _root_.closure_mono h

中文:
定理 子半环.topologicalClosure_mono
  条件: {s t : 子半环 R} (h : s <= t)
  证明: _root_.closure_mono h

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem Subsemiring.topologicalClosure_mono {s t : Subsemiring R} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

/--
Definition of `Subsemiring.commSemiringTopologicalClosure` / `Subsemiring.commSemiringTopologicalClosure` 的定义

English:
abbreviation Subsemiring.commSemiringTopologicalClosure
  signature: [T2Space R] (s : Subsemiring R)
  body: { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

中文:
缩写 子半环.commSemiringTopologicalClosure
  签名: [T2空间 R] (s : 子半环 R)
  定义体: { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

Depends on / 依赖: commMonoidTopologicalClosure, s.toSubmonoid.commMonoidTopologicalClosure, s.topologicalClosure.toSemiring, toSemiring, toSubmonoid, topologicalClosure
-/
abbrev Subsemiring.commSemiringTopologicalClosure [T2Space R] (s : Subsemiring R)
    (hs : forall x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end

section

variable {S : Type*} [TopologicalSpace R] [TopologicalSpace S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [NonUnitalNonAssocSemiring S] [IsTopologicalSemiring R]

中文:
实例 [非幺非结合半环
  签名: R] [非幺非结合半环 S] [是TopologicalSemiring R]
-/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [IsTopologicalSemiring R]
    [IsTopologicalSemiring S] : IsTopologicalSemiring (R × S) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [NonUnitalNonAssocRing S] [IsTopologicalRing R]

中文:
实例 [非幺非结合环
  签名: R] [非幺非结合环 S] [是拓扑环 R]
-/
instance [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [IsTopologicalRing R]
    [IsTopologicalRing S] : IsTopologicalRing (R × S) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [NonUnitalNonAssocSemiring S] [IsSemitopologicalSemiring R]

中文:
实例 [非幺非结合半环
  签名: R] [非幺非结合半环 S] [是SemitopologicalSemiring R]
-/
instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [IsSemitopologicalSemiring R]
    [IsSemitopologicalSemiring S] : IsSemitopologicalSemiring (R × S) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [NonUnitalNonAssocRing S] [IsSemitopologicalRing R]

中文:
实例 [非幺非结合环
  签名: R] [非幺非结合环 S] [是Semitopological环 R]
-/
instance [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [IsSemitopologicalRing R]
    [IsSemitopologicalRing S] : IsSemitopologicalRing (R × S) where

end

/--
Instance `Pi.instIsTopologicalSemiring` / 实例 `Pi.instIsTopologicalSemiring`

English:
instance Pi.instIsTopologicalSemiring
  signature: {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]

中文:
实例 依赖函数类型.instIsTopologicalSemiring
  签名: {ι : 类型} {R : ι -> 类型} [对任意 i, 拓扑空间 (R i)]
-/
instance Pi.instIsTopologicalSemiring {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]
    [forall i, NonUnitalNonAssocSemiring (R i)] [forall i, IsTopologicalSemiring (R i)] :
    IsTopologicalSemiring (forall i, R i) where

/--
Instance `Pi.instIsTopologicalRing` / 实例 `Pi.instIsTopologicalRing`

English:
instance Pi.instIsTopologicalRing
  signature: {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]
  body: ⟨⟩

中文:
实例 依赖函数类型.instIsTopologicalRing
  签名: {ι : 类型} {R : ι -> 类型} [对任意 i, 拓扑空间 (R i)]
  定义体: ⟨⟩
-/
instance Pi.instIsTopologicalRing {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]
    [forall i, NonUnitalNonAssocRing (R i)] [forall i, IsTopologicalRing (R i)] :
    IsTopologicalRing (forall i, R i) := ⟨⟩

/--
Instance `Pi.instIsSemitopologicalSemiring` / 实例 `Pi.instIsSemitopologicalSemiring`

English:
instance Pi.instIsSemitopologicalSemiring
  signature: {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]

中文:
实例 依赖函数类型.instIsSemitopologicalSemiring
  签名: {ι : 类型} {R : ι -> 类型} [对任意 i, 拓扑空间 (R i)]
-/
instance Pi.instIsSemitopologicalSemiring {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]
    [forall i, NonUnitalNonAssocSemiring (R i)] [forall i, IsSemitopologicalSemiring (R i)] :
    IsSemitopologicalSemiring (forall i, R i) where

/--
Instance `Pi.instIsSemitopologicalRing` / 实例 `Pi.instIsSemitopologicalRing`

English:
instance Pi.instIsSemitopologicalRing
  signature: {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]
  body: ⟨⟩

中文:
实例 依赖函数类型.instIsSemitopologicalRing
  签名: {ι : 类型} {R : ι -> 类型} [对任意 i, 拓扑空间 (R i)]
  定义体: ⟨⟩
-/
instance Pi.instIsSemitopologicalRing {ι : Type*} {R : ι -> Type*} [forall i, TopologicalSpace (R i)]
    [forall i, NonUnitalNonAssocRing (R i)] [forall i, IsSemitopologicalRing (R i)] :
    IsSemitopologicalRing (forall i, R i) := ⟨⟩

section MulOpposite

open MulOpposite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [ContinuousAdd R] :
  body: continuousAdd_induced opAddEquiv.symm

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [连续加法 R] :
  定义体: continuousAdd_induced opAddEquiv.symm

Depends on / 依赖: continuousAdd_induced, opAddEquiv, opAddEquiv.symm
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousAdd R] :
    ContinuousAdd Rᵐᵒᵖ :=
  continuousAdd_induced opAddEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [IsSemitopologicalSemiring R] :
  body: ⟨⟩

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [是SemitopologicalSemiring R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsSemitopologicalSemiring R] :
    IsSemitopologicalSemiring Rᵐᵒᵖ := ⟨⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [IsTopologicalSemiring R] :
  body: ⟨⟩

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [是TopologicalSemiring R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring Rᵐᵒᵖ := ⟨⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [TopologicalSpace R] [ContinuousNeg R] : ContinuousNeg Rᵐᵒᵖ
  body: opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl

中文:
实例 [非幺非结合环
  签名: R] [拓扑空间 R] [连续取负 R] : 连续取负 Rᵐᵒᵖ
  定义体: opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [ContinuousNeg R] : ContinuousNeg Rᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [TopologicalSpace R] [IsTopologicalRing R] :
  body: ⟨⟩

中文:
实例 [非幺非结合环
  签名: R] [拓扑空间 R] [是拓扑环 R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing Rᵐᵒᵖ := ⟨⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [TopologicalSpace R] [IsSemitopologicalRing R] :
  body: ⟨⟩

中文:
实例 [非幺非结合环
  签名: R] [拓扑空间 R] [是Semitopological环 R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsSemitopologicalRing R] :
    IsSemitopologicalRing Rᵐᵒᵖ := ⟨⟩

end MulOpposite

section AddOpposite

open AddOpposite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [SeparatelyContinuousMul R] :
  body: separatelyContinuousMul_induced opMulEquiv.symm

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [SeparatelyContinuousMul R] :
  定义体: separatelyContinuousMul_induced opMulEquiv.symm

Depends on / 依赖: opMulEquiv, opMulEquiv.symm, separatelyContinuousMul_induced
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [SeparatelyContinuousMul R] :
    SeparatelyContinuousMul Rᵃᵒᵖ :=
  separatelyContinuousMul_induced opMulEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [IsSemitopologicalSemiring R] :
  body: ⟨⟩

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [是SemitopologicalSemiring R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsSemitopologicalSemiring R] :
    IsSemitopologicalSemiring Rᵃᵒᵖ := ⟨⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [TopologicalSpace R] [IsSemitopologicalRing R] :
  body: ⟨⟩

中文:
实例 [非幺非结合环
  签名: R] [拓扑空间 R] [是Semitopological环 R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsSemitopologicalRing R] :
    IsSemitopologicalRing Rᵃᵒᵖ := ⟨⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [ContinuousMul R] :
  body: continuousMul_induced opMulEquiv.symm

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [连续乘法 R] :
  定义体: continuousMul_induced opMulEquiv.symm
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousMul R] :
    ContinuousMul Rᵃᵒᵖ :=
  continuousMul_induced opMulEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] [TopologicalSpace R] [IsTopologicalSemiring R] :
  body: ⟨⟩

中文:
实例 [非幺非结合半环
  签名: R] [拓扑空间 R] [是TopologicalSemiring R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring Rᵃᵒᵖ := ⟨⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] [TopologicalSpace R] [IsTopologicalRing R] :
  body: ⟨⟩

中文:
实例 [非幺非结合环
  签名: R] [拓扑空间 R] [是拓扑环 R] :
  定义体: ⟨⟩
-/
instance [NonUnitalNonAssocRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing Rᵃᵒᵖ := ⟨⟩

end AddOpposite

section

variable {R : Type*} [NonUnitalNonAssocRing R] [TopologicalSpace R]

/--
theorem `IsTopologicalRing.of_addGroup_of_nhds_zero` / 定理 `IsTopologicalRing.of_addGroup_of_nhds_zero`

English:
theorem IsTopologicalRing.of_addGroup_of_nhds_zero
  statement: [IsTopologicalAddGroup R]
  proof: by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]

中文:
定理 是拓扑环.of_addGroup_of_nhds_zero
  结论: [是拓扑加群 R]
  证明: by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mul, AddMonoidHom.mul_apply, ContinuousAt, mul_apply, mul_zero, nhds_prod_eq, zero_mul
-/
theorem IsTopologicalRing.of_addGroup_of_nhds_zero [IsTopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : forall x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : forall x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : IsTopologicalRing R where
  continuous_mul := by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]

/--
theorem `IsTopologicalRing.of_nhds_zero` / 定理 `IsTopologicalRing.of_nhds_zero`

English:
theorem IsTopologicalRing.of_nhds_zero
  proof: have := IsTopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  IsTopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right

中文:
定理 是拓扑环.of_nhds_zero
  证明: have := IsTopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  IsTopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.of_comm_of_nhds_zero, IsTopologicalRing, IsTopologicalRing.of_addGroup_of_nhds_zero, hmul_left, hmul_right, of_addGroup_of_nhds_zero, of_comm_of_nhds_zero
-/
theorem IsTopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R -> R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R -> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : forall x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : forall x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : forall x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : IsTopologicalRing R :=
  have := IsTopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  IsTopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right

end

variable [TopologicalSpace R]

section

variable [NonUnitalNonAssocRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalRing
  signature: R] : IsTopologicalRing (ULift R) where

中文:
实例 [是拓扑环
  签名: R] : 是拓扑环 (类型层提升 R) where
-/
instance [IsTopologicalRing R] : IsTopologicalRing (ULift R) where

variable [IsSemitopologicalRing R]

/--
theorem `mulLeft_continuous` / 定理 `mulLeft_continuous`

English:
theorem mulLeft_continuous
  given: (x : R)
  statement: Continuous (AddMonoidHom.mulLeft x)
  proof: continuous_id.const_mul _

中文:
定理 mulLeft_continuous
  条件: (x : R)
  结论: 连续 (加法幺半群态射.mulLeft x)
  证明: continuous_id.const_mul _

Depends on / 依赖: const_mul, continuous_id, continuous_id.const_mul
-/
theorem mulLeft_continuous (x : R) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_id.const_mul _

/--
theorem `mulRight_continuous` / 定理 `mulRight_continuous`

English:
theorem mulRight_continuous
  given: (x : R)
  statement: Continuous (AddMonoidHom.mulRight x)
  proof: continuous_id.mul_const _

中文:
定理 mulRight_continuous
  条件: (x : R)
  结论: 连续 (加法幺半群态射.mulRight x)
  证明: continuous_id.mul_const _

Depends on / 依赖: continuous_id, continuous_id.mul_const, mul_const
-/
theorem mulRight_continuous (x : R) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul_const _

end

namespace ContinuousAddEquiv

variable [Semiring R] [IsTopologicalSemiring R]

/-- The additive homeomorphism from a topological ring to itself,
induced by left multiplication by a unit. -/
@[simps! apply]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (r : Rˣ)
  body: r.mulLeft
  map_add' x₁ x₂ := left_distrib ↑r x₁ x₂
  continuous_toFun := continuous_const_mul _
  continuous_invFun := continuous_const_mul _

中文:
定义 mulLeft
  签名: (r : Rˣ)
  定义体: r.mulLeft
  map_add' x₁ x₂ := left_distrib ↑r x₁ x₂
  continuous_toFun := continuous_const_mul _
  continuous_invFun := continuous_const_mul _

Depends on / 依赖: mulLeft, r.mulLeft
-/
def mulLeft (r : Rˣ) : R ≃ₜ+ R where
  __ := r.mulLeft
  map_add' x₁ x₂ := left_distrib ↑r x₁ x₂
  continuous_toFun := continuous_const_mul _
  continuous_invFun := continuous_const_mul _

/-- The additive homeomorphism from a topological ring to itself,
induced by right multiplication by a unit. -/
@[simps! apply]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (r : Rˣ)
  body: r.mulRight
  map_add' x₁ x₂ := right_distrib x₁ x₂ r
  continuous_toFun := continuous_mul_const _
  continuous_invFun := continuous_mul_const _

中文:
定义 mulRight
  签名: (r : Rˣ)
  定义体: r.mulRight
  map_add' x₁ x₂ := right_distrib x₁ x₂ r
  continuous_toFun := continuous_mul_const _
  continuous_invFun := continuous_mul_const _

Depends on / 依赖: mulRight, r.mulRight
-/
def mulRight (r : Rˣ) : R ≃ₜ+ R where
  __ := r.mulRight
  map_add' x₁ x₂ := right_distrib x₁ x₂ r
  continuous_toFun := continuous_mul_const _
  continuous_invFun := continuous_mul_const _

end ContinuousAddEquiv

namespace NonUnitalSubring

variable [NonUnitalRing R]

/--
Instance `instIsTopologicalRing` / 实例 `instIsTopologicalRing`

English:
instance instIsTopologicalRing
  signature: [IsTopologicalRing R] (S : NonUnitalSubring R)
  body: { S.toSubsemigroup.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

中文:
实例 instIsTopologicalRing
  签名: [是拓扑环 R] (S : NonUnital子环 R)
  定义体: { S.toSubsemigroup.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

Depends on / 依赖: IsTopologicalAddGroup, S.toAddSubgroup, S.toSubsemigroup.continuousMul, continuousMul, toAddSubgroup, toSubsemigroup
-/
instance instIsTopologicalRing [IsTopologicalRing R] (S : NonUnitalSubring R) :
    IsTopologicalRing S :=
  { S.toSubsemigroup.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

/--
Instance `instIsSemitopologicalRing` / 实例 `instIsSemitopologicalRing`

English:
instance instIsSemitopologicalRing
  signature: [IsSemitopologicalRing R] (S : NonUnitalSubring R)
  body: { S.toSubsemigroup.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

中文:
实例 instIsSemitopologicalRing
  签名: [是Semitopological环 R] (S : NonUnital子环 R)
  定义体: { S.toSubsemigroup.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

Depends on / 依赖: IsTopologicalAddGroup, S.toAddSubgroup, S.toSubsemigroup.separatelyContinuousMul, separatelyContinuousMul, toAddSubgroup, toSubsemigroup
-/
instance instIsSemitopologicalRing [IsSemitopologicalRing R] (S : NonUnitalSubring R) :
    IsSemitopologicalRing S :=
  { S.toSubsemigroup.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

variable [IsSemitopologicalRing R]

/--
Definition of `topologicalClosure` / `topologicalClosure` 的定义

English:
definition topologicalClosure
  signature: (S : NonUnitalSubring R)
  body: { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

中文:
定义 topologicalClosure
  签名: (S : NonUnital子环 R)
  定义体: { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

Depends on / 依赖: S.toAddSubgroup.topologicalClosure, S.toSubsemigroup.topologicalClosure, _root_, _root_.closure, carrier, closure, toAddSubgroup, toSubsemigroup, topologicalClosure
-/
def topologicalClosure (S : NonUnitalSubring R) : NonUnitalSubring R :=
  { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

/--
theorem `le_topologicalClosure` / 定理 `le_topologicalClosure`

English:
theorem le_topologicalClosure
  given: (s : NonUnitalSubring R)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

中文:
定理 le_topologicalClosure
  条件: (s : NonUnital子环 R)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem le_topologicalClosure (s : NonUnitalSubring R) : s <= s.topologicalClosure :=
  _root_.subset_closure

/--
theorem `isClosed_topologicalClosure` / 定理 `isClosed_topologicalClosure`

English:
theorem isClosed_topologicalClosure
  given: (s : NonUnitalSubring R)
  proof: isClosed_closure

中文:
定理 isClosed_topologicalClosure
  条件: (s : NonUnital子环 R)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem isClosed_topologicalClosure (s : NonUnitalSubring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

/--
theorem `topologicalClosure_minimal` / 定理 `topologicalClosure_minimal`

English:
theorem topologicalClosure_minimal
  statement: (s : NonUnitalSubring R) {t : NonUnitalSubring R} (h : s <= t)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 topologicalClosure_minimal
  结论: (s : NonUnital子环 R) {t : NonUnital子环 R} (h : s <= t)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem topologicalClosure_minimal (s : NonUnitalSubring R) {t : NonUnitalSubring R} (h : s <= t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `topologicalClosure_mono` / 定理 `topologicalClosure_mono`

English:
theorem topologicalClosure_mono
  given: {s t : NonUnitalSubring R} (h : s <= t)
  proof: _root_.closure_mono h

中文:
定理 topologicalClosure_mono
  条件: {s t : NonUnital子环 R} (h : s <= t)
  证明: _root_.closure_mono h

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem topologicalClosure_mono {s t : NonUnitalSubring R} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

/--
Definition of `nonUnitalCommRingTopologicalClosure` / `nonUnitalCommRingTopologicalClosure` 的定义

English:
abbreviation nonUnitalCommRingTopologicalClosure
  signature: [T2Space R] (s : NonUnitalSubring R)
  body: { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

中文:
缩写 nonUnitalCommRingTopologicalClosure
  签名: [T2空间 R] (s : NonUnital子环 R)
  定义体: { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

Depends on / 依赖: commSemigroupTopologicalClosure, s.toSubsemigroup.commSemigroupTopologicalClosure, s.topologicalClosure.toNonUnitalRing, toNonUnitalRing, toSubsemigroup, topologicalClosure
-/
abbrev nonUnitalCommRingTopologicalClosure [T2Space R] (s : NonUnitalSubring R)
    (hs : forall x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubring

variable [Ring R]

/--
Instance `Subring.instIsTopologicalRing` / 实例 `Subring.instIsTopologicalRing`

English:
instance Subring.instIsTopologicalRing
  signature: [IsTopologicalRing R] (S : Subring R)
  body: { S.toSubmonoid.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

中文:
实例 子环.instIsTopologicalRing
  签名: [是拓扑环 R] (S : 子环 R)
  定义体: { S.toSubmonoid.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

Depends on / 依赖: IsTopologicalAddGroup, S.toAddSubgroup, S.toSubmonoid.continuousMul, continuousMul, toAddSubgroup, toSubmonoid
-/
instance Subring.instIsTopologicalRing [IsTopologicalRing R] (S : Subring R) :
    IsTopologicalRing S :=
  { S.toSubmonoid.continuousMul, (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

/--
Instance `Subring.instIsSemitopologicalRing` / 实例 `Subring.instIsSemitopologicalRing`

English:
instance Subring.instIsSemitopologicalRing
  signature: [IsSemitopologicalRing R] (S : Subring R)
  body: { S.toSubmonoid.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

中文:
实例 子环.instIsSemitopologicalRing
  签名: [是Semitopological环 R] (S : 子环 R)
  定义体: { S.toSubmonoid.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

Depends on / 依赖: IsTopologicalAddGroup, S.toAddSubgroup, S.toSubmonoid.separatelyContinuousMul, separatelyContinuousMul, toAddSubgroup, toSubmonoid
-/
instance Subring.instIsSemitopologicalRing [IsSemitopologicalRing R] (S : Subring R) :
    IsSemitopologicalRing S :=
  { S.toSubmonoid.separatelyContinuousMul,
    (inferInstance : IsTopologicalAddGroup S.toAddSubgroup) with }

variable [IsSemitopologicalRing R]

/--
Instance `Subring.continuousSMul` / 实例 `Subring.continuousSMul`

English:
instance Subring.continuousSMul
  signature: (s : Subring R) (X) [TopologicalSpace X] [MulAction R X]
  body: Subsemiring.continuousSMul s.toSubsemiring X

中文:
实例 子环.continuousSMul
  签名: (s : 子环 R) (X) [拓扑空间 X] [乘法作用 R X]
  定义体: Subsemiring.continuousSMul s.toSubsemiring X

Depends on / 依赖: Subsemiring, Subsemiring.continuousSMul, continuousSMul, s.toSubsemiring, toSubsemiring
-/
instance Subring.continuousSMul (s : Subring R) (X) [TopologicalSpace X] [MulAction R X]
    [ContinuousSMul R X] : ContinuousSMul s X :=
  Subsemiring.continuousSMul s.toSubsemiring X

/--
Definition of `Subring.topologicalClosure` / `Subring.topologicalClosure` 的定义

English:
definition Subring.topologicalClosure
  signature: (S : Subring R)
  body: { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

中文:
定义 子环.topologicalClosure
  签名: (S : 子环 R)
  定义体: { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

Depends on / 依赖: S.toAddSubgroup.topologicalClosure, S.toSubmonoid.topologicalClosure, _root_, _root_.closure, carrier, closure, toAddSubgroup, toSubmonoid, topologicalClosure
-/
def Subring.topologicalClosure (S : Subring R) : Subring R :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set R) }

/--
theorem `Subring.le_topologicalClosure` / 定理 `Subring.le_topologicalClosure`

English:
theorem Subring.le_topologicalClosure
  given: (s : Subring R)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

中文:
定理 子环.le_topologicalClosure
  条件: (s : 子环 R)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem Subring.le_topologicalClosure (s : Subring R) : s <= s.topologicalClosure :=
  _root_.subset_closure

/--
theorem `Subring.isClosed_topologicalClosure` / 定理 `Subring.isClosed_topologicalClosure`

English:
theorem Subring.isClosed_topologicalClosure
  given: (s : Subring R)
  proof: isClosed_closure

中文:
定理 子环.isClosed_topologicalClosure
  条件: (s : 子环 R)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem Subring.isClosed_topologicalClosure (s : Subring R) :
    IsClosed (s.topologicalClosure : Set R) := isClosed_closure

/--
theorem `Subring.topologicalClosure_minimal` / 定理 `Subring.topologicalClosure_minimal`

English:
theorem Subring.topologicalClosure_minimal
  statement: (s : Subring R) {t : Subring R} (h : s <= t)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 子环.topologicalClosure_minimal
  结论: (s : 子环 R) {t : 子环 R} (h : s <= t)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem Subring.topologicalClosure_minimal (s : Subring R) {t : Subring R} (h : s <= t)
    (ht : IsClosed (t : Set R)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `Subring.topologicalClosure_mono` / 定理 `Subring.topologicalClosure_mono`

English:
theorem Subring.topologicalClosure_mono
  given: {s t : Subring R} (h : s <= t)
  proof: _root_.closure_mono h

中文:
定理 子环.topologicalClosure_mono
  条件: {s t : 子环 R} (h : s <= t)
  证明: _root_.closure_mono h

Depends on / 依赖: _root_, _root_.closure_mono, closure_mono
-/
theorem Subring.topologicalClosure_mono {s t : Subring R} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  _root_.closure_mono h

/--
Definition of `Subring.commRingTopologicalClosure` / `Subring.commRingTopologicalClosure` 的定义

English:
abbreviation Subring.commRingTopologicalClosure
  signature: [T2Space R] (s : Subring R)
  body: { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

中文:
缩写 子环.commRingTopologicalClosure
  签名: [T2空间 R] (s : 子环 R)
  定义体: { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

Depends on / 依赖: commMonoidTopologicalClosure, s.toSubmonoid.commMonoidTopologicalClosure, s.topologicalClosure.toRing, toRing, toSubmonoid, topologicalClosure
-/
abbrev Subring.commRingTopologicalClosure [T2Space R] (s : Subring R)
    (hs : forall x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end IsTopologicalSemiring

/-!
### Lattice of ring topologies
We define a type class `RingTopology R` which endows a ring `R` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `R` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : R → S` induces `coinduced f : TopologicalSpace R → RingTopology S`. -/


universe u v

/--
Definition of `RingTopology` / `RingTopology` 的定义

English:
structure RingTopology
  parameters: (R : Type u) [Ring R]
  extends: TopologicalSpace R, IsTopologicalRing R
  (no additional axioms)

中文:
结构 环拓扑
  参数: (R : 类型u) [环 R]
  继承: 拓扑空间 R, 是拓扑环 R
  (无附加公理)
-/
structure RingTopology (R : Type u) [Ring R] : Type u
  extends TopologicalSpace R, IsTopologicalRing R

namespace RingTopology

variable {R : Type*} [Ring R]

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: {R : Type u} [Ring R]
  body: ⟨let _ : TopologicalSpace R := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩

中文:
实例 inhabited
  签名: {R : 类型u} [环 R]
  定义体: ⟨let _ : TopologicalSpace R := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩

Depends on / 依赖: TopologicalSpace, continuous_add, continuous_mul, continuous_neg, continuous_top
-/
instance inhabited {R : Type u} [Ring R] : Inhabited (RingTopology R) :=
  ⟨let _ : TopologicalSpace R := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩

/--
theorem `toTopologicalSpace_injective` / 定理 `toTopologicalSpace_injective`

English:
theorem toTopologicalSpace_injective
  proof: by
  intro f g _; cases f; cases g; congr

@[ext]

中文:
定理 toTopologicalSpace_injective
  证明: by
  intro f g _; cases f; cases g; congr

@[ext]
-/
theorem toTopologicalSpace_injective :
    Injective (toTopologicalSpace : RingTopology R -> TopologicalSpace R) := by
  intro f g _; cases f; cases g; congr

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : RingTopology R} (h : f.IsOpen = g.IsOpen)
  statement: f = g
  proof: toTopologicalSpace_injective TopologicalSpace.ext h

中文:
定理 ext
  条件: {f g : 环拓扑 R} (h : f.是开集 = g.是开集)
  结论: f = g
  证明: toTopologicalSpace_injective TopologicalSpace.ext h

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext, toTopologicalSpace_injective
-/
theorem ext {f g : RingTopology R} (h : f.IsOpen = g.IsOpen) : f = g :=
toTopologicalSpace_injective TopologicalSpace.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (RingTopology R)
  body: PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

中文:
实例 :
  签名: 偏序 (环拓扑 R)
  定义体: PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, RingTopology, RingTopology.toTopologicalSpace, toTopologicalSpace, toTopologicalSpace_injective
-/
instance : PartialOrder (RingTopology R) :=
  PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

set_option backward.privateInPublic true in
/--
Definition of `def_sInf` / `def_sInf` 的定义

English:
definition def_sInf
  signature: (S : Set (RingTopology R))
  body: let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
toContinuousMul := continuousMul_sInf forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
toContinuousNeg := continuousNeg_sInf for

中文:
定义 def_sInf
  签名: (S : 集合 (环拓扑 R))
  定义体: let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
toContinuousMul := continuousMul_sInf forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
toContinuousNeg := continuousNeg_sInf for
-/
private def def_sInf (S : Set (RingTopology R)) : RingTopology R :=
  let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
toContinuousMul := continuousMul_sInf forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
toContinuousNeg := continuousNeg_sInf forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousNeg }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (RingTopology R)
  body: def_sInf
  isGLB_sInf _ := .of_image (f := toTopologicalSpace) .rfl (isGLB_sInf _)

中文:
实例 :
  签名: 余mpleteSemilatticeInf (环拓扑 R)
  定义体: def_sInf
  isGLB_sInf _ := .of_image (f := toTopologicalSpace) .rfl (isGLB_sInf _)

Depends on / 依赖: def_sInf
-/
instance : CompleteSemilatticeInf (RingTopology R) where
  sInf := def_sInf
  isGLB_sInf _ := .of_image (f := toTopologicalSpace) .rfl (isGLB_sInf _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (RingTopology R)
  body: completeLatticeOfCompleteSemilatticeInf _

中文:
实例 :
  签名: 完备格 (环拓扑 R)
  定义体: completeLatticeOfCompleteSemilatticeInf _

Depends on / 依赖: completeLatticeOfCompleteSemilatticeInf
-/
instance : CompleteLattice (RingTopology R) :=
  completeLatticeOfCompleteSemilatticeInf _

/--
Definition of `coinduced` / `coinduced` 的定义

English:
definition coinduced
  signature: {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R -> S)
  body: sInf { b : RingTopology S | t.coinduced f <= b.toTopologicalSpace }

中文:
定义 coinduced
  签名: {R S : 类型} [t : 拓扑空间 R] [环 S] (f : R -> S)
  定义体: sInf { b : RingTopology S | t.coinduced f <= b.toTopologicalSpace }

Depends on / 依赖: RingTopology, b.toTopologicalSpace, coinduced, t.coinduced, toTopologicalSpace
-/
def coinduced {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R -> S) : RingTopology S :=
  sInf { b : RingTopology S | t.coinduced f <= b.toTopologicalSpace }

/--
theorem `coinduced_continuous` / 定理 `coinduced_continuous`

English:
theorem coinduced_continuous
  given: {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R -> S)
  proof: continuous_sInf_rng.2 forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

中文:
定理 coinduced_continuous
  条件: {R S : 类型} [t : 拓扑空间 R] [环 S] (f : R -> S)
  证明: continuous_sInf_rng.2 forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

Depends on / 依赖: continuous_iff_coinduced_le, continuous_sInf_rng, forall_mem_image
-/
theorem coinduced_continuous {R S : Type*} [t : TopologicalSpace R] [Ring S] (f : R -> S) :
    Continuous[t, (coinduced f).toTopologicalSpace] f :=
continuous_sInf_rng.2 forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

/--
Definition of `toAddGroupTopology` / `toAddGroupTopology` 的定义

English:
definition toAddGroupTopology
  signature: (t : RingTopology R)
  body: t.toTopologicalSpace
  toIsTopologicalAddGroup :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toIsTopologicalRing

中文:
定义 toAddGroupTopology
  签名: (t : 环拓扑 R)
  定义体: t.toTopologicalSpace
  toIsTopologicalAddGroup :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toIsTopologicalRing

Depends on / 依赖: t.toTopologicalSpace, toTopologicalSpace
-/
def toAddGroupTopology (t : RingTopology R) : AddGroupTopology R where
  toTopologicalSpace := t.toTopologicalSpace
  toIsTopologicalAddGroup :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toIsTopologicalRing

/--
Definition of `toAddGroupTopology.orderEmbedding` / `toAddGroupTopology.orderEmbedding` 的定义

English:
definition toAddGroupTopology.orderEmbedding
  signature: : OrderEmbedding (RingTopology R) (AddGroupTopology R)
  body: OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

中文:
定义 toAddGroupTopology.orderEmbedding
  签名: : OrderEmbedding (环拓扑 R) (加法群拓扑 R)
  定义体: OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

Depends on / 依赖: Iff.rfl, OrderEmbedding, OrderEmbedding.ofMapLEIff, ofMapLEIff, toAddGroupTopology
-/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology R) (AddGroupTopology R) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

end RingTopology

section AbsoluteValue

/--
Definition of `AbsoluteValue.comp` / `AbsoluteValue.comp` 的定义

English:
definition AbsoluteValue.comp
  signature: {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
  body: v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)

中文:
定义 绝对值.comp
  签名: {R S T : 类型} [半环 T] [半环 R] [半环 S] [偏序 S]
  定义体: v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)
-/
def AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) {f : T ->+* R} (hf : Function.Injective f) : AbsoluteValue T S where
  toMulHom := v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)

end AbsoluteValue
