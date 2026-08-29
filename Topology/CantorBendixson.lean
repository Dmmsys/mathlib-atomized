/-
Copyright (c) 2026 Zikang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zikang Yu
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FixedPointApproximants
public import Mathlib.Topology.DerivedSet

/-!
# Cantor-Bendixson derivatives and perfect kernel

This file defines the transfinite iteration of the relative derived-set operator
and the associated perfect kernel.

For closed sets, the relative derived set agrees with `derivedSet`, so this recovers the usual
Cantor-Bendixson derivative sequence of a closed set.

## Main definitions

* `CantorBendixson.iteratedDerivedSet s a`: the `a`-th transfinite iterate of `relDerivedSet`
  starting from `s`.
* `CantorBendixson.perfectKernel s`: the largest perfect subset of `s`, defined as the
  intersection of all iterated derived sets of `s`.

## Main statements

* `CantorBendixson.iteratedDerivedSet_constant_iff_preperfect`: a set is preperfect if and only
  if every iterated derived set is equal to the original set.
* `CantorBendixson.iteratedDerivedSet_stay`: the iterated derived-set sequence eventually
  stabilizes.
* `CantorBendixson.perfect_perfectKernel`: the perfect kernel of a closed set is perfect.
* `CantorBendixson.subset_perfectKernel_of_perfect`: the perfect kernel is the largest perfect
  subset.

## Notation

* `sᵈ[a]`: the `a`-th iterated relative derived set of `s`.

## Implementation notes

* We define `iteratedDerivedSet` using `OrdinalApprox.gfpApprox` applied to `relDerivedSet`.
  This keeps the transfinite sequence antitone for arbitrary sets.
* If `s` is closed, then `relDerivedSet s = derivedSet s`, so successor stages agree with the
  ambient derived-set operator.

## TODO

* Pointwise and setwise Cantor-Bendixson ranks.
* A generalized Cantor-Bendixson decomposition theorem for arbitrary topological spaces and
  arbitrary cardinalities of topological bases.

-/

@[expose] public section

open Filter Set Cardinal OrdinalApprox Function

universe u

namespace CantorBendixson

section

variable {X : Type u} [TopologicalSpace X]

/--
Definition of `iteratedDerivedSet` / `iteratedDerivedSet` 的定义

English:
definition iteratedDerivedSet
  signature: (s : Set X)
  body: gfpApprox relDerivedSet s

@[inherit_doc CantorBendixson.iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

中文:
定义 iteratedDerivedSet
  签名: (s : 集合 X)
  定义体: gfpApprox relDerivedSet s

@[inherit_doc CantorBendixson.iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

Depends on / 依赖: gfpApprox, relDerivedSet
-/
def iteratedDerivedSet (s : Set X) : Ordinal -> Set X :=
  gfpApprox relDerivedSet s

@[inherit_doc CantorBendixson.iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

variable {s t : Set X} {a b : Ordinal}

@[simp]
/--
theorem `iteratedDerivedSet_zero` / 定理 `iteratedDerivedSet_zero`

English:
theorem iteratedDerivedSet_zero
  proof: by
  simp [iteratedDerivedSet, gfpApprox_zero]

@[simp]

中文:
定理 iteratedDerivedSet_zero
  证明: by
  simp [iteratedDerivedSet, gfpApprox_zero]

@[simp]

Depends on / 依赖: gfpApprox_zero, iteratedDerivedSet
-/
theorem iteratedDerivedSet_zero :
    sᵈ[0] = s := by
  simp [iteratedDerivedSet, gfpApprox_zero]

@[simp]
/--
theorem `iteratedDerivedSet_succ` / 定理 `iteratedDerivedSet_succ`

English:
theorem iteratedDerivedSet_succ
  proof: by
  simpa [iteratedDerivedSet] using
    gfpApprox_add_one relDerivedSet relDerivedSet_subset a

中文:
定理 iteratedDerivedSet_succ
  证明: by
  simpa [iteratedDerivedSet] using
    gfpApprox_add_one relDerivedSet relDerivedSet_subset a

Depends on / 依赖: gfpApprox_add_one, iteratedDerivedSet, relDerivedSet, relDerivedSet_subset
-/
theorem iteratedDerivedSet_succ :
    sᵈ[a + 1] = relDerivedSet (sᵈ[a]) := by
  simpa [iteratedDerivedSet] using
    gfpApprox_add_one relDerivedSet relDerivedSet_subset a

/--
theorem `iteratedDerivedSet_limit` / 定理 `iteratedDerivedSet_limit`

English:
theorem iteratedDerivedSet_limit
  given: (ha : Order.IsSuccLimit a)
  proof: by
  simpa [iteratedDerivedSet] using gfpApprox_of_isSuccLimit relDerivedSet ha

中文:
定理 iteratedDerivedSet_limit
  条件: (ha : Order.是SuccLimit a)
  证明: by
  simpa [iteratedDerivedSet] using gfpApprox_of_isSuccLimit relDerivedSet ha

Depends on / 依赖: gfpApprox_of_isSuccLimit, iteratedDerivedSet, relDerivedSet
-/
theorem iteratedDerivedSet_limit (ha : Order.IsSuccLimit a) :
    sᵈ[a] = ⋂ b : Set.Iio a, sᵈ[b] := by
  simpa [iteratedDerivedSet] using gfpApprox_of_isSuccLimit relDerivedSet ha

/--
theorem `iteratedDerivedSet_constant_iff_preperfect` / 定理 `iteratedDerivedSet_constant_iff_preperfect`

English:
theorem iteratedDerivedSet_constant_iff_preperfect
  proof: by
  rw [preperfect_iff_eq_relDerivedSet]; rw [eq_comm]; rw [← (gfpApprox_eq_all_of_fixedPoint relDerivedSet (relDerivedSet_subset))]
  simp [iteratedDerivedSet]

中文:
定理 iteratedDerivedSet_constant_iff_preperfect
  证明: by
  rw [preperfect_iff_eq_relDerivedSet]; rw [eq_comm]; rw [← (gfpApprox_eq_all_of_fixedPoint relDerivedSet (relDerivedSet_subset))]
  simp [iteratedDerivedSet]

Depends on / 依赖: eq_comm, gfpApprox_eq_all_of_fixedPoint, iteratedDerivedSet, preperfect_iff_eq_relDerivedSet, relDerivedSet, relDerivedSet_subset
-/
theorem iteratedDerivedSet_constant_iff_preperfect :
    Preperfect s ↔ forall a : Ordinal, sᵈ[a] = s := by
  rw [preperfect_iff_eq_relDerivedSet]; rw [eq_comm]; rw [← (gfpApprox_eq_all_of_fixedPoint relDerivedSet (relDerivedSet_subset))]
  simp [iteratedDerivedSet]

/--
theorem `isClosed_iteratedDerivedSet` / 定理 `isClosed_iteratedDerivedSet`

English:
theorem isClosed_iteratedDerivedSet
  given: (hs : IsClosed s)
  proof: by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [iteratedDerivedSet_zero]
  | add_one a ha =>
    simp_all [ha.relDerivedSet_eq, isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
    simpa [iteratedDerivedSet_limit ha] using
      isClosed_iInter fun i => isClosed_iInter fun hi => ih i hi

中文:
定理 isClosed_iteratedDerivedSet
  条件: (hs : 是闭集 s)
  证明: by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [iteratedDerivedSet_zero]
  | add_one a ha =>
    simp_all [ha.relDerivedSet_eq, isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
    simpa [iteratedDerivedSet_limit ha] using
      isClosed_iInter fun i => isClosed_iInter fun hi => ih i hi

Depends on / 依赖: Ordinal, Ordinal.limitRecOn, add_one, derivedSet_mono, ha.relDerivedSet_eq, isClosed_iInter, isClosed_iff_derivedSet_subset, iteratedDerivedSet_limit, iteratedDerivedSet_zero, limitRecOn, relDerivedSet_eq
-/
theorem isClosed_iteratedDerivedSet (hs : IsClosed s) :
    forall a : Ordinal, IsClosed sᵈ[a] := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [iteratedDerivedSet_zero]
  | add_one a ha =>
    simp_all [ha.relDerivedSet_eq, isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
    simpa [iteratedDerivedSet_limit ha] using
      isClosed_iInter fun i => isClosed_iInter fun hi => ih i hi

/--
theorem `iteratedDerivedSet_antitone` / 定理 `iteratedDerivedSet_antitone`

English:
theorem iteratedDerivedSet_antitone
  given: (s : Set X)
  proof: gfpApprox_anti_right relDerivedSet

中文:
定理 iteratedDerivedSet_antitone
  条件: (s : 集合 X)
  证明: gfpApprox_anti_right relDerivedSet

Depends on / 依赖: gfpApprox_anti_right, relDerivedSet
-/
theorem iteratedDerivedSet_antitone (s : Set X) :
    Antitone (iteratedDerivedSet s) := gfpApprox_anti_right relDerivedSet

/--
theorem `iteratedDerivedSet_mono` / 定理 `iteratedDerivedSet_mono`

English:
theorem iteratedDerivedSet_mono
  proof: gfpApprox_mono_mid _

中文:
定理 iteratedDerivedSet_mono
  证明: gfpApprox_mono_mid _

Depends on / 依赖: gfpApprox_mono_mid
-/
theorem iteratedDerivedSet_mono :
    Monotone (fun s : Set X => iteratedDerivedSet s) :=
  gfpApprox_mono_mid _

/--
theorem `mem_fixedPoints_of_iteratedDerivedSet_succ_eq` / 定理 `mem_fixedPoints_of_iteratedDerivedSet_succ_eq`

English:
theorem mem_fixedPoints_of_iteratedDerivedSet_succ_eq
  given: (ha : sᵈ[a + 1] = sᵈ[a])
  proof: by
  rw [Function.mem_fixedPoints_iff]
  simpa [iteratedDerivedSet_succ] using ha.symm

中文:
定理 mem_fixedPoints_of_iteratedDerivedSet_succ_eq
  条件: (ha : sᵈ[a + 1] = sᵈ[a])
  证明: by
  rw [Function.mem_fixedPoints_iff]
  simpa [iteratedDerivedSet_succ] using ha.symm

Depends on / 依赖: Function, Function.mem_fixedPoints_iff, ha.symm, iteratedDerivedSet_succ, mem_fixedPoints_iff
-/
theorem mem_fixedPoints_of_iteratedDerivedSet_succ_eq (ha : sᵈ[a + 1] = sᵈ[a]) :
    sᵈ[a] in fixedPoints relDerivedSet := by
  rw [Function.mem_fixedPoints_iff]
  simpa [iteratedDerivedSet_succ] using ha.symm

/--
theorem `iteratedDerivedSet_mem_fixedPoints` / 定理 `iteratedDerivedSet_mem_fixedPoints`

English:
theorem iteratedDerivedSet_mem_fixedPoints
  given: (s : Set X)
  proof: by
  refine ⟨(Order.succ #(Set X)).ord,
    gfpApprox_ord_mem_fixedPoint relDerivedSet relDerivedSet_subset⟩

中文:
定理 iteratedDerivedSet_mem_fixedPoints
  条件: (s : 集合 X)
  证明: by
  refine ⟨(Order.succ #(Set X)).ord,
    gfpApprox_ord_mem_fixedPoint relDerivedSet relDerivedSet_subset⟩

Depends on / 依赖: Order.succ, gfpApprox_ord_mem_fixedPoint, relDerivedSet, relDerivedSet_subset
-/
theorem iteratedDerivedSet_mem_fixedPoints (s : Set X) :
    exists a : Ordinal, sᵈ[a] in fixedPoints relDerivedSet := by
  refine ⟨(Order.succ #(Set X)).ord,
    gfpApprox_ord_mem_fixedPoint relDerivedSet relDerivedSet_subset⟩

/--
Definition of `perfectKernel` / `perfectKernel` 的定义

English:
definition perfectKernel
  signature: (s : Set X)
  body: ⋂ a : Ordinal, sᵈ[a]

中文:
定义 perfectKernel
  签名: (s : 集合 X)
  定义体: ⋂ a : Ordinal, sᵈ[a]

Depends on / 依赖: Ordinal
-/
def perfectKernel (s : Set X) : Set X :=
  ⋂ a : Ordinal, sᵈ[a]

/--
theorem `perfectKernel_subset_iteratedDerivedSet` / 定理 `perfectKernel_subset_iteratedDerivedSet`

English:
theorem perfectKernel_subset_iteratedDerivedSet
  given: (s : Set X) (a : Ordinal)
  proof: Set.iInter_subset _ a

中文:
定理 perfectKernel_subset_iteratedDerivedSet
  条件: (s : 集合 X) (a : 序数)
  证明: Set.iInter_subset _ a

Depends on / 依赖: Set.iInter_subset, iInter_subset
-/
theorem perfectKernel_subset_iteratedDerivedSet (s : Set X) (a : Ordinal) :
    perfectKernel s subseteq sᵈ[a] :=
  Set.iInter_subset _ a

/--
theorem `perfectKernel_subset` / 定理 `perfectKernel_subset`

English:
theorem perfectKernel_subset
  given: (s : Set X)
  proof: by
  simpa [iteratedDerivedSet_zero] using perfectKernel_subset_iteratedDerivedSet s 0

中文:
定理 perfectKernel_subset
  条件: (s : 集合 X)
  证明: by
  simpa [iteratedDerivedSet_zero] using perfectKernel_subset_iteratedDerivedSet s 0

Depends on / 依赖: iteratedDerivedSet_zero, perfectKernel_subset_iteratedDerivedSet
-/
theorem perfectKernel_subset (s : Set X) :
    perfectKernel s subseteq s := by
  simpa [iteratedDerivedSet_zero] using perfectKernel_subset_iteratedDerivedSet s 0

/--
theorem `perfectKernel_mono` / 定理 `perfectKernel_mono`

English:
theorem perfectKernel_mono
  given: (hst : s subseteq t)
  proof: by
  simpa [perfectKernel] using Set.iInter_mono'' (iteratedDerivedSet_mono hst)

中文:
定理 perfectKernel_mono
  条件: (hst : s subseteq t)
  证明: by
  simpa [perfectKernel] using Set.iInter_mono'' (iteratedDerivedSet_mono hst)

Depends on / 依赖: Set.iInter_mono, iInter_mono, iteratedDerivedSet_mono, perfectKernel
-/
theorem perfectKernel_mono (hst : s subseteq t) :
    perfectKernel s subseteq perfectKernel t := by
  simpa [perfectKernel] using Set.iInter_mono'' (iteratedDerivedSet_mono hst)

/--
theorem `isClosed_perfectKernel` / 定理 `isClosed_perfectKernel`

English:
theorem isClosed_perfectKernel
  given: (hs : IsClosed s)
  proof: isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[simp]

中文:
定理 isClosed_perfectKernel
  条件: (hs : 是闭集 s)
  证明: isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[simp]

Depends on / 依赖: isClosed_iInter, isClosed_iteratedDerivedSet
-/
theorem isClosed_perfectKernel (hs : IsClosed s) :
    IsClosed (perfectKernel s) :=
  isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[simp]
/--
theorem `perfectKernel_empty` / 定理 `perfectKernel_empty`

English:
theorem perfectKernel_empty
  proof: by
  simpa using perfectKernel_subset ∅

中文:
定理 perfectKernel_empty
  证明: by
  simpa using perfectKernel_subset ∅

Depends on / 依赖: perfectKernel_subset
-/
theorem perfectKernel_empty :
    perfectKernel (∅ : Set X) = ∅ := by
  simpa using perfectKernel_subset ∅

/--
theorem `perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints` / 定理 `perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints`

English:
theorem perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints
  proof: by
  refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
  refine Set.subset_iInter fun i => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone s hi.le
  · exact (gfpApprox_eq_of_mem_fixedPoints relDerivedSet hi ha).ge

中文:
定理 perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints
  证明: by
  refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
  refine Set.subset_iInter fun i => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone s hi.le
  · exact (gfpApprox_eq_of_mem_fixedPoints relDerivedSet hi ha).ge

Depends on / 依赖: Set.subset_iInter, gfpApprox_eq_of_mem_fixedPoints, hi.le, iteratedDerivedSet_antitone, le_antisymm, lt_or_ge, perfectKernel_subset_iteratedDerivedSet, relDerivedSet, subset_iInter
-/
theorem perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints
    (ha : sᵈ[a] in fixedPoints relDerivedSet) :
    perfectKernel s = sᵈ[a] := by
  refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
  refine Set.subset_iInter fun i => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone s hi.le
  · exact (gfpApprox_eq_of_mem_fixedPoints relDerivedSet hi ha).ge

/--
theorem `_root_.Perfect.subset_perfectKernel` / 定理 `_root_.Perfect.subset_perfectKernel`

English:
theorem _root_.Perfect.subset_perfectKernel
  proof: by
  refine Set.subset_iInter fun i => ?_
  simpa [iteratedDerivedSet_constant_iff_preperfect.mp hP.acc i] using
    iteratedDerivedSet_mono hPs i

中文:
定理 _root_.完美.subset_perfectKernel
  证明: by
  refine Set.subset_iInter fun i => ?_
  simpa [iteratedDerivedSet_constant_iff_preperfect.mp hP.acc i] using
    iteratedDerivedSet_mono hPs i

Depends on / 依赖: Set.subset_iInter, hP.acc, iteratedDerivedSet_constant_iff_preperfect, iteratedDerivedSet_constant_iff_preperfect.mp, iteratedDerivedSet_mono, subset_iInter
-/
theorem _root_.Perfect.subset_perfectKernel
    {P : Set X} (hP : Perfect P) (hPs : P subseteq s) :
    P subseteq perfectKernel s := by
  refine Set.subset_iInter fun i => ?_
  simpa [iteratedDerivedSet_constant_iff_preperfect.mp hP.acc i] using
    iteratedDerivedSet_mono hPs i

/--
theorem `perfect_perfectKernel` / 定理 `perfect_perfectKernel`

English:
theorem perfect_perfectKernel
  given: (hs : IsClosed s)
  proof: by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_mem_fixedPoints s
  rw [perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints ha]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [(isClosed_iteratedDerivedSet hs a).relDerivedSet_eq] using
    (Function.mem_fixedPoints_iff.mp ha).symm

中文:
定理 perfect_perfectKernel
  条件: (hs : 是闭集 s)
  证明: by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_mem_fixedPoints s
  rw [perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints ha]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [(isClosed_iteratedDerivedSet hs a).relDerivedSet_eq] using
    (Function.mem_fixedPoints_iff.mp ha).symm

Depends on / 依赖: Function, Function.mem_fixedPoints_iff.mp, isClosed_iteratedDerivedSet, iteratedDerivedSet_mem_fixedPoints, mem_fixedPoints_iff, perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints, perfect_iff_eq_derivedSet, perfect_iff_eq_derivedSet.mpr, relDerivedSet_eq
-/
theorem perfect_perfectKernel (hs : IsClosed s) :
    Perfect (perfectKernel s) := by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_mem_fixedPoints s
  rw [perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints ha]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [(isClosed_iteratedDerivedSet hs a).relDerivedSet_eq] using
    (Function.mem_fixedPoints_iff.mp ha).symm

/--
theorem `perfectKernel_idem` / 定理 `perfectKernel_idem`

English:
theorem perfectKernel_idem
  given: (hs : IsClosed s)
  proof: subset_antisymm (perfectKernel_subset _)
    (perfect_perfectKernel hs).subset_perfectKernel Subset.rfl

中文:
定理 perfectKernel_idem
  条件: (hs : 是闭集 s)
  证明: subset_antisymm (perfectKernel_subset _)
    (perfect_perfectKernel hs).subset_perfectKernel Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, perfectKernel_subset, perfect_perfectKernel, subset_antisymm, subset_perfectKernel
-/
theorem perfectKernel_idem (hs : IsClosed s) :
    perfectKernel (perfectKernel s) = perfectKernel s :=
subset_antisymm (perfectKernel_subset _)
    (perfect_perfectKernel hs).subset_perfectKernel Subset.rfl

end

end CantorBendixson
