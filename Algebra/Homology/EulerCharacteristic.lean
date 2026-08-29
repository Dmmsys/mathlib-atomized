/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Euler characteristic of homological complexes

The Euler characteristic is defined using the `ComplexShape.EulerCharSigns` typeclass,
which provides the alternating signs for each index. This allows the definition to work
uniformly for chain complexes, cochain complexes, and complexes with other index types.

The definitions work on graded objects, with the homological complex versions
defined as abbreviations that apply the graded object versions to `C.X` and `C.homology`.

## Junk values

These definitions may have junk values from `finsum` (0 for infinite support) and
`Module.finrank` (0 for modules not free of finite rank).

## Main definitions

* `ComplexShape.EulerCharSigns`: Typeclass providing alternating signs for Euler characteristic
* `GradedObject.eulerChar`: The Euler characteristic of a graded object using `finsum`
* `GradedObject.finrankSupport`: Indices where `Module.finrank` is nonzero
* `HomologicalComplex.eulerChar`: The Euler characteristic using `finsum`
* `HomologicalComplex.homologyEulerChar`: The homological Euler characteristic using `finsum`

## Main results

* `GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum` equals the
  finite sum when the graded object has finite support contained in the given set
* `HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum` equals
  the finite sum when the complex has finite support contained in the given set
* `HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset`: The `finsum`
  homological Euler characteristic equals the finite sum when homology has finite support

-/

@[expose] public section

namespace ComplexShape

variable {ι : Type*} (c : ComplexShape ι)

/--
Definition of `EulerCharSigns` / `EulerCharSigns` 的定义

English:
class EulerCharSigns
  parameters: where
  axioms and operations (2):
    - χ : ι -> Intˣ
    - χ_next({i j : ι} (h : c.Rel i j)) : χ j = - χ i

中文:
类 EulerCharSigns
  参数: where
  公理与运算 (2 个):
    - χ : ι -> 整数ˣ
    - χ_next({i j : ι} (h : c.关系 i j)) : χ j = - χ i
-/
class EulerCharSigns where
  /-- The sign for each index -/
  χ : ι -> Intˣ
  /-- Signs alternate along relations in the complex shape -/
  χ_next {i j : ι} (h : c.Rel i j) : χ j = - χ i

variable [c.EulerCharSigns]

/--
Definition of `χ` / `χ` 的定义

English:
abbreviation χ
  signature: : ι -> Intˣ
  body: EulerCharSigns.χ c

中文:
缩写 χ
  签名: : ι -> 整数ˣ
  定义体: EulerCharSigns.χ c

Depends on / 依赖: EulerCharSigns
-/
abbrev χ : ι -> Intˣ := EulerCharSigns.χ c

/--
lemma `χ_next` / 引理 `χ_next`

English:
lemma χ_next
  given: {i j : ι} (h : c.Rel i j)
  statement: c.χ j = - c.χ i
  proof: EulerCharSigns.χ_next h

中文:
引理 χ_next
  条件: {i j : ι} (h : c.关系 i j)
  结论: c.χ j = - c.χ i
  证明: EulerCharSigns.χ_next h

Depends on / 依赖: EulerCharSigns
-/
lemma χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

/--
lemma `χ_prev` / 引理 `χ_prev`

English:
lemma χ_prev
  given: {i j : ι} (h : c.Rel i j)
  statement: c.χ i = - c.χ j
  proof: by simp [c.χ_next h]

@[simps]

中文:
引理 χ_prev
  条件: {i j : ι} (h : c.关系 i j)
  结论: c.χ i = - c.χ j
  证明: by simp [c.χ_next h]

@[simps]
-/
lemma χ_prev {i j : ι} (h : c.Rel i j) : c.χ i = - c.χ j := by simp [c.χ_next h]

@[simps]
/--
Instance `eulerCharSignsUpInt` / 实例 `eulerCharSignsUpInt`

English:
instance eulerCharSignsUpInt
  signature: : (up Int).EulerCharSigns where
  body: Int.negOnePow
  χ_next := by rintro _ _ rfl; rw [Int.negOnePow_succ]

@[simps]

中文:
实例 eulerCharSignsUp整数
  签名: : (up 整数).EulerCharSigns where
  定义体: Int.negOnePow
  χ_next := by rintro _ _ rfl; rw [Int.negOnePow_succ]

@[simps]

Depends on / 依赖: Int.negOnePow, negOnePow
-/
instance eulerCharSignsUpInt : (up Int).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; rw [Int.negOnePow_succ]

@[simps]
/--
Instance `eulerCharSignsDownInt` / 实例 `eulerCharSignsDownInt`

English:
instance eulerCharSignsDownInt
  signature: : (down Int).EulerCharSigns where
  body: Int.negOnePow
  χ_next := by rintro _ _ rfl; simp [Int.negOnePow_succ]

中文:
实例 eulerCharSignsDown整数
  签名: : (down 整数).EulerCharSigns where
  定义体: Int.negOnePow
  χ_next := by rintro _ _ rfl; simp [Int.negOnePow_succ]

Depends on / 依赖: Int.negOnePow, negOnePow
-/
instance eulerCharSignsDownInt : (down Int).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; simp [Int.negOnePow_succ]

set_option backward.isDefEq.respectTransparency false in
@[simps]
/--
Instance `eulerCharSignsUpNat` / 实例 `eulerCharSignsUpNat`

English:
instance eulerCharSignsUpNat
  signature: : (up Nat).EulerCharSigns where
  body: (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

中文:
实例 eulerCharSignsUp自然数
  签名: : (up 自然数).EulerCharSigns where
  定义体: (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]
-/
instance eulerCharSignsUpNat : (up Nat).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

set_option backward.isDefEq.respectTransparency false in
@[simps]
/--
Instance `eulerCharSignsDownNat` / 实例 `eulerCharSignsDownNat`

English:
instance eulerCharSignsDownNat
  signature: : (down Nat).EulerCharSigns where
  body: (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

中文:
实例 eulerCharSignsDown自然数
  签名: : (down 自然数).EulerCharSigns where
  定义体: (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]
-/
instance eulerCharSignsDownNat : (down Nat).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

end ComplexShape

open ComplexShape CategoryTheory

variable {R : Type*} [Ring R] {ι : Type*}

namespace GradedObject

variable (c : ComplexShape ι) [c.EulerCharSigns]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `finrankSupport` / `finrankSupport` 的定义

English:
definition finrankSupport
  signature: (X : CategoryTheory.GradedObject ι (ModuleCat R))
  body: Function.support (fun i => Module.finrank R (X i))

中文:
定义 finrankSupport
  签名: (X : 范畴论.GradedObject ι (模范畴 R))
  定义体: Function.support (fun i => Module.finrank R (X i))

Depends on / 依赖: Function, Function.support, Module, Module.finrank, finrank, support
-/
noncomputable def finrankSupport (X : CategoryTheory.GradedObject ι (ModuleCat R)) : Set ι :=
  Function.support (fun i => Module.finrank R (X i))

/--
lemma `finrankSupport_subset_iff` / 引理 `finrankSupport_subset_iff`

English:
lemma finrankSupport_subset_iff
  given: (X : CategoryTheory.GradedObject ι (ModuleCat R)) (s : Set ι)
  proof: Function.support_subset_iff'

中文:
引理 finrankSupport_subset_iff
  条件: (X : 范畴论.GradedObject ι (模范畴 R)) (s : 集合 ι)
  证明: Function.support_subset_iff'

Depends on / 依赖: Function, Function.support_subset_iff, support_subset_iff
-/
lemma finrankSupport_subset_iff (X : CategoryTheory.GradedObject ι (ModuleCat R)) (s : Set ι) :
    finrankSupport X subseteq s ↔ forall i ∉ s, Module.finrank R (X i) = 0 :=
  Function.support_subset_iff'

/--
Definition of `eulerChar` / `eulerChar` 的定义

English:
definition eulerChar
  signature: (X : CategoryTheory.GradedObject ι (ModuleCat R))
  body: ∑ᶠ i : ι, (c.χ i : Int) * Module.finrank R (X i)

中文:
定义 eulerChar
  签名: (X : 范畴论.GradedObject ι (模范畴 R))
  定义体: ∑ᶠ i : ι, (c.χ i : Int) * Module.finrank R (X i)

Depends on / 依赖: Module, Module.finrank, finrank
-/
noncomputable def eulerChar (X : CategoryTheory.GradedObject ι (ModuleCat R)) : Int :=
  ∑ᶠ i : ι, (c.χ i : Int) * Module.finrank R (X i)

/--
lemma `support_eulerChar_summand` / 引理 `support_eulerChar_summand`

English:
lemma support_eulerChar_summand
  given: (X : CategoryTheory.GradedObject ι (ModuleCat R))
  proof: by
  simp only [finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]

中文:
引理 support_eulerChar_summand
  条件: (X : 范畴论.GradedObject ι (模范畴 R))
  证明: by
  simp only [finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]
-/
private lemma support_eulerChar_summand (X : CategoryTheory.GradedObject ι (ModuleCat R)) :
    Function.support (fun i => (c.χ i : Int) * Module.finrank R (X i)) = finrankSupport X := by
  simp only [finrankSupport, Function.support_mul_of_ne_zero_left (fun i => Units.ne_zero (c.χ i))]
  ext i; simp [Function.mem_support]

/--
theorem `eulerChar_eq_sum_finSet_of_finrankSupport_subset` / 定理 `eulerChar_eq_sum_finSet_of_finrankSupport_subset`

English:
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset
  proof: by
  simp only [eulerChar]
  rw [finsum_eq_sum_of_support_subset]
  exact (support_eulerChar_summand c X).symm ▸ h_support

中文:
定理 eulerChar_eq_sum_finSet_of_finrankSupport_subset
  证明: by
  simp only [eulerChar]
  rw [finsum_eq_sum_of_support_subset]
  exact (support_eulerChar_summand c X).symm ▸ h_support

Depends on / 依赖: eulerChar, finsum_eq_sum_of_support_subset, h_support, support_eulerChar_summand
-/
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (X : CategoryTheory.GradedObject ι (ModuleCat R)) (indices : Finset ι)
    (h_support : finrankSupport X subseteq indices) :
    eulerChar c X = ∑ i in indices, (c.χ i : Int) * Module.finrank R (X i) := by
  simp only [eulerChar]
  rw [finsum_eq_sum_of_support_subset]
  exact (support_eulerChar_summand c X).symm ▸ h_support

end GradedObject

namespace HomologicalComplex

variable {c : ComplexShape ι} [c.EulerCharSigns]

/--
Definition of `eulerChar` / `eulerChar` 的定义

English:
abbreviation eulerChar
  signature: (C : HomologicalComplex (ModuleCat R) c)
  body: GradedObject.eulerChar c C.X

中文:
缩写 eulerChar
  签名: (C : 同调复形 (模范畴 R) c)
  定义体: GradedObject.eulerChar c C.X

Depends on / 依赖: GradedObject, GradedObject.eulerChar, eulerChar
-/
noncomputable abbrev eulerChar (C : HomologicalComplex (ModuleCat R) c) : Int :=
  GradedObject.eulerChar c C.X

/--
Definition of `homologyEulerChar` / `homologyEulerChar` 的定义

English:
abbreviation homologyEulerChar
  signature: (C : HomologicalComplex (ModuleCat R) c)
  body: GradedObject.eulerChar c (fun i => C.homology i)

中文:
缩写 homologyEulerChar
  签名: (C : 同调复形 (模范畴 R) c)
  定义体: GradedObject.eulerChar c (fun i => C.homology i)

Depends on / 依赖: C.homology, GradedObject, GradedObject.eulerChar, eulerChar, homology
-/
noncomputable abbrev homologyEulerChar (C : HomologicalComplex (ModuleCat R) c)
    [forall i : ι, C.HasHomology i] : Int :=
  GradedObject.eulerChar c (fun i => C.homology i)

/--
theorem `eulerChar_eq_sum_finSet_of_finrankSupport_subset` / 定理 `eulerChar_eq_sum_finSet_of_finrankSupport_subset`

English:
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset
  statement: (C : HomologicalComplex (ModuleCat R) c)
  proof: GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c C.X indices h_support

中文:
定理 eulerChar_eq_sum_finSet_of_finrankSupport_subset
  结论: (C : 同调复形 (模范畴 R) c)
  证明: GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c C.X indices h_support

Depends on / 依赖: GradedObject, GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset, eulerChar_eq_sum_finSet_of_finrankSupport_subset, h_support, indices
-/
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset (C : HomologicalComplex (ModuleCat R) c)
    (indices : Finset ι)
    (h_support : GradedObject.finrankSupport C.X subseteq indices) :
    eulerChar C = ∑ i in indices, (c.χ i : Int) * Module.finrank R (C.X i) :=
  GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c C.X indices h_support

/--
theorem `homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset` / 定理 `homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset`

English:
theorem homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
  proof: GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c
    (fun i => C.homology i) indices h_support

中文:
定理 homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
  证明: GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c
    (fun i => C.homology i) indices h_support

Depends on / 依赖: C.homology, GradedObject, GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset, eulerChar_eq_sum_finSet_of_finrankSupport_subset, h_support, homology, indices
-/
theorem homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (C : HomologicalComplex (ModuleCat R) c) [forall i : ι, C.HasHomology i] (indices : Finset ι)
    (h_support : GradedObject.finrankSupport (fun i => C.homology i) subseteq indices) :
    homologyEulerChar C = ∑ i in indices, (c.χ i : Int) * Module.finrank R (C.homology i) :=
  GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c
    (fun i => C.homology i) indices h_support

end HomologicalComplex
