/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Generators in triangulated categories

We define the notions of strong and classical generators in (pre)triangulated categories.
This is not to be confused with `ObjectProperty.IsStrongGenerator` defined in
`CategoryTheory/Generator`.

## Main definitions

- `ObjectProperty.triangEnvelopeIter P n`: The object property of all objects reachable from `P`
  by shifts, binary products, retracts and at most `n` extensions.
- `ObjectProperty.triangEnvelope P`: The triangulated envelope of `P`, i.e., the object property
  of all objects reachable from `P` by shifts, binary products, retracts and extensions. This is
  the smallest triangulated object property closed under retracts that contains `P`, see
  `ObjectProperty.triangEnvelope_le_iff`.
- `ObjectProperty.IsStrongTriangulatedGenerator P`: `P` is a strong triangulated generator if
  there exists `n` such that every object is in `P.triangEnvelopeIter n`.
- `ObjectProperty.IsClassicalTriangulatedGenerator P`: `P` is a classical triangulated generator
  if every object is in `P.triangEnvelope`.

## Main results

- `ObjectProperty.triangEnvelope_le_iff`: The universal property of `P.triangEnvelope`: it is
  the smallest triangulated object property closed under retracts that contains `P`.
- `ObjectProperty.IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator`: A strong
  triangulated generator is a classical triangulated generator.

## TODO

* Prove that if `C` has a strong generator and `P` is a classical generator, then `P` is a
  strong generator (stacks 0FXA).

## References

* [Bondal and Van den Bergh, *Generators and representability of functors in commutative and
  noncommutative geometry*][bondal_vandenbergh_2003]
* [Stacks 09SJ](https://stacks.math.columbia.edu/tag/09SJ)

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C Int] [Preadditive C]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/--
Definition of `triangEnvelopeIter` / `triangEnvelopeIter` 的定义

English:
abbreviation triangEnvelopeIter
  signature: (n : Nat)
  body: ((P.shiftClosure Int).binaryProductsClosure.retractClosure.extensionProductIter n).retractClosure

@[simp]

中文:
缩写 triangEnvelopeIter
  签名: (n : 自然数)
  定义体: ((P.shiftClosure Int).binaryProductsClosure.retractClosure.extensionProductIter n).retractClosure

@[simp]

Depends on / 依赖: P.shiftClosure, binaryProductsClosure, binaryProductsClosure.retractClosure.extensionProductIter, extensionProductIter, retractClosure, shiftClosure
-/
abbrev triangEnvelopeIter (n : Nat) : ObjectProperty C :=
  ((P.shiftClosure Int).binaryProductsClosure.retractClosure.extensionProductIter n).retractClosure

@[simp]
/--
lemma `triangEnvelopeIter_zero` / 引理 `triangEnvelopeIter_zero`

English:
lemma triangEnvelopeIter_zero
  proof: by
  rw [triangEnvelopeIter]; rw [extensionProductIter_zero]; rw [retractClosure_eq_self]

中文:
引理 triangEnvelopeIter_zero
  证明: by
  rw [triangEnvelopeIter]; rw [extensionProductIter_zero]; rw [retractClosure_eq_self]

Depends on / 依赖: extensionProductIter_zero, retractClosure_eq_self, triangEnvelopeIter
-/
lemma triangEnvelopeIter_zero :
    P.triangEnvelopeIter 0 = (P.shiftClosure Int).binaryProductsClosure.retractClosure := by
  rw [triangEnvelopeIter]; rw [extensionProductIter_zero]; rw [retractClosure_eq_self]

/--
lemma `triangEnvelopeIter_succ` / 引理 `triangEnvelopeIter_succ`

English:
lemma triangEnvelopeIter_succ
  given: (n : Nat)
  proof: by
  rw [triangEnvelopeIter]; rw [extensionProductIter_succ]; rw [← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

中文:
引理 triangEnvelopeIter_succ
  条件: (n : 自然数)
  证明: by
  rw [triangEnvelopeIter]; rw [extensionProductIter_succ]; rw [← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

Depends on / 依赖: extensionProductIter_succ, retractClosure_extensionProduct_retractClosure_retractClosure, triangEnvelopeIter
-/
lemma triangEnvelopeIter_succ (n : Nat) :
    P.triangEnvelopeIter (n + 1) =
      (extensionProduct (P.shiftClosure Int).binaryProductsClosure.retractClosure
         (P.triangEnvelopeIter n)).retractClosure := by
  rw [triangEnvelopeIter]; rw [extensionProductIter_succ]; rw [← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

/--
lemma `triangEnvelopeIter_succ'` / 引理 `triangEnvelopeIter_succ'`

English:
lemma triangEnvelopeIter_succ'
  given: [IsTriangulated C] (n : Nat)
  proof: by
  rw [triangEnvelopeIter]; rw [extensionProductIter_succ']; rw [← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

中文:
引理 triangEnvelopeIter_succ'
  条件: [IsTriangulated C] (n : 自然数)
  证明: by
  rw [triangEnvelopeIter]; rw [extensionProductIter_succ']; rw [← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

Depends on / 依赖: extensionProductIter_succ, retractClosure_extensionProduct_retractClosure_retractClosure, triangEnvelopeIter
-/
lemma triangEnvelopeIter_succ' [IsTriangulated C] (n : Nat) :
    P.triangEnvelopeIter (n + 1) =
      (extensionProduct (P.triangEnvelopeIter n)
        (P.shiftClosure Int).binaryProductsClosure.retractClosure).retractClosure := by
  rw [triangEnvelopeIter]; rw [extensionProductIter_succ']; rw [← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp

/--
lemma `triangEnvelopeIter_add` / 引理 `triangEnvelopeIter_add`

English:
lemma triangEnvelopeIter_add
  given: [IsTriangulated C] {n m n' : Nat} (h : n = n' + 1 := by lia)
  proof: by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add _ h]

中文:
引理 triangEnvelopeIter_add
  条件: [IsTriangulated C] {n m n' : 自然数} (h : n = n' + 1 := by lia)
  证明: by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add _ h]

Depends on / 依赖: P.triangEnvelopeIter, extensionProduct, extensionProductIter_add, retractClosure, retractClosure_extensionProduct_retractClosure_retractClosure, triangEnvelopeIter
-/
lemma triangEnvelopeIter_add [IsTriangulated C] {n m n' : Nat} (h : n = n' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n') (P.triangEnvelopeIter m)).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add _ h]

/--
lemma `triangEnvelopeIter_add'` / 引理 `triangEnvelopeIter_add'`

English:
lemma triangEnvelopeIter_add'
  given: [IsTriangulated C] {n m m' : Nat} (h : m = m' + 1 := by lia)
  proof: by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add' _ h]

中文:
引理 triangEnvelopeIter_add'
  条件: [IsTriangulated C] {n m m' : 自然数} (h : m = m' + 1 := by lia)
  证明: by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add' _ h]

Depends on / 依赖: P.triangEnvelopeIter, extensionProduct, extensionProductIter_add, retractClosure, retractClosure_extensionProduct_retractClosure_retractClosure, triangEnvelopeIter
-/
lemma triangEnvelopeIter_add' [IsTriangulated C] {n m m' : Nat} (h : m = m' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n) (P.triangEnvelopeIter m')).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add' _ h]

variable {P} in
/--
lemma `monotone_triangEnvelopeIter` / 引理 `monotone_triangEnvelopeIter`

English:
lemma monotone_triangEnvelopeIter
  given: {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat)
  proof: monotone_retractClosure monotone_extensionProductIter
    (monotone_retractClosure <| limitsClosure_monotone _ <| monotone_shiftClosure hPQ) n

中文:
引理 monotone_triangEnvelopeIter
  条件: {Q : Object命题erty C} (hPQ : P <= Q) (n : 自然数)
  证明: monotone_retractClosure monotone_extensionProductIter
    (monotone_retractClosure <| limitsClosure_monotone _ <| monotone_shiftClosure hPQ) n

Depends on / 依赖: limitsClosure_monotone, monotone_extensionProductIter, monotone_retractClosure, monotone_shiftClosure
-/
lemma monotone_triangEnvelopeIter {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat) :
    P.triangEnvelopeIter n <= Q.triangEnvelopeIter n :=
monotone_retractClosure monotone_extensionProductIter
    (monotone_retractClosure <| limitsClosure_monotone _ <| monotone_shiftClosure hPQ) n

/--
lemma `monotone'_triangEnvelopeIter` / 引理 `monotone'_triangEnvelopeIter`

English:
lemma monotone'_triangEnvelopeIter
  given: {n m : Nat} (h : n <= m := by lia)
  proof: by
  apply monotone_retractClosure
  by_cases! hP : P.Nonempty
  · exact monotone'_extensionProductIter _ h
  · simp [hP]

中文:
引理 monotone'_triangEnvelopeIter
  条件: {n m : 自然数} (h : n <= m := by lia)
  证明: by
  apply monotone_retractClosure
  by_cases! hP : P.Nonempty
  · exact monotone'_extensionProductIter _ h
  · simp [hP]

Depends on / 依赖: Nonempty, P.Nonempty, P.triangEnvelopeIter, _extensionProductIter, monotone, monotone_retractClosure, triangEnvelopeIter
-/
lemma monotone'_triangEnvelopeIter {n m : Nat} (h : n <= m := by lia) :
    P.triangEnvelopeIter n <= P.triangEnvelopeIter m := by
  apply monotone_retractClosure
  by_cases! hP : P.Nonempty
  · exact monotone'_extensionProductIter _ h
  · simp [hP]

/--
lemma `le_triangEnvelopeIter` / 引理 `le_triangEnvelopeIter`

English:
lemma le_triangEnvelopeIter
  given: (n : Nat)
  statement: P <= P.triangEnvelopeIter n
  proof: calc
    P <= P.shiftClosure Int := le_shiftClosure _
    _ <= (P.shiftClosure Int).binaryProductsClosure := le_limitsClosure _ _
    _ <= (P.shiftClosure Int).binaryProductsClosure.retractClosure := le_retractClosure _
    _ <= P.triangEnvelopeIter n := by
      rw [← triangEnvelopeIter_zero]
     

中文:
引理 le_triangEnvelopeIter
  条件: (n : 自然数)
  结论: P <= P.triangEnvelopeIter n
  证明: calc
    P <= P.shiftClosure Int := le_shiftClosure _
    _ <= (P.shiftClosure Int).binaryProductsClosure := le_limitsClosure _ _
    _ <= (P.shiftClosure Int).binaryProductsClosure.retractClosure := le_retractClosure _
    _ <= P.triangEnvelopeIter n := by
      rw [← triangEnvelopeIter_zero]
     

Depends on / 依赖: Nat.zero_le, P.monotone, P.shiftClosure, P.triangEnvelopeIter, _triangEnvelopeIter, binaryProductsClosure, binaryProductsClosure.retractClosure, le_limitsClosure, le_retractClosure, le_shiftClosure, monotone, retractClosure, shiftClosure, triangEnvelopeIter, triangEnvelopeIter_zero, zero_le
-/
lemma le_triangEnvelopeIter (n : Nat) : P <= P.triangEnvelopeIter n :=
  calc
    P <= P.shiftClosure Int := le_shiftClosure _
    _ <= (P.shiftClosure Int).binaryProductsClosure := le_limitsClosure _ _
    _ <= (P.shiftClosure Int).binaryProductsClosure.retractClosure := le_retractClosure _
    _ <= P.triangEnvelopeIter n := by
      rw [← triangEnvelopeIter_zero]
      exact P.monotone'_triangEnvelopeIter (Nat.zero_le n)

/-- An object property `P` is called a strong triangulated generator, if every object
can be reached from objects in `P` by shifts, binary products, retracts and at most `n`
extensions, for some fixed `n`. -/
@[stacks 09SJ "(2)"]
/--
Definition of `IsStrongTriangulatedGenerator` / `IsStrongTriangulatedGenerator` 的定义

English:
definition IsStrongTriangulatedGenerator
  signature: : Prop
  body: exists n, P.triangEnvelopeIter n = ⊤

中文:
定义 IsStrongTriangulatedGenerator
  签名: : 命题
  定义体: exists n, P.triangEnvelopeIter n = ⊤

Depends on / 依赖: P.triangEnvelopeIter, triangEnvelopeIter
-/
def IsStrongTriangulatedGenerator : Prop := exists n, P.triangEnvelopeIter n = ⊤

/--
lemma `isStrongTriangulatedGenerator_iff` / 引理 `isStrongTriangulatedGenerator_iff`

English:
lemma isStrongTriangulatedGenerator_iff
  proof: Iff.rfl

中文:
引理 isStrongTriangulatedGenerator_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isStrongTriangulatedGenerator_iff :
    P.IsStrongTriangulatedGenerator ↔ exists n, P.triangEnvelopeIter n = ⊤ := Iff.rfl

/--
Definition of `triangEnvelope` / `triangEnvelope` 的定义

English:
definition triangEnvelope
  signature: : ObjectProperty C
  body: ⨆ n, P.triangEnvelopeIter n

中文:
定义 triangEnvelope
  签名: : Object命题erty C
  定义体: ⨆ n, P.triangEnvelopeIter n

Depends on / 依赖: P.triangEnvelopeIter, triangEnvelopeIter
-/
def triangEnvelope : ObjectProperty C := ⨆ n, P.triangEnvelopeIter n

/--
lemma `prop_triangEnvelope_iff` / 引理 `prop_triangEnvelope_iff`

English:
lemma prop_triangEnvelope_iff
  given: (X : C)
  statement: P.triangEnvelope X ↔ exists n, P.triangEnvelopeIter n X
  proof: prop_iSup_iff _ X

中文:
引理 prop_triangEnvelope_iff
  条件: (X : C)
  结论: P.triangEnvelope X ↔ 存在 n, P.triangEnvelopeIter n X
  证明: prop_iSup_iff _ X

Depends on / 依赖: prop_iSup_iff
-/
lemma prop_triangEnvelope_iff (X : C) : P.triangEnvelope X ↔ exists n, P.triangEnvelopeIter n X :=
  prop_iSup_iff _ X

/--
lemma `triangEnvelopeIter_le_triangEnvelope` / 引理 `triangEnvelopeIter_le_triangEnvelope`

English:
lemma triangEnvelopeIter_le_triangEnvelope
  given: (n : Nat)
  statement: P.triangEnvelopeIter n <= P.triangEnvelope
  proof: le_iSup _ _

中文:
引理 triangEnvelopeIter_le_triangEnvelope
  条件: (n : 自然数)
  结论: P.triangEnvelopeIter n <= P.triangEnvelope
  证明: le_iSup _ _

Depends on / 依赖: le_iSup
-/
lemma triangEnvelopeIter_le_triangEnvelope (n : Nat) : P.triangEnvelopeIter n <= P.triangEnvelope :=
  le_iSup _ _

/--
lemma `le_triangEnvelope` / 引理 `le_triangEnvelope`

English:
lemma le_triangEnvelope
  statement: P <= P.triangEnvelope
  proof: (P.le_triangEnvelopeIter 0).trans (P.triangEnvelopeIter_le_triangEnvelope 0)

中文:
引理 le_triangEnvelope
  结论: P <= P.triangEnvelope
  证明: (P.le_triangEnvelopeIter 0).trans (P.triangEnvelopeIter_le_triangEnvelope 0)

Depends on / 依赖: P.le_triangEnvelopeIter, P.triangEnvelopeIter_le_triangEnvelope, le_triangEnvelopeIter, triangEnvelopeIter_le_triangEnvelope
-/
lemma le_triangEnvelope : P <= P.triangEnvelope :=
  (P.le_triangEnvelopeIter 0).trans (P.triangEnvelopeIter_le_triangEnvelope 0)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : P.triangEnvelope.Nonempty
  body: .mono P.le_triangEnvelope

中文:
实例 [P.Nonempty]
  签名: : P.triangEnvelope.Nonempty
  定义体: .mono P.le_triangEnvelope

Depends on / 依赖: P.le_triangEnvelope, le_triangEnvelope
-/
instance [P.Nonempty] : P.triangEnvelope.Nonempty :=
  .mono P.le_triangEnvelope

variable {P} in
/--
lemma `monotone_triangEnvelope` / 引理 `monotone_triangEnvelope`

English:
lemma monotone_triangEnvelope
  given: {Q : ObjectProperty C} (h : P <= Q)
  proof: iSup_le fun n => (P.monotone_triangEnvelopeIter h n).trans
    (Q.triangEnvelopeIter_le_triangEnvelope n)

中文:
引理 monotone_triangEnvelope
  条件: {Q : Object命题erty C} (h : P <= Q)
  证明: iSup_le fun n => (P.monotone_triangEnvelopeIter h n).trans
    (Q.triangEnvelopeIter_le_triangEnvelope n)

Depends on / 依赖: P.monotone_triangEnvelopeIter, Q.triangEnvelopeIter_le_triangEnvelope, iSup_le, monotone_triangEnvelopeIter, triangEnvelopeIter_le_triangEnvelope
-/
lemma monotone_triangEnvelope {Q : ObjectProperty C} (h : P <= Q) :
    P.triangEnvelope <= Q.triangEnvelope :=
  iSup_le fun n => (P.monotone_triangEnvelopeIter h n).trans
    (Q.triangEnvelopeIter_le_triangEnvelope n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.triangEnvelope.IsStableUnderRetracts
  body: by
    intro X Y r hY
    rw [prop_triangEnvelope_iff] at hY ⊢
    obtain ⟨n, hn⟩ := hY
    exact ⟨n, IsStableUnderRetracts.of_retract r hn⟩

中文:
实例 :
  签名: P.triangEnvelope.IsStableUnderRetracts
  定义体: by
    intro X Y r hY
    rw [prop_triangEnvelope_iff] at hY ⊢
    obtain ⟨n, hn⟩ := hY
    exact ⟨n, IsStableUnderRetracts.of_retract r hn⟩

Depends on / 依赖: IsStableUnderRetracts, IsStableUnderRetracts.of_retract, of_retract, prop_triangEnvelope_iff
-/
instance : P.triangEnvelope.IsStableUnderRetracts where
  of_retract := by
    intro X Y r hY
    rw [prop_triangEnvelope_iff] at hY ⊢
    obtain ⟨n, hn⟩ := hY
    exact ⟨n, IsStableUnderRetracts.of_retract r hn⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.triangEnvelope.IsStableUnderShift Int
  body: IsStableUnderShiftBy.mk by
    intro X hX
    rw [prop_triangEnvelope_iff] at hX
    obtain ⟨n, hn⟩ := hX
    rw [prop_shift_iff]; rw [prop_triangEnvelope_iff]
    exact ⟨n, IsStableUnderShiftBy.le_shift _ hn⟩

中文:
实例 :
  签名: P.triangEnvelope.IsStableUnderShift 整数
  定义体: IsStableUnderShiftBy.mk by
    intro X hX
    rw [prop_triangEnvelope_iff] at hX
    obtain ⟨n, hn⟩ := hX
    rw [prop_shift_iff]; rw [prop_triangEnvelope_iff]
    exact ⟨n, IsStableUnderShiftBy.le_shift _ hn⟩

Depends on / 依赖: IsStableUnderShiftBy, IsStableUnderShiftBy.le_shift, IsStableUnderShiftBy.mk, le_shift, prop_shift_iff, prop_triangEnvelope_iff
-/
instance : P.triangEnvelope.IsStableUnderShift Int where
isStableUnderShiftBy a := IsStableUnderShiftBy.mk by
    intro X hX
    rw [prop_triangEnvelope_iff] at hX
    obtain ⟨n, hn⟩ := hX
    rw [prop_shift_iff]; rw [prop_triangEnvelope_iff]
    exact ⟨n, IsStableUnderShiftBy.le_shift _ hn⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangulated
  signature: C] : P.triangEnvelope.IsTriangulatedClosed₂
  body: by
  apply IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₂
  rw [prop_triangEnvelope_iff] at h₁ h₂ ⊢
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use n + (m + 1)
  rw [triangEnvelopeIter_add' P rfl]
  exact le_retractClosure _ _ ⟨_, _, _, _, _, hT, hn, hm⟩

中文:
实例 [IsTriangulated
  签名: C] : P.triangEnvelope.IsTriangulatedClosed₂
  定义体: by
  apply IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₂
  rw [prop_triangEnvelope_iff] at h₁ h₂ ⊢
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use n + (m + 1)
  rw [triangEnvelopeIter_add' P rfl]
  exact le_retractClosure _ _ ⟨_, _, _, _, _, hT, hn, hm⟩

Depends on / 依赖: le_retractClosure, prop_triangEnvelope_iff, triangEnvelopeIter_add
-/
instance [IsTriangulated C] : P.triangEnvelope.IsTriangulatedClosed₂ := by
  apply IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₂
  rw [prop_triangEnvelope_iff] at h₁ h₂ ⊢
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use n + (m + 1)
  rw [triangEnvelopeIter_add' P rfl]
  exact le_retractClosure _ _ ⟨_, _, _, _, _, hT, hn, hm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: [IsTriangulated C]

中文:
实例 [P.Nonempty]
  签名: [IsTriangulated C]
-/
instance [P.Nonempty] [IsTriangulated C] : P.triangEnvelope.IsTriangulated where

/--
lemma `triangEnvelope_le_iff` / 引理 `triangEnvelope_le_iff`

English:
lemma triangEnvelope_le_iff
  given: {Q : ObjectProperty C} [Q.IsStableUnderRetracts] [Q.IsTriangulated]
  proof: by
  refine ⟨fun h => le_trans P.le_triangEnvelope h, fun h => ?_⟩
  rw [triangEnvelope]; rw [iSup_le_iff]
  intro n
  rw [triangEnvelopeIter]; rw [retractClosure_le_iff]
  apply extensionProductIter_le_of_isTriangulatedClosed₂
  rwa [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure

中文:
引理 triangEnvelope_le_iff
  条件: {Q : Object命题erty C} [Q.IsStableUnderRetracts] [Q.IsTriangulated]
  证明: by
  refine ⟨fun h => le_trans P.le_triangEnvelope h, fun h => ?_⟩
  rw [triangEnvelope]; rw [iSup_le_iff]
  intro n
  rw [triangEnvelopeIter]; rw [retractClosure_le_iff]
  apply extensionProductIter_le_of_isTriangulatedClosed₂
  rwa [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure

Depends on / 依赖: P.le_triangEnvelope, binaryProductsClosure_le_iff, iSup_le_iff, le_trans, le_triangEnvelope, retractClosure_le_iff, shiftClosure_le_iff, triangEnvelope, triangEnvelopeIter
-/
lemma triangEnvelope_le_iff {Q : ObjectProperty C} [Q.IsStableUnderRetracts] [Q.IsTriangulated] :
    P.triangEnvelope <= Q ↔ P <= Q := by
  refine ⟨fun h => le_trans P.le_triangEnvelope h, fun h => ?_⟩
  rw [triangEnvelope]; rw [iSup_le_iff]
  intro n
  rw [triangEnvelopeIter]; rw [retractClosure_le_iff]
  apply extensionProductIter_le_of_isTriangulatedClosed₂
  rwa [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure_le_iff]

/-- An object property `P` is called a classical generator, if every object can be reached
from objects in `P` by shifts, binary products, retracts and extensions. -/
@[stacks 09SJ "(1)"]
/--
Definition of `IsClassicalTriangulatedGenerator` / `IsClassicalTriangulatedGenerator` 的定义

English:
definition IsClassicalTriangulatedGenerator
  signature: : Prop
  body: P.triangEnvelope = ⊤

中文:
定义 IsClassicalTriangulatedGenerator
  签名: : 命题
  定义体: P.triangEnvelope = ⊤

Depends on / 依赖: P.triangEnvelope, triangEnvelope
-/
def IsClassicalTriangulatedGenerator : Prop := P.triangEnvelope = ⊤

/--
lemma `isClassicalTriangulatedGenerator_iff` / 引理 `isClassicalTriangulatedGenerator_iff`

English:
lemma isClassicalTriangulatedGenerator_iff
  proof: Iff.rfl

中文:
引理 isClassicalTriangulatedGenerator_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isClassicalTriangulatedGenerator_iff :
    P.IsClassicalTriangulatedGenerator ↔ P.triangEnvelope = ⊤ := Iff.rfl

/--
lemma `IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator` / 引理 `IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator`

English:
lemma IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator
  proof: by
  obtain ⟨n, hn⟩ := h
  rw [isClassicalTriangulatedGenerator_iff]; rw [eq_top_iff]
  exact hn ▸ (P.triangEnvelopeIter_le_triangEnvelope n)

中文:
引理 IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator
  证明: by
  obtain ⟨n, hn⟩ := h
  rw [isClassicalTriangulatedGenerator_iff]; rw [eq_top_iff]
  exact hn ▸ (P.triangEnvelopeIter_le_triangEnvelope n)

Depends on / 依赖: P.triangEnvelopeIter_le_triangEnvelope, eq_top_iff, isClassicalTriangulatedGenerator_iff, triangEnvelopeIter_le_triangEnvelope
-/
lemma IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator
    (h : P.IsStrongTriangulatedGenerator) : P.IsClassicalTriangulatedGenerator := by
  obtain ⟨n, hn⟩ := h
  rw [isClassicalTriangulatedGenerator_iff]; rw [eq_top_iff]
  exact hn ▸ (P.triangEnvelopeIter_le_triangEnvelope n)

end CategoryTheory.ObjectProperty
