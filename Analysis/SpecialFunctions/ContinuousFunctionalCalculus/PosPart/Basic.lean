/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # The positive (and negative) parts of a selfadjoint element in a C⋆-algebra

This file defines the positive and negative parts of a selfadjoint element in a C⋆-algebra via
the continuous functional calculus and develops the basic API, including the uniqueness of the
positive and negative parts.
-/

public section

open scoped NNReal

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module Real A] [SMulCommClass Real A A] [IsScalarTower Real A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]

namespace CStarAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosPart A
  body: cfcₙ (·⁺ : Real -> Real)

中文:
实例 :
  签名: PosPart A
  定义体: cfcₙ (·⁺ : Real -> Real)
-/
noncomputable instance : PosPart A where
  posPart := cfcₙ (·⁺ : Real -> Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NegPart A
  body: cfcₙ (·⁻ : Real -> Real)

中文:
实例 :
  签名: NegPart A
  定义体: cfcₙ (·⁻ : Real -> Real)
-/
noncomputable instance : NegPart A where
  negPart := cfcₙ (·⁻ : Real -> Real)

end CStarAlgebra

namespace CFC

/--
lemma `posPart_def` / 引理 `posPart_def`

English:
lemma posPart_def
  given: (a : A)
  statement: a⁺ = cfcₙ (·⁺ : Real -> Real) a
  proof: rfl

中文:
引理 posPart_def
  条件: (a : A)
  结论: a⁺ = cfcₙ (·⁺ : 实数 -> 实数) a
  证明: rfl
-/
lemma posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a := rfl

/--
lemma `negPart_def` / 引理 `negPart_def`

English:
lemma negPart_def
  given: (a : A)
  statement: a⁻ = cfcₙ (·⁻ : Real -> Real) a
  proof: rfl

@[simp]

中文:
引理 negPart_def
  条件: (a : A)
  结论: a⁻ = cfcₙ (·⁻ : 实数 -> 实数) a
  证明: rfl

@[simp]
-/
lemma negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a := rfl

@[simp]
/--
lemma `posPart_zero` / 引理 `posPart_zero`

English:
lemma posPart_zero
  statement: (0 : A)⁺ = 0
  proof: by simp [posPart_def]

@[simp]

中文:
引理 posPart_zero
  结论: (0 : A)⁺ = 0
  证明: by simp [posPart_def]

@[simp]

Depends on / 依赖: posPart_def
-/
lemma posPart_zero : (0 : A)⁺ = 0 := by simp [posPart_def]

@[simp]
/--
lemma `negPart_zero` / 引理 `negPart_zero`

English:
lemma negPart_zero
  statement: (0 : A)⁻ = 0
  proof: by simp [negPart_def]

中文:
引理 negPart_zero
  结论: (0 : A)⁻ = 0
  证明: by simp [negPart_def]

Depends on / 依赖: negPart_def
-/
lemma negPart_zero : (0 : A)⁻ = 0 := by simp [negPart_def]

/--
lemma `posPart_eq_zero_of_not_isSelfAdjoint` / 引理 `posPart_eq_zero_of_not_isSelfAdjoint`

English:
lemma posPart_eq_zero_of_not_isSelfAdjoint
  given: {a : A} (ha : ¬IsSelfAdjoint a)
  statement: a⁺ = 0
  proof: cfcₙ_apply_of_not_predicate a ha

中文:
引理 posPart_eq_zero_of_not_isSelfAdjoint
  条件: {a : A} (ha : ¬IsSelfAdjoint a)
  结论: a⁺ = 0
  证明: cfcₙ_apply_of_not_predicate a ha
-/
lemma posPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁺ = 0 :=
  cfcₙ_apply_of_not_predicate a ha

/--
lemma `negPart_eq_zero_of_not_isSelfAdjoint` / 引理 `negPart_eq_zero_of_not_isSelfAdjoint`

English:
lemma negPart_eq_zero_of_not_isSelfAdjoint
  given: {a : A} (ha : ¬IsSelfAdjoint a)
  statement: a⁻ = 0
  proof: cfcₙ_apply_of_not_predicate a ha

@[simp]

中文:
引理 negPart_eq_zero_of_not_isSelfAdjoint
  条件: {a : A} (ha : ¬IsSelfAdjoint a)
  结论: a⁻ = 0
  证明: cfcₙ_apply_of_not_predicate a ha

@[simp]
-/
lemma negPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁻ = 0 :=
  cfcₙ_apply_of_not_predicate a ha

@[simp]
/--
lemma `posPart_mul_negPart` / 引理 `posPart_mul_negPart`

English:
lemma posPart_mul_negPart
  given: (a : A)
  statement: a⁺ * a⁻ = 0
  proof: by
  rw [posPart_def]; rw [negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero Real a]
    refine cfcₙ_congr (fun x _ => ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

@[simp]

中文:
引理 posPart_mul_negPart
  条件: (a : A)
  结论: a⁺ * a⁻ = 0
  证明: by
  rw [posPart_def]; rw [negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero Real a]
    refine cfcₙ_congr (fun x _ => ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

@[simp]

Depends on / 依赖: IsSelfAdjoint, _root_, _root_.negPart_def, _root_.posPart_def, le_total, negPart_def, posPart_def
-/
lemma posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0 := by
  rw [posPart_def]; rw [negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero Real a]
    refine cfcₙ_congr (fun x _ => ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

@[simp]
/--
lemma `negPart_mul_posPart` / 引理 `negPart_mul_posPart`

English:
lemma negPart_mul_posPart
  given: (a : A)
  statement: a⁻ * a⁺ = 0
  proof: by
  rw [posPart_def]; rw [negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero Real a]
    refine cfcₙ_congr (fun x _ => ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total 0 x
  · simp [cfcₙ_apply_of_not_predicate a ha]

中文:
引理 negPart_mul_posPart
  条件: (a : A)
  结论: a⁻ * a⁺ = 0
  证明: by
  rw [posPart_def]; rw [negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero Real a]
    refine cfcₙ_congr (fun x _ => ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total 0 x
  · simp [cfcₙ_apply_of_not_predicate a ha]

Depends on / 依赖: IsSelfAdjoint, _root_, _root_.negPart_def, _root_.posPart_def, le_total, negPart_def, posPart_def
-/
lemma negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0 := by
  rw [posPart_def]; rw [negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero Real a]
    refine cfcₙ_congr (fun x _ => ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total 0 x
  · simp [cfcₙ_apply_of_not_predicate a ha]

/--
lemma `posPart_sub_negPart` / 引理 `posPart_sub_negPart`

English:
lemma posPart_sub_negPart
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  statement: a⁺ - a⁻ = a
  proof: by
  rw [posPart_def]; rw [negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id Real a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

中文:
引理 posPart_sub_negPart
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  结论: a⁺ - a⁻ = a
  证明: by
  rw [posPart_def]; rw [negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id Real a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

Depends on / 依赖: _root_, _root_.posPart_sub_negPart, cfc_tac, conv_rhs, negPart_def, posPart_def, posPart_sub_negPart
-/
lemma posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : a⁺ - a⁻ = a := by
  rw [posPart_def]; rw [negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id Real a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

section Unique

variable [T2Space A]

@[simp]
/--
lemma `posPart_neg` / 引理 `posPart_neg`

English:
lemma posPart_neg
  given: (a : A)
  statement: (-a)⁺ = a⁻
  proof: by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h => ha (by simpa using h.neg)
    rw [posPart_def]; rw [negPart_def]; rw [cfcₙ_apply_of_not_predicate a ha]; rw [cfcₙ_apply_of_not_predicate _ ha']

@[si

中文:
引理 posPart_neg
  条件: (a : A)
  结论: (-a)⁺ = a⁻
  证明: by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h => ha (by simpa using h.neg)
    rw [posPart_def]; rw [negPart_def]; rw [cfcₙ_apply_of_not_predicate a ha]; rw [cfcₙ_apply_of_not_predicate _ ha']

@[si

Depends on / 依赖: IsSelfAdjoint, h.neg, negPart_def, posPart_def
-/
lemma posPart_neg (a : A) : (-a)⁺ = a⁻ := by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h => ha (by simpa using h.neg)
    rw [posPart_def]; rw [negPart_def]; rw [cfcₙ_apply_of_not_predicate a ha]; rw [cfcₙ_apply_of_not_predicate _ ha']

@[simp]
/--
lemma `negPart_neg` / 引理 `negPart_neg`

English:
lemma negPart_neg
  given: (a : A)
  statement: (-a)⁻ = a⁺
  proof: by
  rw [← eq_comm]; rw [← sub_eq_zero]; rw [← posPart_neg]; rw [neg_neg]; rw [sub_self]

中文:
引理 negPart_neg
  条件: (a : A)
  结论: (-a)⁻ = a⁺
  证明: by
  rw [← eq_comm]; rw [← sub_eq_zero]; rw [← posPart_neg]; rw [neg_neg]; rw [sub_self]

Depends on / 依赖: eq_comm, neg_neg, posPart_neg, sub_eq_zero, sub_self
-/
lemma negPart_neg (a : A) : (-a)⁻ = a⁺ := by
  rw [← eq_comm]; rw [← sub_eq_zero]; rw [← posPart_neg]; rw [neg_neg]; rw [sub_self]

section SMul

variable [StarModule Real A]

@[simp]
/--
lemma `posPart_smul` / 引理 `posPart_smul`

English:
lemma posPart_smul
  given: {r : Real>=0} {a : A}
  statement: (r • a)⁺ = r • a⁺
  proof: by
  by_cases ha : IsSelfAdjoint a
  · simp only [CFC.posPart_def, NNReal.smul_def]
    rw [← cfcₙ_comp_smul ..]; rw [← cfcₙ_smul ..]
    refine cfcₙ_congr fun x hx => ?_
    simp [_root_.posPart_def, mul_max_of_nonneg]
  · obtain (rfl | hr) := eq_or_ne r 0
    · simp
.mpr ha · have := (not_iff_not.

中文:
引理 posPart_smul
  条件: {r : 实数>=0} {a : A}
  结论: (r • a)⁺ = r • a⁺
  证明: by
  by_cases ha : IsSelfAdjoint a
  · simp only [CFC.posPart_def, NNReal.smul_def]
    rw [← cfcₙ_comp_smul ..]; rw [← cfcₙ_smul ..]
    refine cfcₙ_congr fun x hx => ?_
    simp [_root_.posPart_def, mul_max_of_nonneg]
  · obtain (rfl | hr) := eq_or_ne r 0
    · simp
.mpr ha · have := (not_iff_not.

Depends on / 依赖: CFC.posPart_def, IsSelfAdjoint, IsSelfAdjoint.all, NNReal, NNReal.smul_def, _root_, _root_.posPart_def, eq_or_ne, hr.isUnit, isUnit, mul_max_of_nonneg, not_iff_not, not_iff_not.mpr, posPart_def, smul_def, smul_iff
-/
lemma posPart_smul {r : Real>=0} {a : A} : (r • a)⁺ = r • a⁺ := by
  by_cases ha : IsSelfAdjoint a
  · simp only [CFC.posPart_def, NNReal.smul_def]
    rw [← cfcₙ_comp_smul ..]; rw [← cfcₙ_smul ..]
    refine cfcₙ_congr fun x hx => ?_
    simp [_root_.posPart_def, mul_max_of_nonneg]
  · obtain (rfl | hr) := eq_or_ne r 0
    · simp
.mpr ha · have := (not_iff_not.mpr <| (IsSelfAdjoint.all r).smul_iff hr.isUnit (x := a))
      simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha,
        cfcₙ_apply_of_not_predicate _ this]

@[simp]
/--
lemma `negPart_smul` / 引理 `negPart_smul`

English:
lemma negPart_smul
  given: {r : Real>=0} {a : A}
  statement: (r • a)⁻ = r • a⁻
  proof: by
  simpa using posPart_smul (r := r) (a := -a)

中文:
引理 negPart_smul
  条件: {r : 实数>=0} {a : A}
  结论: (r • a)⁻ = r • a⁻
  证明: by
  simpa using posPart_smul (r := r) (a := -a)

Depends on / 依赖: posPart_smul
-/
lemma negPart_smul {r : Real>=0} {a : A} : (r • a)⁻ = r • a⁻ := by
  simpa using posPart_smul (r := r) (a := -a)

/--
lemma `posPart_smul_of_nonneg` / 引理 `posPart_smul_of_nonneg`

English:
lemma posPart_smul_of_nonneg
  given: {r : Real} (hr : 0 <= r) {a : A}
  statement: (r • a)⁺ = r • a⁺
  proof: posPart_smul (r := ⟨r, hr⟩)

中文:
引理 posPart_smul_of_nonneg
  条件: {r : 实数} (hr : 0 <= r) {a : A}
  结论: (r • a)⁺ = r • a⁺
  证明: posPart_smul (r := ⟨r, hr⟩)

Depends on / 依赖: posPart_smul
-/
lemma posPart_smul_of_nonneg {r : Real} (hr : 0 <= r) {a : A} : (r • a)⁺ = r • a⁺ :=
  posPart_smul (r := ⟨r, hr⟩)

/--
lemma `posPart_smul_of_nonpos` / 引理 `posPart_smul_of_nonpos`

English:
lemma posPart_smul_of_nonpos
  given: {r : Real} (hr : r <= 0) {a : A}
  statement: (r • a)⁺ = -r • a⁻
  proof: by
  nth_rw 1 [← neg_neg r]
  rw [neg_smul]; rw [← smul_neg]; rw [posPart_smul_of_nonneg (neg_nonneg.mpr hr)]; rw [posPart_neg]

中文:
引理 posPart_smul_of_nonpos
  条件: {r : 实数} (hr : r <= 0) {a : A}
  结论: (r • a)⁺ = -r • a⁻
  证明: by
  nth_rw 1 [← neg_neg r]
  rw [neg_smul]; rw [← smul_neg]; rw [posPart_smul_of_nonneg (neg_nonneg.mpr hr)]; rw [posPart_neg]

Depends on / 依赖: neg_neg, neg_nonneg, neg_nonneg.mpr, neg_smul, nth_rw, posPart_neg, posPart_smul_of_nonneg, smul_neg
-/
lemma posPart_smul_of_nonpos {r : Real} (hr : r <= 0) {a : A} : (r • a)⁺ = -r • a⁻ := by
  nth_rw 1 [← neg_neg r]
  rw [neg_smul]; rw [← smul_neg]; rw [posPart_smul_of_nonneg (neg_nonneg.mpr hr)]; rw [posPart_neg]

/--
lemma `negPart_smul_of_nonneg` / 引理 `negPart_smul_of_nonneg`

English:
lemma negPart_smul_of_nonneg
  given: {r : Real} (hr : 0 <= r) {a : A}
  statement: (r • a)⁻ = r • a⁻
  proof: by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonpos (by simpa), neg_neg]

中文:
引理 negPart_smul_of_nonneg
  条件: {r : 实数} (hr : 0 <= r) {a : A}
  结论: (r • a)⁻ = r • a⁻
  证明: by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonpos (by simpa), neg_neg]

Depends on / 依赖: conv_lhs, negPart_neg, neg_neg, neg_smul, posPart_smul_of_nonpos
-/
lemma negPart_smul_of_nonneg {r : Real} (hr : 0 <= r) {a : A} : (r • a)⁻ = r • a⁻ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonpos (by simpa), neg_neg]

/--
lemma `negPart_smul_of_nonpos` / 引理 `negPart_smul_of_nonpos`

English:
lemma negPart_smul_of_nonpos
  given: {r : Real} (hr : r <= 0) {a : A}
  statement: (r • a)⁻ = -r • a⁺
  proof: by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonneg (by simpa)]

中文:
引理 negPart_smul_of_nonpos
  条件: {r : 实数} (hr : r <= 0) {a : A}
  结论: (r • a)⁻ = -r • a⁺
  证明: by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonneg (by simpa)]

Depends on / 依赖: HasInjectiveDimensionLT, Injective, conv_lhs, negPart_neg, neg_neg, neg_smul, posPart_smul_of_nonneg
-/
lemma negPart_smul_of_nonpos {r : Real} (hr : r <= 0) {a : A} : (r • a)⁻ = -r • a⁺ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonneg (by simpa)]

end SMul

end Unique

variable [PartialOrder A] [StarOrderedRing A]

@[aesop norm apply (rule_sets := [CStarAlgebra])]
/--
lemma `posPart_nonneg` / 引理 `posPart_nonneg`

English:
lemma posPart_nonneg
  given: (a : A)
  proof: cfcₙ_nonneg (fun x _ => by positivity)

@[aesop norm apply (rule_sets := [CStarAlgebra])]

中文:
引理 posPart_nonneg
  条件: (a : A)
  证明: cfcₙ_nonneg (fun x _ => by positivity)

@[aesop norm apply (rule_sets := [CStarAlgebra])]
-/
lemma posPart_nonneg (a : A) :
    0 <= a⁺ :=
  cfcₙ_nonneg (fun x _ => by positivity)

@[aesop norm apply (rule_sets := [CStarAlgebra])]
/--
lemma `negPart_nonneg` / 引理 `negPart_nonneg`

English:
lemma negPart_nonneg
  given: (a : A)
  proof: cfcₙ_nonneg (fun x _ => by positivity)

中文:
引理 negPart_nonneg
  条件: (a : A)
  证明: cfcₙ_nonneg (fun x _ => by positivity)
-/
lemma negPart_nonneg (a : A) :
    0 <= a⁻ :=
  cfcₙ_nonneg (fun x _ => by positivity)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SelfAdjointDecompose A
  body: ⟨a⁺, a⁻, by cfc_tac, by cfc_tac, (posPart_sub_negPart a).symm⟩

中文:
实例 :
  签名: SelfAdjointDecompose A
  定义体: ⟨a⁺, a⁻, by cfc_tac, by cfc_tac, (posPart_sub_negPart a).symm⟩

Depends on / 依赖: cfc_tac, posPart_sub_negPart
-/
instance : SelfAdjointDecompose A where
  exists_nonneg_sub_nonneg {a} ha := ⟨a⁺, a⁻, by cfc_tac, by cfc_tac, (posPart_sub_negPart a).symm⟩

/--
lemma `posPart_eq_of_eq_sub_negPart` / 引理 `posPart_eq_of_eq_sub_negPart`

English:
lemma posPart_eq_of_eq_sub_negPart
  given: {a b : A} (hab : a = b - a⁻) (hb : 0 <= b := by cfc_tac)
  proof: by
  have ha := hab.symm ▸ hb.isSelfAdjoint.sub (negPart_nonneg a).isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hab
  simpa using hab

中文:
引理 posPart_eq_of_eq_sub_negPart
  条件: {a b : A} (hab : a = b - a⁻) (hb : 0 <= b := by cfc_tac)
  证明: by
  have ha := hab.symm ▸ hb.isSelfAdjoint.sub (negPart_nonneg a).isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hab
  simpa using hab

Depends on / 依赖: cfc_tac, hab.symm, hb.isSelfAdjoint.sub, isSelfAdjoint, negPart_nonneg, nth_rw, posPart_sub_negPart
-/
lemma posPart_eq_of_eq_sub_negPart {a b : A} (hab : a = b - a⁻) (hb : 0 <= b := by cfc_tac) :
    a⁺ = b := by
  have ha := hab.symm ▸ hb.isSelfAdjoint.sub (negPart_nonneg a).isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hab
  simpa using hab

/--
lemma `negPart_eq_of_eq_PosPart_sub` / 引理 `negPart_eq_of_eq_PosPart_sub`

English:
lemma negPart_eq_of_eq_PosPart_sub
  given: {a c : A} (hac : a = a⁺ - c) (hc : 0 <= c := by cfc_tac)
  proof: by
  have ha := hac.symm ▸ (posPart_nonneg a).isSelfAdjoint.sub hc.isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hac
  simpa using hac

中文:
引理 negPart_eq_of_eq_PosPart_sub
  条件: {a c : A} (hac : a = a⁺ - c) (hc : 0 <= c := by cfc_tac)
  证明: by
  have ha := hac.symm ▸ (posPart_nonneg a).isSelfAdjoint.sub hc.isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hac
  simpa using hac

Depends on / 依赖: cfc_tac, hac.symm, hc.isSelfAdjoint, isSelfAdjoint, isSelfAdjoint.sub, nth_rw, posPart_nonneg, posPart_sub_negPart
-/
lemma negPart_eq_of_eq_PosPart_sub {a c : A} (hac : a = a⁺ - c) (hc : 0 <= c := by cfc_tac) :
    a⁻ = c := by
  have ha := hac.symm ▸ (posPart_nonneg a).isSelfAdjoint.sub hc.isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hac
  simpa using hac

/--
lemma `le_posPart` / 引理 `le_posPart`

English:
lemma le_posPart
  given: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  statement: a <= a⁺
  proof: by
  simpa [posPart_sub_negPart a] using sub_le_self a⁺ (negPart_nonneg a)

中文:
引理 le_posPart
  条件: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  结论: a <= a⁺
  证明: by
  simpa [posPart_sub_negPart a] using sub_le_self a⁺ (negPart_nonneg a)

Depends on / 依赖: cfc_tac, negPart_nonneg, posPart_sub_negPart, sub_le_self
-/
lemma le_posPart {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : a <= a⁺ := by
  simpa [posPart_sub_negPart a] using sub_le_self a⁺ (negPart_nonneg a)

/--
lemma `neg_negPart_le` / 引理 `neg_negPart_le`

English:
lemma neg_negPart_le
  given: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  statement: -a⁻ <= a
  proof: by
  simpa only [posPart_sub_negPart a, ← sub_eq_add_neg]
    using le_add_of_nonneg_left (a := -a⁻) (posPart_nonneg a)

中文:
引理 neg_negPart_le
  条件: {a : A} (ha : IsSelfAdjoint a := by cfc_tac)
  结论: -a⁻ <= a
  证明: by
  simpa only [posPart_sub_negPart a, ← sub_eq_add_neg]
    using le_add_of_nonneg_left (a := -a⁻) (posPart_nonneg a)

Depends on / 依赖: ShortComplex, ShortComplex.Splitting.ofHasBinaryBiproduct, Splitting, cfc_tac, le_add_of_nonneg_left, ofHasBinaryBiproduct, posPart_nonneg, posPart_sub_negPart, shortExact, shortExact.hasInjectiveDimensionLT_X, sub_eq_add_neg
-/
lemma neg_negPart_le {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : -a⁻ <= a := by
  simpa only [posPart_sub_negPart a, ← sub_eq_add_neg]
    using le_add_of_nonneg_left (a := -a⁻) (posPart_nonneg a)

variable [NonnegSpectrumClass Real A]

/--
lemma `posPart_eq_self` / 引理 `posPart_eq_self`

English:
lemma posPart_eq_self
  given: (a : A)
  statement: a⁺ = a ↔ 0 <= a
  proof: by
  refine ⟨fun ha => ha ▸ posPart_nonneg a, fun ha => ?_⟩
  conv_rhs => rw [← cfcₙ_id Real a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx => ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

中文:
引理 posPart_eq_self
  条件: (a : A)
  结论: a⁺ = a ↔ 0 <= a
  证明: by
  refine ⟨fun ha => ha ▸ posPart_nonneg a, fun ha => ?_⟩
  conv_rhs => rw [← cfcₙ_id Real a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx => ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

Depends on / 依赖: _root_, _root_.posPart_def, conv_rhs, posPart_def, posPart_nonneg, quasispectrum_nonneg_of_nonneg
-/
lemma posPart_eq_self (a : A) : a⁺ = a ↔ 0 <= a := by
  refine ⟨fun ha => ha ▸ posPart_nonneg a, fun ha => ?_⟩
  conv_rhs => rw [← cfcₙ_id Real a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx => ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

/--
lemma `negPart_eq_zero_iff` / 引理 `negPart_eq_zero_iff`

English:
lemma negPart_eq_zero_iff
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  rw [← posPart_eq_self]; rw [eq_comm (b := a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

中文:
引理 negPart_eq_zero_iff
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  rw [← posPart_eq_self]; rw [eq_comm (b := a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

Depends on / 依赖: cfc_tac, eq_comm, nth_rw, posPart_eq_self, posPart_sub_negPart
-/
lemma negPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁻ = 0 ↔ 0 <= a := by
  rw [← posPart_eq_self]; rw [eq_comm (b := a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

/--
lemma `negPart_eq_neg` / 引理 `negPart_eq_neg`

English:
lemma negPart_eq_neg
  given: (a : A)
  statement: a⁻ = -a ↔ a <= 0
  proof: by
  rw [← neg_inj]; rw [neg_neg]; rw [eq_comm]
  refine ⟨fun ha => by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha => ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def]; rw [← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id R

中文:
引理 negPart_eq_neg
  条件: (a : A)
  结论: a⁻ = -a ↔ a <= 0
  证明: by
  rw [← neg_inj]; rw [neg_neg]; rw [eq_comm]
  refine ⟨fun ha => by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha => ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def]; rw [← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id R

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.neg, Set.mem_neg, Unitization, Unitization.inr_neg, Unitization.quasispectrum, Unitization.quasispectrum_eq_spectrum_inr, conv_lhs, eq_comm, inr_neg, mem_neg, negPart_def, negPart_nonneg, neg_eq, neg_inj, neg_neg, neg_nonneg, neg_nonpos, of_nonneg, quasispectrum
-/
lemma negPart_eq_neg (a : A) : a⁻ = -a ↔ a <= 0 := by
  rw [← neg_inj]; rw [neg_neg]; rw [eq_comm]
  refine ⟨fun ha => by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha => ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def]; rw [← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id Real a]
  refine cfcₙ_congr fun x hx => ?_
  rw [Unitization.quasispectrum_eq_spectrum_inr Real]; rw [← neg_neg x]; rw [← Set.mem_neg]; rw [spectrum.neg_eq]; rw [← Unitization.inr_neg]; rw [← Unitization.quasispectrum_eq_spectrum_inr Real] at hx
  rw [← neg_eq_iff_eq_neg]; rw [eq_comm]
  simpa using quasispectrum_nonneg_of_nonneg _ ha _ hx

/--
lemma `posPart_eq_zero_iff` / 引理 `posPart_eq_zero_iff`

English:
lemma posPart_eq_zero_iff
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  rw [← negPart_eq_neg]; rw [eq_comm (b := -a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

local notation "σₙ" => quasispectrum

中文:
引理 posPart_eq_zero_iff
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  rw [← negPart_eq_neg]; rw [eq_comm (b := -a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

local notation "σₙ" => quasispectrum

Depends on / 依赖: cfc_tac, eq_comm, negPart_eq_neg, nth_rw, posPart_sub_negPart
-/
lemma posPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁺ = 0 ↔ a <= 0 := by
  rw [← negPart_eq_neg]; rw [eq_comm (b := -a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

local notation "σₙ" => quasispectrum

open ContinuousMapZero

variable [IsSemitopologicalRing A] [T2Space A]

set_option backward.isDefEq.respectTransparency false in
open NonUnitalContinuousFunctionalCalculus in
/--
lemma `posPart_negPart_unique` / 引理 `posPart_negPart_unique`

English:
lemma posPart_negPart_unique
  statement: {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
  proof: by
  /- The key idea is to show that `cfcₙ f a = cfcₙ f b + cfcₙ f (-c)` for all real-valued `f`
  continuous on the union of the spectra of `a`, `b`, and `-c`. Then apply this to `f = (·⁺)`.
  The equality holds because both sides constitute star homomorphisms which agree on `f = id` since
  `a = b

中文:
引理 posPart_negPart_unique
  结论: {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
  证明: by
  /- The key idea is to show that `cfcₙ f a = cfcₙ f b + cfcₙ f (-c)` for all real-valued `f`
  continuous on the union of the spectra of `a`, `b`, and `-c`. Then apply this to `f = (·⁺)`.
  The equality holds because both sides constitute star homomorphisms which agree on `f = id` since
  `a = b

Depends on / 依赖: cfc_tac
-/
lemma posPart_negPart_unique {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
    (hb : 0 <= b := by cfc_tac) (hc : 0 <= c := by cfc_tac) :
    a⁺ = b ∧ a⁻ = c := by
  /- The key idea is to show that `cfcₙ f a = cfcₙ f b + cfcₙ f (-c)` for all real-valued `f`
  continuous on the union of the spectra of `a`, `b`, and `-c`. Then apply this to `f = (·⁺)`.
  The equality holds because both sides constitute star homomorphisms which agree on `f = id` since
  `a = b - c`. -/
  /- `a`, `b`, `-c` are selfadjoint. -/
  have hb' : IsSelfAdjoint b := .of_nonneg hb
have hc' : IsSelfAdjoint (-c) := .neg .of_nonneg hc
have ha : IsSelfAdjoint a := habc ▸ hb'.sub .of_nonneg hc
  /- It suffices to show `b = a⁺` since `a⁺ - a⁻ = a = b - c` -/
  rw [and_iff_left_of_imp ?of_b_eq]
  case of_b_eq =>
    rintro rfl
    exact negPart_eq_of_eq_PosPart_sub habc hc
  /- `s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)` is compact and each of these sets are subsets of `s`.
  Moreover, `0 ∈ s`. -/
  let s := σₙ Real a union σₙ Real b union σₙ Real (-c)
  have hs : CompactSpace s := by
refine isCompact_iff_compactSpace.mp (IsCompact.union ?_ ?_).union ?_
    all_goals exact isCompact_quasispectrum _
  obtain ⟨has, hbs, hcs⟩ : σₙ Real a subseteq s ∧ σₙ Real b subseteq s ∧ σₙ Real (-c) subseteq s := by grind
  have : Fact (0 in s) := ⟨by aesop⟩
  /- The continuous functional calculi for functions `f g : C(s, ℝ)₀` applied to `b` and `(-c)`
  are orthogonal (i.e., the product is always zero). -/
  have mul₁ (f g : C(s, Real)₀) :
      (cfcₙHomSuperset hb' hbs f) * (cfcₙHomSuperset hc' hcs g) = 0 := by
    refine f.nonUnitalStarAlgHom_apply_mul_eq_zero _ _ ?id ?star_id
      (cfcₙHomSuperset_continuous hb' hbs)
    case' star_id => rw [star_trivial]
    all_goals
      refine g.mul_nonUnitalStarAlgHom_apply_eq_zero _ _ ?_ ?_
        (cfcₙHomSuperset_continuous hc' hcs)
      all_goals simp only [star_trivial, cfcₙHomSuperset_id hb' hbs,
        cfcₙHomSuperset_id hc' hcs, mul_neg, hbc, neg_zero]
  have mul₂ (f g : C(s, Real)₀) : (cfcₙHomSuperset hc' hcs f) * (cfcₙHomSuperset hb' hbs g) = 0 := by
    simpa only [star_mul, star_zero, ← map_star, star_trivial] using congr(star $(mul₁ g f))
  /- `fun f ↦ cfcₙ f b + cfcₙ f (-c)` defines a star homomorphism `ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` which
  agrees with the star homomorphism `cfcₙ · a : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` since
  `cfcₙ id a = a = b - c = cfcₙ id b + cfcₙ id (-c)`. -/
  let ψ : C(s, Real)₀ ->⋆ₙₐ[Real] A :=
    { (cfcₙHomSuperset hb' hbs : C(s, Real)₀ ->ₗ[Real] A) + (cfcₙHomSuperset hc' hcs : C(s, Real)₀ ->ₗ[Real] A)
        with
      toFun := cfcₙHomSuperset hb' hbs + cfcₙHomSuperset hc' hcs
      map_zero' := by simp [-cfcₙHomSuperset_apply]
      map_mul' := fun f g => by
        simp only [Pi.add_apply, map_mul, mul_add, add_mul, mul₂, add_zero, mul₁,
          zero_add]
      map_star' := fun f => by simp [← map_star] }
  have key : (cfcₙHomSuperset ha has) = ψ :=
    have : ContinuousMapZero.UniqueHom Real A := inferInstance
    ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id s
    (cfcₙHomSuperset ha has) ψ (cfcₙHomSuperset_continuous ha has)
    ((cfcₙHomSuperset_continuous hb' hbs).add (cfcₙHomSuperset_continuous hc' hcs))
    (by simpa [ψ, -cfcₙHomSuperset_apply, cfcₙHomSuperset_id, sub_eq_add_neg] using habc)
  /- Applying the equality of star homomorphisms to the function `(·⁺ : ℝ → ℝ)` we find that
  `b = cfcₙ id b + cfcₙ 0 (-c) = cfcₙ (·⁺) b - cfcₙ (·⁺) (-c) = cfcₙ (·⁺) a = a⁺`, where the
  second equality follows because these functions are equal on the spectra of `b` and `-c`,
  respectively, since `0 ≤ b` and `-c ≤ 0`. -/
  let f : C(s, Real)₀ := ⟨⟨(·⁺), by fun_prop⟩, by simp; norm_cast⟩
  replace key := congr($key f)
  simp only [cfcₙHomSuperset_apply, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk, ψ,
    Pi.add_apply, cfcₙHom_eq_cfcₙ_extend (·⁺)] at key
  symm
  calc
    b = cfcₙ (id : Real -> Real) b + cfcₙ (0 : Real -> Real) (-c) := by simp [cfcₙ_id Real b]
    _ = _ := by
      congr! 1
      all_goals
        refine cfcₙ_congr fun x hx => Eq.symm ?_
        lift x to σₙ Real _ using hx
        simp only [Subtype.val_injective.extend_apply, comp_apply, coe_mk,
          ContinuousMap.coe_mk, Subtype.map_coe, id_eq, _root_.posPart_eq_self, f, Pi.zero_apply,
          posPart_eq_zero]
      · exact quasispectrum_nonneg_of_nonneg b hb x.val x.property
      · obtain ⟨x, hx⟩ := x
        simp only [← neg_nonneg]
        rw [Unitization.quasispectrum_eq_spectrum_inr Real (-c)]; rw [Unitization.inr_neg]; rw [← spectrum.neg_eq]; rw [Set.mem_neg]; rw [← Unitization.quasispectrum_eq_spectrum_inr Real c]
          at hx
        exact quasispectrum_nonneg_of_nonneg c hc _ hx
    _ = _ := key.symm
    _ = a⁺ := by
      refine cfcₙ_congr fun x hx => ?_
      lift x to σₙ Real a using hx
      simp [f]

end CFC

end NonUnital

section Unital

namespace CFC

variable {A : Type*} [Ring A] [Algebra Real A] [StarRing A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
variable [T2Space A]

@[simp]
/--
lemma `posPart_one` / 引理 `posPart_one`

English:
lemma posPart_one
  statement: (1 : A)⁺ = 1
  proof: by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]

中文:
引理 posPart_one
  结论: (1 : A)⁺ = 1
  证明: by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]

Depends on / 依赖: CFC.posPart_def, posPart_def
-/
lemma posPart_one : (1 : A)⁺ = 1 := by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]
/--
lemma `negPart_one` / 引理 `negPart_one`

English:
lemma negPart_one
  statement: (1 : A)⁻ = 0
  proof: by
  rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]

中文:
引理 negPart_one
  结论: (1 : A)⁻ = 0
  证明: by
  rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]

Depends on / 依赖: CFC.negPart_def, negPart_def
-/
lemma negPart_one : (1 : A)⁻ = 0 := by
  rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]
/--
lemma `posPart_algebraMap` / 引理 `posPart_algebraMap`

English:
lemma posPart_algebraMap
  given: (r : Real)
  statement: (algebraMap Real A r)⁺ = algebraMap Real A r⁺
  proof: by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]

中文:
引理 posPart_algebraMap
  条件: (r : 实数)
  结论: (algebraMap 实数 A r)⁺ = algebraMap 实数 A r⁺
  证明: by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]

Depends on / 依赖: CFC.posPart_def, posPart_def
-/
lemma posPart_algebraMap (r : Real) : (algebraMap Real A r)⁺ = algebraMap Real A r⁺ := by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]
  simp

@[simp]
/--
lemma `negPart_algebraMap` / 引理 `negPart_algebraMap`

English:
lemma negPart_algebraMap
  given: (r : Real)
  statement: (algebraMap Real A r)⁻ = algebraMap Real A r⁻
  proof: by
  rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc]
  simp

中文:
引理 negPart_algebraMap
  条件: (r : 实数)
  结论: (algebraMap 实数 A r)⁻ = algebraMap 实数 A r⁻
  证明: by
  rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc]
  simp

Depends on / 依赖: CFC.negPart_def, negPart_def
-/
lemma negPart_algebraMap (r : Real) : (algebraMap Real A r)⁻ = algebraMap Real A r⁻ := by
  rw [CFC.negPart_def]; rw [cfcₙ_eq_cfc]
  simp

open NNReal in
@[simp]
/--
lemma `posPart_algebraMap_nnreal` / 引理 `posPart_algebraMap_nnreal`

English:
lemma posPart_algebraMap_nnreal
  given: (r : Real>=0)
  statement: (algebraMap Real>=0 A r)⁺ = algebraMap Real>=0 A r
  proof: by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]; rw [IsScalarTower.algebraMap_apply Real>=0 Real A]
  simp

中文:
引理 posPart_algebraMap_nnreal
  条件: (r : 实数>=0)
  结论: (algebraMap 实数>=0 A r)⁺ = algebraMap 实数>=0 A r
  证明: by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]; rw [IsScalarTower.algebraMap_apply Real>=0 Real A]
  simp

Depends on / 依赖: CFC.posPart_def, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, posPart_def
-/
lemma posPart_algebraMap_nnreal (r : Real>=0) : (algebraMap Real>=0 A r)⁺ = algebraMap Real>=0 A r := by
  rw [CFC.posPart_def]; rw [cfcₙ_eq_cfc]; rw [IsScalarTower.algebraMap_apply Real>=0 Real A]
  simp

open NNReal in
@[simp]
/--
lemma `posPart_natCast` / 引理 `posPart_natCast`

English:
lemma posPart_natCast
  given: (n : Nat)
  statement: (n : A)⁺ = n
  proof: by
  rw [← map_natCast (algebraMap Real>=0 A)]; rw [posPart_algebraMap_nnreal]

中文:
引理 posPart_natCast
  条件: (n : 自然数)
  结论: (n : A)⁺ = n
  证明: by
  rw [← map_natCast (algebraMap Real>=0 A)]; rw [posPart_algebraMap_nnreal]

Depends on / 依赖: algebraMap, map_natCast, posPart_algebraMap_nnreal
-/
lemma posPart_natCast (n : Nat) : (n : A)⁺ = n := by
  rw [← map_natCast (algebraMap Real>=0 A)]; rw [posPart_algebraMap_nnreal]

end CFC

end Unital

section SpanNonneg

variable {A : Type*} [NonUnitalRing A] [Module Complex A] [SMulCommClass Complex A A] [IsScalarTower Complex A A]
variable [StarRing A] [TopologicalSpace A] [StarModule Complex A]
variable [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]

open Submodule Complex
open scoped ComplexStarModule

/--
lemma `CStarAlgebra.linear_combination_nonneg` / 引理 `CStarAlgebra.linear_combination_nonneg`

English:
lemma CStarAlgebra.linear_combination_nonneg
  given: (x : A)
  proof: by
  rw [CFC.posPart_sub_negPart _ (ℜ x).2]; rw [← smul_sub]; rw [CFC.posPart_sub_negPart _ (ℑ x).2]; rw [realPart_add_I_smul_imaginaryPart x]

中文:
引理 CStarAlgebra.linear_combination_nonneg
  条件: (x : A)
  证明: by
  rw [CFC.posPart_sub_negPart _ (ℜ x).2]; rw [← smul_sub]; rw [CFC.posPart_sub_negPart _ (ℑ x).2]; rw [realPart_add_I_smul_imaginaryPart x]

Depends on / 依赖: CFC.posPart_sub_negPart, posPart_sub_negPart, realPart_add_I_smul_imaginaryPart, smul_sub
-/
lemma CStarAlgebra.linear_combination_nonneg (x : A) :
    ((ℜ x : A)⁺ - (ℜ x : A)⁻) + (I • (ℑ x : A)⁺ - I • (ℑ x : A)⁻) = x := by
  rw [CFC.posPart_sub_negPart _ (ℜ x).2]; rw [← smul_sub]; rw [CFC.posPart_sub_negPart _ (ℑ x).2]; rw [realPart_add_I_smul_imaginaryPart x]

variable [PartialOrder A] [StarOrderedRing A]

/--
lemma `CStarAlgebra.span_nonneg` / 引理 `CStarAlgebra.span_nonneg`

English:
lemma CStarAlgebra.span_nonneg
  statement: Submodule.span Complex {a : A | 0 <= a} = ⊤
  proof: by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← CStarAlgebra.linear_combination_nonneg x]
  apply_rules [sub_mem, Submodule.smul_mem, add_mem]
  all_goals
    refine subset_span ?_
    first | apply CFC.negPart_nonneg | apply CFC.posPart_nonneg

中文:
引理 CStarAlgebra.span_nonneg
  结论: Submodule.span Complex {a : A | 0 <= a} = ⊤
  证明: by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← CStarAlgebra.linear_combination_nonneg x]
  apply_rules [sub_mem, Submodule.smul_mem, add_mem]
  all_goals
    refine subset_span ?_
    first | apply CFC.negPart_nonneg | apply CFC.posPart_nonneg

Depends on / 依赖: CFC.negPart_nonneg, CFC.posPart_nonneg, CStarAlgebra, CStarAlgebra.linear_combination_nonneg, Submodule, Submodule.smul_mem, add_mem, all_goals, apply_rules, eq_top_iff, eq_top_iff.mpr, linear_combination_nonneg, negPart_nonneg, posPart_nonneg, smul_mem, sub_mem, subset_span
-/
lemma CStarAlgebra.span_nonneg : Submodule.span Complex {a : A | 0 <= a} = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← CStarAlgebra.linear_combination_nonneg x]
  apply_rules [sub_mem, Submodule.smul_mem, add_mem]
  all_goals
    refine subset_span ?_
    first | apply CFC.negPart_nonneg | apply CFC.posPart_nonneg

end SpanNonneg
