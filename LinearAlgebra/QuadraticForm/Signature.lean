/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Signature of a quadratic form

We define the signature of a quadratic form over a linearly ordered field, and show that it can be
computed from any sum-of-squares representation.

## Main results and definitions

* `QuadraticForm.sigPos`, `QuadraticForm.sigNeg`: for a quadratic form `Q`, the maximal dimension
  of a subspace on which `Q` is positive-definite (resp. negative-definite).
* `QuadraticForm.sigPos_of_equiv_weightedSumOfSquares`,
  `QuadraticForm.sigNeg_of_equiv_weightedSumOfSquares`: for any isomorphism from `Q` to a
  weighted sum of squares, `Q.sigPos` and `Q.sigNeg` are the number of positive and negative
  weights. (This is the uniqueness part of **Sylvester's law of inertia**; the existence is
  `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared` in file
  `Mathlib.LinearAlgebra.QuadraticForm.Real`.)

## Acknowledgements

This file is based on work carried out by Sina Keller, Philipp Schumann, and Nicolas Trutmann in
the course of their studies at ETH Zürich.
-/

open Finset QuadraticMap

public noncomputable section

variable {R M M' : Type*} [AddCommGroup M] [AddCommGroup M']

section LinearOrder

variable [CommRing R] [LinearOrder R] [Module R M] (Q : QuadraticForm R M)
  [Module R M'] {Q' : QuadraticForm R M'} {V : Submodule R M}

section Equiv
variable {Q}

/--
lemma `QuadraticMap.IsometryEquiv.map_posDef_iff` / 引理 `QuadraticMap.IsometryEquiv.map_posDef_iff`

English:
lemma QuadraticMap.IsometryEquiv.map_posDef_iff
  given: (e : IsometryEquiv Q Q')
  proof: by
  simp [PosDef, -Submodule.mem_map_equiv]

中文:
引理 二次映射.等距等价.map_posDef_iff
  条件: (e : 等距等价 Q Q')
  证明: by
  simp [PosDef, -Submodule.mem_map_equiv]
-/
@[simp] lemma QuadraticMap.IsometryEquiv.map_posDef_iff (e : IsometryEquiv Q Q') :
    (Q'.restrict (V.map e.toLinearMap)).PosDef ↔ (Q.restrict V).PosDef := by
  simp [PosDef, -Submodule.mem_map_equiv]

/--
lemma `QuadraticMap.IsometryEquiv.map_negDef_iff` / 引理 `QuadraticMap.IsometryEquiv.map_negDef_iff`

English:
lemma QuadraticMap.IsometryEquiv.map_negDef_iff
  given: (e : IsometryEquiv Q Q')
  proof: by
  simp [PosDef, -Submodule.mem_map_equiv]

中文:
引理 二次映射.等距等价.map_negDef_iff
  条件: (e : 等距等价 Q Q')
  证明: by
  simp [PosDef, -Submodule.mem_map_equiv]
-/
@[simp] lemma QuadraticMap.IsometryEquiv.map_negDef_iff (e : IsometryEquiv Q Q') :
    ((-Q').restrict (V.map e.toLinearMap)).PosDef ↔ ((-Q).restrict V).PosDef := by
  simp [PosDef, -Submodule.mem_map_equiv]

end Equiv

open scoped Classical in
/-- For quadratic forms on finite-dimensional spaces, the maximal finrank of a positive-definite
subspace of `M`. (Defined as `0` if `M` is infinite-dimensional). -/
/--
Definition of `sigPos` / `sigPos` 的定义

English:
definition sigPos
  signature: : Nat
  body: max' {r in Iic (Module.finrank R M) |
    exists V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef}
  ⟨Module.finrank R (⊥ : Submodule R M), by
    simp only [mem_filter, mem_Iic]
    refine ⟨?_, ⟨⊥, rfl, fun x hx' => (hx' <| Subsingleton.elim x 0).elim⟩⟩
    nontriviality R
    simp

中文:
定义 sigPos
  签名: : 自然数
  定义体: max' {r in Iic (Module.finrank R M) |
    exists V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef}
  ⟨Module.finrank R (⊥ : Submodule R M), by
    simp only [mem_filter, mem_Iic]
    refine ⟨?_, ⟨⊥, rfl, fun x hx' => (hx' <| Subsingleton.elim x 0).elim⟩⟩
    nontriviality R
    simp

Depends on / 依赖: Module, Module.finrank, finrank
-/
def sigPos : Nat := max' {r in Iic (Module.finrank R M) |
    exists V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef}
  ⟨Module.finrank R (⊥ : Submodule R M), by
    simp only [mem_filter, mem_Iic]
    refine ⟨?_, ⟨⊥, rfl, fun x hx' => (hx' <| Subsingleton.elim x 0).elim⟩⟩
    nontriviality R
    simp [finrank_bot]⟩

/--
lemma `sigPos_le_finrank` / 引理 `sigPos_le_finrank`

English:
lemma sigPos_le_finrank
  statement: sigPos Q <= Module.finrank R M
  proof: by
  classical
exact mem_Iic.mp mem_of_mem_filter _ max'_mem _ _

中文:
引理 sigPos_le_finrank
  结论: sigPos Q <= 模.finrank R M
  证明: by
  classical
exact mem_Iic.mp mem_of_mem_filter _ max'_mem _ _

Depends on / 依赖: _mem, classical, mem_Iic, mem_Iic.mp, mem_of_mem_filter
-/
lemma sigPos_le_finrank : sigPos Q <= Module.finrank R M := by
  classical
exact mem_Iic.mp mem_of_mem_filter _ max'_mem _ _

/--
lemma `sigPos_isGreatest` / 引理 `sigPos_isGreatest`

English:
lemma sigPos_isGreatest
  given: [Module.Finite R M] [StrongRankCondition R]
  statement: IsGreatest
  proof: by
  classical
  refine ⟨(mem_filter.mp <| max'_mem _ _).2, ?_⟩
  rintro _ ⟨V, rfl, hV⟩
  apply le_max'
  rw [mem_filter]; rw [mem_Iic]
  exact ⟨V.finrank_le, V, rfl, hV⟩

中文:
引理 sigPos_isGreatest
  条件: [模.有限 R M] [StrongRankCondition R]
  结论: IsGreatest
  证明: by
  classical
  refine ⟨(mem_filter.mp <| max'_mem _ _).2, ?_⟩
  rintro _ ⟨V, rfl, hV⟩
  apply le_max'
  rw [mem_filter]; rw [mem_Iic]
  exact ⟨V.finrank_le, V, rfl, hV⟩

Depends on / 依赖: V.finrank_le, _mem, classical, finrank_le, le_max, mem_Iic, mem_filter, mem_filter.mp
-/
lemma sigPos_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
    {r | exists V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef} (sigPos Q) := by
  classical
  refine ⟨(mem_filter.mp <| max'_mem _ _).2, ?_⟩
  rintro _ ⟨V, rfl, hV⟩
  apply le_max'
  rw [mem_filter]; rw [mem_Iic]
  exact ⟨V.finrank_le, V, rfl, hV⟩

/--
lemma `exists_finrank_eq_sigPos_and_posDef` / 引理 `exists_finrank_eq_sigPos_and_posDef`

English:
lemma exists_finrank_eq_sigPos_and_posDef
  given: [Module.Finite R M] [StrongRankCondition R]
  proof: (sigPos_isGreatest Q).1

中文:
引理 存在_finrank_eq_sigPos_and_posDef
  条件: [模.有限 R M] [StrongRankCondition R]
  证明: (sigPos_isGreatest Q).1

Depends on / 依赖: sigPos_isGreatest
-/
lemma exists_finrank_eq_sigPos_and_posDef [Module.Finite R M] [StrongRankCondition R] :
    exists V : Submodule R M, Module.finrank R V = sigPos Q ∧ (Q.restrict V).PosDef :=
  (sigPos_isGreatest Q).1

/--
lemma `le_sigPos_of_posDef` / 引理 `le_sigPos_of_posDef`

English:
lemma le_sigPos_of_posDef
  statement: [Module.Finite R M] [StrongRankCondition R]
  proof: (sigPos_isGreatest Q).2 ⟨V, by tauto⟩

中文:
引理 le_sigPos_of_posDef
  结论: [模.有限 R M] [StrongRankCondition R]
  证明: (sigPos_isGreatest Q).2 ⟨V, by tauto⟩

Depends on / 依赖: sigPos_isGreatest
-/
lemma le_sigPos_of_posDef [Module.Finite R M] [StrongRankCondition R]
    {V : Submodule R M} (hV : (Q.restrict V).PosDef) :
    Module.finrank R V <= sigPos Q :=
  (sigPos_isGreatest Q).2 ⟨V, by tauto⟩

/--
Definition of `sigNeg` / `sigNeg` 的定义

English:
definition sigNeg
  signature: : Nat
  body: sigPos (-Q)

中文:
定义 sigNeg
  签名: : 自然数
  定义体: sigPos (-Q)

Depends on / 依赖: sigPos
-/
def sigNeg : Nat := sigPos (-Q)

/--
lemma `sigNeg_isGreatest` / 引理 `sigNeg_isGreatest`

English:
lemma sigNeg_isGreatest
  given: [Module.Finite R M] [StrongRankCondition R]
  statement: IsGreatest
  proof: sigPos_isGreatest (-Q)

中文:
引理 sigNeg_isGreatest
  条件: [模.有限 R M] [StrongRankCondition R]
  结论: IsGreatest
  证明: sigPos_isGreatest (-Q)

Depends on / 依赖: sigPos_isGreatest
-/
lemma sigNeg_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
    {r | exists V : Submodule R M, Module.finrank R V = r ∧ ((-Q).restrict V).PosDef} (sigNeg Q) :=
  sigPos_isGreatest (-Q)

/--
lemma `exists_finrank_eq_sigNeg_and_negDef` / 引理 `exists_finrank_eq_sigNeg_and_negDef`

English:
lemma exists_finrank_eq_sigNeg_and_negDef
  given: [Module.Finite R M] [StrongRankCondition R]
  proof: exists_finrank_eq_sigPos_and_posDef (-Q)

中文:
引理 存在_finrank_eq_sigNeg_and_negDef
  条件: [模.有限 R M] [StrongRankCondition R]
  证明: exists_finrank_eq_sigPos_and_posDef (-Q)

Depends on / 依赖: exists_finrank_eq_sigPos_and_posDef
-/
lemma exists_finrank_eq_sigNeg_and_negDef [Module.Finite R M] [StrongRankCondition R] :
    exists V : Submodule R M, Module.finrank R V = sigNeg Q ∧ ((-Q).restrict V).PosDef :=
  exists_finrank_eq_sigPos_and_posDef (-Q)

/--
lemma `le_sigNeg_of_negDef` / 引理 `le_sigNeg_of_negDef`

English:
lemma le_sigNeg_of_negDef
  statement: [Module.Finite R M] [StrongRankCondition R]
  proof: le_sigPos_of_posDef (-Q) hV

中文:
引理 le_sigNeg_of_negDef
  结论: [模.有限 R M] [StrongRankCondition R]
  证明: le_sigPos_of_posDef (-Q) hV

Depends on / 依赖: le_sigPos_of_posDef
-/
lemma le_sigNeg_of_negDef [Module.Finite R M] [StrongRankCondition R]
    {V : Submodule R M} (hV : ((-Q).restrict V).PosDef) :
    Module.finrank R V <= sigNeg Q :=
  le_sigPos_of_posDef (-Q) hV

variable {Q}

/--
lemma `sigPos_neg` / 引理 `sigPos_neg`

English:
lemma sigPos_neg
  statement: sigPos (-Q) = sigNeg Q
  proof: by rfl -- `by` needed since def not exposed

中文:
引理 sigPos_neg
  结论: sigPos (-Q) = sigNeg Q
  证明: by rfl -- `by` needed since def not exposed
-/
@[simp] lemma sigPos_neg : sigPos (-Q) = sigNeg Q := by rfl -- `by` needed since def not exposed

/--
lemma `sigNeg_neg` / 引理 `sigNeg_neg`

English:
lemma sigNeg_neg
  statement: sigNeg (-Q) = sigPos Q
  proof: by rw [← sigPos_neg, neg_neg]

中文:
引理 sigNeg_neg
  结论: sigNeg (-Q) = sigPos Q
  证明: by rw [← sigPos_neg, neg_neg]
-/
@[simp] lemma sigNeg_neg : sigNeg (-Q) = sigPos Q := by rw [← sigPos_neg, neg_neg]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `QuadraticMap.Equivalent.sigPos_eq` / 引理 `QuadraticMap.Equivalent.sigPos_eq`

English:
lemma QuadraticMap.Equivalent.sigPos_eq
  given: (h : Equivalent Q Q')
  statement: sigPos Q = sigPos Q'
  proof: by
  obtain ⟨e⟩ := h
  unfold sigPos
  congr! with j
  · apply (Submodule.orderIsoMapComap e.toLinearEquiv).exists_congr
    intro V
    refine .and ?_ (IsometryEquiv.map_posDef_iff _).symm
    revert j
    rw [eq_iff_eq_cancel_right]
    exact (e.finrank_map_eq _).symm
  · exact e.toLinearEquiv.fin

中文:
引理 二次映射.Equivalent.sigPos_eq
  条件: (h : Equivalent Q Q')
  结论: sigPos Q = sigPos Q'
  证明: by
  obtain ⟨e⟩ := h
  unfold sigPos
  congr! with j
  · apply (Submodule.orderIsoMapComap e.toLinearEquiv).exists_congr
    intro V
    refine .and ?_ (IsometryEquiv.map_posDef_iff _).symm
    revert j
    rw [eq_iff_eq_cancel_right]
    exact (e.finrank_map_eq _).symm
  · exact e.toLinearEquiv.fin

Depends on / 依赖: IsometryEquiv, IsometryEquiv.map_posDef_iff, Submodule, Submodule.orderIsoMapComap, e.finrank_map_eq, e.toLinearEquiv, e.toLinearEquiv.finrank_eq, eq_iff_eq_cancel_right, exists_congr, finrank_eq, finrank_map_eq, map_posDef_iff, orderIsoMapComap, revert, sigPos, toLinearEquiv
-/
lemma QuadraticMap.Equivalent.sigPos_eq (h : Equivalent Q Q') : sigPos Q = sigPos Q' := by
  obtain ⟨e⟩ := h
  unfold sigPos
  congr! with j
  · apply (Submodule.orderIsoMapComap e.toLinearEquiv).exists_congr
    intro V
    refine .and ?_ (IsometryEquiv.map_posDef_iff _).symm
    revert j
    rw [eq_iff_eq_cancel_right]
    exact (e.finrank_map_eq _).symm
  · exact e.toLinearEquiv.finrank_eq

/--
lemma `QuadraticMap.Equivalent.sigNeg_eq` / 引理 `QuadraticMap.Equivalent.sigNeg_eq`

English:
lemma QuadraticMap.Equivalent.sigNeg_eq
  given: (h : Equivalent Q Q')
  statement: sigNeg Q = sigNeg Q'
  proof: sigPos_eq match h with | ⟨e⟩ => ⟨e, by simp⟩

中文:
引理 二次映射.Equivalent.sigNeg_eq
  条件: (h : Equivalent Q Q')
  结论: sigNeg Q = sigNeg Q'
  证明: sigPos_eq match h with | ⟨e⟩ => ⟨e, by simp⟩

Depends on / 依赖: sigPos_eq
-/
lemma QuadraticMap.Equivalent.sigNeg_eq (h : Equivalent Q Q') : sigNeg Q = sigNeg Q' :=
sigPos_eq match h with | ⟨e⟩ => ⟨e, by simp⟩

end LinearOrder

section Field
namespace QuadraticForm

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [Module 𝕜 M] [Module 𝕜 M'] {Q : QuadraticForm 𝕜 M}

/--
lemma `sigPos_add_finrank_le_of_nonpos` / 引理 `sigPos_add_finrank_le_of_nonpos`

English:
lemma sigPos_add_finrank_le_of_nonpos
  statement: [FiniteDimensional 𝕜 M]
  proof: by
  obtain ⟨Vp, hr, hVp⟩ := exists_finrank_eq_sigPos_and_posDef Q
  rw [← hr]
  apply Submodule.finrank_add_finrank_le_of_disjoint
  intro W hWp hWm
  rw [le_bot_iff]; rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx'
  have := hVp ⟨x, hWp hx⟩ (by simpa using hx')
  have := hV x (hWm hx)
  gri

中文:
引理 sigPos_add_finrank_le_of_nonpos
  结论: [有限维 𝕜 M]
  证明: by
  obtain ⟨Vp, hr, hVp⟩ := exists_finrank_eq_sigPos_and_posDef Q
  rw [← hr]
  apply Submodule.finrank_add_finrank_le_of_disjoint
  intro W hWp hWm
  rw [le_bot_iff]; rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx'
  have := hVp ⟨x, hWp hx⟩ (by simpa using hx')
  have := hV x (hWm hx)
  gri

Depends on / 依赖: Submodule, Submodule.eq_bot_iff, Submodule.finrank_add_finrank_le_of_disjoint, eq_bot_iff, exists_finrank_eq_sigPos_and_posDef, finrank_add_finrank_le_of_disjoint, le_bot_iff, restrict_apply
-/
lemma sigPos_add_finrank_le_of_nonpos [FiniteDimensional 𝕜 M]
    {V : Subspace 𝕜 M} (hV : forall x in V, Q x <= 0) :
    sigPos Q + Module.finrank 𝕜 V <= Module.finrank 𝕜 M := by
  obtain ⟨Vp, hr, hVp⟩ := exists_finrank_eq_sigPos_and_posDef Q
  rw [← hr]
  apply Submodule.finrank_add_finrank_le_of_disjoint
  intro W hWp hWm
  rw [le_bot_iff]; rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx'
  have := hVp ⟨x, hWp hx⟩ (by simpa using hx')
  have := hV x (hWm hx)
  grind [restrict_apply]

variable {ι : Type*} [Fintype ι] {w : ι -> 𝕜} [IsStrictOrderedRing 𝕜]

/--
lemma `posDef_spanSubset` / 引理 `posDef_spanSubset`

English:
lemma posDef_spanSubset
  given: (s : Set ι) (hs : forall i in s, 0 < w i)
  proof: by (weightedSumSquares 𝕜 w).restrict (Pi.spanSubset 𝕜 s)
  intro ⟨v, hv⟩ hv'
  rw [restrict_apply]; rw [weightedSumSquares_apply]
  apply sum_pos'
  · intro i _
    by_cases hi : i in s
    · exact smul_nonneg (hs i hi).le (mul_self_nonneg _)
    · simp [Pi.mem_spanSubset_iff.mp hv i hi]
  · simp on

中文:
引理 posDef_spanSubset
  条件: (s : 集合 ι) (hs : 对任意 i in s, 0 < w i)
  证明: by (weightedSumSquares 𝕜 w).restrict (Pi.spanSubset 𝕜 s)
  intro ⟨v, hv⟩ hv'
  rw [restrict_apply]; rw [weightedSumSquares_apply]
  apply sum_pos'
  · intro i _
    by_cases hi : i in s
    · exact smul_nonneg (hs i hi).le (mul_self_nonneg _)
    · simp [Pi.mem_spanSubset_iff.mp hv i hi]
  · simp on
-/
private lemma posDef_spanSubset (s : Set ι) (hs : forall i in s, 0 < w i) :
.PosDef := by (weightedSumSquares 𝕜 w).restrict (Pi.spanSubset 𝕜 s)
  intro ⟨v, hv⟩ hv'
  rw [restrict_apply]; rw [weightedSumSquares_apply]
  apply sum_pos'
  · intro i _
    by_cases hi : i in s
    · exact smul_nonneg (hs i hi).le (mul_self_nonneg _)
    · simp [Pi.mem_spanSubset_iff.mp hv i hi]
  · simp only [ne_eq, Submodule.mk_eq_zero, funext_iff, not_forall, Pi.zero_apply] at hv'
    obtain ⟨i, hi⟩ := hv'
    refine ⟨i, mem_univ _, ?_⟩
    have : i in s := by
      contrapose hi
      exact Pi.mem_spanSubset_iff.mp hv i hi
    exact smul_pos (hs i this) (mul_self_pos.mpr hi)

/--
lemma `negSemidef_spanSubset` / 引理 `negSemidef_spanSubset`

English:
lemma negSemidef_spanSubset
  given: (s : Set ι) (hs : forall i in s, w i <= 0)
  proof: by
  intro x hx
  simp only [weightedSumSquares_apply, smul_eq_mul]
  apply sum_nonpos
  intro i _
  by_cases hi : i in s
  · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi) (mul_self_nonneg _)
  · rw [Pi.mem_spanSubset_iff.mp hx i hi, mul_zero, mul_zero]

中文:
引理 negSemidef_spanSubset
  条件: (s : 集合 ι) (hs : 对任意 i in s, w i <= 0)
  证明: by
  intro x hx
  simp only [weightedSumSquares_apply, smul_eq_mul]
  apply sum_nonpos
  intro i _
  by_cases hi : i in s
  · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi) (mul_self_nonneg _)
  · rw [Pi.mem_spanSubset_iff.mp hx i hi, mul_zero, mul_zero]
-/
private lemma negSemidef_spanSubset (s : Set ι) (hs : forall i in s, w i <= 0) :
    forall x in Pi.spanSubset 𝕜 s, (weightedSumSquares 𝕜 w) x <= 0 := by
  intro x hx
  simp only [weightedSumSquares_apply, smul_eq_mul]
  apply sum_nonpos
  intro i _
  by_cases hi : i in s
  · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi) (mul_self_nonneg _)
  · rw [Pi.mem_spanSubset_iff.mp hx i hi, mul_zero, mul_zero]

/--
lemma `sigPos_weightedSumSquares` / 引理 `sigPos_weightedSumSquares`

English:
lemma sigPos_weightedSumSquares
  proof: by
  let p : Set ι := {i | 0 < w i}
  let m : Set ι := {i | w i <= 0}
  convert_to sigPos _ = p.ncard
  have : p.ncard + m.ncard = Nat.card ι := by
    convert! Set.ncard_add_ncard_compl p
    ext
    grind
  have : p.ncard <= sigPos (weightedSumSquares 𝕜 w) :=
    (sigPos_isGreatest _).2 ⟨Pi.spanSu

中文:
引理 sigPos_weightedSumSquares
  证明: by
  let p : Set ι := {i | 0 < w i}
  let m : Set ι := {i | w i <= 0}
  convert_to sigPos _ = p.ncard
  have : p.ncard + m.ncard = Nat.card ι := by
    convert! Set.ncard_add_ncard_compl p
    ext
    grind
  have : p.ncard <= sigPos (weightedSumSquares 𝕜 w) :=
    (sigPos_isGreatest _).2 ⟨Pi.spanSu

Depends on / 依赖: Nat.card, Pi.dim_spanSubset, Pi.spanSubset, Set.ncard_add_ncard_compl, convert, convert_to, dim_spanSubset, m.ncard, ncard_add_ncard_compl, negSemidef_spanSubset, p.ncard, posDef_spanSubset, sigPos, sigPos_add_finrank_le_of_nonpos, sigPos_isGreatest, spanSubset, weightedSumSquares
-/
lemma sigPos_weightedSumSquares :
    sigPos (weightedSumSquares 𝕜 w) = {i | 0 < w i}.ncard := by
  let p : Set ι := {i | 0 < w i}
  let m : Set ι := {i | w i <= 0}
  convert_to sigPos _ = p.ncard
  have : p.ncard + m.ncard = Nat.card ι := by
    convert! Set.ncard_add_ncard_compl p
    ext
    grind
  have : p.ncard <= sigPos (weightedSumSquares 𝕜 w) :=
    (sigPos_isGreatest _).2 ⟨Pi.spanSubset 𝕜 p, Pi.dim_spanSubset,
      posDef_spanSubset p (by grind)⟩
  suffices sigPos (weightedSumSquares 𝕜 w) + m.ncard <= Nat.card ι by lia
simpa using sigPos_add_finrank_le_of_nonpos negSemidef_spanSubset m (fun _ hi => hi)

/--
lemma `sigNeg_weightedSumSquares` / 引理 `sigNeg_weightedSumSquares`

English:
lemma sigNeg_weightedSumSquares
  proof: by
  simp only [sigNeg]
  convert! sigPos_weightedSumSquares (w := -w) using 2
  · ext; simp
  · simp

中文:
引理 sigNeg_weightedSumSquares
  证明: by
  simp only [sigNeg]
  convert! sigPos_weightedSumSquares (w := -w) using 2
  · ext; simp
  · simp

Depends on / 依赖: convert, sigNeg, sigPos_weightedSumSquares
-/
lemma sigNeg_weightedSumSquares :
    sigNeg (weightedSumSquares 𝕜 w) = {i | w i < 0}.ncard := by
  simp only [sigNeg]
  convert! sigPos_weightedSumSquares (w := -w) using 2
  · ext; simp
  · simp

/--
lemma `sigPos_add_sigNeg_add_radical₁` / 引理 `sigPos_add_sigNeg_add_radical₁`

English:
lemma sigPos_add_sigNeg_add_radical₁
  proof: by
  rw [radical_weightedSumSquares]; rw [sigPos_weightedSumSquares]; rw [sigNeg_weightedSumSquares]; rw [Pi.dim_spanSubset]
  calc {i | 0 < w i}.ncard + {i | w i < 0}.ncard + {i | w i = 0}.ncard
  _ = {i | 0 < w i}.ncard + {i | w i <= 0}.ncard := by
    rw [add_assoc]; rw [add_left_cancel_iff]; rw 

中文:
引理 sigPos_add_sigNeg_add_radical₁
  证明: by
  rw [radical_weightedSumSquares]; rw [sigPos_weightedSumSquares]; rw [sigNeg_weightedSumSquares]; rw [Pi.dim_spanSubset]
  calc {i | 0 < w i}.ncard + {i | w i < 0}.ncard + {i | w i = 0}.ncard
  _ = {i | 0 < w i}.ncard + {i | w i <= 0}.ncard := by
    rw [add_assoc]; rw [add_left_cancel_iff]; rw 
-/
private lemma sigPos_add_sigNeg_add_radical₁ :
    sigPos (weightedSumSquares 𝕜 w) + sigNeg (weightedSumSquares 𝕜 w) +
      Module.finrank 𝕜 (weightedSumSquares 𝕜 w).radical = Nat.card ι := by
  rw [radical_weightedSumSquares]; rw [sigPos_weightedSumSquares]; rw [sigNeg_weightedSumSquares]; rw [Pi.dim_spanSubset]
  calc {i | 0 < w i}.ncard + {i | w i < 0}.ncard + {i | w i = 0}.ncard
  _ = {i | 0 < w i}.ncard + {i | w i <= 0}.ncard := by
    rw [add_assoc]; rw [add_left_cancel_iff]; rw [← Set.ncard_union_eq]
    · congr! 1
      ext
      grind
    · grind [disjoint_iff_ne]
  _ = Set.univ.ncard := by
    rw [← Set.ncard_union_eq]
    · congr! 1
      ext
      grind [le_iff_lt_or_eq]
    · grind [disjoint_iff_ne]
  _ = Nat.card ι := Set.ncard_univ _

/--
lemma `sigPos_add_sigNeg_add_radical` / 引理 `sigPos_add_sigNeg_add_radical`

English:
lemma sigPos_add_sigNeg_add_radical
  given: [FiniteDimensional 𝕜 M]
  proof: by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w, e⟩ := Q.equivalent_weightedSumSquares
  rw [e.sigPos_eq]; rw [e.sigNeg_eq]; rw [e.rank_radical_eq]
  convert! QuadraticForm.sigPos_add_sigNeg_add_radical₁ (w := w)
  exact Eq.symm (Nat.card_fin (Module.finrank 𝕜 M))

中文:
引理 sigPos_add_sigNeg_add_radical
  条件: [有限维 𝕜 M]
  证明: by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w, e⟩ := Q.equivalent_weightedSumSquares
  rw [e.sigPos_eq]; rw [e.sigNeg_eq]; rw [e.rank_radical_eq]
  convert! QuadraticForm.sigPos_add_sigNeg_add_radical₁ (w := w)
  exact Eq.symm (Nat.card_fin (Module.finrank 𝕜 M))

Depends on / 依赖: Eq.symm, Invertible, Module, Module.finrank, Nat.card_fin, NeZero, NeZero.ne, Q.equivalent_weightedSumSquares, QuadraticForm, QuadraticForm.sigPos_add_sigNeg_add_radical, card_fin, convert, e.rank_radical_eq, e.sigNeg_eq, e.sigPos_eq, equivalent_weightedSumSquares, finrank, invertibleOfNonzero, rank_radical_eq, sigNeg_eq
-/
lemma sigPos_add_sigNeg_add_radical [FiniteDimensional 𝕜 M] :
    sigPos Q + sigNeg Q + Module.finrank 𝕜 Q.radical = Module.finrank 𝕜 M := by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w, e⟩ := Q.equivalent_weightedSumSquares
  rw [e.sigPos_eq]; rw [e.sigNeg_eq]; rw [e.rank_radical_eq]
  convert! QuadraticForm.sigPos_add_sigNeg_add_radical₁ (w := w)
  exact Eq.symm (Nat.card_fin (Module.finrank 𝕜 M))

/--
lemma `sigPos_of_equiv_weightedSumSquares` / 引理 `sigPos_of_equiv_weightedSumSquares`

English:
lemma sigPos_of_equiv_weightedSumSquares
  given: (hQ : Equivalent Q (weightedSumSquares 𝕜 w))
  proof: by
  rw [hQ.sigPos_eq]
  exact sigPos_weightedSumSquares

中文:
引理 sigPos_of_equiv_weightedSumSquares
  条件: (hQ : Equivalent Q (weightedSumSquares 𝕜 w))
  证明: by
  rw [hQ.sigPos_eq]
  exact sigPos_weightedSumSquares

Depends on / 依赖: hQ.sigPos_eq, sigPos_eq, sigPos_weightedSumSquares
-/
lemma sigPos_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    sigPos Q = {i | 0 < w i}.ncard := by
  rw [hQ.sigPos_eq]
  exact sigPos_weightedSumSquares

/--
lemma `sigNeg_of_equiv_weightedSumSquares` / 引理 `sigNeg_of_equiv_weightedSumSquares`

English:
lemma sigNeg_of_equiv_weightedSumSquares
  given: (hQ : Equivalent Q (weightedSumSquares 𝕜 w))
  proof: by
  rw [hQ.sigNeg_eq]
  exact sigNeg_weightedSumSquares

中文:
引理 sigNeg_of_equiv_weightedSumSquares
  条件: (hQ : Equivalent Q (weightedSumSquares 𝕜 w))
  证明: by
  rw [hQ.sigNeg_eq]
  exact sigNeg_weightedSumSquares

Depends on / 依赖: hQ.sigNeg_eq, sigNeg_eq, sigNeg_weightedSumSquares
-/
lemma sigNeg_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    sigNeg Q = {i | w i < 0}.ncard := by
  rw [hQ.sigNeg_eq]
  exact sigNeg_weightedSumSquares

end QuadraticForm
