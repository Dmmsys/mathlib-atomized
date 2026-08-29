/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Extensions with Finite Transcendence Degree

A field extension L/K has finite transcendence degree if
the transcendence degree of L over K is finite.
Equivalently, if L is an algebraic extension of a finitely generated field extension of K.
-/

public section

open IntermediateField

/--
Definition of `FinTrdeg` / `FinTrdeg` 的定义

English:
class FinTrdeg
  parameters: (K L : Type*) [Field K] [Field L] [Algebra K L]
  axioms and operations (1):
    - exists_fg_isAlgebraic((K L)) : exists E : IntermediateField K L, E.FG ∧ Algebra.IsAlgebraic E L

中文:
类 FinTrdeg
  参数: (K L : 类型) [Field K] [Field L] [Algebra K L]
  公理与运算 (1 个):
    - exists_fg_isAlgebraic((K L)) : 存在 E : 整数ermediateField K L, E.FG ∧ Algebra.IsAlgebraic E L
-/
class FinTrdeg (K L : Type*) [Field K] [Field L] [Algebra K L] where
  exists_fg_isAlgebraic (K L) : exists E : IntermediateField K L, E.FG ∧ Algebra.IsAlgebraic E L

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (K L) in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsAlgebraic
  signature: K L] : FinTrdeg K L where
  body: ⟨⊥, IntermediateField.fg_bot, inferInstance⟩

中文:
实例 [Algebra.IsAlgebraic
  签名: K L] : FinTrdeg K L where
  定义体: ⟨⊥, IntermediateField.fg_bot, inferInstance⟩

Depends on / 依赖: IntermediateField, IntermediateField.fg_bot, fg_bot
-/
instance [Algebra.IsAlgebraic K L] : FinTrdeg K L where
  exists_fg_isAlgebraic := ⟨⊥, IntermediateField.fg_bot, inferInstance⟩

variable (K L) in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.EssFiniteType
  signature: K L] : FinTrdeg K L where
  body: ⟨⊤, IntermediateField.fg_top_iff.mpr ‹_›, inferInstance⟩

中文:
实例 [Algebra.EssFiniteType
  签名: K L] : FinTrdeg K L where
  定义体: ⟨⊤, IntermediateField.fg_top_iff.mpr ‹_›, inferInstance⟩

Depends on / 依赖: IntermediateField, IntermediateField.fg_top_iff.mpr, fg_top_iff
-/
instance [Algebra.EssFiniteType K L] : FinTrdeg K L where
  exists_fg_isAlgebraic := ⟨⊤, IntermediateField.fg_top_iff.mpr ‹_›, inferInstance⟩

/--
theorem `finTrdeg_iff_trdeg` / 定理 `finTrdeg_iff_trdeg`

English:
theorem finTrdeg_iff_trdeg
  statement: FinTrdeg K L ↔ Algebra.trdeg K L < .aleph0
  proof: by
  constructor
  · intro ⟨E, fg, alg⟩
    rw [← trdeg_add_eq K E]; rw [trdeg_eq_zero_iff.2 alg]; rw [add_zero]
    rw [← essFiniteType_iff]; rw [Algebra.essFiniteType_iff_exists_subalgebra] at fg
    obtain ⟨S₀, M, fin, islocal⟩ := fg
    rw [← trdeg_add_eq K S₀]; rw [trdeg_eq_zero_iff.2 islocal.i

中文:
定理 finTrdeg_iff_trdeg
  结论: FinTrdeg K L ↔ Algebra.trdeg K L < .aleph0
  证明: by
  constructor
  · intro ⟨E, fg, alg⟩
    rw [← trdeg_add_eq K E]; rw [trdeg_eq_zero_iff.2 alg]; rw [add_zero]
    rw [← essFiniteType_iff]; rw [Algebra.essFiniteType_iff_exists_subalgebra] at fg
    obtain ⟨S₀, M, fin, islocal⟩ := fg
    rw [← trdeg_add_eq K S₀]; rw [trdeg_eq_zero_iff.2 islocal.i

Depends on / 依赖: Algebra, Algebra.essFiniteType_iff_exists_subalgebra, Cardinal, Cardinal.lt_aleph0_iff_set_finite, Finite, add_zero, cardinalMk_eq_trdeg, essFiniteType_iff, essFiniteType_iff_exists_subalgebra, exists_isTranscendenceBasis, hs.cardinalMk_eq_trdeg.trans_lt, isAlgebraic, islocal, islocal.isAlgebraic, lt_aleph0_iff_set_finite, s.Finite, trans_lt, trdeg_add_eq, trdeg_eq_zero_iff, trdeg_lt_aleph0_of_finiteType
-/
theorem finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K L < .aleph0 := by
  constructor
  · intro ⟨E, fg, alg⟩
    rw [← trdeg_add_eq K E]; rw [trdeg_eq_zero_iff.2 alg]; rw [add_zero]
    rw [← essFiniteType_iff]; rw [Algebra.essFiniteType_iff_exists_subalgebra] at fg
    obtain ⟨S₀, M, fin, islocal⟩ := fg
    rw [← trdeg_add_eq K S₀]; rw [trdeg_eq_zero_iff.2 islocal.isAlgebraic]; rw [add_zero]
    exact trdeg_lt_aleph0_of_finiteType
  · intro h
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
    have fin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.1 (hs.cardinalMk_eq_trdeg.trans_lt h)
    constructor
    refine ⟨adjoin K s, fg_adjoin_of_finite fin, ?_⟩
    have alg := hs.isAlgebraic_field
    rwa [Subtype.range_coe] at alg

alias ⟨_, FinTrdeg.of_trdeg⟩ := finTrdeg_iff_trdeg

variable (K L) in
/--
theorem `trdeg_lt_aleph0` / 定理 `trdeg_lt_aleph0`

English:
theorem trdeg_lt_aleph0
  given: [FinTrdeg K L]
  statement: Algebra.trdeg K L < .aleph0
  proof: finTrdeg_iff_trdeg.mp ‹_›

中文:
定理 trdeg_lt_aleph0
  条件: [FinTrdeg K L]
  结论: Algebra.trdeg K L < .aleph0
  证明: finTrdeg_iff_trdeg.mp ‹_›

Depends on / 依赖: finTrdeg_iff_trdeg, finTrdeg_iff_trdeg.mp
-/
theorem trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .aleph0 :=
  finTrdeg_iff_trdeg.mp ‹_›

/--
theorem `FinTrdeg.trans` / 定理 `FinTrdeg.trans`

English:
theorem FinTrdeg.trans
  statement: (K E L : Type*) [Field K] [Field E] [Field L]
  proof: by
  rw [finTrdeg_iff_trdeg]; rw [← Cardinal.lift_lt_aleph0]; rw [← lift_trdeg_add_eq K E L]; rw [Cardinal.add_lt_aleph0_iff]; rw [Cardinal.lift_lt_aleph0]; rw [Cardinal.lift_lt_aleph0]
  exact ⟨trdeg_lt_aleph0 K E, trdeg_lt_aleph0 E L⟩

中文:
定理 FinTrdeg.trans
  结论: (K E L : 类型) [Field K] [Field E] [Field L]
  证明: by
  rw [finTrdeg_iff_trdeg]; rw [← Cardinal.lift_lt_aleph0]; rw [← lift_trdeg_add_eq K E L]; rw [Cardinal.add_lt_aleph0_iff]; rw [Cardinal.lift_lt_aleph0]; rw [Cardinal.lift_lt_aleph0]
  exact ⟨trdeg_lt_aleph0 K E, trdeg_lt_aleph0 E L⟩

Depends on / 依赖: Cardinal, Cardinal.add_lt_aleph0_iff, Cardinal.lift_lt_aleph0, add_lt_aleph0_iff, finTrdeg_iff_trdeg, lift_lt_aleph0, lift_trdeg_add_eq, trdeg_lt_aleph0
-/
theorem FinTrdeg.trans (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FinTrdeg K E] [FinTrdeg E L] : FinTrdeg K L := by
  rw [finTrdeg_iff_trdeg]; rw [← Cardinal.lift_lt_aleph0]; rw [← lift_trdeg_add_eq K E L]; rw [Cardinal.add_lt_aleph0_iff]; rw [Cardinal.lift_lt_aleph0]; rw [Cardinal.lift_lt_aleph0]
  exact ⟨trdeg_lt_aleph0 K E, trdeg_lt_aleph0 E L⟩

/--
theorem `finite_of_isTranscendenceBasis` / 定理 `finite_of_isTranscendenceBasis`

English:
theorem finite_of_isTranscendenceBasis
  statement: [FinTrdeg K L] {ι : Type*} {x : ι -> L}
  proof: by
  rw [← Cardinal.mk_lt_aleph0_iff]; rw [← Cardinal.lift_lt_aleph0]; rw [hx.lift_cardinalMk_eq_trdeg]; rw [Cardinal.lift_lt_aleph0]
  exact trdeg_lt_aleph0 K L

中文:
定理 finite_of_isTranscendenceBasis
  结论: [FinTrdeg K L] {ι : 类型} {x : ι -> L}
  证明: by
  rw [← Cardinal.mk_lt_aleph0_iff]; rw [← Cardinal.lift_lt_aleph0]; rw [hx.lift_cardinalMk_eq_trdeg]; rw [Cardinal.lift_lt_aleph0]
  exact trdeg_lt_aleph0 K L

Depends on / 依赖: Cardinal, Cardinal.lift_lt_aleph0, Cardinal.mk_lt_aleph0_iff, hx.lift_cardinalMk_eq_trdeg, lift_cardinalMk_eq_trdeg, lift_lt_aleph0, mk_lt_aleph0_iff, trdeg_lt_aleph0
-/
theorem finite_of_isTranscendenceBasis [FinTrdeg K L] {ι : Type*} {x : ι -> L}
    (hx : IsTranscendenceBasis K x) : Finite ι := by
  rw [← Cardinal.mk_lt_aleph0_iff]; rw [← Cardinal.lift_lt_aleph0]; rw [hx.lift_cardinalMk_eq_trdeg]; rw [Cardinal.lift_lt_aleph0]
  exact trdeg_lt_aleph0 K L

/--
theorem `finite_of_algebraicIndependent` / 定理 `finite_of_algebraicIndependent`

English:
theorem finite_of_algebraicIndependent
  statement: [FinTrdeg K L] {ι : Type*} {x : ι -> L}
  proof: by
  rw [← Cardinal.mk_lt_aleph0_iff]; rw [← Cardinal.lift_lt_aleph0]
  exact hx.lift_cardinalMk_le_trdeg.trans_lt (Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0 K L))

中文:
定理 finite_of_algebraicIndependent
  结论: [FinTrdeg K L] {ι : 类型} {x : ι -> L}
  证明: by
  rw [← Cardinal.mk_lt_aleph0_iff]; rw [← Cardinal.lift_lt_aleph0]
  exact hx.lift_cardinalMk_le_trdeg.trans_lt (Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0 K L))

Depends on / 依赖: Cardinal, Cardinal.lift_lt_aleph0, Cardinal.lift_lt_aleph0.mpr, Cardinal.mk_lt_aleph0_iff, Decidable, hx.lift_cardinalMk_le_trdeg.trans_lt, lift_cardinalMk_le_trdeg, lift_lt_aleph0, mk_lt_aleph0_iff, trans_lt, trdeg_lt_aleph0
-/
theorem finite_of_algebraicIndependent [FinTrdeg K L] {ι : Type*} {x : ι -> L}
    (hx : AlgebraicIndependent K x) : Finite ι := by
  rw [← Cardinal.mk_lt_aleph0_iff]; rw [← Cardinal.lift_lt_aleph0]
  exact hx.lift_cardinalMk_le_trdeg.trans_lt (Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0 K L))

/--
theorem `FinTrdeg.of_isTranscendenceBasis` / 定理 `FinTrdeg.of_isTranscendenceBasis`

English:
theorem FinTrdeg.of_isTranscendenceBasis
  statement: {ι : Type*} [Finite ι] {x : ι -> L}
  proof: by
  rw [finTrdeg_iff_trdeg]; rw [← Cardinal.lift_lt_aleph0]; rw [← hx.lift_cardinalMk_eq_trdeg]; rw [Cardinal.lift_lt_aleph0]
  exact Cardinal.mk_lt_aleph0

中文:
定理 FinTrdeg.of_isTranscendenceBasis
  结论: {ι : 类型} [Finite ι] {x : ι -> L}
  证明: by
  rw [finTrdeg_iff_trdeg]; rw [← Cardinal.lift_lt_aleph0]; rw [← hx.lift_cardinalMk_eq_trdeg]; rw [Cardinal.lift_lt_aleph0]
  exact Cardinal.mk_lt_aleph0

Depends on / 依赖: Cardinal, Cardinal.lift_lt_aleph0, Cardinal.mk_lt_aleph0, finTrdeg_iff_trdeg, hx.lift_cardinalMk_eq_trdeg, lift_cardinalMk_eq_trdeg, lift_lt_aleph0, mk_lt_aleph0
-/
theorem FinTrdeg.of_isTranscendenceBasis {ι : Type*} [Finite ι] {x : ι -> L}
    (hx : IsTranscendenceBasis K x) : FinTrdeg K L := by
  rw [finTrdeg_iff_trdeg]; rw [← Cardinal.lift_lt_aleph0]; rw [← hx.lift_cardinalMk_eq_trdeg]; rw [Cardinal.lift_lt_aleph0]
  exact Cardinal.mk_lt_aleph0

variable (K L) in
/--
theorem `exists_finset_isTranscendenceBasis` / 定理 `exists_finset_isTranscendenceBasis`

English:
theorem exists_finset_isTranscendenceBasis
  given: [FinTrdeg K L]
  proof: by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  obtain ⟨s, rfl⟩ := Finset.mem_range_coe_iff.2
    (Set.finite_coe_iff.1 (finite_of_isTranscendenceBasis hs))
  exact ⟨s, hs⟩

中文:
定理 exists_finset_isTranscendenceBasis
  条件: [FinTrdeg K L]
  证明: by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  obtain ⟨s, rfl⟩ := Finset.mem_range_coe_iff.2
    (Set.finite_coe_iff.1 (finite_of_isTranscendenceBasis hs))
  exact ⟨s, hs⟩

Depends on / 依赖: Finset, Finset.mem_range_coe_iff, Set.finite_coe_iff, exists_isTranscendenceBasis, finite_coe_iff, finite_of_isTranscendenceBasis, mem_range_coe_iff
-/
theorem exists_finset_isTranscendenceBasis [FinTrdeg K L] :
    exists s : Finset L, IsTranscendenceBasis K ((↑) : s -> L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  obtain ⟨s, rfl⟩ := Finset.mem_range_coe_iff.2
    (Set.finite_coe_iff.1 (finite_of_isTranscendenceBasis hs))
  exact ⟨s, hs⟩
