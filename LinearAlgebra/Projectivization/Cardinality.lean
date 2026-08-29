/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Finite.Sum
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Cardinality of projective spaces

We compute the cardinality of `ℙ k V` if `k` is a finite field.

-/

@[expose] public section

namespace Projectivization

open scoped LinearAlgebra.Projectivization

section

variable (k V : Type*) [DivisionRing k] [AddCommGroup V] [Module k V]

/--
Definition of `equivQuotientOrbitRel` / `equivQuotientOrbitRel` 的定义

English:
definition equivQuotientOrbitRel
  signature: : ℙ k V ≃ Quotient (MulAction.orbitRel kˣ { v : V // v != 0 })
  body: Quotient.congr (Equiv.refl _) (fun x y => (Units.orbitRel_nonZero_iff k V x y).symm)

中文:
定义 equivQuotientOrbitRel
  签名: : ℙ k V ≃ 商 (乘法作用.orbitRel kˣ { v : V // v != 0 })
  定义体: Quotient.congr (Equiv.refl _) (fun x y => (Units.orbitRel_nonZero_iff k V x y).symm)

Depends on / 依赖: Equiv.refl, Quotient, Quotient.congr, Regular, Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure, Units.orbitRel_nonZero_iff, of_sigmaCompactSpace_of_isLocallyFiniteMeasure, orbitRel_nonZero_iff
-/
def equivQuotientOrbitRel : ℙ k V ≃ Quotient (MulAction.orbitRel kˣ { v : V // v != 0 }) :=
  Quotient.congr (Equiv.refl _) (fun x y => (Units.orbitRel_nonZero_iff k V x y).symm)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `nonZeroEquivProjectivizationProdUnits` / `nonZeroEquivProjectivizationProdUnits` 的定义

English:
definition nonZeroEquivProjectivizationProdUnits
  signature: : { v : V // v != 0 } ≃ ℙ k V × kˣ
  body: let e := MulAction.selfEquivOrbitsQuotientProd fun b => by
    rw [(Units.nonZeroSubMul k V).stabilizer_of_subMul]; rw [Module.stabilizer_units_eq_bot_of_ne_zero k b.property]
  e.trans (Equiv.prodCongrLeft (fun _ => (equivQuotientOrbitRel k V).symm))

中文:
定义 nonZeroEquivProjectivizationProdUnits
  签名: : { v : V // v != 0 } ≃ ℙ k V × kˣ
  定义体: let e := MulAction.selfEquivOrbitsQuotientProd fun b => by
    rw [(Units.nonZeroSubMul k V).stabilizer_of_subMul]; rw [Module.stabilizer_units_eq_bot_of_ne_zero k b.property]
  e.trans (Equiv.prodCongrLeft (fun _ => (equivQuotientOrbitRel k V).symm))

Depends on / 依赖: Equiv.prodCongrLeft, Module, Module.stabilizer_units_eq_bot_of_ne_zero, MulAction, MulAction.selfEquivOrbitsQuotientProd, Units.nonZeroSubMul, b.property, e.trans, equivQuotientOrbitRel, nonZeroSubMul, prodCongrLeft, property, selfEquivOrbitsQuotientProd, stabilizer_of_subMul, stabilizer_units_eq_bot_of_ne_zero
-/
noncomputable def nonZeroEquivProjectivizationProdUnits : { v : V // v != 0 } ≃ ℙ k V × kˣ :=
let e := MulAction.selfEquivOrbitsQuotientProd fun b => by
    rw [(Units.nonZeroSubMul k V).stabilizer_of_subMul]; rw [Module.stabilizer_units_eq_bot_of_ne_zero k b.property]
  e.trans (Equiv.prodCongrLeft (fun _ => (equivQuotientOrbitRel k V).symm))

/--
Instance `isEmpty_of_subsingleton` / 实例 `isEmpty_of_subsingleton`

English:
instance isEmpty_of_subsingleton
  signature: [Subsingleton V]
  body: by
  have : IsEmpty { v : V // v != 0 } := ⟨fun v => v.2 (Subsingleton.elim v.1 0)⟩
  simpa using (nonZeroEquivProjectivizationProdUnits k V).symm.isEmpty

中文:
实例 isEmpty_of_subsingleton
  签名: [子单例 V]
  定义体: by
  have : IsEmpty { v : V // v != 0 } := ⟨fun v => v.2 (Subsingleton.elim v.1 0)⟩
  simpa using (nonZeroEquivProjectivizationProdUnits k V).symm.isEmpty

Depends on / 依赖: IsEmpty, Subsingleton, Subsingleton.elim, isEmpty, nonZeroEquivProjectivizationProdUnits, symm.isEmpty
-/
instance isEmpty_of_subsingleton [Subsingleton V] : IsEmpty (ℙ k V) := by
  have : IsEmpty { v : V // v != 0 } := ⟨fun v => v.2 (Subsingleton.elim v.1 0)⟩
  simpa using (nonZeroEquivProjectivizationProdUnits k V).symm.isEmpty

/--
Instance `finite_of_finite` / 实例 `finite_of_finite`

English:
instance finite_of_finite
  signature: [Finite V]
  body: have : Finite (ℙ k V × kˣ) := Finite.of_equiv _ (nonZeroEquivProjectivizationProdUnits k V)
  Finite.prod_left kˣ

中文:
实例 finite_of_finite
  签名: [有限 V]
  定义体: have : Finite (ℙ k V × kˣ) := Finite.of_equiv _ (nonZeroEquivProjectivizationProdUnits k V)
  Finite.prod_left kˣ

Depends on / 依赖: Finite, Finite.of_equiv, Finite.prod_left, nonZeroEquivProjectivizationProdUnits, of_equiv, prod_left
-/
instance finite_of_finite [Finite V] : Finite (ℙ k V) :=
  have : Finite (ℙ k V × kˣ) := Finite.of_equiv _ (nonZeroEquivProjectivizationProdUnits k V)
  Finite.prod_left kˣ

/--
lemma `finite_iff_of_finite` / 引理 `finite_iff_of_finite`

English:
lemma finite_iff_of_finite
  given: [Finite k]
  statement: Finite (ℙ k V) ↔ Finite V
  proof: by
  classical
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let e := nonZeroEquivProjectivizationProdUnits k V
  have : Finite { v : V // v != 0 } := Finite.of_equiv _ e.symm
  let eq : { v : V // v != 0 } oplus Unit ≃ V :=
    ⟨(Sum.elim Subtype.val (fun _ => 0)), fun v => if h : v = 0 then Sum

中文:
引理 finite_iff_of_finite
  条件: [有限 k]
  结论: 有限 (ℙ k V) ↔ 有限 V
  证明: by
  classical
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let e := nonZeroEquivProjectivizationProdUnits k V
  have : Finite { v : V // v != 0 } := Finite.of_equiv _ e.symm
  let eq : { v : V // v != 0 } oplus Unit ≃ V :=
    ⟨(Sum.elim Subtype.val (fun _ => 0)), fun v => if h : v = 0 then Sum

Depends on / 依赖: Finite, Finite.of_equiv, Subtype, Subtype.val, Sum.elim, Sum.inl, Sum.inr, classical, e.symm, nonZeroEquivProjectivizationProdUnits, of_equiv
-/
lemma finite_iff_of_finite [Finite k] : Finite (ℙ k V) ↔ Finite V := by
  classical
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  let e := nonZeroEquivProjectivizationProdUnits k V
  have : Finite { v : V // v != 0 } := Finite.of_equiv _ e.symm
  let eq : { v : V // v != 0 } oplus Unit ≃ V :=
    ⟨(Sum.elim Subtype.val (fun _ => 0)), fun v => if h : v = 0 then Sum.inr () else Sum.inl ⟨v, h⟩,
      by intro x; aesop, by intro x; aesop⟩
  exact Finite.of_equiv _ eq

/--
lemma `card` / 引理 `card`

English:
lemma card
  statement: Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1)
  proof: by
  nontriviality V
  cases finite_or_infinite k with
  | inr h =>
    have : Infinite V := Module.Free.infinite k V
    simp
  | inl h =>
  cases finite_or_infinite V with
  | inr h =>
    have := not_iff_not.mpr (finite_iff_of_finite k V)
    push Not at this
    have : Infinite (ℙ k V) := by rwa

中文:
引理 card
  结论: 自然数.card V - 1 = 自然数.card (ℙ k V) * (自然数.card k - 1)
  证明: by
  nontriviality V
  cases finite_or_infinite k with
  | inr h =>
    have : Infinite V := Module.Free.infinite k V
    simp
  | inl h =>
  cases finite_or_infinite V with
  | inr h =>
    have := not_iff_not.mpr (finite_iff_of_finite k V)
    push Not at this
    have : Infinite (ℙ k V) := by rwa

Depends on / 依赖: Fintype, Fintype.card, Fintype.ofFinite, Infinite, Module, Module.Free.infinite, classical, finite_iff_of_finite, finite_or_infinite, infinite, nontriviality, not_iff_not, not_iff_not.mpr, ofFinite
-/
lemma card : Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1) := by
  nontriviality V
  cases finite_or_infinite k with
  | inr h =>
    have : Infinite V := Module.Free.infinite k V
    simp
  | inl h =>
  cases finite_or_infinite V with
  | inr h =>
    have := not_iff_not.mpr (finite_iff_of_finite k V)
    push Not at this
    have : Infinite (ℙ k V) := by rwa [this]
    simp
  | inl h =>
  classical
  have : Fintype V := Fintype.ofFinite V
  have : Fintype (ℙ k V) := Fintype.ofFinite (ℙ k V)
  have : Fintype k := Fintype.ofFinite k
  have hV : Fintype.card { v : V // v != 0 } = Fintype.card V - 1 := by simp
  simp_rw [← Fintype.card_eq_nat_card, ← Fintype.card_units (α := k), ← hV]
  rw [Fintype.card_congr (nonZeroEquivProjectivizationProdUnits k V)]; rw [Fintype.card_prod]

/--
lemma `card'` / 引理 `card'`

English:
lemma card'
  given: [Finite V]
  statement: Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1
  proof: by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  lia

中文:
引理 card'
  条件: [有限 V]
  结论: 自然数.card V = 自然数.card (ℙ k V) * (自然数.card k - 1) + 1
  证明: by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  lia

Depends on / 依赖: Nat.card, Nat.card_pos, card_pos
-/
lemma card' [Finite V] : Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1 := by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  lia

end

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/--
lemma `card''` / 引理 `card''`

English:
lemma card''
  given: [Finite k]
  statement: Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1)
  proof: by
  have : 1 < Nat.card k := Finite.one_lt_card
  rw [card k]; rw [Nat.mul_div_cancel]
  lia

中文:
引理 card''
  条件: [有限 k]
  结论: 自然数.card (ℙ k V) = (自然数.card V - 1) / (自然数.card k - 1)
  证明: by
  have : 1 < Nat.card k := Finite.one_lt_card
  rw [card k]; rw [Nat.mul_div_cancel]
  lia

Depends on / 依赖: Finite, Finite.one_lt_card, Nat.card, Nat.mul_div_cancel, mul_div_cancel, one_lt_card
-/
lemma card'' [Finite k] : Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1) := by
  have : 1 < Nat.card k := Finite.one_lt_card
  rw [card k]; rw [Nat.mul_div_cancel]
  lia

/--
lemma `card_of_finrank` / 引理 `card_of_finrank`

English:
lemma card_of_finrank
  given: [Finite k] {n : Nat} (h : Module.finrank k V = n)
  proof: by
  wlog hf : Finite V
  · have : Infinite (ℙ k V) := by
      contrapose! hf
      rwa [finite_iff_of_finite] at hf
    have : n = 0 := by
      rw [← h]
      apply Module.finrank_of_not_finite
      contrapose hf
      simpa using Module.finite_of_finite k
    simp [this]
  have : 1 < Nat.card k

中文:
引理 card_of_finrank
  条件: [有限 k] {n : 自然数} (h : 模.finrank k V = n)
  证明: by
  wlog hf : Finite V
  · have : Infinite (ℙ k V) := by
      contrapose! hf
      rwa [finite_iff_of_finite] at hf
    have : n = 0 := by
      rw [← h]
      apply Module.finrank_of_not_finite
      contrapose hf
      simpa using Module.finite_of_finite k
    simp [this]
  have : 1 < Nat.card k

Depends on / 依赖: Finite, Finite.one_lt_card, Infinite, LinearEquiv, LinearEquiv.ofFinrankEq, Module, Module.finite_of_finite, Module.finrank_of_not_finite, Nat.card, Nat.card_congr, Nat.card_fun, Nat.mul_right_cancel, card_congr, card_fun, contrapose, e.toEquiv, finite_iff_of_finite, finite_of_finite, finrank_of_not_finite, mul_right_cancel
-/
lemma card_of_finrank [Finite k] {n : Nat} (h : Module.finrank k V = n) :
    Nat.card (ℙ k V) = ∑ i in Finset.range n, Nat.card k ^ i := by
  wlog hf : Finite V
  · have : Infinite (ℙ k V) := by
      contrapose! hf
      rwa [finite_iff_of_finite] at hf
    have : n = 0 := by
      rw [← h]
      apply Module.finrank_of_not_finite
      contrapose hf
      simpa using Module.finite_of_finite k
    simp [this]
  have : 1 < Nat.card k := Finite.one_lt_card
  refine Nat.mul_right_cancel (m := Nat.card k - 1) (by lia) ?_
  let e : V ≃ₗ[k] (Fin n -> k) := LinearEquiv.ofFinrankEq _ _ (by simpa)
  have hc : Nat.card V = Nat.card k ^ n := by simp [Nat.card_congr e.toEquiv, Nat.card_fun]
  zify
  conv_rhs => rw [Int.natCast_sub this.le, Int.natCast_one, geom_sum_mul]
  rw [← Int.natCast_mul]; rw [← card k V]; rw [hc]
  simp

/--
lemma `card_of_finrank_two` / 引理 `card_of_finrank_two`

English:
lemma card_of_finrank_two
  given: [Finite k] (h : Module.finrank k V = 2)
  proof: by
  simp [card_of_finrank k V h]

中文:
引理 card_of_finrank_two
  条件: [有限 k] (h : 模.finrank k V = 2)
  证明: by
  simp [card_of_finrank k V h]

Depends on / 依赖: card_of_finrank
-/
lemma card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) :
    Nat.card (ℙ k V) = Nat.card k + 1 := by
  simp [card_of_finrank k V h]

end Projectivization
