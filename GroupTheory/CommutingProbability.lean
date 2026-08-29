/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Qify

/-!
# Commuting Probability

This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite type with a multiplication operation.

## TODO
* Neumann's theorem.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

noncomputable section

open Fintype

variable (M : Type*) [Mul M]

/--
Definition of `commProb` / `commProb` 的定义

English:
definition commProb
  signature: : Rat
  body: Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : Rat) ^ 2

中文:
定义 commProb
  签名: : 有理数
  定义体: Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : Rat) ^ 2

Depends on / 依赖: Commute, Nat.card
-/
def commProb : Rat :=
  Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : Rat) ^ 2

/--
theorem `commProb_def` / 定理 `commProb_def`

English:
theorem commProb_def
  proof: rfl

中文:
定理 commProb_def
  证明: rfl
-/
theorem commProb_def :
    commProb M = Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : Rat) ^ 2 :=
  rfl

/--
theorem `commProb_prod` / 定理 `commProb_prod`

English:
theorem commProb_prod
  given: (M' : Type*) [Mul M']
  statement: commProb (M × M') = commProb M * commProb M'
  proof: by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

中文:
定理 commProb_prod
  条件: (M' : 类型) [乘法 M']
  结论: commProb (M × M') = commProb M * commProb M'
  证明: by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

Depends on / 依赖: Commute, Nat.card_congr, Nat.card_prod, Nat.cast_mul, Prod.ext_iff, SemiconjBy, card_congr, card_prod, cast_mul, commProb_def, div_mul_div_comm, ext_iff, mul_pow, simp_rw
-/
theorem commProb_prod (M' : Type*) [Mul M'] : commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

/--
theorem `commProb_pi` / 定理 `commProb_pi`

English:
theorem commProb_pi
  given: {α : Type*} (i : α -> Type*) [Fintype α] [forall a, Mul (i a)]
  proof: by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ← Nat.cast_prod,
    ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

中文:
定理 commProb_pi
  条件: {α : 类型} (i : α -> 类型) [有限类型 α] [对任意 a, 乘法 (i a)]
  证明: by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ← Nat.cast_prod,
    ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

Depends on / 依赖: Commute, Finset, Finset.prod_div_distrib, Finset.prod_pow, Nat.card_congr, Nat.card_pi, Nat.cast_prod, SemiconjBy, card_congr, card_pi, cast_prod, commProb_def, funext_iff, prod_div_distrib, prod_pow, simp_rw
-/
theorem commProb_pi {α : Type*} (i : α -> Type*) [Fintype α] [forall a, Mul (i a)] :
    commProb (forall a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ← Nat.cast_prod,
    ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

/--
theorem `commProb_function` / 定理 `commProb_function`

English:
theorem commProb_function
  given: {α β : Type*} [Fintype α] [Mul β]
  proof: by
  rw [commProb_pi]; rw [Finset.prod_const]; rw [Finset.card_univ]

@[simp]

中文:
定理 commProb_function
  条件: {α β : 类型} [有限类型 α] [乘法 β]
  证明: by
  rw [commProb_pi]; rw [Finset.prod_const]; rw [Finset.card_univ]

@[simp]

Depends on / 依赖: Finset, Finset.card_univ, Finset.prod_const, card_univ, commProb_pi, prod_const
-/
theorem commProb_function {α β : Type*} [Fintype α] [Mul β] :
    commProb (α -> β) = (commProb β) ^ Fintype.card α := by
  rw [commProb_pi]; rw [Finset.prod_const]; rw [Finset.card_univ]

@[simp]
/--
theorem `commProb_eq_zero_of_infinite` / 定理 `commProb_eq_zero_of_infinite`

English:
theorem commProb_eq_zero_of_infinite
  given: [Infinite M]
  statement: commProb M = 0
  proof: div_eq_zero_iff.2 (Or.inl (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite))

中文:
定理 commProb_eq_zero_of_infinite
  条件: [无限 M]
  结论: commProb M = 0
  证明: div_eq_zero_iff.2 (Or.inl (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite))

Depends on / 依赖: Nat.card_eq_zero_of_infinite, Nat.cast_eq_zero, Or.inl, card_eq_zero_of_infinite, cast_eq_zero, div_eq_zero_iff
-/
theorem commProb_eq_zero_of_infinite [Infinite M] : commProb M = 0 :=
  div_eq_zero_iff.2 (Or.inl (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite))

variable [Finite M]

/--
theorem `commProb_pos` / 定理 `commProb_pos`

English:
theorem commProb_pos
  given: [h : Nonempty M]
  statement: 0 < commProb M
  proof: h.elim fun x =>
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)

中文:
定理 commProb_pos
  条件: [h : 非空 M]
  结论: 0 < commProb M
  证明: h.elim fun x =>
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)

Depends on / 依赖: Finite, Finite.card_pos, Finite.card_pos_iff.mpr, Nat.cast_pos.mpr, card_pos, card_pos_iff, cast_pos, div_pos, h.elim, pow_pos
-/
theorem commProb_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x =>
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)

/--
theorem `commProb_le_one` / 定理 `commProb_le_one`

English:
theorem commProb_le_one
  statement: commProb M <= 1
  proof: by
  refine div_le_one_of_le₀ ?_ (sq_nonneg (Nat.card M : Rat))
  norm_cast
  rw [sq]; rw [← Nat.card_prod]
  apply Finite.card_subtype_le

中文:
定理 commProb_le_one
  结论: commProb M <= 1
  证明: by
  refine div_le_one_of_le₀ ?_ (sq_nonneg (Nat.card M : Rat))
  norm_cast
  rw [sq]; rw [← Nat.card_prod]
  apply Finite.card_subtype_le

Depends on / 依赖: Finite, Finite.card_subtype_le, Nat.card, Nat.card_prod, card_prod, card_subtype_le, sq_nonneg
-/
theorem commProb_le_one : commProb M <= 1 := by
  refine div_le_one_of_le₀ ?_ (sq_nonneg (Nat.card M : Rat))
  norm_cast
  rw [sq]; rw [← Nat.card_prod]
  apply Finite.card_subtype_le

variable {M}

/--
theorem `commProb_eq_one_iff` / 定理 `commProb_eq_one_iff`

English:
theorem commProb_eq_one_iff
  given: [h : Nonempty M]
  statement: commProb M = 1 ↔ IsMulCommutative M
  proof: by
  classical
  have := Fintype.ofFinite M
  rw [commProb]; rw [← Set.coe_ofPred]; rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq]; rw [← Nat.cast_pow]; rw [Nat.cast_inj]; rw [sq]; rw [← card_prod]; rw [set_fintype_card_eq_univ_iff]; rw [Set.eq_univ_iff_forall]
  · exact ⟨fun h => ⟨⟨fun x y => h (x, y)⟩⟩, fun h x => mul_comm' ..⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)

中文:
定理 commProb_eq_one_iff
  条件: [h : 非空 M]
  结论: commProb M = 1 ↔ 是MulCommutative M
  证明: by
  classical
  have := Fintype.ofFinite M
  rw [commProb]; rw [← Set.coe_ofPred]; rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq]; rw [← Nat.cast_pow]; rw [Nat.cast_inj]; rw [sq]; rw [← card_prod]; rw [set_fintype_card_eq_univ_iff]; rw [Set.eq_univ_iff_forall]
  · exact ⟨fun h => ⟨⟨fun x y => h (x, y)⟩⟩, fun h x => mul_comm' ..⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.cast_inj, Nat.cast_ne_zero.mpr, Nat.cast_pow, Set.coe_ofPred, Set.eq_univ_iff_forall, card_eq_fintype_card, card_ne_zero, card_prod, cast_inj, cast_ne_zero, cast_pow, classical, coe_ofPred, commProb, div_eq_one_iff_eq, eq_univ_iff_forall, mul_comm
-/
theorem commProb_eq_one_iff [h : Nonempty M] : commProb M = 1 ↔ IsMulCommutative M := by
  classical
  have := Fintype.ofFinite M
  rw [commProb]; rw [← Set.coe_ofPred]; rw [Nat.card_eq_fintype_card]; rw [Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq]; rw [← Nat.cast_pow]; rw [Nat.cast_inj]; rw [sq]; rw [← card_prod]; rw [set_fintype_card_eq_univ_iff]; rw [Set.eq_univ_iff_forall]
  · exact ⟨fun h => ⟨⟨fun x y => h (x, y)⟩⟩, fun h x => mul_comm' ..⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)

variable (G : Type*) [Group G]

/--
theorem `commProb_def'` / 定理 `commProb_def'`

English:
theorem commProb_def'
  statement: commProb G = Nat.card (ConjClasses G) / Nat.card G
  proof: by
  rw [commProb]; rw [card_comm_eq_card_conjClasses_mul_card]; rw [Nat.cast_mul]; rw [sq]
  by_cases h : (Nat.card G : Rat) = 0
  · rw [h, zero_mul, div_zero, div_zero]
  · exact mul_div_mul_right _ _ h

中文:
定理 commProb_def'
  结论: commProb G = 自然数.card (ConjClasses G) / 自然数.card G
  证明: by
  rw [commProb]; rw [card_comm_eq_card_conjClasses_mul_card]; rw [Nat.cast_mul]; rw [sq]
  by_cases h : (Nat.card G : Rat) = 0
  · rw [h, zero_mul, div_zero, div_zero]
  · exact mul_div_mul_right _ _ h

Depends on / 依赖: Nat.card, Nat.cast_mul, card_comm_eq_card_conjClasses_mul_card, cast_mul, commProb, div_zero, mul_div_mul_right, zero_mul
-/
theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb]; rw [card_comm_eq_card_conjClasses_mul_card]; rw [Nat.cast_mul]; rw [sq]
  by_cases h : (Nat.card G : Rat) = 0
  · rw [h, zero_mul, div_zero, div_zero]
  · exact mul_div_mul_right _ _ h

variable {G}
variable [Finite G] (H : Subgroup G)

/--
theorem `Subgroup.commProb_subgroup_le` / 定理 `Subgroup.commProb_subgroup_le`

English:
theorem Subgroup.commProb_subgroup_le
  statement: commProb H <= commProb G * (H.index : Rat) ^ 2
  proof: by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def]; rw [commProb_def]; rw [div_le_iff₀]; rw [mul_assoc]; rw [← mul_pow]; rw [← Nat.cast_mul]; rw [mul_comm H.index]; rw [H.card_mul_index]; rw [div_mul_cancel₀]; rw [Nat.cast_le]
  · refine Nat.card_le_card_of_injective (fun p => ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) ?_
    exact fun p q h => by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2

中文:
定理 子群.commProb_subgroup_le
  结论: commProb H <= commProb G * (H.index : 有理数) ^ 2
  证明: by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def]; rw [commProb_def]; rw [div_le_iff₀]; rw [mul_assoc]; rw [← mul_pow]; rw [← Nat.cast_mul]; rw [mul_comm H.index]; rw [H.card_mul_index]; rw [div_mul_cancel₀]; rw [Nat.cast_le]
  · refine Nat.card_le_card_of_injective (fun p => ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) ?_
    exact fun p q h => by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2
-/
theorem Subgroup.commProb_subgroup_le : commProb H <= commProb G * (H.index : Rat) ^ 2 := by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def]; rw [commProb_def]; rw [div_le_iff₀]; rw [mul_assoc]; rw [← mul_pow]; rw [← Nat.cast_mul]; rw [mul_comm H.index]; rw [H.card_mul_index]; rw [div_mul_cancel₀]; rw [Nat.cast_le]
  · refine Nat.card_le_card_of_injective (fun p => ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) ?_
    exact fun p q h => by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2

/--
theorem `Subgroup.commProb_quotient_le` / 定理 `Subgroup.commProb_quotient_le`

English:
theorem Subgroup.commProb_quotient_le
  given: [H.Normal]
  statement: commProb (G ⧸ H) <= commProb G * Nat.card H
  proof: by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def']; rw [commProb_def']; rw [div_le_iff₀]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [← Subgroup.index]; rw [H.card_mul_index]; rw [div_mul_cancel₀]; rw [Nat.cast_le]
  · apply Nat.card_le_card_of_surjective (f := ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.mk''_surjective
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos

中文:
定理 子群.commProb_quotient_le
  条件: [H.正规]
  结论: commProb (G ⧸ H) <= commProb G * 自然数.card H
  证明: by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def']; rw [commProb_def']; rw [div_le_iff₀]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [← Subgroup.index]; rw [H.card_mul_index]; rw [div_mul_cancel₀]; rw [Nat.cast_le]
  · apply Nat.card_le_card_of_surjective (f := ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.mk''_surjective
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos
-/
theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) <= commProb G * Nat.card H := by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def']; rw [commProb_def']; rw [div_le_iff₀]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [← Subgroup.index]; rw [H.card_mul_index]; rw [div_mul_cancel₀]; rw [Nat.cast_le]
  · apply Nat.card_le_card_of_surjective (f := ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.mk''_surjective
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos

variable (G)

/--
theorem `inv_card_commutator_le_commProb` / 定理 `inv_card_commutator_le_commProb`

English:
theorem inv_card_commutator_le_commProb
  statement: (↑(Nat.card (commutator G)))⁻¹ <= commProb G
  proof: (inv_le_iff_one_le_mul₀ (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).to_isCommutative))
      (commutator G).commProb_quotient_le)

中文:
定理 inv_card_commutator_le_commProb
  结论: (↑(自然数.card (commutator G)))⁻¹ <= commProb G
  证明: (inv_le_iff_one_le_mul₀ (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).to_isCommutative))
      (commutator G).commProb_quotient_le)

Depends on / 依赖: Abelianization, Abelianization.commGroup, Finite, Finite.card_pos, Nat.cast_pos.mpr, card_pos, cast_pos, commGroup, commProb_eq_one_iff, commProb_eq_one_iff.mpr, commProb_quotient_le, commutator, ge_of_eq, le_trans, to_isCommutative
-/
theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ <= commProb G :=
  (inv_le_iff_one_le_mul₀ (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).to_isCommutative))
      (commutator G).commProb_quotient_le)

-- Construction of group with commuting probability 1/n
namespace DihedralGroup

/--
lemma `commProb_odd` / 引理 `commProb_odd`

English:
lemma commProb_odd
  given: {n : Nat} (hn : Odd n)
  proof: by
  rw [commProb_def']; rw [DihedralGroup.card_conjClasses_odd hn]; rw [nat_card]
  qify [show 2 ∣ n + 3 by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.odd_iff.mp hn]]
  rw [div_div]; rw [← mul_assoc]
  congr
  norm_num

中文:
引理 commProb_odd
  条件: {n : 自然数} (hn : Odd n)
  证明: by
  rw [commProb_def']; rw [DihedralGroup.card_conjClasses_odd hn]; rw [nat_card]
  qify [show 2 ∣ n + 3 by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.odd_iff.mp hn]]
  rw [div_div]; rw [← mul_assoc]
  congr
  norm_num

Depends on / 依赖: DihedralGroup, DihedralGroup.card_conjClasses_odd, Nat.add_mod, Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp, add_mod, card_conjClasses_odd, commProb_def, div_div, dvd_iff_mod_eq_zero, mul_assoc, nat_card, odd_iff
-/
lemma commProb_odd {n : Nat} (hn : Odd n) :
    commProb (DihedralGroup n) = (n + 3) / (4 * n) := by
  rw [commProb_def']; rw [DihedralGroup.card_conjClasses_odd hn]; rw [nat_card]
  qify [show 2 ∣ n + 3 by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.odd_iff.mp hn]]
  rw [div_div]; rw [← mul_assoc]
  congr
  norm_num

/--
Definition of `reciprocalFactors` / `reciprocalFactors` 的定义

English:
definition reciprocalFactors
  signature: (n : Nat)
  body: if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

中文:
定义 reciprocalFactors
  签名: (n : 自然数)
  定义体: if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

Depends on / 依赖: reciprocalFactors
-/
def reciprocalFactors (n : Nat) : List Nat :=
  if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

/--
lemma `reciprocalFactors_zero` / 引理 `reciprocalFactors_zero`

English:
lemma reciprocalFactors_zero
  statement: reciprocalFactors 0 = [0]
  proof: by
  unfold reciprocalFactors; rfl

中文:
引理 reciprocalFactors_zero
  结论: reciprocalFactors 0 = [0]
  证明: by
  unfold reciprocalFactors; rfl
-/
@[simp] lemma reciprocalFactors_zero : reciprocalFactors 0 = [0] := by
  unfold reciprocalFactors; rfl

/--
lemma `reciprocalFactors_one` / 引理 `reciprocalFactors_one`

English:
lemma reciprocalFactors_one
  statement: reciprocalFactors 1 = []
  proof: by
  unfold reciprocalFactors; rfl

中文:
引理 reciprocalFactors_one
  结论: reciprocalFactors 1 = []
  证明: by
  unfold reciprocalFactors; rfl
-/
@[simp] lemma reciprocalFactors_one : reciprocalFactors 1 = [] := by
  unfold reciprocalFactors; rfl

/--
lemma `reciprocalFactors_even` / 引理 `reciprocalFactors_even`

English:
lemma reciprocalFactors_even
  given: {n : Nat} (h0 : n != 0) (h2 : Even n)
  proof: by
  have h1 : n != 1 := by
    rintro rfl
    norm_num at h2
  rw [reciprocalFactors]; rw [dif_neg h0]; rw [dif_neg h1]; rw [if_pos h2]

中文:
引理 reciprocalFactors_even
  条件: {n : 自然数} (h0 : n != 0) (h2 : Even n)
  证明: by
  have h1 : n != 1 := by
    rintro rfl
    norm_num at h2
  rw [reciprocalFactors]; rw [dif_neg h0]; rw [dif_neg h1]; rw [if_pos h2]

Depends on / 依赖: dif_neg, if_pos, reciprocalFactors
-/
lemma reciprocalFactors_even {n : Nat} (h0 : n != 0) (h2 : Even n) :
    reciprocalFactors n = 3 :: reciprocalFactors (n / 2) := by
  have h1 : n != 1 := by
    rintro rfl
    norm_num at h2
  rw [reciprocalFactors]; rw [dif_neg h0]; rw [dif_neg h1]; rw [if_pos h2]

/--
lemma `reciprocalFactors_odd` / 引理 `reciprocalFactors_odd`

English:
lemma reciprocalFactors_odd
  given: {n : Nat} (h1 : n != 1) (h2 : Odd n)
  proof: by
  have h0 : n != 0 := by
    rintro rfl
    norm_num [← Nat.not_even_iff_odd] at h2
  rw [reciprocalFactors]; rw [dif_neg h0]; rw [dif_neg h1]; rw [if_neg (Nat.not_even_iff_odd.2 h2)]

中文:
引理 reciprocalFactors_odd
  条件: {n : 自然数} (h1 : n != 1) (h2 : Odd n)
  证明: by
  have h0 : n != 0 := by
    rintro rfl
    norm_num [← Nat.not_even_iff_odd] at h2
  rw [reciprocalFactors]; rw [dif_neg h0]; rw [dif_neg h1]; rw [if_neg (Nat.not_even_iff_odd.2 h2)]

Depends on / 依赖: Nat.not_even_iff_odd, dif_neg, if_neg, not_even_iff_odd, reciprocalFactors
-/
lemma reciprocalFactors_odd {n : Nat} (h1 : n != 1) (h2 : Odd n) :
    reciprocalFactors n = n % 4 * n :: reciprocalFactors (n / 4 + 1) := by
  have h0 : n != 0 := by
    rintro rfl
    norm_num [← Nat.not_even_iff_odd] at h2
  rw [reciprocalFactors]; rw [dif_neg h0]; rw [dif_neg h1]; rw [if_neg (Nat.not_even_iff_odd.2 h2)]

/--
Definition of `Product` / `Product` 的定义

English:
abbreviation Product
  signature: (l : List Nat)
  body: forall i : Fin l.length, DihedralGroup l[i]

中文:
缩写 积
  签名: (l : 列表 自然数)
  定义体: forall i : Fin l.length, DihedralGroup l[i]

Depends on / 依赖: DihedralGroup, l.length, length
-/
abbrev Product (l : List Nat) : Type :=
  forall i : Fin l.length, DihedralGroup l[i]

/--
lemma `commProb_nil` / 引理 `commProb_nil`

English:
lemma commProb_nil
  statement: commProb (Product []) = 1
  proof: by
  simp [Product, commProb_pi]

中文:
引理 commProb_nil
  结论: commProb (积 []) = 1
  证明: by
  simp [Product, commProb_pi]

Depends on / 依赖: Product, commProb_pi
-/
lemma commProb_nil : commProb (Product []) = 1 := by
  simp [Product, commProb_pi]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `commProb_cons` / 引理 `commProb_cons`

English:
lemma commProb_cons
  given: (n : Nat) (l : List Nat)
  proof: by
  simp only [commProb_pi, Fin.prod_univ_succ, Fin.getElem_fin, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_zero, List.length_cons, List.getElem_cons_succ]

中文:
引理 commProb_cons
  条件: (n : 自然数) (l : 列表 自然数)
  证明: by
  simp only [commProb_pi, Fin.prod_univ_succ, Fin.getElem_fin, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_zero, List.length_cons, List.getElem_cons_succ]

Depends on / 依赖: Fin.getElem_fin, Fin.prod_univ_succ, Fin.val_succ, Fin.val_zero, List.getElem_cons_succ, List.getElem_cons_zero, List.length_cons, commProb_pi, getElem_cons_succ, getElem_cons_zero, getElem_fin, length_cons, prod_univ_succ, val_succ, val_zero
-/
lemma commProb_cons (n : Nat) (l : List Nat) :
    commProb (Product (n :: l)) = commProb (DihedralGroup n) * commProb (Product l) := by
  simp only [commProb_pi, Fin.prod_univ_succ, Fin.getElem_fin, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_zero, List.length_cons, List.getElem_cons_succ]

/--
theorem `commProb_reciprocal` / 定理 `commProb_reciprocal`

English:
theorem commProb_reciprocal
  given: (n : Nat)
  proof: by
  by_cases h0 : n = 0
  · rw [h0, reciprocalFactors_zero, commProb_cons, commProb_nil, mul_one, Nat.cast_zero, div_zero]
    apply commProb_eq_zero_of_infinite
  by_cases h1 : n = 1
  · rw [h1, reciprocalFactors_one, commProb_nil, Nat.cast_one, div_one]
  rcases Nat.even_or_odd n with h2 | h2
  · rw [reciprocalFactors_even h0 h2, commProb_cons, commProb_reciprocal (n / 2),
        commProb_odd (by decide)]
    simp [field, h2.two_dvd]
    norm_num
  · rw [reciprocalFactors_odd h1 h2, commProb_cons, commProb_reciprocal (n / 4 + 1)]
    have hn : Odd (n % 4) := by grind
    rw [commProb_odd (hn.mul h2)]; rw [div_mul_div_comm]; rw [div_eq_div_iff] <;> norm_cast
    · grind [Nat.div_add_mod n 4, Odd]
    · positivity [hn.pos.ne']

中文:
定理 commProb_reciprocal
  条件: (n : 自然数)
  证明: by
  by_cases h0 : n = 0
  · rw [h0, reciprocalFactors_zero, commProb_cons, commProb_nil, mul_one, Nat.cast_zero, div_zero]
    apply commProb_eq_zero_of_infinite
  by_cases h1 : n = 1
  · rw [h1, reciprocalFactors_one, commProb_nil, Nat.cast_one, div_one]
  rcases Nat.even_or_odd n with h2 | h2
  · rw [reciprocalFactors_even h0 h2, commProb_cons, commProb_reciprocal (n / 2),
        commProb_odd (by decide)]
    simp [field, h2.two_dvd]
    norm_num
  · rw [reciprocalFactors_odd h1 h2, commProb_cons, commProb_reciprocal (n / 4 + 1)]
    have hn : Odd (n % 4) := by grind
    rw [commProb_odd (hn.mul h2)]; rw [div_mul_div_comm]; rw [div_eq_div_iff] <;> norm_cast
    · grind [Nat.div_add_mod n 4, Odd]
    · positivity [hn.pos.ne']

Depends on / 依赖: Nat.cast_one, Nat.cast_zero, Nat.even_or_odd, cast_one, cast_zero, commProb_cons, commProb_eq_zero_of_infinite, commProb_nil, commProb_odd, commProb_reciprocal, div_one, div_zero, even_or_odd, h2.two_dvd, mul_one, reciprocalFactors_even, reciprocalFactors_odd, reciprocalFactors_one, reciprocalFactors_zero, two_dvd
-/
theorem commProb_reciprocal (n : Nat) :
    commProb (Product (reciprocalFactors n)) = 1 / n := by
  by_cases h0 : n = 0
  · rw [h0, reciprocalFactors_zero, commProb_cons, commProb_nil, mul_one, Nat.cast_zero, div_zero]
    apply commProb_eq_zero_of_infinite
  by_cases h1 : n = 1
  · rw [h1, reciprocalFactors_one, commProb_nil, Nat.cast_one, div_one]
  rcases Nat.even_or_odd n with h2 | h2
  · rw [reciprocalFactors_even h0 h2, commProb_cons, commProb_reciprocal (n / 2),
        commProb_odd (by decide)]
    simp [field, h2.two_dvd]
    norm_num
  · rw [reciprocalFactors_odd h1 h2, commProb_cons, commProb_reciprocal (n / 4 + 1)]
    have hn : Odd (n % 4) := by grind
    rw [commProb_odd (hn.mul h2)]; rw [div_mul_div_comm]; rw [div_eq_div_iff] <;> norm_cast
    · grind [Nat.div_add_mod n 4, Odd]
    · positivity [hn.pos.ne']

end DihedralGroup
