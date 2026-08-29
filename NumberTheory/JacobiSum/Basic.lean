/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# Jacobi Sums

This file defines the *Jacobi sum* of two multiplicative characters `χ` and `ψ` on a finite
commutative ring `R` with values in another commutative ring `R'`:

`jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)`

(see `jacobiSum`) and provides some basic results and API lemmas on Jacobi sums.

## References

We essentially follow
* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
  (Section 8.3)][IrelandRosen1990]

but generalize where appropriate.

This is based on Lean code written as part of the bachelor's thesis of Alexander Spahl.
-/

@[expose] public section

open Finset

/-!
### Jacobi sums: definition and first properties
-/

section Def

-- need `Fintype` instead of `Finite` to make `jacobiSum` computable.
variable {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']

/--
Definition of `jacobiSum` / `jacobiSum` 的定义

English:
definition jacobiSum
  signature: (χ ψ : MulChar R R')
  body: ∑ x : R, χ x * ψ (1 - x)

中文:
定义 jacobiSum
  签名: (χ ψ : 乘法特征 R R')
  定义体: ∑ x : R, χ x * ψ (1 - x)
-/
def jacobiSum (χ ψ : MulChar R R') : R' :=
  ∑ x : R, χ x * ψ (1 - x)

/--
lemma `jacobiSum_comm` / 引理 `jacobiSum_comm`

English:
lemma jacobiSum_comm
  given: (χ ψ : MulChar R R')
  statement: jacobiSum χ ψ = jacobiSum ψ χ
  proof: by
  simp only [jacobiSum, mul_comm (χ _)]
  rw [← (Equiv.subLeft 1).sum_comp]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

中文:
引理 jacobiSum_comm
  条件: (χ ψ : 乘法特征 R R')
  结论: jacobiSum χ ψ = jacobiSum ψ χ
  证明: by
  simp only [jacobiSum, mul_comm (χ _)]
  rw [← (Equiv.subLeft 1).sum_comp]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

Depends on / 依赖: Equiv.subLeft, Equiv.subLeft_apply, jacobiSum, mul_comm, subLeft, subLeft_apply, sub_sub_cancel, sum_comp
-/
lemma jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ := by
  simp only [jacobiSum, mul_comm (χ _)]
  rw [← (Equiv.subLeft 1).sum_comp]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

/--
lemma `jacobiSum_ringHomComp` / 引理 `jacobiSum_ringHomComp`

English:
lemma jacobiSum_ringHomComp
  given: {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' ->+* R'')
  proof: by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

中文:
引理 jacobiSum_ringHomComp
  条件: {R'' : 类型} [交换环 R''] (χ ψ : 乘法特征 R R') (f : R' ->+* R'')
  证明: by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, MulChar, MulChar.coe_mk, MulChar.ringHomComp, OneHom, OneHom.coe_mk, coe_mk, jacobiSum, map_mul, map_sum, ringHomComp
-/
lemma jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' ->+* R'') :
    jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ ψ) := by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

end Def

/-!
### Jacobi sums over finite fields
-/

section CommRing

variable {F R : Type*} [CommRing F] [Nontrivial F] [Fintype F] [DecidableEq F] [CommRing R]

/--
lemma `jacobiSum_eq_sum_sdiff` / 引理 `jacobiSum_eq_sum_sdiff`

English:
lemma jacobiSum_eq_sum_sdiff
  given: (χ ψ : MulChar F R)
  proof: by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, sub_eq_add_neg, left_eq_add,
    neg_eq_zero]
  apply sum_eq_zero
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, χ.map_zero, neg_zero, add_zero, map_one,
    mul_one, forall_eq, add_neg_cancel, ψ.map_zero, mul_zero, and_self]

中文:
引理 jacobiSum_eq_sum_sdiff
  条件: (χ ψ : 乘法特征 F R)
  证明: by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, sub_eq_add_neg, left_eq_add,
    neg_eq_zero]
  apply sum_eq_zero
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, χ.map_zero, neg_zero, add_zero, map_one,
    mul_one, forall_eq, add_neg_cancel, ψ.map_zero, mul_zero, and_self]

Depends on / 依赖: add_neg_cancel, add_zero, and_self, forall_eq, forall_eq_or_imp, jacobiSum, left_eq_add, map_one, map_zero, mem_insert, mem_singleton, mul_one, mul_zero, neg_eq_zero, neg_zero, sub_eq_add_neg, subset_univ, sum_eq_zero, sum_sdiff_eq_sub
-/
lemma jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x in univ \ {0,1}, χ x * ψ (1 - x) := by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, sub_eq_add_neg, left_eq_add,
    neg_eq_zero]
  apply sum_eq_zero
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, χ.map_zero, neg_zero, add_zero, map_one,
    mul_one, forall_eq, add_neg_cancel, ψ.map_zero, mul_zero, and_self]

/--
lemma `jacobiSum_eq_aux` / 引理 `jacobiSum_eq_aux`

English:
lemma jacobiSum_eq_aux
  given: (χ ψ : MulChar F R)
  proof: by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show forall x y : R]; rw [x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib]; rw [sum_sub_distrib]; rw [sum_add_distrib]
  conv => enter [1, 1, 1, 2, 2, x]; rw [← Equiv.subLeft_apply 1]
  rw [(Equiv.subLeft 1).sum_comp ψ]; rw [Fintype.card_eq_sum_ones]; rw [Nat.cast_sum]; rw [Nat.cast_one]; rw [sum_sdiff_eq_sub (subset_univ _)]; rw [← sub_zero (_ - _ + _)]; rw [add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one]; rw [sub_zero]; rw [ψ.map_one]; rw [χ.map_one]; rw [sub_self]; rw [mul_zero]; rw [zero_mul]; rw [add_zero]

中文:
引理 jacobiSum_eq_aux
  条件: (χ ψ : 乘法特征 F R)
  证明: by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show forall x y : R]; rw [x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib]; rw [sum_sub_distrib]; rw [sum_add_distrib]
  conv => enter [1, 1, 1, 2, 2, x]; rw [← Equiv.subLeft_apply 1]
  rw [(Equiv.subLeft 1).sum_comp ψ]; rw [Fintype.card_eq_sum_ones]; rw [Nat.cast_sum]; rw [Nat.cast_one]; rw [sum_sdiff_eq_sub (subset_univ _)]; rw [← sub_zero (_ - _ + _)]; rw [add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one]; rw [sub_zero]; rw [ψ.map_one]; rw [χ.map_one]; rw [sub_self]; rw [mul_zero]; rw [zero_mul]; rw [add_zero]
-/
private lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
                      ∑ x in univ \ {0, 1}, (χ x - 1) * (ψ (1 - x) - 1) := by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show forall x y : R]; rw [x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib]; rw [sum_sub_distrib]; rw [sum_add_distrib]
  conv => enter [1, 1, 1, 2, 2, x]; rw [← Equiv.subLeft_apply 1]
  rw [(Equiv.subLeft 1).sum_comp ψ]; rw [Fintype.card_eq_sum_ones]; rw [Nat.cast_sum]; rw [Nat.cast_one]; rw [sum_sdiff_eq_sub (subset_univ _)]; rw [← sub_zero (_ - _ + _)]; rw [add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one]; rw [sub_zero]; rw [ψ.map_one]; rw [χ.map_one]; rw [sub_self]; rw [mul_zero]; rw [zero_mul]; rw [add_zero]

end CommRing

section FiniteField

variable {F R : Type*} [Field F] [Fintype F] [CommRing R]

/--
theorem `jacobiSum_trivial_trivial` / 定理 `jacobiSum_trivial_trivial`

English:
theorem jacobiSum_trivial_trivial
  proof: by
  classical
  rw [jacobiSum_eq_sum_sdiff]
  have : forall x in univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intro x hx
    rw [← map_mul]; rw [MulChar.trivial_apply]; rw [if_pos]
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
    simpa only [isUnit_iff_ne_zero, mul_ne_zero_iff, ne_eq, sub_eq_zero, @eq_comm _ _ x] using hx
  calc ∑ x in univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ in univ \ {0, 1}, 1 := sum_congr rfl this
  _ = #(univ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff_of_subset (subset_univ _)]; rw [card_univ]; rw [card_pair zero_ne_one]; rw [Nat.cast_sub Nat.add_one_le_of_lt Fintype.one_lt_card]; rw [Nat.cast_two]

中文:
定理 jacobiSum_trivial_trivial
  证明: by
  classical
  rw [jacobiSum_eq_sum_sdiff]
  have : forall x in univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intro x hx
    rw [← map_mul]; rw [MulChar.trivial_apply]; rw [if_pos]
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
    simpa only [isUnit_iff_ne_zero, mul_ne_zero_iff, ne_eq, sub_eq_zero, @eq_comm _ _ x] using hx
  calc ∑ x in univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ in univ \ {0, 1}, 1 := sum_congr rfl this
  _ = #(univ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff_of_subset (subset_univ _)]; rw [card_univ]; rw [card_pair zero_ne_one]; rw [Nat.cast_sub Nat.add_one_le_of_lt Fintype.one_lt_card]; rw [Nat.cast_two]

Depends on / 依赖: MulChar, MulChar.trivial, MulChar.trivial_apply, classical, eq_comm, if_pos, isUnit_iff_ne_zero, jacobiSum_eq_sum_sdiff, map_mul, mem_insert, mem_sdiff, mem_singleton, mem_univ, mul_ne_zero_iff, ne_eq, not_or, sub_eq_zero, trivial_apply, true_and
-/
theorem jacobiSum_trivial_trivial :
    jacobiSum (MulChar.trivial F R) (MulChar.trivial F R) = Fintype.card F - 2 := by
  classical
  rw [jacobiSum_eq_sum_sdiff]
  have : forall x in univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intro x hx
    rw [← map_mul]; rw [MulChar.trivial_apply]; rw [if_pos]
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
    simpa only [isUnit_iff_ne_zero, mul_ne_zero_iff, ne_eq, sub_eq_zero, @eq_comm _ _ x] using hx
  calc ∑ x in univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ in univ \ {0, 1}, 1 := sum_congr rfl this
  _ = #(univ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff_of_subset (subset_univ _)]; rw [card_univ]; rw [card_pair zero_ne_one]; rw [Nat.cast_sub Nat.add_one_le_of_lt Fintype.one_lt_card]; rw [Nat.cast_two]

/--
theorem `jacobiSum_one_one` / 定理 `jacobiSum_one_one`

English:
theorem jacobiSum_one_one
  statement: jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2
  proof: jacobiSum_trivial_trivial

中文:
定理 jacobiSum_one_one
  结论: jacobiSum (1 : 乘法特征 F R) 1 = 有限类型.card F - 2
  证明: jacobiSum_trivial_trivial

Depends on / 依赖: jacobiSum_trivial_trivial
-/
theorem jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2 :=
  jacobiSum_trivial_trivial

variable [IsDomain R] -- needed for `MulChar.sum_eq_zero_of_ne_one`

/--
theorem `jacobiSum_one_nontrivial` / 定理 `jacobiSum_one_nontrivial`

English:
theorem jacobiSum_one_nontrivial
  given: {χ : MulChar F R} (hχ : χ != 1)
  statement: jacobiSum 1 χ = -1
  proof: by
  classical
  have : ∑ x in univ \ {0, 1}, ((1 : MulChar F R) x - 1) * (χ (1 - x) - 1) = 0 := by
    apply Finset.sum_eq_zero
    simp +contextual only [mem_sdiff, mem_univ, mem_insert, mem_singleton,
      not_or, ← isUnit_iff_ne_zero, true_and, MulChar.one_apply, sub_self, zero_mul,
      implies_true]
  simp only [jacobiSum_eq_aux, MulChar.sum_one_eq_card_units, MulChar.sum_eq_zero_of_ne_one hχ,
    add_zero, Fintype.card_eq_card_units_add_one (α := F), Nat.cast_add, Nat.cast_one,
    sub_add_cancel_left, this]

中文:
定理 jacobiSum_one_nontrivial
  条件: {χ : 乘法特征 F R} (hχ : χ != 1)
  结论: jacobiSum 1 χ = -1
  证明: by
  classical
  have : ∑ x in univ \ {0, 1}, ((1 : MulChar F R) x - 1) * (χ (1 - x) - 1) = 0 := by
    apply Finset.sum_eq_zero
    simp +contextual only [mem_sdiff, mem_univ, mem_insert, mem_singleton,
      not_or, ← isUnit_iff_ne_zero, true_and, MulChar.one_apply, sub_self, zero_mul,
      implies_true]
  simp only [jacobiSum_eq_aux, MulChar.sum_one_eq_card_units, MulChar.sum_eq_zero_of_ne_one hχ,
    add_zero, Fintype.card_eq_card_units_add_one (α := F), Nat.cast_add, Nat.cast_one,
    sub_add_cancel_left, this]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Fintype, Fintype.card_eq_card_units_add_one, MulChar, MulChar.one_apply, MulChar.sum_eq_zero_of_ne_one, MulChar.sum_one_eq_card_units, Nat.cast_add, Nat.cast_one, add_zero, card_eq_card_units_add_one, cast_add, cast_one, classical, contextual, implies_true, isUnit_iff_ne_zero, jacobiSum_eq_aux, mem_insert
-/
theorem jacobiSum_one_nontrivial {χ : MulChar F R} (hχ : χ != 1) : jacobiSum 1 χ = -1 := by
  classical
  have : ∑ x in univ \ {0, 1}, ((1 : MulChar F R) x - 1) * (χ (1 - x) - 1) = 0 := by
    apply Finset.sum_eq_zero
    simp +contextual only [mem_sdiff, mem_univ, mem_insert, mem_singleton,
      not_or, ← isUnit_iff_ne_zero, true_and, MulChar.one_apply, sub_self, zero_mul,
      implies_true]
  simp only [jacobiSum_eq_aux, MulChar.sum_one_eq_card_units, MulChar.sum_eq_zero_of_ne_one hχ,
    add_zero, Fintype.card_eq_card_units_add_one (α := F), Nat.cast_add, Nat.cast_one,
    sub_add_cancel_left, this]

/--
theorem `jacobiSum_nontrivial_inv` / 定理 `jacobiSum_nontrivial_inv`

English:
theorem jacobiSum_nontrivial_inv
  given: {χ : MulChar F R} (hχ : χ != 1)
  statement: jacobiSum χ χ⁻¹ = -χ (-1)
  proof: by
  classical
  rw [jacobiSum]
  conv => enter [1, 2, x]; rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  rw [sum_eq_sum_sdiff_singleton_add (mem_univ (1 : F))]; rw [sub_self]; rw [div_zero]; rw [χ.map_zero]; rw [add_zero]
  have : ∑ x in univ \ {1}, χ (x / (1 - x)) = ∑ x in univ \ {-1}, χ x := by
    refine sum_bij' (fun a _ => a / (1 - a)) (fun b _ => b / (1 + b)) (fun x hx => ?_)
      (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun _ _ => rfl)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx ⊢
      rw [div_eq_iff <| sub_ne_zero.mpr ((ne_eq ..).symm ▸ hx).symm]; rw [mul_sub]; rw [mul_one]; rw [neg_one_mul]; rw [sub_neg_eq_add]; rw [right_eq_add]; rw [neg_eq_zero]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy ⊢
      rw [div_eq_iff fun h => hy <| eq_neg_of_add_eq_zero_right h]; rw [one_mul]; rw [right_eq_add]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm]; rw [← sub_eq_zero] at hx
      simp [field]
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm]; rw [neg_eq_iff_eq_neg]; rw [← sub_eq_zero]; rw [sub_neg_eq_add] at hy
      simp [field]
  rw [this]; rw [← add_eq_zero_iff_eq_neg]; rw [← sum_eq_sum_sdiff_singleton_add (mem_univ (-1 : F))]
  exact MulChar.sum_eq_zero_of_ne_one hχ

中文:
定理 jacobiSum_nontrivial_inv
  条件: {χ : 乘法特征 F R} (hχ : χ != 1)
  结论: jacobiSum χ χ⁻¹ = -χ (-1)
  证明: by
  classical
  rw [jacobiSum]
  conv => enter [1, 2, x]; rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  rw [sum_eq_sum_sdiff_singleton_add (mem_univ (1 : F))]; rw [sub_self]; rw [div_zero]; rw [χ.map_zero]; rw [add_zero]
  have : ∑ x in univ \ {1}, χ (x / (1 - x)) = ∑ x in univ \ {-1}, χ x := by
    refine sum_bij' (fun a _ => a / (1 - a)) (fun b _ => b / (1 + b)) (fun x hx => ?_)
      (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun _ _ => rfl)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx ⊢
      rw [div_eq_iff <| sub_ne_zero.mpr ((ne_eq ..).symm ▸ hx).symm]; rw [mul_sub]; rw [mul_one]; rw [neg_one_mul]; rw [sub_neg_eq_add]; rw [right_eq_add]; rw [neg_eq_zero]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy ⊢
      rw [div_eq_iff fun h => hy <| eq_neg_of_add_eq_zero_right h]; rw [one_mul]; rw [right_eq_add]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm]; rw [← sub_eq_zero] at hx
      simp [field]
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm]; rw [neg_eq_iff_eq_neg]; rw [← sub_eq_zero]; rw [sub_neg_eq_add] at hy
      simp [field]
  rw [this]; rw [← add_eq_zero_iff_eq_neg]; rw [← sum_eq_sum_sdiff_singleton_add (mem_univ (-1 : F))]
  exact MulChar.sum_eq_zero_of_ne_one hχ

Depends on / 依赖: MulChar, MulChar.inv_apply, add_zero, classical, div_eq_mul_inv, div_zero, inv_apply, jacobiSum, map_mul, map_zero, mem_sdiff, mem_singleton, mem_univ, sub_self, sum_bij, sum_eq_sum_sdiff_singleton_add
-/
theorem jacobiSum_nontrivial_inv {χ : MulChar F R} (hχ : χ != 1) : jacobiSum χ χ⁻¹ = -χ (-1) := by
  classical
  rw [jacobiSum]
  conv => enter [1, 2, x]; rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  rw [sum_eq_sum_sdiff_singleton_add (mem_univ (1 : F))]; rw [sub_self]; rw [div_zero]; rw [χ.map_zero]; rw [add_zero]
  have : ∑ x in univ \ {1}, χ (x / (1 - x)) = ∑ x in univ \ {-1}, χ x := by
    refine sum_bij' (fun a _ => a / (1 - a)) (fun b _ => b / (1 + b)) (fun x hx => ?_)
      (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun _ _ => rfl)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx ⊢
      rw [div_eq_iff <| sub_ne_zero.mpr ((ne_eq ..).symm ▸ hx).symm]; rw [mul_sub]; rw [mul_one]; rw [neg_one_mul]; rw [sub_neg_eq_add]; rw [right_eq_add]; rw [neg_eq_zero]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy ⊢
      rw [div_eq_iff fun h => hy <| eq_neg_of_add_eq_zero_right h]; rw [one_mul]; rw [right_eq_add]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm]; rw [← sub_eq_zero] at hx
      simp [field]
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm]; rw [neg_eq_iff_eq_neg]; rw [← sub_eq_zero]; rw [sub_neg_eq_add] at hy
      simp [field]
  rw [this]; rw [← add_eq_zero_iff_eq_neg]; rw [← sum_eq_sum_sdiff_singleton_add (mem_univ (-1 : F))]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/--
theorem `jacobiSum_mul_nontrivial` / 定理 `jacobiSum_mul_nontrivial`

English:
theorem jacobiSum_mul_nontrivial
  given: {χ φ : MulChar F R} (h : χ * φ != 1) (ψ : AddChar F R)
  proof: by
  classical
  rw [gaussSum_mul _ _ ψ]; rw [sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]
  conv =>
    enter [2, 2, 2, x]
    rw [zero_sub]; rw [neg_eq_neg_one_mul x]; rw [map_mul]; rw [mul_left_comm (χ x) (φ (-1))]; rw [← MulChar.mul_apply]; rw [ψ.map_zero_eq_one]; rw [mul_one]
  rw [← mul_sum _ _ (φ (-1))]; rw [MulChar.sum_eq_zero_of_ne_one h]; rw [mul_zero]; rw [add_zero]
  have sum_eq : forall t in univ \ {0}, (∑ x : F, χ x * φ (t - x)) * ψ t =
      (∑ y : F, χ (t * y) * φ (t - (t * y))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at ht
    exact congrArg (· * ψ t) (Equiv.sum_comp (Equiv.mulLeft₀ t ht) _).symm
  simp_rw [← sum_mul, sum_congr rfl sum_eq, ← mul_one_sub, map_mul, mul_assoc]
  conv => enter [2, 2, t, 1, 2, x, 2]; rw [← mul_assoc, mul_comm (χ x) (φ t)]
  simp_rw [← mul_assoc, ← MulChar.mul_apply, mul_assoc, ← mul_sum, mul_right_comm]
  rw [← jacobiSum]; rw [← sum_mul]; rw [gaussSum]; rw [sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]; rw [(χ * φ).map_zero]; rw [zero_mul]; rw [add_zero]

中文:
定理 jacobiSum_mul_nontrivial
  条件: {χ φ : 乘法特征 F R} (h : χ * φ != 1) (ψ : 加法特征 F R)
  证明: by
  classical
  rw [gaussSum_mul _ _ ψ]; rw [sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]
  conv =>
    enter [2, 2, 2, x]
    rw [zero_sub]; rw [neg_eq_neg_one_mul x]; rw [map_mul]; rw [mul_left_comm (χ x) (φ (-1))]; rw [← MulChar.mul_apply]; rw [ψ.map_zero_eq_one]; rw [mul_one]
  rw [← mul_sum _ _ (φ (-1))]; rw [MulChar.sum_eq_zero_of_ne_one h]; rw [mul_zero]; rw [add_zero]
  have sum_eq : forall t in univ \ {0}, (∑ x : F, χ x * φ (t - x)) * ψ t =
      (∑ y : F, χ (t * y) * φ (t - (t * y))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at ht
    exact congrArg (· * ψ t) (Equiv.sum_comp (Equiv.mulLeft₀ t ht) _).symm
  simp_rw [← sum_mul, sum_congr rfl sum_eq, ← mul_one_sub, map_mul, mul_assoc]
  conv => enter [2, 2, t, 1, 2, x, 2]; rw [← mul_assoc, mul_comm (χ x) (φ t)]
  simp_rw [← mul_assoc, ← MulChar.mul_apply, mul_assoc, ← mul_sum, mul_right_comm]
  rw [← jacobiSum]; rw [← sum_mul]; rw [gaussSum]; rw [sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]; rw [(χ * φ).map_zero]; rw [zero_mul]; rw [add_zero]

Depends on / 依赖: MulChar, MulChar.mul_apply, MulChar.sum_eq_zero_of_ne_one, add_zero, classical, gaussSum_mul, map_mul, map_zero_eq_one, mem_univ, mul_apply, mul_left_comm, mul_one, mul_sum, mul_zero, neg_eq_neg_one_mul, sum_eq, sum_eq_sum_sdiff_singleton_add, sum_eq_zero_of_ne_one, zero_sub
-/
theorem jacobiSum_mul_nontrivial {χ φ : MulChar F R} (h : χ * φ != 1) (ψ : AddChar F R) :
    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ := by
  classical
  rw [gaussSum_mul _ _ ψ]; rw [sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]
  conv =>
    enter [2, 2, 2, x]
    rw [zero_sub]; rw [neg_eq_neg_one_mul x]; rw [map_mul]; rw [mul_left_comm (χ x) (φ (-1))]; rw [← MulChar.mul_apply]; rw [ψ.map_zero_eq_one]; rw [mul_one]
  rw [← mul_sum _ _ (φ (-1))]; rw [MulChar.sum_eq_zero_of_ne_one h]; rw [mul_zero]; rw [add_zero]
  have sum_eq : forall t in univ \ {0}, (∑ x : F, χ x * φ (t - x)) * ψ t =
      (∑ y : F, χ (t * y) * φ (t - (t * y))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at ht
    exact congrArg (· * ψ t) (Equiv.sum_comp (Equiv.mulLeft₀ t ht) _).symm
  simp_rw [← sum_mul, sum_congr rfl sum_eq, ← mul_one_sub, map_mul, mul_assoc]
  conv => enter [2, 2, t, 1, 2, x, 2]; rw [← mul_assoc, mul_comm (χ x) (φ t)]
  simp_rw [← mul_assoc, ← MulChar.mul_apply, mul_assoc, ← mul_sum, mul_right_comm]
  rw [← jacobiSum]; rw [← sum_mul]; rw [gaussSum]; rw [sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]; rw [(χ * φ).map_zero]; rw [zero_mul]; rw [add_zero]

end FiniteField

section field_field

variable {F F' : Type*} [Fintype F] [Field F] [Field F']

/--
theorem `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum` / 定理 `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`

English:
theorem jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum
  statement: (h : (Fintype.card F : F') != 0)
  proof: by
  rw [eq_div_iff <| gaussSum_ne_zero_of_nontrivial h hχφ hψ]; rw [mul_comm]
  exact jacobiSum_mul_nontrivial hχφ ψ

中文:
定理 jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum
  结论: (h : (有限类型.card F : F') != 0)
  证明: by
  rw [eq_div_iff <| gaussSum_ne_zero_of_nontrivial h hχφ hψ]; rw [mul_comm]
  exact jacobiSum_mul_nontrivial hχφ ψ

Depends on / 依赖: eq_div_iff, gaussSum_ne_zero_of_nontrivial, jacobiSum_mul_nontrivial, mul_comm
-/
theorem jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (h : (Fintype.card F : F') != 0)
    {χ φ : MulChar F F'} (hχφ : χ * φ != 1) {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ := by
  rw [eq_div_iff <| gaussSum_ne_zero_of_nontrivial h hχφ hψ]; rw [mul_comm]
  exact jacobiSum_mul_nontrivial hχφ ψ

open AddChar MulChar in
/--
lemma `jacobiSum_mul_jacobiSum_inv` / 引理 `jacobiSum_mul_jacobiSum_inv`

English:
lemma jacobiSum_mul_jacobiSum_inv
  statement: (h : ringChar F' != ringChar F) {χ φ : MulChar F F'} (hχ : χ != 1)
  proof: by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- Obtain primitive additive character `ψ : F → FF'`.
  let ψ := FiniteField.primitiveChar F F' h
  -- the target field of `ψ`
  let FF' := CyclotomicField ψ.n F'
  -- Consider `χ` and `φ` as characters `F → FF'`.
  let χ' := χ.ringHomComp (algebraMap F' FF')
  let φ' := φ.ringHomComp (algebraMap F' FF')
  have hinj := (algebraMap F' FF').injective
  apply hinj
  rw [map_mul]; rw [← jacobiSum_ringHomComp]; rw [← jacobiSum_ringHomComp]
  have Hχφ : χ' * φ' != 1 := by
    rw [← ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hχφ
  have Hχφ' : χ'⁻¹ * φ'⁻¹ != 1 := by
    rwa [← mul_inv, inv_ne_one]
  have Hχ : χ' != 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hχ
  have Hφ : φ' != 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hφ
  have Hcard : (Fintype.card F : FF') != 0 := by
    intro H
    simp only [hc, Nat.cast_pow, ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] at H
exact h (Algebra.ringChar_eq F' FF').trans CharP.ringChar_of_prime_eq_zero hp H
  have H := (gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim).trans_ne Hcard
  apply_fun (gaussSum (χ' * φ') ψ.char * gaussSum (χ' * φ')⁻¹ ψ.char⁻¹ * ·)
    using mul_right_injective₀ H
  simp only
  rw [mul_mul_mul_comm]; rw [jacobiSum_mul_nontrivial Hχφ]; rw [mul_inv]; rw [← ringHomComp_inv]; rw [← ringHomComp_inv]; rw [jacobiSum_mul_nontrivial Hχφ']; rw [map_natCast]; rw [← mul_mul_mul_comm]; rw [gaussSum_mul_gaussSum_eq_card Hχ ψ.prim]; rw [gaussSum_mul_gaussSum_eq_card Hφ ψ.prim]; rw [← mul_inv]; rw [gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim]

中文:
引理 jacobiSum_mul_jacobiSum_inv
  结论: (h : ringChar F' != ringChar F) {χ φ : 乘法特征 F F'} (hχ : χ != 1)
  证明: by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- Obtain primitive additive character `ψ : F → FF'`.
  let ψ := FiniteField.primitiveChar F F' h
  -- the target field of `ψ`
  let FF' := CyclotomicField ψ.n F'
  -- Consider `χ` and `φ` as characters `F → FF'`.
  let χ' := χ.ringHomComp (algebraMap F' FF')
  let φ' := φ.ringHomComp (algebraMap F' FF')
  have hinj := (algebraMap F' FF').injective
  apply hinj
  rw [map_mul]; rw [← jacobiSum_ringHomComp]; rw [← jacobiSum_ringHomComp]
  have Hχφ : χ' * φ' != 1 := by
    rw [← ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hχφ
  have Hχφ' : χ'⁻¹ * φ'⁻¹ != 1 := by
    rwa [← mul_inv, inv_ne_one]
  have Hχ : χ' != 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hχ
  have Hφ : φ' != 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hφ
  have Hcard : (Fintype.card F : FF') != 0 := by
    intro H
    simp only [hc, Nat.cast_pow, ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] at H
exact h (Algebra.ringChar_eq F' FF').trans CharP.ringChar_of_prime_eq_zero hp H
  have H := (gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim).trans_ne Hcard
  apply_fun (gaussSum (χ' * φ') ψ.char * gaussSum (χ' * φ')⁻¹ ψ.char⁻¹ * ·)
    using mul_right_injective₀ H
  simp only
  rw [mul_mul_mul_comm]; rw [jacobiSum_mul_nontrivial Hχφ]; rw [mul_inv]; rw [← ringHomComp_inv]; rw [← ringHomComp_inv]; rw [jacobiSum_mul_nontrivial Hχφ']; rw [map_natCast]; rw [← mul_mul_mul_comm]; rw [gaussSum_mul_gaussSum_eq_card Hχ ψ.prim]; rw [gaussSum_mul_gaussSum_eq_card Hφ ψ.prim]; rw [← mul_inv]; rw [gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim]

Depends on / 依赖: FiniteField, FiniteField.card, ringChar
-/
lemma jacobiSum_mul_jacobiSum_inv (h : ringChar F' != ringChar F) {χ φ : MulChar F F'} (hχ : χ != 1)
    (hφ : φ != 1) (hχφ : χ * φ != 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- Obtain primitive additive character `ψ : F → FF'`.
  let ψ := FiniteField.primitiveChar F F' h
  -- the target field of `ψ`
  let FF' := CyclotomicField ψ.n F'
  -- Consider `χ` and `φ` as characters `F → FF'`.
  let χ' := χ.ringHomComp (algebraMap F' FF')
  let φ' := φ.ringHomComp (algebraMap F' FF')
  have hinj := (algebraMap F' FF').injective
  apply hinj
  rw [map_mul]; rw [← jacobiSum_ringHomComp]; rw [← jacobiSum_ringHomComp]
  have Hχφ : χ' * φ' != 1 := by
    rw [← ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hχφ
  have Hχφ' : χ'⁻¹ * φ'⁻¹ != 1 := by
    rwa [← mul_inv, inv_ne_one]
  have Hχ : χ' != 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hχ
  have Hφ : φ' != 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hφ
  have Hcard : (Fintype.card F : FF') != 0 := by
    intro H
    simp only [hc, Nat.cast_pow, ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] at H
exact h (Algebra.ringChar_eq F' FF').trans CharP.ringChar_of_prime_eq_zero hp H
  have H := (gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim).trans_ne Hcard
  apply_fun (gaussSum (χ' * φ') ψ.char * gaussSum (χ' * φ')⁻¹ ψ.char⁻¹ * ·)
    using mul_right_injective₀ H
  simp only
  rw [mul_mul_mul_comm]; rw [jacobiSum_mul_nontrivial Hχφ]; rw [mul_inv]; rw [← ringHomComp_inv]; rw [← ringHomComp_inv]; rw [jacobiSum_mul_nontrivial Hχφ']; rw [map_natCast]; rw [← mul_mul_mul_comm]; rw [gaussSum_mul_gaussSum_eq_card Hχ ψ.prim]; rw [gaussSum_mul_gaussSum_eq_card Hφ ψ.prim]; rw [← mul_inv]; rw [gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim]

end field_field

section image

variable {F R : Type*} [Field F] [CommRing R] [IsDomain R]

open Algebra

section finite

variable [Finite F]

private
/--
lemma `MulChar.exists_apply_sub_one_eq_mul_sub_one` / 引理 `MulChar.exists_apply_sub_one_eq_mul_sub_one`

English:
lemma MulChar.exists_apply_sub_one_eq_mul_sub_one
  statement: {n : Nat} [NeZero n] {χ : MulChar F R} {μ : R}
  proof: by
  obtain ⟨k, _, hk⟩ := exists_apply_eq_pow hχ hμ hx
  refine hk ▸ ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ => Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

private

中文:
引理 乘法特征.存在_apply_sub_one_eq_mul_sub_one
  结论: {n : 自然数} [NeZero n] {χ : 乘法特征 F R} {μ : R}
  证明: by
  obtain ⟨k, _, hk⟩ := exists_apply_eq_pow hχ hμ hx
  refine hk ▸ ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ => Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

private

Depends on / 依赖: Finset, Finset.range, Subalgebra, Subalgebra.pow_mem, Subalgebra.sum_mem, exists_apply_eq_pow, geom_sum_mul, pow_mem, self_mem_adjoin_singleton, sum_mem
-/
lemma MulChar.exists_apply_sub_one_eq_mul_sub_one {n : Nat} [NeZero n] {χ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hμ : IsPrimitiveRoot μ n) {x : F} (hx : x != 0) :
    exists z in Int[μ], χ x - 1 = z * (μ - 1) := by
  obtain ⟨k, _, hk⟩ := exists_apply_eq_pow hχ hμ hx
  refine hk ▸ ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ => Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

private
/--
lemma `MulChar.exists_apply_sub_one_mul_apply_sub_one` / 引理 `MulChar.exists_apply_sub_one_mul_apply_sub_one`

English:
lemma MulChar.exists_apply_sub_one_mul_apply_sub_one
  statement: {n : Nat} [NeZero n] {χ ψ : MulChar F R}
  proof: by
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨0, Subalgebra.zero_mem _, by rw [sub_zero, ψ.map_one, sub_self, mul_zero, zero_mul]⟩
  rcases eq_or_ne x 1 with rfl | hx₁
  · exact ⟨0, Subalgebra.zero_mem _, by rw [χ.map_one, sub_self, zero_mul, zero_mul]⟩
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.exists_apply_sub_one_eq_mul_sub_one hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ :=
    MulChar.exists_apply_sub_one_eq_mul_sub_one hψ hμ (sub_ne_zero_of_ne hx₁.symm)
  rewrite [Hz₁, Hz₂, sq]
  exact ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_mul_mul_comm ..⟩

中文:
引理 乘法特征.存在_apply_sub_one_mul_apply_sub_one
  结论: {n : 自然数} [NeZero n] {χ ψ : 乘法特征 F R}
  证明: by
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨0, Subalgebra.zero_mem _, by rw [sub_zero, ψ.map_one, sub_self, mul_zero, zero_mul]⟩
  rcases eq_or_ne x 1 with rfl | hx₁
  · exact ⟨0, Subalgebra.zero_mem _, by rw [χ.map_one, sub_self, zero_mul, zero_mul]⟩
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.exists_apply_sub_one_eq_mul_sub_one hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ :=
    MulChar.exists_apply_sub_one_eq_mul_sub_one hψ hμ (sub_ne_zero_of_ne hx₁.symm)
  rewrite [Hz₁, Hz₂, sq]
  exact ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_mul_mul_comm ..⟩

Depends on / 依赖: MulChar, MulChar.exists_apply_sub_one_eq_mul_sub_one, Subalgebra, Subalgebra.mul_mem, Subalgebra.zero_mem, eq_or_ne, exists_apply_sub_one_eq_mul_sub_one, map_one, mul_mem, mul_zero, rewrite, sub_ne_zero_of_ne, sub_self, sub_zero, zero_mem, zero_mul
-/
lemma MulChar.exists_apply_sub_one_mul_apply_sub_one {n : Nat} [NeZero n] {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hμ : IsPrimitiveRoot μ n) (x : F) :
    exists z in Int[μ], (χ x - 1) * (ψ (1 - x) - 1) = z * (μ - 1) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨0, Subalgebra.zero_mem _, by rw [sub_zero, ψ.map_one, sub_self, mul_zero, zero_mul]⟩
  rcases eq_or_ne x 1 with rfl | hx₁
  · exact ⟨0, Subalgebra.zero_mem _, by rw [χ.map_one, sub_self, zero_mul, zero_mul]⟩
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.exists_apply_sub_one_eq_mul_sub_one hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ :=
    MulChar.exists_apply_sub_one_eq_mul_sub_one hψ hμ (sub_ne_zero_of_ne hx₁.symm)
  rewrite [Hz₁, Hz₂, sq]
  exact ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_mul_mul_comm ..⟩

end finite

variable [Fintype F]

/--
lemma `jacobiSum_mem_algebraAdjoin_of_pow_eq_one` / 引理 `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`

English:
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq_one
  statement: {n : Nat} [NeZero n] {χ φ : MulChar F R}
  proof: Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hχ hμ _)
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hφ hμ _)

中文:
引理 jacobiSum_mem_algebraAdjoin_of_pow_eq_one
  结论: {n : 自然数} [NeZero n] {χ φ : 乘法特征 F R}
  证明: Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hχ hμ _)
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hφ hμ _)

Depends on / 依赖: MulChar, MulChar.apply_mem_algebraAdjoin_of_pow_eq_one, Subalgebra, Subalgebra.mul_mem, Subalgebra.sum_mem, apply_mem_algebraAdjoin_of_pow_eq_one, mul_mem, sum_mem
-/
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq_one {n : Nat} [NeZero n] {χ φ : MulChar F R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ φ in Int[μ] :=
  Subalgebra.sum_mem _ fun _ _ => Subalgebra.mul_mem _
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hχ hμ _)
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hφ hμ _)

/--
lemma `exists_jacobiSum_eq_neg_one_add` / 引理 `exists_jacobiSum_eq_neg_one_add`

English:
lemma exists_jacobiSum_eq_neg_one_add
  statement: {n : Nat} (hn : 2 < n) {χ ψ : MulChar F R}
  proof: by
  obtain ⟨q, hq⟩ := hn'
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.self_sub_one_pow_dvd_order hn
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_one_one]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Hz₁]
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀]; rw [jacobiSum_one_nontrivial hψ₀]; rw [zero_mul]; rw [add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm]; rw [hψ₀]; rw [jacobiSum_one_nontrivial hχ₀]; rw [zero_mul]; rw [add_zero]
  · classical
    rw [jacobiSum_eq_aux]; rw [MulChar.sum_eq_zero_of_ne_one hχ₀]; rw [MulChar.sum_eq_zero_of_ne_one hψ₀]; rw [hq]
    have : NeZero n := ⟨by lia⟩
    have H := MulChar.exists_apply_sub_one_mul_apply_sub_one hχ hψ hμ
    have Hcs x := (H x).choose_spec
    refine ⟨-q * z₁ + ∑ x in (univ \ {0, 1} : Finset F), (H x).choose, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ => (Hcs x).1
    · conv => enter [1, 2, 2, x]; rw [(Hcs x).2]
      rw [← Finset.sum_mul]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Hz₁]
      ring

中文:
引理 存在_jacobiSum_eq_neg_one_add
  结论: {n : 自然数} (hn : 2 < n) {χ ψ : 乘法特征 F R}
  证明: by
  obtain ⟨q, hq⟩ := hn'
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.self_sub_one_pow_dvd_order hn
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_one_one]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Hz₁]
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀]; rw [jacobiSum_one_nontrivial hψ₀]; rw [zero_mul]; rw [add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm]; rw [hψ₀]; rw [jacobiSum_one_nontrivial hχ₀]; rw [zero_mul]; rw [add_zero]
  · classical
    rw [jacobiSum_eq_aux]; rw [MulChar.sum_eq_zero_of_ne_one hχ₀]; rw [MulChar.sum_eq_zero_of_ne_one hψ₀]; rw [hq]
    have : NeZero n := ⟨by lia⟩
    have H := MulChar.exists_apply_sub_one_mul_apply_sub_one hχ hψ hμ
    have Hcs x := (H x).choose_spec
    refine ⟨-q * z₁ + ∑ x in (univ \ {0, 1} : Finset F), (H x).choose, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ => (Hcs x).1
    · conv => enter [1, 2, 2, x]; rw [(Hcs x).2]
      rw [← Finset.sum_mul]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Hz₁]
      ring

Depends on / 依赖: Nat.cast_add, Nat.cast_mul, Nat.sub_eq_iff_eq_add, NeZero, NeZero.one_le, Subalgebra, Subalgebra.mul_mem, Subalgebra.natCast_mem, Subalgebra.zero_mem, add_zero, cast_add, cast_mul, jacobiSum_one_nontrivial, jacobiSum_one_one, mul_mem, natCast_mem, one_le, self_sub_one_pow_dvd_order, sub_eq_iff_eq_add, zero_mem
-/
lemma exists_jacobiSum_eq_neg_one_add {n : Nat} (hn : 2 < n) {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hn' : n ∣ Fintype.card F - 1)
    (hμ : IsPrimitiveRoot μ n) :
    exists z in Int[μ], jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2 := by
  obtain ⟨q, hq⟩ := hn'
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.self_sub_one_pow_dvd_order hn
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_one_one]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Hz₁]
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀]; rw [jacobiSum_one_nontrivial hψ₀]; rw [zero_mul]; rw [add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm]; rw [hψ₀]; rw [jacobiSum_one_nontrivial hχ₀]; rw [zero_mul]; rw [add_zero]
  · classical
    rw [jacobiSum_eq_aux]; rw [MulChar.sum_eq_zero_of_ne_one hχ₀]; rw [MulChar.sum_eq_zero_of_ne_one hψ₀]; rw [hq]
    have : NeZero n := ⟨by lia⟩
    have H := MulChar.exists_apply_sub_one_mul_apply_sub_one hχ hψ hμ
    have Hcs x := (H x).choose_spec
    refine ⟨-q * z₁ + ∑ x in (univ \ {0, 1} : Finset F), (H x).choose, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ => (Hcs x).1
    · conv => enter [1, 2, 2, x]; rw [(Hcs x).2]
      rw [← Finset.sum_mul]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Hz₁]
      ring

end image

section GaussSum

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]

/--
lemma `gaussSum_pow_eq_prod_jacobiSum_aux` / 引理 `gaussSum_pow_eq_prod_jacobiSum_aux`

English:
lemma gaussSum_pow_eq_prod_jacobiSum_aux
  statement: (χ : MulChar F R) (ψ : AddChar F R) {n : Nat}
  proof: by
  induction n, hn₁ using Nat.le_induction with
  | base => simp only [pow_one, le_refl, Ico_eq_empty_of_le, prod_empty, mul_one]
  | succ n hn ih =>
specialize ih lt_trans (Nat.lt_succ_self n) hn₂
      have gauss_rw : gaussSum (χ ^ n) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ n) * gaussSum (χ ^ (n + 1)) ψ := by
        have hχn : χ * (χ ^ n) != 1 :=
          pow_succ' χ n ▸ pow_ne_one_of_lt_orderOf n.add_one_ne_zero hn₂
        rw [mul_comm]; rw [← jacobiSum_mul_nontrivial hχn]; rw [mul_comm]; rw [← pow_succ']
      apply_fun (· * gaussSum χ ψ) at ih
      rw [mul_right_comm]; rw [← pow_succ]; rw [gauss_rw] at ih
      rw [ih]; rw [Finset.prod_Ico_succ_top hn]; rw [mul_rotate]; rw [mul_assoc]

中文:
引理 gaussSum_pow_eq_prod_jacobiSum_aux
  结论: (χ : 乘法特征 F R) (ψ : 加法特征 F R) {n : 自然数}
  证明: by
  induction n, hn₁ using Nat.le_induction with
  | base => simp only [pow_one, le_refl, Ico_eq_empty_of_le, prod_empty, mul_one]
  | succ n hn ih =>
specialize ih lt_trans (Nat.lt_succ_self n) hn₂
      have gauss_rw : gaussSum (χ ^ n) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ n) * gaussSum (χ ^ (n + 1)) ψ := by
        have hχn : χ * (χ ^ n) != 1 :=
          pow_succ' χ n ▸ pow_ne_one_of_lt_orderOf n.add_one_ne_zero hn₂
        rw [mul_comm]; rw [← jacobiSum_mul_nontrivial hχn]; rw [mul_comm]; rw [← pow_succ']
      apply_fun (· * gaussSum χ ψ) at ih
      rw [mul_right_comm]; rw [← pow_succ]; rw [gauss_rw] at ih
      rw [ih]; rw [Finset.prod_Ico_succ_top hn]; rw [mul_rotate]; rw [mul_assoc]

Depends on / 依赖: Ico_eq_empty_of_le, Nat.le_induction, Nat.lt_succ_self, add_one_ne_zero, apply_fun, gaussSum, gauss_rw, jacobiSum, jacobiSum_mul_nontrivial, le_induction, le_refl, lt_succ_self, lt_trans, mul_comm, mul_one, n.add_one_ne_zero, pow_ne_one_of_lt_orderOf, pow_one, pow_succ, prod_empty
-/
lemma gaussSum_pow_eq_prod_jacobiSum_aux (χ : MulChar F R) (ψ : AddChar F R) {n : Nat}
    (hn₁ : 0 < n) (hn₂ : n < orderOf χ) :
    gaussSum χ ψ ^ n = gaussSum (χ ^ n) ψ * ∏ j in Ico 1 n, jacobiSum χ (χ ^ j) := by
  induction n, hn₁ using Nat.le_induction with
  | base => simp only [pow_one, le_refl, Ico_eq_empty_of_le, prod_empty, mul_one]
  | succ n hn ih =>
specialize ih lt_trans (Nat.lt_succ_self n) hn₂
      have gauss_rw : gaussSum (χ ^ n) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ n) * gaussSum (χ ^ (n + 1)) ψ := by
        have hχn : χ * (χ ^ n) != 1 :=
          pow_succ' χ n ▸ pow_ne_one_of_lt_orderOf n.add_one_ne_zero hn₂
        rw [mul_comm]; rw [← jacobiSum_mul_nontrivial hχn]; rw [mul_comm]; rw [← pow_succ']
      apply_fun (· * gaussSum χ ψ) at ih
      rw [mul_right_comm]; rw [← pow_succ]; rw [gauss_rw] at ih
      rw [ih]; rw [Finset.prod_Ico_succ_top hn]; rw [mul_rotate]; rw [mul_assoc]

/--
theorem `gaussSum_pow_eq_prod_jacobiSum` / 定理 `gaussSum_pow_eq_prod_jacobiSum`

English:
theorem gaussSum_pow_eq_prod_jacobiSum
  statement: {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2 <= orderOf χ)
  proof: by
  have := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ (n := orderOf χ - 1) (by lia) (by lia)
  apply_fun (gaussSum χ ψ * ·) at this
  rw [← pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos (by lia)] at this
  have hχ₁ : χ != 1 :=
    fun h => ((orderOf_one (G := MulChar F R) ▸ h ▸ hχ).trans_lt Nat.one_lt_two).false
  rw [this]; rw [← mul_assoc]; rw [gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ]

中文:
定理 gaussSum_pow_eq_prod_jacobiSum
  结论: {χ : 乘法特征 F R} {ψ : 加法特征 F R} (hχ : 2 <= orderOf χ)
  证明: by
  have := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ (n := orderOf χ - 1) (by lia) (by lia)
  apply_fun (gaussSum χ ψ * ·) at this
  rw [← pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos (by lia)] at this
  have hχ₁ : χ != 1 :=
    fun h => ((orderOf_one (G := MulChar F R) ▸ h ▸ hχ).trans_lt Nat.one_lt_two).false
  rw [this]; rw [← mul_assoc]; rw [gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ]

Depends on / 依赖: MulChar, Nat.one_lt_two, Nat.sub_one_add_one_eq_of_pos, apply_fun, gaussSum, gaussSum_mul_gaussSum_pow_orderOf_sub_one, gaussSum_pow_eq_prod_jacobiSum_aux, mul_assoc, one_lt_two, orderOf, orderOf_one, pow_succ, sub_one_add_one_eq_of_pos, trans_lt
-/
theorem gaussSum_pow_eq_prod_jacobiSum {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2 <= orderOf χ)
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ orderOf χ =
      χ (-1) * Fintype.card F * ∏ i in Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) := by
  have := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ (n := orderOf χ - 1) (by lia) (by lia)
  apply_fun (gaussSum χ ψ * ·) at this
  rw [← pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos (by lia)] at this
  have hχ₁ : χ != 1 :=
    fun h => ((orderOf_one (G := MulChar F R) ▸ h ▸ hχ).trans_lt Nat.one_lt_two).false
  rw [this]; rw [← mul_assoc]; rw [gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ]

end GaussSum
