/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.W.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinalMk_le_max_aleph0_of_finite` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `WType β` is at most the maximum of the
cardinality of `α` and `ℵ₀`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `WType` to `MvPolynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `MvPolynomial`.

## Tags

W, W type, cardinal, first order
-/

public section


universe u v

variable {α : Type u} {β : α -> Type v}

noncomputable section

namespace WType

open Cardinal


/--
theorem `cardinalMk_eq_sum_lift` / 定理 `cardinalMk_eq_sum_lift`

English:
theorem cardinalMk_eq_sum_lift
  statement: #(WType β) = sum fun a => #(WType β) ^ lift.{u} #(β a)
  proof: (mk_congr <| equivSigma β).trans by
    simp_rw [mk_sigma, mk_arrow]; rw [lift_id'.{v, u}, lift_umax.{v, u}]

中文:
定理 cardinalMk_eq_sum_lift
  结论: #(WType β) = 求和 fun a => #(WType β) ^ lift.{u} #(β a)
  证明: (mk_congr <| equivSigma β).trans by
    simp_rw [mk_sigma, mk_arrow]; rw [lift_id'.{v, u}, lift_umax.{v, u}]

Depends on / 依赖: equivSigma, lift_id, lift_umax, mk_arrow, mk_congr, mk_sigma, simp_rw
-/
theorem cardinalMk_eq_sum_lift : #(WType β) = sum fun a => #(WType β) ^ lift.{u} #(β a) :=
(mk_congr <| equivSigma β).trans by
    simp_rw [mk_sigma, mk_arrow]; rw [lift_id'.{v, u}, lift_umax.{v, u}]

/--
theorem `cardinalMk_le_of_le'` / 定理 `cardinalMk_le_of_le'`

English:
theorem cardinalMk_le_of_le'
  statement: {κ : Cardinal.{max u v}}
  proof: by
  induction κ using Cardinal.inductionOn with | _ γ
  simp_rw [← lift_umax.{v, u}] at hκ
  nth_rewrite 1 [← lift_id'.{v, u} #γ] at hκ
  simp_rw [← mk_arrow, ← mk_sigma, le_def] at hκ
  obtain ⟨hκ⟩ := hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

中文:
定理 cardinalMk_le_of_le'
  结论: {κ : 基数.{最大值 u v}}
  证明: by
  induction κ using Cardinal.inductionOn with | _ γ
  simp_rw [← lift_umax.{v, u}] at hκ
  nth_rewrite 1 [← lift_id'.{v, u} #γ] at hκ
  simp_rw [← mk_arrow, ← mk_sigma, le_def] at hκ
  obtain ⟨hκ⟩ := hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

Depends on / 依赖: Cardinal, Cardinal.inductionOn, Cardinal.mk_le_of_injective, elim_injective, inductionOn, le_def, lift_id, lift_umax, mk_arrow, mk_le_of_injective, mk_sigma, nth_rewrite, simp_rw
-/
theorem cardinalMk_le_of_le' {κ : Cardinal.{max u v}}
    (hκ : (sum fun a : α => κ ^ lift.{u} #(β a)) <= κ) :
    #(WType β) <= κ := by
  induction κ using Cardinal.inductionOn with | _ γ
  simp_rw [← lift_umax.{v, u}] at hκ
  nth_rewrite 1 [← lift_id'.{v, u} #γ] at hκ
  simp_rw [← mk_arrow, ← mk_sigma, le_def] at hκ
  obtain ⟨hκ⟩ := hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

/--
theorem `cardinalMk_le_max_aleph0_of_finite'` / 定理 `cardinalMk_le_max_aleph0_of_finite'`

English:
theorem cardinalMk_le_max_aleph0_of_finite'
  given: [forall a, Finite (β a)]
  proof: (isEmpty_or_nonempty α).elim (fun _ => by simp)
    fun hn =>
    let m := max (lift.{v} #α) ℵ₀
cardinalMk_le_of_le'
      calc
        (Cardinal.sum fun a => m ^ lift.{u} #(β a)) <= lift.{v} #α * ⨆ a, m ^ lift.{u} #(β a) :=
          Cardinal.sum_le_lift_mk_mul_iSup _
        _ <= m * ⨆ a, m ^ lift.{u} #(β a) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = m :=
          mul_eq_left (le_max_right _ _)
(ciSup_le' fun _ => pow_le (le_max_right _ _) (lt_aleph0_of_finite _))
pos_iff_ne_zero.1
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α := hn
                  refine le_trans ?_ (le_ciSup bddAbove_of_small a)
                  rw [← power_zero]
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph0_pos.trans_le (le_max_right _ _))) zero_le)

中文:
定理 cardinalMk_le_max_aleph0_of_finite'
  条件: [对任意 a, 有限 (β a)]
  证明: (isEmpty_or_nonempty α).elim (fun _ => by simp)
    fun hn =>
    let m := max (lift.{v} #α) ℵ₀
cardinalMk_le_of_le'
      calc
        (Cardinal.sum fun a => m ^ lift.{u} #(β a)) <= lift.{v} #α * ⨆ a, m ^ lift.{u} #(β a) :=
          Cardinal.sum_le_lift_mk_mul_iSup _
        _ <= m * ⨆ a, m ^ lift.{u} #(β a) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = m :=
          mul_eq_left (le_max_right _ _)
(ciSup_le' fun _ => pow_le (le_max_right _ _) (lt_aleph0_of_finite _))
pos_iff_ne_zero.1
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α := hn
                  refine le_trans ?_ (le_ciSup bddAbove_of_small a)
                  rw [← power_zero]
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph0_pos.trans_le (le_max_right _ _))) zero_le)

Depends on / 依赖: Cardinal, Cardinal.sum, Cardinal.sum_le_lift_mk_mul_iSup, Nonempt, Order.succ_le_iff, cardinalMk_le_of_le, ciSup_le, isEmpty_or_nonempty, le_max_left, le_max_right, le_rfl, lt_aleph0_of_finite, mul_eq_left, mul_le_mul, pos_iff_ne_zero, pow_le, succ_le_iff, succ_zero, sum_le_lift_mk_mul_iSup
-/
theorem cardinalMk_le_max_aleph0_of_finite' [forall a, Finite (β a)] :
    #(WType β) <= max (lift.{v} #α) ℵ₀ :=
  (isEmpty_or_nonempty α).elim (fun _ => by simp)
    fun hn =>
    let m := max (lift.{v} #α) ℵ₀
cardinalMk_le_of_le'
      calc
        (Cardinal.sum fun a => m ^ lift.{u} #(β a)) <= lift.{v} #α * ⨆ a, m ^ lift.{u} #(β a) :=
          Cardinal.sum_le_lift_mk_mul_iSup _
        _ <= m * ⨆ a, m ^ lift.{u} #(β a) := mul_le_mul' (le_max_left _ _) le_rfl
        _ = m :=
          mul_eq_left (le_max_right _ _)
(ciSup_le' fun _ => pow_le (le_max_right _ _) (lt_aleph0_of_finite _))
pos_iff_ne_zero.1
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α := hn
                  refine le_trans ?_ (le_ciSup bddAbove_of_small a)
                  rw [← power_zero]
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph0_pos.trans_le (le_max_right _ _))) zero_le)

variable {β : α -> Type u}

/--
theorem `cardinalMk_eq_sum` / 定理 `cardinalMk_eq_sum`

English:
theorem cardinalMk_eq_sum
  statement: #(WType β) = sum (fun a : α => #(WType β) ^ #(β a))
  proof: cardinalMk_eq_sum_lift.trans by simp_rw [lift_id]

中文:
定理 cardinalMk_eq_sum
  结论: #(WType β) = 求和 (fun a : α => #(WType β) ^ #(β a))
  证明: cardinalMk_eq_sum_lift.trans by simp_rw [lift_id]

Depends on / 依赖: DFinsupp, DFinsupp.single, cardinalMk_eq_sum_lift, cardinalMk_eq_sum_lift.trans, lift_id, simp_rw, single, x.sum
-/
theorem cardinalMk_eq_sum : #(WType β) = sum (fun a : α => #(WType β) ^ #(β a)) :=
cardinalMk_eq_sum_lift.trans by simp_rw [lift_id]

/--
theorem `cardinalMk_le_of_le` / 定理 `cardinalMk_le_of_le`

English:
theorem cardinalMk_le_of_le
  given: {κ : Cardinal.{u}} (hκ : (sum fun a : α => κ ^ #(β a)) <= κ)
  proof: cardinalMk_le_of_le' by simp_rw [lift_id]; exact hκ

中文:
定理 cardinalMk_le_of_le
  条件: {κ : 基数.{u}} (hκ : (求和 fun a : α => κ ^ #(β a)) <= κ)
  证明: cardinalMk_le_of_le' by simp_rw [lift_id]; exact hκ

Depends on / 依赖: cardinalMk_le_of_le, lift_id, simp_rw
-/
theorem cardinalMk_le_of_le {κ : Cardinal.{u}} (hκ : (sum fun a : α => κ ^ #(β a)) <= κ) :
#(WType β) <= κ := cardinalMk_le_of_le' by simp_rw [lift_id]; exact hκ

/--
theorem `cardinalMk_le_max_aleph0_of_finite` / 定理 `cardinalMk_le_max_aleph0_of_finite`

English:
theorem cardinalMk_le_max_aleph0_of_finite
  given: [forall a, Finite (β a)]
  statement: #(WType β) <= max #α ℵ₀
  proof: cardinalMk_le_max_aleph0_of_finite'.trans_eq by rw [lift_id]

中文:
定理 cardinalMk_le_max_aleph0_of_finite
  条件: [对任意 a, 有限 (β a)]
  结论: #(WType β) <= 最大值 #α ℵ₀
  证明: cardinalMk_le_max_aleph0_of_finite'.trans_eq by rw [lift_id]

Depends on / 依赖: cardinalMk_le_max_aleph0_of_finite, lift_id, trans_eq
-/
theorem cardinalMk_le_max_aleph0_of_finite [forall a, Finite (β a)] : #(WType β) <= max #α ℵ₀ :=
cardinalMk_le_max_aleph0_of_finite'.trans_eq by rw [lift_id]

end WType
