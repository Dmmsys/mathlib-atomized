/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Cardinality of algebraic extensions

This file contains results on cardinality of algebraic extensions.
-/

public section


universe u v

open Cardinal Module
open scoped Polynomial

namespace Algebra.IsAlgebraic

variable (R : Type u) [CommRing R] [IsDomain R] (L : Type v) [CommRing L] [IsDomain L] [Algebra R L]
variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

/--
theorem `lift_cardinalMk_le_sigma_polynomial` / 定理 `lift_cardinalMk_le_sigma_polynomial`

English:
theorem lift_cardinalMk_le_sigma_polynomial
  proof: by
  have := @lift_mk_le_lift_mk_of_injective L (Σ p : R[X], {x : L | x in p.aroots L})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      ⟨p.1, x, by
        dsimp
        have := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
        rw [Polynomial.mem_roots this]; rw [Polynomial.IsRoot]; rw [Polynomial.eval_map]; rw [← Polynomial.aeval_def]; rw [p.2.2]⟩)
    fun x y => by
      intro h
      simp only [Set.coe_ofPred, ne_eq, Set.mem_ofPred_eq, Sigma.mk.inj_iff] at h
      refine (Subtype.heq_iff_coe_eq ?_).1 h.2
      simp only [h.1, forall_true_iff]
  rwa [lift_umax, lift_id'.{v}] at this

中文:
定理 lift_cardinalMk_le_sigma_polynomial
  证明: by
  have := @lift_mk_le_lift_mk_of_injective L (Σ p : R[X], {x : L | x in p.aroots L})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      ⟨p.1, x, by
        dsimp
        have := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
        rw [Polynomial.mem_roots this]; rw [Polynomial.IsRoot]; rw [Polynomial.eval_map]; rw [← Polynomial.aeval_def]; rw [p.2.2]⟩)
    fun x y => by
      intro h
      simp only [Set.coe_ofPred, ne_eq, Set.mem_ofPred_eq, Sigma.mk.inj_iff] at h
      refine (Subtype.heq_iff_coe_eq ?_).1 h.2
      simp only [h.1, forall_true_iff]
  rwa [lift_umax, lift_id'.{v}] at this

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, Classical, Classical.indefiniteDescription, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsAlgebraic, IsRoot, Polynomial, Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map, Polynomial.map_ne_zero_iff, Polynomial.mem_roots, Set.coe_ofPred, Set.mem_ofPred_eq, Sigma.mk.inj_iff, aeval_def, algebraMap_injective, aroots
-/
theorem lift_cardinalMk_le_sigma_polynomial :
    lift.{u} #L <= #(Σ p : R[X], { x : L // x in p.aroots L }) := by
  have := @lift_mk_le_lift_mk_of_injective L (Σ p : R[X], {x : L | x in p.aroots L})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      ⟨p.1, x, by
        dsimp
        have := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
        rw [Polynomial.mem_roots this]; rw [Polynomial.IsRoot]; rw [Polynomial.eval_map]; rw [← Polynomial.aeval_def]; rw [p.2.2]⟩)
    fun x y => by
      intro h
      simp only [Set.coe_ofPred, ne_eq, Set.mem_ofPred_eq, Sigma.mk.inj_iff] at h
      refine (Subtype.heq_iff_coe_eq ?_).1 h.2
      simp only [h.1, forall_true_iff]
  rwa [lift_umax, lift_id'.{v}] at this

/--
theorem `lift_cardinalMk_le_max` / 定理 `lift_cardinalMk_le_max`

English:
theorem lift_cardinalMk_le_max
  statement: lift.{u} #L <= lift.{v} #R ⊔ ℵ₀
  proof: calc
    lift.{u} #L <= #(Σ p : R[X], { x : L // x in p.aroots L }) :=
      lift_cardinalMk_le_sigma_polynomial R L
    _ = Cardinal.sum fun p : R[X] => #{x : L | x in p.aroots L} := by
      rw [← mk_sigma]; rfl
    _ <= Cardinal.sum.{u, v} fun _ : R[X] => ℵ₀ :=
      (sum_le_sum _ _ fun _ => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = lift.{v} #(R[X]) * ℵ₀ := by rw [sum_const, lift_aleph0]
_ <= lift.{v} (#R ⊔ ℵ₀) ⊔ ℵ₀ ⊔ ℵ₀ := (mul_le_max _ _).trans by
      gcongr; simp only [lift_le, Polynomial.cardinalMk_le_max]
    _ = _ := by simp

中文:
定理 lift_cardinalMk_le_max
  结论: lift.{u} #L <= lift.{v} #R ⊔ ℵ₀
  证明: calc
    lift.{u} #L <= #(Σ p : R[X], { x : L // x in p.aroots L }) :=
      lift_cardinalMk_le_sigma_polynomial R L
    _ = Cardinal.sum fun p : R[X] => #{x : L | x in p.aroots L} := by
      rw [← mk_sigma]; rfl
    _ <= Cardinal.sum.{u, v} fun _ : R[X] => ℵ₀ :=
      (sum_le_sum _ _ fun _ => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = lift.{v} #(R[X]) * ℵ₀ := by rw [sum_const, lift_aleph0]
_ <= lift.{v} (#R ⊔ ℵ₀) ⊔ ℵ₀ ⊔ ℵ₀ := (mul_le_max _ _).trans by
      gcongr; simp only [lift_le, Polynomial.cardinalMk_le_max]
    _ = _ := by simp

Depends on / 依赖: Cardinal, Cardinal.sum, Multiset, Multiset.finite_toSet, Polynomial, Polynomial.cardinalMk_le_max, aroots, cardinalMk_le_max, finite_toSet, lift_aleph0, lift_cardinalMk_le_sigma_polynomial, lift_le, lt_aleph0, lt_aleph0.le, mk_sigma, mul_le_max, p.aroots, sum_const, sum_le_sum
-/
theorem lift_cardinalMk_le_max : lift.{u} #L <= lift.{v} #R ⊔ ℵ₀ :=
  calc
    lift.{u} #L <= #(Σ p : R[X], { x : L // x in p.aroots L }) :=
      lift_cardinalMk_le_sigma_polynomial R L
    _ = Cardinal.sum fun p : R[X] => #{x : L | x in p.aroots L} := by
      rw [← mk_sigma]; rfl
    _ <= Cardinal.sum.{u, v} fun _ : R[X] => ℵ₀ :=
      (sum_le_sum _ _ fun _ => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = lift.{v} #(R[X]) * ℵ₀ := by rw [sum_const, lift_aleph0]
_ <= lift.{v} (#R ⊔ ℵ₀) ⊔ ℵ₀ ⊔ ℵ₀ := (mul_le_max _ _).trans by
      gcongr; simp only [lift_le, Polynomial.cardinalMk_le_max]
    _ = _ := by simp

variable (L : Type u) [CommRing L] [IsDomain L] [Algebra R L]
variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

/--
theorem `cardinalMk_le_sigma_polynomial` / 定理 `cardinalMk_le_sigma_polynomial`

English:
theorem cardinalMk_le_sigma_polynomial
  proof: by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L

中文:
定理 cardinalMk_le_sigma_polynomial
  证明: by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L

Depends on / 依赖: lift_cardinalMk_le_sigma_polynomial, lift_id
-/
theorem cardinalMk_le_sigma_polynomial :
    #L <= #(Σ p : R[X], { x : L // x in p.aroots L }) := by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L

/-- The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀`. -/
@[stacks 09GK]
/--
theorem `cardinalMk_le_max` / 定理 `cardinalMk_le_max`

English:
theorem cardinalMk_le_max
  statement: #L <= max #R ℵ₀
  proof: by
  simpa only [lift_id] using lift_cardinalMk_le_max R L

中文:
定理 cardinalMk_le_max
  结论: #L <= 最大值 #R ℵ₀
  证明: by
  simpa only [lift_id] using lift_cardinalMk_le_max R L

Depends on / 依赖: lift_cardinalMk_le_max, lift_id
-/
theorem cardinalMk_le_max : #L <= max #R ℵ₀ := by
  simpa only [lift_id] using lift_cardinalMk_le_max R L

end Algebra.IsAlgebraic
