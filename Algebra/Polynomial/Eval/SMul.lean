/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluating polynomials and scalar multiplication

## Main results
* `eval₂_smul`, `eval_smul`, `map_smul`, `comp_smul`: the functions preserve scalar multiplication
* `Polynomial.leval`: `Polynomial.eval` as linear map

-/

@[expose] public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R ->+* S) (x : S)

@[simp]
/--
theorem `eval₂_smul` / 定理 `eval₂_smul`

English:
theorem eval₂_smul
  given: (g : R ->+* S) (p : R[X]) (x : S) {s : R}
  proof: by
  have A : p.natDegree < p.natDegree.succ := Nat.lt_succ_self _
  have B : (s • p).natDegree < p.natDegree.succ := (natDegree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum]; rw [eval₂_eq_sum]; rw [sum_over_range' _ _ _ A]; rw [sum_over_range' _ _ _ B] <;>
    simp [mul_sum, mul_assoc]

中文:
定理 eval₂_smul
  条件: (g : R ->+* S) (p : R[X]) (x : S) {s : R}
  证明: by
  have A : p.natDegree < p.natDegree.succ := Nat.lt_succ_self _
  have B : (s • p).natDegree < p.natDegree.succ := (natDegree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum]; rw [eval₂_eq_sum]; rw [sum_over_range' _ _ _ A]; rw [sum_over_range' _ _ _ B] <;>
    simp [mul_sum, mul_assoc]

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self, mul_assoc, mul_sum, natDegree, natDegree_smul_le, p.natDegree, p.natDegree.succ, sum_over_range, trans_lt
-/
theorem eval₂_smul (g : R ->+* S) (p : R[X]) (x : S) {s : R} :
    eval₂ g x (s • p) = g s * eval₂ g x p := by
  have A : p.natDegree < p.natDegree.succ := Nat.lt_succ_self _
  have B : (s • p).natDegree < p.natDegree.succ := (natDegree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum]; rw [eval₂_eq_sum]; rw [sum_over_range' _ _ _ A]; rw [sum_over_range' _ _ _ B] <;>
    simp [mul_sum, mul_assoc]

end

section Eval

variable {x : R}

@[simp]
/--
theorem `eval_smul` / 定理 `eval_smul`

English:
theorem eval_smul
  statement: [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p : R[X])
  proof: by
  rw [← smul_one_smul R s p]; rw [eval]; rw [eval₂_smul]; rw [RingHom.id_apply]; rw [smul_one_mul]; rw [eval₂_id]

中文:
定理 eval_smul
  结论: [SMulZero类 S R] [标量塔 S R R] (s : S) (p : R[X])
  证明: by
  rw [← smul_one_smul R s p]; rw [eval]; rw [eval₂_smul]; rw [RingHom.id_apply]; rw [smul_one_mul]; rw [eval₂_id]

Depends on / 依赖: RingHom, RingHom.id_apply, id_apply, smul_one_mul, smul_one_smul
-/
theorem eval_smul [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p : R[X])
    (x : R) : (s • p).eval x = s • p.eval x := by
  rw [← smul_one_smul R s p]; rw [eval]; rw [eval₂_smul]; rw [RingHom.id_apply]; rw [smul_one_mul]; rw [eval₂_id]

/-- `Polynomial.eval` as linear map -/
@[simps]
/--
Definition of `leval` / `leval` 的定义

English:
definition leval
  signature: {R : Type*} [Semiring R] (r : R)
  body: f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r

中文:
定义 leval
  签名: {R : 类型} [半环 R] (r : R)
  定义体: f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r

Depends on / 依赖: f.eval
-/
def leval {R : Type*} [Semiring R] (r : R) : R[X] ->ₗ[R] R where
  toFun f := f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r

end Eval

section Comp

@[simp]
/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p q : R[X])
  proof: by
  rw [← smul_one_smul R s p]; rw [comp]; rw [comp]; rw [eval₂_smul]; rw [← smul_eq_C_mul]; rw [smul_assoc]; rw [one_smul]

中文:
定理 smul_comp
  条件: [SMulZero类 S R] [标量塔 S R R] (s : S) (p q : R[X])
  证明: by
  rw [← smul_one_smul R s p]; rw [comp]; rw [comp]; rw [eval₂_smul]; rw [← smul_eq_C_mul]; rw [smul_assoc]; rw [one_smul]

Depends on / 依赖: one_smul, smul_assoc, smul_eq_C_mul, smul_one_smul
-/
theorem smul_comp [SMulZeroClass S R] [IsScalarTower S R R] (s : S) (p q : R[X]) :
    (s • p).comp q = s • p.comp q := by
  rw [← smul_one_smul R s p]; rw [comp]; rw [comp]; rw [eval₂_smul]; rw [← smul_eq_C_mul]; rw [smul_assoc]; rw [one_smul]

end Comp

section Map

variable [Semiring S]
variable (f : R ->+* S)

@[simp]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (r : R)
  statement: (r • p).map f = f r • p.map f
  proof: by
  rw [map]; rw [eval₂_smul]; rw [RingHom.comp_apply]; rw [C_mul']

中文:
定理 map_smul
  条件: (r : R)
  结论: (r • p).map f = f r • p.map f
  证明: by
  rw [map]; rw [eval₂_smul]; rw [RingHom.comp_apply]; rw [C_mul']
-/
protected theorem map_smul (r : R) : (r • p).map f = f r • p.map f := by
  rw [map]; rw [eval₂_smul]; rw [RingHom.comp_apply]; rw [C_mul']

end Map

end Semiring

end Polynomial
