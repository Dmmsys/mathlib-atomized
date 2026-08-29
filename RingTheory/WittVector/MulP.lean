/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.IsPoly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mulN_isPoly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

variable {p : Nat} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p -- type as `\bbW`

open MvPolynomial

noncomputable section

variable (p) in
/--
Definition of `wittMulN` / `wittMulN` 的定义

English:
definition wittMulN
  signature: : Nat -> Nat -> MvPolynomial Nat Int

中文:
定义 wittMulN
  签名: : 自然数 -> 自然数 -> 多元多项式 自然数 整数
-/
noncomputable def wittMulN : Nat -> Nat -> MvPolynomial Nat Int
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![wittMulN n, X]) (wittAdd p k)

/--
theorem `mulN_coeff` / 定理 `mulN_coeff`

English:
theorem mulN_coeff
  given: (n : Nat) (x : 𝕎 R) (k : Nat)
  proof: by
  induction n generalizing k with
  | zero => simp only [Nat.cast_zero, mul_zero, zero_coeff, wittMulN, Pi.zero_apply, map_zero]
  | succ n ih =>
    rw [wittMulN]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [mul_add]; rw [mul_one]; rw [aeval_bind₁]; rw [add_coeff]
    apply eval₂Hom_congr (RingHom

中文:
定理 mulN_coeff
  条件: (n : 自然数) (x : 𝕎 R) (k : 自然数)
  证明: by
  induction n generalizing k with
  | zero => simp only [Nat.cast_zero, mul_zero, zero_coeff, wittMulN, Pi.zero_apply, map_zero]
  | succ n ih =>
    rw [wittMulN]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [mul_add]; rw [mul_one]; rw [aeval_bind₁]; rw [add_coeff]
    apply eval₂Hom_congr (RingHom

Depends on / 依赖: Function, Function.uncurry, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Pi.zero_apply, RingHom, RingHom.ext_int, add_coeff, aeval_X, cast_add, cast_one, cast_zero, cons_val_one, cons_val_zero, ext_int, fin_cases
-/
theorem mulN_coeff (n : Nat) (x : 𝕎 R) (k : Nat) :
    (x * n).coeff k = aeval x.coeff (wittMulN p n k) := by
  induction n generalizing k with
  | zero => simp only [Nat.cast_zero, mul_zero, zero_coeff, wittMulN, Pi.zero_apply, map_zero]
  | succ n ih =>
    rw [wittMulN]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [mul_add]; rw [mul_one]; rw [aeval_bind₁]; rw [add_coeff]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1 ⟨b, i⟩
    fin_cases b
    · simp [Function.uncurry, Matrix.cons_val_zero, ih]
    · simp [Function.uncurry, Matrix.cons_val_one, aeval_X]

variable (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly]
/--
theorem `mulN_isPoly` / 定理 `mulN_isPoly`

English:
theorem mulN_isPoly
  given: (n : Nat)
  statement: IsPoly p fun _ _Rcr x => x * n
  proof: ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mulN_coeff n x k⟩⟩

@[simp]

中文:
定理 mulN_isPoly
  条件: (n : 自然数)
  结论: 是Poly p fun _ _Rcr x => x * n
  证明: ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mulN_coeff n x k⟩⟩

@[simp]

Depends on / 依赖: _Rcr, mulN_coeff, wittMulN
-/
theorem mulN_isPoly (n : Nat) : IsPoly p fun _ _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mulN_coeff n x k⟩⟩

@[simp]
/--
theorem `bind₁_wittMulN_wittPolynomial` / 定理 `bind₁_wittMulN_wittPolynomial`

English:
theorem bind₁_wittMulN_wittPolynomial
  given: (n k : Nat)
  proof: by
  induction n with
  | zero => simp [wittMulN, zero_mul, bind₁_zero_wittPolynomial]
  | succ n ih =>
    rw [wittMulN]; rw [← bind₁_bind₁]; rw [wittAdd]; rw [wittStructureInt_prop]
    simp only [map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul]; rw [one_mul]; rw [bind₁_rename]; rw [bind₁_r

中文:
定理 bind₁_wittMulN_wittPolynomial
  条件: (n k : 自然数)
  证明: by
  induction n with
  | zero => simp [wittMulN, zero_mul, bind₁_zero_wittPolynomial]
  | succ n ih =>
    rw [wittMulN]; rw [← bind₁_bind₁]; rw [wittAdd]; rw [wittStructureInt_prop]
    simp only [map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul]; rw [one_mul]; rw [bind₁_rename]; rw [bind₁_r

Depends on / 依赖: AlgHom, AlgHom.id_apply, Function, Function.comp_def, Function.uncurry, Matrix, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.cast_succ, add_mul, cast_succ, comp_def, cons_val_one, cons_val_zero, id_apply, map_add, one_mul, uncurry, wittAdd, wittMulN
-/
theorem bind₁_wittMulN_wittPolynomial (n k : Nat) :
    bind₁ (wittMulN p n) (wittPolynomial p Int k) = n * wittPolynomial p Int k := by
  induction n with
  | zero => simp [wittMulN, zero_mul, bind₁_zero_wittPolynomial]
  | succ n ih =>
    rw [wittMulN]; rw [← bind₁_bind₁]; rw [wittAdd]; rw [wittStructureInt_prop]
    simp only [map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul]; rw [one_mul]; rw [bind₁_rename]; rw [bind₁_rename]
    simp only [ih, Function.uncurry, Function.comp_def, bind₁_X_left, AlgHom.id_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

end

end WittVector
