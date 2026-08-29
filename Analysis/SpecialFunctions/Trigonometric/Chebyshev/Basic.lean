/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for the real
(`Real.cos`) and complex (`Complex.cos`) cosine and the real (`Real.cosh`) and complex
(`Complex.cosh`) hyperbolic cosine.
-/

public section


namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

@[simp, norm_cast]
/--
theorem `complex_ofReal_eval_T` / 定理 `complex_ofReal_eval_T`

English:
theorem complex_ofReal_eval_T
  statement: forall (x : Real) n, (((T Real n).eval x : Real) : Complex) = (T Complex n).eval (x : Complex)
  proof: @algebraMap_eval_T Real Complex _ _ _

@[simp, norm_cast]

中文:
定理 complex_ofReal_eval_T
  结论: 对任意 (x : 实数) n, (((T 实数 n).eval x : 实数) : Complex) = (T Complex n).eval (x : Complex)
  证明: @algebraMap_eval_T Real Complex _ _ _

@[simp, norm_cast]

Depends on / 依赖: algebraMap_eval_T
-/
theorem complex_ofReal_eval_T : forall (x : Real) n, (((T Real n).eval x : Real) : Complex) = (T Complex n).eval (x : Complex) :=
  @algebraMap_eval_T Real Complex _ _ _

@[simp, norm_cast]
/--
theorem `complex_ofReal_eval_U` / 定理 `complex_ofReal_eval_U`

English:
theorem complex_ofReal_eval_U
  statement: forall (x : Real) n, (((U Real n).eval x : Real) : Complex) = (U Complex n).eval (x : Complex)
  proof: @algebraMap_eval_U Real Complex _ _ _

@[simp, norm_cast]

中文:
定理 complex_ofReal_eval_U
  结论: 对任意 (x : 实数) n, (((U 实数 n).eval x : 实数) : Complex) = (U Complex n).eval (x : Complex)
  证明: @algebraMap_eval_U Real Complex _ _ _

@[simp, norm_cast]

Depends on / 依赖: algebraMap_eval_U
-/
theorem complex_ofReal_eval_U : forall (x : Real) n, (((U Real n).eval x : Real) : Complex) = (U Complex n).eval (x : Complex) :=
  @algebraMap_eval_U Real Complex _ _ _

@[simp, norm_cast]
/--
theorem `complex_ofReal_eval_C` / 定理 `complex_ofReal_eval_C`

English:
theorem complex_ofReal_eval_C
  statement: forall (x : Real) n, (((C Real n).eval x : Real) : Complex) = (C Complex n).eval (x : Complex)
  proof: @algebraMap_eval_C Real Complex _ _ _

@[simp, norm_cast]

中文:
定理 complex_ofReal_eval_C
  结论: 对任意 (x : 实数) n, (((C 实数 n).eval x : 实数) : Complex) = (C Complex n).eval (x : Complex)
  证明: @algebraMap_eval_C Real Complex _ _ _

@[simp, norm_cast]

Depends on / 依赖: algebraMap_eval_C
-/
theorem complex_ofReal_eval_C : forall (x : Real) n, (((C Real n).eval x : Real) : Complex) = (C Complex n).eval (x : Complex) :=
  @algebraMap_eval_C Real Complex _ _ _

@[simp, norm_cast]
/--
theorem `complex_ofReal_eval_S` / 定理 `complex_ofReal_eval_S`

English:
theorem complex_ofReal_eval_S
  statement: forall (x : Real) n, (((S Real n).eval x : Real) : Complex) = (S Complex n).eval (x : Complex)
  proof: @algebraMap_eval_S Real Complex _ _ _

中文:
定理 complex_ofReal_eval_S
  结论: 对任意 (x : 实数) n, (((S 实数 n).eval x : 实数) : Complex) = (S Complex n).eval (x : Complex)
  证明: @algebraMap_eval_S Real Complex _ _ _

Depends on / 依赖: algebraMap_eval_S
-/
theorem complex_ofReal_eval_S : forall (x : Real) n, (((S Real n).eval x : Real) : Complex) = (S Complex n).eval (x : Complex) :=
  @algebraMap_eval_S Real Complex _ _ _

/-! ### Complex versions -/

section Complex

open Complex

variable (θ : Complex)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
/--
theorem `T_complex_cos` / 定理 `T_complex_cos`

English:
theorem T_complex_cos
  given: (n : Int)
  statement: (T Complex n).eval (cos θ) = cos (n * θ)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add,
      cos_add_cos]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [T_

中文:
定理 T_complex_cos
  条件: (n : 整数)
  结论: (T Complex n).eval (cos θ) = cos (n * θ)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add,
      cos_add_cos]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [T_

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_sub_one, add_two, cos_add_cos, eval_X, eval_mul, eval_ofNat, eval_sub, induct, neg_add_one, ring_nf, sub_eq_iff_eq_add
-/
theorem T_complex_cos (n : Int) : (T Complex n).eval (cos θ) = cos (n * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add,
      cos_add_cos]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, ih1, ih2, sub_eq_iff_eq_add',
      cos_add_cos]
    push_cast
    ring_nf

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/--
theorem `U_complex_cos` / 定理 `U_complex_cos`

English:
theorem U_complex_cos
  given: (n : Int)
  statement: (U Complex n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [one_add_one_eq_two, sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cas

中文:
定理 U_complex_cos
  条件: (n : 整数)
  结论: (U Complex n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [one_add_one_eq_two, sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cas

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, U_add_two, U_sub_one, add_two, eval_X, eval_mul, eval_ofNat, eval_sub, induct, mul_assoc, neg_add_one, one_add_one_eq_two, ring_nf, sin_add_sin, sin_two_mul, sub_eq_iff_eq_add, sub_mul
-/
theorem U_complex_cos (n : Int) : (U Complex n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp [one_add_one_eq_two, sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add, sin_add_sin]
    push_cast
    ring_nf
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_X, eval_ofNat, sub_mul,
      mul_assoc, ih1, ih2, sub_eq_iff_eq_add', sin_add_sin]
    push_cast
    ring_nf

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`. -/
@[simp]
/--
theorem `C_two_mul_complex_cos` / 定理 `C_two_mul_complex_cos`

English:
theorem C_two_mul_complex_cos
  given: (n : Int)
  statement: (C Complex n).eval (2 * cos θ) = 2 * cos (n * θ)
  proof: by
  simp [C_eq_two_mul_T_comp_half_mul_X]

中文:
定理 C_two_mul_complex_cos
  条件: (n : 整数)
  结论: (C Complex n).eval (2 * cos θ) = 2 * cos (n * θ)
  证明: by
  simp [C_eq_two_mul_T_comp_half_mul_X]

Depends on / 依赖: C_eq_two_mul_T_comp_half_mul_X
-/
theorem C_two_mul_complex_cos (n : Int) : (C Complex n).eval (2 * cos θ) = 2 * cos (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/--
theorem `S_two_mul_complex_cos` / 定理 `S_two_mul_complex_cos`

English:
theorem S_two_mul_complex_cos
  given: (n : Int)
  statement: (S Complex n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ)
  proof: by
  simp [S_eq_U_comp_half_mul_X]

中文:
定理 S_two_mul_complex_cos
  条件: (n : 整数)
  结论: (S Complex n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ)
  证明: by
  simp [S_eq_U_comp_half_mul_X]

Depends on / 依赖: S_eq_U_comp_half_mul_X
-/
theorem S_two_mul_complex_cos (n : Int) : (S Complex n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`. -/
@[simp]
/--
theorem `T_complex_cosh` / 定理 `T_complex_cosh`

English:
theorem T_complex_cosh
  given: (n : Int)
  statement: (T Complex n).eval (cosh θ) = cosh (n * θ)
  proof: calc
  (T Complex n).eval (cosh θ)
  _ = (T Complex n).eval (cos (θ * I)) := by rw [cos_mul_I]
  _ = cos (n * (θ * I)) := T_complex_cos (θ * I) n
  _ = cos (n * θ * I) := by rw [mul_assoc]
  _ = cosh (n * θ) := cos_mul_I (n * θ)

中文:
定理 T_complex_cosh
  条件: (n : 整数)
  结论: (T Complex n).eval (cosh θ) = cosh (n * θ)
  证明: calc
  (T Complex n).eval (cosh θ)
  _ = (T Complex n).eval (cos (θ * I)) := by rw [cos_mul_I]
  _ = cos (n * (θ * I)) := T_complex_cos (θ * I) n
  _ = cos (n * θ * I) := by rw [mul_assoc]
  _ = cosh (n * θ) := cos_mul_I (n * θ)
-/
theorem T_complex_cosh (n : Int) : (T Complex n).eval (cosh θ) = cosh (n * θ) := calc
  (T Complex n).eval (cosh θ)
  _ = (T Complex n).eval (cos (θ * I)) := by rw [cos_mul_I]
  _ = cos (n * (θ * I)) := T_complex_cos (θ * I) n
  _ = cos (n * θ * I) := by rw [mul_assoc]
  _ = cosh (n * θ) := cos_mul_I (n * θ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/--
theorem `U_complex_cosh` / 定理 `U_complex_cosh`

English:
theorem U_complex_cosh
  given: (n : Int)
  statement: (U Complex n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ)
  proof: calc
  (U Complex n).eval (cosh θ) * sinh θ
  _ = (U Complex n).eval (cos (θ * I)) * sin (θ * I) * (-I) := by simp [cos_mul_I, sin_mul_I, mul_assoc]
  _ = sin ((n + 1) * (θ * I)) * (-I) := by rw [U_complex_cos]
  _ = sin ((n + 1) * θ * I) * (-I) := by rw [mul_assoc]
  _ = sinh ((n + 1) * θ) := by
  

中文:
定理 U_complex_cosh
  条件: (n : 整数)
  结论: (U Complex n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ)
  证明: calc
  (U Complex n).eval (cosh θ) * sinh θ
  _ = (U Complex n).eval (cos (θ * I)) * sin (θ * I) * (-I) := by simp [cos_mul_I, sin_mul_I, mul_assoc]
  _ = sin ((n + 1) * (θ * I)) * (-I) := by rw [U_complex_cos]
  _ = sin ((n + 1) * θ * I) * (-I) := by rw [mul_assoc]
  _ = sinh ((n + 1) * θ) := by
  
-/
theorem U_complex_cosh (n : Int) : (U Complex n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ) := calc
  (U Complex n).eval (cosh θ) * sinh θ
  _ = (U Complex n).eval (cos (θ * I)) * sin (θ * I) * (-I) := by simp [cos_mul_I, sin_mul_I, mul_assoc]
  _ = sin ((n + 1) * (θ * I)) * (-I) := by rw [U_complex_cos]
  _ = sin ((n + 1) * θ * I) * (-I) := by rw [mul_assoc]
  _ = sinh ((n + 1) * θ) := by
    rw [sin_mul_I ((n + 1) * θ)]; rw [mul_assoc]; rw [mul_neg]; rw [I_mul_I]; rw [neg_neg]; rw [mul_one]

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`. -/
@[simp]
/--
theorem `C_two_mul_complex_cosh` / 定理 `C_two_mul_complex_cosh`

English:
theorem C_two_mul_complex_cosh
  given: (n : Int)
  statement: (C Complex n).eval (2 * cosh θ) = 2 * cosh (n * θ)
  proof: by
  simp [C_eq_two_mul_T_comp_half_mul_X]

中文:
定理 C_two_mul_complex_cosh
  条件: (n : 整数)
  结论: (C Complex n).eval (2 * cosh θ) = 2 * cosh (n * θ)
  证明: by
  simp [C_eq_two_mul_T_comp_half_mul_X]

Depends on / 依赖: C_eq_two_mul_T_comp_half_mul_X
-/
theorem C_two_mul_complex_cosh (n : Int) : (C Complex n).eval (2 * cosh θ) = 2 * cosh (n * θ) := by
  simp [C_eq_two_mul_T_comp_half_mul_X]

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/--
theorem `S_two_mul_complex_cosh` / 定理 `S_two_mul_complex_cosh`

English:
theorem S_two_mul_complex_cosh
  given: (n : Int)
  statement: (S Complex n).eval (2 * cosh θ) * sinh θ =
  proof: by
  simp [S_eq_U_comp_half_mul_X]

中文:
定理 S_two_mul_complex_cosh
  条件: (n : 整数)
  结论: (S Complex n).eval (2 * cosh θ) * sinh θ =
  证明: by
  simp [S_eq_U_comp_half_mul_X]

Depends on / 依赖: S_eq_U_comp_half_mul_X
-/
theorem S_two_mul_complex_cosh (n : Int) : (S Complex n).eval (2 * cosh θ) * sinh θ =
    sinh ((n + 1) * θ) := by
  simp [S_eq_U_comp_half_mul_X]

end Complex

/-! ### Real versions -/

section Real

open Real

variable (θ : Real) (n : Int)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
/--
theorem `T_real_cos` / 定理 `T_real_cos`

English:
theorem T_real_cos
  statement: (T Real n).eval (cos θ) = cos (n * θ)
  proof: mod_cast T_complex_cos θ n

中文:
定理 T_real_cos
  结论: (T 实数 n).eval (cos θ) = cos (n * θ)
  证明: mod_cast T_complex_cos θ n

Depends on / 依赖: T_complex_cos, mod_cast
-/
theorem T_real_cos : (T Real n).eval (cos θ) = cos (n * θ) := mod_cast T_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/--
theorem `U_real_cos` / 定理 `U_real_cos`

English:
theorem U_real_cos
  statement: (U Real n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
  proof: mod_cast U_complex_cos θ n

中文:
定理 U_real_cos
  结论: (U 实数 n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
  证明: mod_cast U_complex_cos θ n

Depends on / 依赖: U_complex_cos, mod_cast
-/
theorem U_real_cos : (U Real n).eval (cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast U_complex_cos θ n

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cos θ` to the value `2 * cos (n * θ)`. -/
@[simp]
/--
theorem `C_two_mul_real_cos` / 定理 `C_two_mul_real_cos`

English:
theorem C_two_mul_real_cos
  statement: (C Real n).eval (2 * cos θ) = 2 * cos (n * θ)
  proof: mod_cast C_two_mul_complex_cos θ n

中文:
定理 C_two_mul_real_cos
  结论: (C 实数 n).eval (2 * cos θ) = 2 * cos (n * θ)
  证明: mod_cast C_two_mul_complex_cos θ n

Depends on / 依赖: C_two_mul_complex_cos, mod_cast
-/
theorem C_two_mul_real_cos : (C Real n).eval (2 * cos θ) = 2 * cos (n * θ) :=
  mod_cast C_two_mul_complex_cos θ n

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cos θ` to the value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
/--
theorem `S_two_mul_real_cos` / 定理 `S_two_mul_real_cos`

English:
theorem S_two_mul_real_cos
  statement: (S Real n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ)
  proof: mod_cast S_two_mul_complex_cos θ n

中文:
定理 S_two_mul_real_cos
  结论: (S 实数 n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ)
  证明: mod_cast S_two_mul_complex_cos θ n

Depends on / 依赖: S_two_mul_complex_cos, mod_cast
-/
theorem S_two_mul_real_cos : (S Real n).eval (2 * cos θ) * sin θ = sin ((n + 1) * θ) :=
  mod_cast S_two_mul_complex_cos θ n

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cosh θ` to the
value `cosh (n * θ)`. -/
@[simp]
/--
theorem `T_real_cosh` / 定理 `T_real_cosh`

English:
theorem T_real_cosh
  given: (n : Int)
  statement: (T Real n).eval (cosh θ) = cosh (n * θ)
  proof: mod_cast T_complex_cosh θ n

中文:
定理 T_real_cosh
  条件: (n : 整数)
  结论: (T 实数 n).eval (cosh θ) = cosh (n * θ)
  证明: mod_cast T_complex_cosh θ n

Depends on / 依赖: T_complex_cosh, mod_cast
-/
theorem T_real_cosh (n : Int) : (T Real n).eval (cosh θ) = cosh (n * θ) := mod_cast T_complex_cosh θ n

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cosh θ` to the
value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/--
theorem `U_real_cosh` / 定理 `U_real_cosh`

English:
theorem U_real_cosh
  given: (n : Int)
  statement: (U Real n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ)
  proof: mod_cast U_complex_cosh θ n

中文:
定理 U_real_cosh
  条件: (n : 整数)
  结论: (U 实数 n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ)
  证明: mod_cast U_complex_cosh θ n

Depends on / 依赖: U_complex_cosh, mod_cast
-/
theorem U_real_cosh (n : Int) : (U Real n).eval (cosh θ) * sinh θ = sinh ((n + 1) * θ) :=
  mod_cast U_complex_cosh θ n

/-- The `n`-th rescaled Chebyshev polynomial of the first kind (Vieta–Lucas polynomial) evaluates on
`2 * cosh θ` to the value `2 * cosh (n * θ)`. -/
@[simp]
/--
theorem `C_two_mul_real_cosh` / 定理 `C_two_mul_real_cosh`

English:
theorem C_two_mul_real_cosh
  given: (n : Int)
  statement: (C Real n).eval (2 * cosh θ) = 2 * cosh (n * θ)
  proof: mod_cast C_two_mul_complex_cosh θ n

中文:
定理 C_two_mul_real_cosh
  条件: (n : 整数)
  结论: (C 实数 n).eval (2 * cosh θ) = 2 * cosh (n * θ)
  证明: mod_cast C_two_mul_complex_cosh θ n

Depends on / 依赖: C_two_mul_complex_cosh, mod_cast
-/
theorem C_two_mul_real_cosh (n : Int) : (C Real n).eval (2 * cosh θ) = 2 * cosh (n * θ) :=
  mod_cast C_two_mul_complex_cosh θ n

/-- The `n`-th rescaled Chebyshev polynomial of the second kind (Vieta–Fibonacci polynomial)
evaluates on `2 * cosh θ` to the value `sinh ((n + 1) * θ) / sinh θ`. -/
@[simp]
/--
theorem `S_two_mul_real_cosh` / 定理 `S_two_mul_real_cosh`

English:
theorem S_two_mul_real_cosh
  given: (n : Int)
  statement: (S Real n).eval (2 * cosh θ) * sinh θ = sinh ((n + 1) * θ)
  proof: mod_cast S_two_mul_complex_cosh θ n

中文:
定理 S_two_mul_real_cosh
  条件: (n : 整数)
  结论: (S 实数 n).eval (2 * cosh θ) * sinh θ = sinh ((n + 1) * θ)
  证明: mod_cast S_two_mul_complex_cosh θ n

Depends on / 依赖: S_two_mul_complex_cosh, mod_cast
-/
theorem S_two_mul_real_cosh (n : Int) : (S Real n).eval (2 * cosh θ) * sinh θ = sinh ((n + 1) * θ) :=
  mod_cast S_two_mul_complex_cosh θ n

end Real

end Polynomial.Chebyshev
