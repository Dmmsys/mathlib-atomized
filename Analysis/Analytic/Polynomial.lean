/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Polynomials are analytic

This file combines the analysis and algebra libraries and shows that evaluation of a polynomial
is an analytic function.
-/

public section

variable {𝕜 E A B : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CommSemiring A] {z : E} {s : Set E}

section Polynomial
open Polynomial

variable [NormedRing B] [NormedAlgebra 𝕜 B] [Algebra A B] {f : E -> B}

/--
theorem `AnalyticWithinAt.aeval_polynomial` / 定理 `AnalyticWithinAt.aeval_polynomial`

English:
theorem AnalyticWithinAt.aeval_polynomial
  given: (hf : AnalyticWithinAt 𝕜 f s z) (p : A[X])
  proof: by
  refine p.induction_on (fun k => ?_) (fun p q hp hq => ?_) fun p i hp => ?_
  · simp_rw [aeval_C]; apply analyticWithinAt_const
  · simp_rw [aeval_add]; exact hp.add hq
  · convert! hp.mul hf
    simp_rw [pow_succ, aeval_mul, ← mul_assoc, aeval_X]

中文:
定理 AnalyticWithinAt.aeval_polynomial
  条件: (hf : AnalyticWithinAt 𝕜 f s z) (p : A[X])
  证明: by
  refine p.induction_on (fun k => ?_) (fun p q hp hq => ?_) fun p i hp => ?_
  · simp_rw [aeval_C]; apply analyticWithinAt_const
  · simp_rw [aeval_add]; exact hp.add hq
  · convert! hp.mul hf
    simp_rw [pow_succ, aeval_mul, ← mul_assoc, aeval_X]

Depends on / 依赖: aeval_C, aeval_X, aeval_add, aeval_mul, analyticWithinAt_const, convert, hp.add, hp.mul, induction_on, mul_assoc, p.induction_on, pow_succ, simp_rw
-/
theorem AnalyticWithinAt.aeval_polynomial (hf : AnalyticWithinAt 𝕜 f s z) (p : A[X]) :
    AnalyticWithinAt 𝕜 (fun x => aeval (f x) p) s z := by
  refine p.induction_on (fun k => ?_) (fun p q hp hq => ?_) fun p i hp => ?_
  · simp_rw [aeval_C]; apply analyticWithinAt_const
  · simp_rw [aeval_add]; exact hp.add hq
  · convert! hp.mul hf
    simp_rw [pow_succ, aeval_mul, ← mul_assoc, aeval_X]

/--
theorem `AnalyticAt.aeval_polynomial` / 定理 `AnalyticAt.aeval_polynomial`

English:
theorem AnalyticAt.aeval_polynomial
  given: (hf : AnalyticAt 𝕜 f z) (p : A[X])
  proof: by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.aeval_polynomial p

中文:
定理 AnalyticAt.aeval_polynomial
  条件: (hf : AnalyticAt 𝕜 f z) (p : A[X])
  证明: by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.aeval_polynomial p

Depends on / 依赖: aeval_polynomial, analyticWithinAt_univ, hf.aeval_polynomial
-/
theorem AnalyticAt.aeval_polynomial (hf : AnalyticAt 𝕜 f z) (p : A[X]) :
    AnalyticAt 𝕜 (fun x => aeval (f x) p) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.aeval_polynomial p

/--
theorem `AnalyticOnNhd.aeval_polynomial` / 定理 `AnalyticOnNhd.aeval_polynomial`

English:
theorem AnalyticOnNhd.aeval_polynomial
  given: (hf : AnalyticOnNhd 𝕜 f s) (p : A[X])
  proof: fun x hx => (hf x hx).aeval_polynomial p

中文:
定理 AnalyticOnNhd.aeval_polynomial
  条件: (hf : AnalyticOnNhd 𝕜 f s) (p : A[X])
  证明: fun x hx => (hf x hx).aeval_polynomial p

Depends on / 依赖: aeval_polynomial
-/
theorem AnalyticOnNhd.aeval_polynomial (hf : AnalyticOnNhd 𝕜 f s) (p : A[X]) :
    AnalyticOnNhd 𝕜 (fun x => aeval (f x) p) s := fun x hx => (hf x hx).aeval_polynomial p

/--
theorem `AnalyticOn.aeval_polynomial` / 定理 `AnalyticOn.aeval_polynomial`

English:
theorem AnalyticOn.aeval_polynomial
  given: (hf : AnalyticOn 𝕜 f s) (p : A[X])
  proof: fun x hx => (hf x hx).aeval_polynomial p

中文:
定理 AnalyticOn.aeval_polynomial
  条件: (hf : AnalyticOn 𝕜 f s) (p : A[X])
  证明: fun x hx => (hf x hx).aeval_polynomial p

Depends on / 依赖: aeval_polynomial
-/
theorem AnalyticOn.aeval_polynomial (hf : AnalyticOn 𝕜 f s) (p : A[X]) :
    AnalyticOn 𝕜 (fun x => aeval (f x) p) s := fun x hx => (hf x hx).aeval_polynomial p

/--
theorem `AnalyticOnNhd.eval_polynomial` / 定理 `AnalyticOnNhd.eval_polynomial`

English:
theorem AnalyticOnNhd.eval_polynomial
  given: {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X])
  proof: analyticOnNhd_id.aeval_polynomial p

中文:
定理 AnalyticOnNhd.eval_polynomial
  条件: {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X])
  证明: analyticOnNhd_id.aeval_polynomial p

Depends on / 依赖: aeval_polynomial, analyticOnNhd_id, analyticOnNhd_id.aeval_polynomial
-/
theorem AnalyticOnNhd.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) :
    AnalyticOnNhd 𝕜 (eval · p) Set.univ := analyticOnNhd_id.aeval_polynomial p

/--
theorem `AnalyticOn.eval_polynomial` / 定理 `AnalyticOn.eval_polynomial`

English:
theorem AnalyticOn.eval_polynomial
  given: {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X])
  proof: analyticOn_id.aeval_polynomial p

中文:
定理 AnalyticOn.eval_polynomial
  条件: {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X])
  证明: analyticOn_id.aeval_polynomial p

Depends on / 依赖: aeval_polynomial, analyticOn_id, analyticOn_id.aeval_polynomial
-/
theorem AnalyticOn.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) :
    AnalyticOn 𝕜 (eval · p) Set.univ := analyticOn_id.aeval_polynomial p

end Polynomial

section MvPolynomial
open MvPolynomial

variable [NormedCommRing B] [NormedAlgebra 𝕜 B] [Algebra A B] {σ : Type*} {f : E -> σ -> B}

/--
theorem `AnalyticAt.aeval_mvPolynomial` / 定理 `AnalyticAt.aeval_mvPolynomial`

English:
theorem AnalyticAt.aeval_mvPolynomial
  given: (hf : forall i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A)
  proof: by
  apply p.induction_on (fun k => ?_) (fun p q hp hq => ?_) fun p i hp => ?_ -- `refine` doesn't work
  · simp_rw [aeval_C]; apply analyticAt_const
  · simp_rw [map_add]; exact hp.add hq
  · simp_rw [map_mul, aeval_X]; exact hp.mul (hf i)

中文:
定理 AnalyticAt.aeval_mvPolynomial
  条件: (hf : 对任意 i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A)
  证明: by
  apply p.induction_on (fun k => ?_) (fun p q hp hq => ?_) fun p i hp => ?_ -- `refine` doesn't work
  · simp_rw [aeval_C]; apply analyticAt_const
  · simp_rw [map_add]; exact hp.add hq
  · simp_rw [map_mul, aeval_X]; exact hp.mul (hf i)

Depends on / 依赖: aeval_C, aeval_X, analyticAt_const, hp.add, hp.mul, induction_on, map_add, map_mul, p.induction_on, simp_rw
-/
theorem AnalyticAt.aeval_mvPolynomial (hf : forall i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A) :
    AnalyticAt 𝕜 (fun x => aeval (f x) p) z := by
  apply p.induction_on (fun k => ?_) (fun p q hp hq => ?_) fun p i hp => ?_ -- `refine` doesn't work
  · simp_rw [aeval_C]; apply analyticAt_const
  · simp_rw [map_add]; exact hp.add hq
  · simp_rw [map_mul, aeval_X]; exact hp.mul (hf i)

/--
theorem `AnalyticOnNhd.aeval_mvPolynomial` / 定理 `AnalyticOnNhd.aeval_mvPolynomial`

English:
theorem AnalyticOnNhd.aeval_mvPolynomial
  proof: fun x hx => .aeval_mvPolynomial (hf · x hx) p

中文:
定理 AnalyticOnNhd.aeval_mvPolynomial
  证明: fun x hx => .aeval_mvPolynomial (hf · x hx) p

Depends on / 依赖: aeval_mvPolynomial
-/
theorem AnalyticOnNhd.aeval_mvPolynomial
    (hf : forall i, AnalyticOnNhd 𝕜 (f · i) s) (p : MvPolynomial σ A) :
    AnalyticOnNhd 𝕜 (fun x => aeval (f x) p) s := fun x hx => .aeval_mvPolynomial (hf · x hx) p

/--
theorem `AnalyticOnNhd.eval_continuousLinearMap` / 定理 `AnalyticOnNhd.eval_continuousLinearMap`

English:
theorem AnalyticOnNhd.eval_continuousLinearMap
  given: (f : E ->L[𝕜] σ -> B) (p : MvPolynomial σ B)
  proof: fun x _ => .aeval_mvPolynomial (fun i => ((ContinuousLinearMap.proj i).comp f).analyticAt x) p

中文:
定理 AnalyticOnNhd.eval_continuousLinearMap
  条件: (f : E ->L[𝕜] σ -> B) (p : MvPolynomial σ B)
  证明: fun x _ => .aeval_mvPolynomial (fun i => ((ContinuousLinearMap.proj i).comp f).analyticAt x) p

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.proj, aeval_mvPolynomial, analyticAt
-/
theorem AnalyticOnNhd.eval_continuousLinearMap (f : E ->L[𝕜] σ -> B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x => eval (f x) p) Set.univ :=
  fun x _ => .aeval_mvPolynomial (fun i => ((ContinuousLinearMap.proj i).comp f).analyticAt x) p

/--
theorem `AnalyticOnNhd.eval_continuousLinearMap'` / 定理 `AnalyticOnNhd.eval_continuousLinearMap'`

English:
theorem AnalyticOnNhd.eval_continuousLinearMap'
  given: (f : σ -> E ->L[𝕜] B) (p : MvPolynomial σ B)
  proof: fun x _ => .aeval_mvPolynomial (fun i => (f i).analyticAt x) p

中文:
定理 AnalyticOnNhd.eval_continuousLinearMap'
  条件: (f : σ -> E ->L[𝕜] B) (p : MvPolynomial σ B)
  证明: fun x _ => .aeval_mvPolynomial (fun i => (f i).analyticAt x) p

Depends on / 依赖: aeval_mvPolynomial, analyticAt
-/
theorem AnalyticOnNhd.eval_continuousLinearMap' (f : σ -> E ->L[𝕜] B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x => eval (f · x) p) Set.univ :=
  fun x _ => .aeval_mvPolynomial (fun i => (f i).analyticAt x) p

variable [CompleteSpace 𝕜] [T2Space E] [FiniteDimensional 𝕜 E]

/--
theorem `AnalyticOnNhd.eval_linearMap` / 定理 `AnalyticOnNhd.eval_linearMap`

English:
theorem AnalyticOnNhd.eval_linearMap
  given: (f : E ->ₗ[𝕜] σ -> B) (p : MvPolynomial σ B)
  proof: AnalyticOnNhd.eval_continuousLinearMap { f with cont := f.continuous_of_finiteDimensional } p

中文:
定理 AnalyticOnNhd.eval_linearMap
  条件: (f : E ->ₗ[𝕜] σ -> B) (p : MvPolynomial σ B)
  证明: AnalyticOnNhd.eval_continuousLinearMap { f with cont := f.continuous_of_finiteDimensional } p

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.eval_continuousLinearMap, continuous_of_finiteDimensional, eval_continuousLinearMap, f.continuous_of_finiteDimensional
-/
theorem AnalyticOnNhd.eval_linearMap (f : E ->ₗ[𝕜] σ -> B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x => eval (f x) p) Set.univ :=
  AnalyticOnNhd.eval_continuousLinearMap { f with cont := f.continuous_of_finiteDimensional } p

/--
theorem `AnalyticOnNhd.eval_linearMap'` / 定理 `AnalyticOnNhd.eval_linearMap'`

English:
theorem AnalyticOnNhd.eval_linearMap'
  given: (f : σ -> E ->ₗ[𝕜] B) (p : MvPolynomial σ B)
  proof: AnalyticOnNhd.eval_linearMap (.pi f) p

中文:
定理 AnalyticOnNhd.eval_linearMap'
  条件: (f : σ -> E ->ₗ[𝕜] B) (p : MvPolynomial σ B)
  证明: AnalyticOnNhd.eval_linearMap (.pi f) p

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.eval_linearMap, eval_linearMap
-/
theorem AnalyticOnNhd.eval_linearMap' (f : σ -> E ->ₗ[𝕜] B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x => eval (f · x) p) Set.univ := AnalyticOnNhd.eval_linearMap (.pi f) p

/--
theorem `AnalyticOnNhd.eval_mvPolynomial` / 定理 `AnalyticOnNhd.eval_mvPolynomial`

English:
theorem AnalyticOnNhd.eval_mvPolynomial
  given: [Fintype σ] (p : MvPolynomial σ 𝕜)
  proof: AnalyticOnNhd.eval_linearMap (.id (R := 𝕜) (M := σ -> 𝕜)) p

中文:
定理 AnalyticOnNhd.eval_mvPolynomial
  条件: [Fintype σ] (p : MvPolynomial σ 𝕜)
  证明: AnalyticOnNhd.eval_linearMap (.id (R := 𝕜) (M := σ -> 𝕜)) p

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.eval_linearMap, eval_linearMap
-/
theorem AnalyticOnNhd.eval_mvPolynomial [Fintype σ] (p : MvPolynomial σ 𝕜) :
    AnalyticOnNhd 𝕜 (eval · p) Set.univ :=
  AnalyticOnNhd.eval_linearMap (.id (R := 𝕜) (M := σ -> 𝕜)) p

end MvPolynomial
