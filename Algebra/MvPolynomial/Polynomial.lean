/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Some lemmas relating polynomials and multivariable polynomials.
-/

public section

namespace MvPolynomial

variable {R S σ : Type*}

/--
theorem `polynomial_eval_eval₂` / 定理 `polynomial_eval_eval₂`

English:
theorem polynomial_eval_eval₂
  statement: [CommSemiring R] [CommSemiring S]
  proof: by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

中文:
定理 polynomial_eval_eval₂
  结论: [交换半环 R] [交换半环 S]
  证明: by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

Depends on / 依赖: induction_on
-/
theorem polynomial_eval_eval₂ [CommSemiring R] [CommSemiring S]
    {x : S} (f : R ->+* Polynomial S) (g : σ -> Polynomial S) (p : MvPolynomial σ R) :
    Polynomial.eval x (eval₂ f g p) =
      eval₂ ((Polynomial.evalRingHom x).comp f) (fun s => Polynomial.eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

/--
theorem `eval_polynomial_eval_finSuccEquiv` / 定理 `eval_polynomial_eval_finSuccEquiv`

English:
theorem eval_polynomial_eval_finSuccEquiv
  statement: {n : Nat} {x : Fin n -> R}
  proof: by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, polynomial_eval_eval₂, eval_eval₂]
  conv in RingHom.comp _ _ =>
    refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp
  simp only [eval₂_id]
  congr
  funext i
  refine Fin.cases (by simp) (by simp) i

中文:
定理 eval_polynomial_eval_finSuccEquiv
  结论: {n : 自然数} {x : 有限集 n -> R}
  证明: by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, polynomial_eval_eval₂, eval_eval₂]
  conv in RingHom.comp _ _ =>
    refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp
  simp only [eval₂_id]
  congr
  funext i
  refine Fin.cases (by simp) (by simp) i

Depends on / 依赖: Fin.cases, RingHom, RingHom.comp, RingHom.ext, RingHom.id, finSuccEquiv_apply
-/
theorem eval_polynomial_eval_finSuccEquiv {n : Nat} {x : Fin n -> R}
    [CommSemiring R] (f : MvPolynomial (Fin (n + 1)) R) (q : MvPolynomial (Fin n) R) :
    (eval x) (Polynomial.eval q (finSuccEquiv R n f)) = eval (Fin.cases (eval x q) x) f := by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, polynomial_eval_eval₂, eval_eval₂]
  conv in RingHom.comp _ _ =>
    refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp
  simp only [eval₂_id]
  congr
  funext i
  refine Fin.cases (by simp) (by simp) i

end MvPolynomial
