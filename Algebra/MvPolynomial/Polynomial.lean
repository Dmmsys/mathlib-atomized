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

/-
**MvPolynomial.polynomial_eval_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polynomial_eval_eval₂ [CommSemiring R] [CommSemiring S]
    {x : S} (f : R →+* Polynomial S) (g : σ → Polynomial S) (p : MvPolynomial σ R) :
    Polynomial.eval x (eval₂ f g p) =
      eval₂ ((Polynomial.evalRingHom x).comp f) (fun s => Polynomial.eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]
/-
**MvPolynomial.eval_polynomial_eval_finSuccEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：eval_polynomial_eval_finSuccEquiv {n : Nat} {x : Fin n -> R} [CommSemiring
 R] (f : MvPolynomial (Fin (n + 1)) R) (q : MvPolynomial (Fin n) R) : (eval x) (
Polynomial.eval q (finSuccEquiv R n f)) = eval (Fin.cases (eval x q) x) f
参数：f : MvPolynomial (Fin (n + 1)) R；q : MvPolynomial (Fin n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.finSuccEquiv_apply`：finSuccEquiv_apply (p : MvPolynomial (F
in (n + 1)) R) : finSuccEquiv R n p = eval₂Hom (Polynomial.C.comp (C : R ->+* Mv
Polynomial (Fin n) R)…
· 使用定理 `MvPolynomial.polynomial_eval_eval₂`：polynomial_eval_eval₂ [CommSemiring 
R] [CommSemiring S] {x : S} (f : R ->+* Polynomial S) (g : σ -> Polynomial S) (p
 : MvPolynomial σ R) : P…
· 使用定理 `MvPolynomial.eval_eval₂`：eval_eval₂ {S τ : Type*} {x : τ -> S} [CommSemi
ring S] (f : R ->+* MvPolynomial τ S) (g : σ -> MvPolynomial τ S) (p : MvPolynom
ial σ R) : ev…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eval_polynomial_eval_finSuccEquiv {n : ℕ} {x : Fin n → R}
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

