/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.Algebra.AlgebraNF
public import Mathlib.Tactic.Polynomial.Core

/-!
# Polynomial
An extensible tactic for proving equality of polynomial expressions implemented using `algebra`.
To add support for a new polynomial-like type, one needs to do three things:
* Implement a polynomial extension that lets `polynomial` infer the base ring from the algebraic
  type. For example:
```
@[polynomial_infer_base]
def polynomialInferBase : PolynomialExt where
  infer e := do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure
```
* Tag any preprocessing lemmas with @[polynomial_pre]. This would include a lemma saying that
`C = algebraMap _ _` so that `algebra` knows how to normalize it.
* Tag any postprocessing lemmas with @[polynomial_post], so that `polynomial_nf` produces a pretty
expression.
-/

open Lean Mathlib.Tactic Mathlib.Tactic.Algebra Parser.Tactic Elab Meta Qq

public meta section

namespace Mathlib.Tactic.Polynomial

/-- Infer base ring for `Polynomial R` -/
@[polynomial_infer_base]
/-
**Mathlib.Tactic.Polynomial.polynomialInferBase** 是 Mathlib 中的一个定义，位于命名空间 `Mathl
ib.Tactic.Polynomial`。
形式化陈述：polynomialInferBase : PolynomialExt where infer e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Infer base ring for `Polynomial R`
-/
def polynomialInferBase : PolynomialExt where
  infer e := do
  match_expr e with
  | Polynomial R _ => pure R
  | _ => failure

section Lemmas

variable {σ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

attribute [polynomial_post] mul_one Algebra.smul_def Polynomial.algebraMap_eq

@[polynomial_pre]
/-
**Mathlib.Tactic.Polynomial.monomial_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.Polynomial`。
形式化陈述：monomial_eq_smul (a : R) (n : Nat) : Polynomial.monomial n a = a • (.X ^ n
)
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.smul_eq_C_mul`：smul_eq_C_mul (a : R) : a • p = C a * p
-/
theorem monomial_eq_smul (a : R) (n : ℕ) : Polynomial.monomial n a = a • (.X ^ n) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.smul_eq_C_mul]

-- `polynomial_pre` contains a lemma sending `C -> algebraMap`, so `C` is not simp normal form.
@[polynomial_pre]
/-
**Mathlib.Tactic.Polynomial.map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Polynomial`。
形式化陈述：map_algebraMap (r : R) : Polynomial.map (algebraMap R A) (algebraMap R (Po
lynomial R) r) = algebraMap A (Polynomial A) (algebraMap R A r)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_algebraMap (r : R) :
    Polynomial.map (algebraMap R A) (algebraMap R (Polynomial R) r) =
    algebraMap A (Polynomial A) (algebraMap R A r) := by
  simp

end Lemmas

open Mathlib.Meta AtomM

attribute [polynomial_pre] Polynomial.C_eq_algebraMap
  Polynomial.monomial_eq_smul Polynomial.map_add Polynomial.map_mul Polynomial.map_pow
  Polynomial.map_X Polynomial.map_natCast Polynomial.map_intCast

/- TODO: we don't currently have a good way to normalize monomials of MvPolynomials. These are
indexed by finsupps, making it difficult to turn into the appropriate normal form. -/
/-- Run the `polynomial_pre` simpset to turn nonstandard spellings of `algebraMap` such as
`Polynomial.C` into `algebraMap` -/
/-
**Mathlib.Tactic.Polynomial.preprocess** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.Polynomial`。
形式化陈述：preprocess (e : Expr) : MetaM Simp.Result
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Run the `polynomial_pre` simpset to turn nonstandard spellings of `algebraMap` s
uch as
`Polynomial.C` into `algebraMap`
-/
def preprocess (e : Expr) : MetaM Simp.Result := do
  let preThms ← polynomialPreExt.getTheorems
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[preThms])
  pure (← Simp.main e ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

open Tactic

/-- `polynomial` solves equalities of `Polynomial`s and similar types.

Given a goal which is an equality in `Polynomial R` with a commutative ring `R`, `polynomial`
turns both sides of the equation into a normal form by expanding out the brackets. It then closes
the goal if both sides contain the same terms and fails otherwise. `polynomial_nf` normalizes all
subexpressions at a given location.

Variants of `polynomial` include:
* `polynomial`: normalize both sides of an equation and close the goal if they are equal
* `polynomial!`: run `polynomial` at default transparency
* `polynomial_nf`: normalize all subexpression of the goal
* `polynomial_nf at h₁ h₂ ⊢`: normalize all subexpressions at hypotheses `h₁` `h₁` and the goal
* `polynomial_nf at *`: normalize all subexpressions of all local hypotheses and the goal
* `polynomial_nf!`: run `polynomial_nf` at default transparency

The `polynomial` tactic can be extended to work with algebras other than `Polynomial` using the
attributes `polynomial_infer_base`, `polynomial_pre` and `polynomial_post`. This is only possible
if the base ring can be inferred from the structure of the type.

Examples:

```
example (a : ℚ) : (X + C a) * (X - C a) = X^2 + C (a^2) := by polynomial

example {P : ℚ[X] → Prop} (h : P (X ^ 2 + X + C 4⁻¹)) : P ((X + C 2⁻¹) ^ 2) := by
  polynomial_nf at h ⊢
  exact h
```

-/
elab (name := polynomial) "polynomial" tk:"!"? : tactic =>
  withMainContext do
    let g ← getMainGoal
    let some (α, _, _) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
      | throwError "polynomial failed: not an equality"
    let mut β : Expr := default
    try
      β ← Polynomial.inferBase α
    catch _ =>
      throwError "polynomial failed: not an equality of (mv)polynomials"
    let some g ← transformAtTarget (fun e _ ↦ Polynomial.preprocess e) "polynomial" .silent g
      default | done
    let some g ← transformAtTarget (fun e _ ↦ Algebra.preprocess e) "polynomial" .silent g
      default | done
    AtomM.run (if tk.isSome then .default else .reducible)
      (Algebra.proveEq (some (← getLevelQ' β)) g)

@[tactic_alt polynomial]
macro "polynomial!" : tactic => `(tactic| polynomial !)

/-- A cleanup routine, which simplifies normalized expressions to a more human-friendly format.
This is the `algebra_nf` cleanup routine with a little extra work to turn scalar multiplication
into `(MV)Polynomial.C` -/
/-
**Mathlib.Tactic.Polynomial.cleanup** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Po
lynomial`。
形式化陈述：cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result
参数：cfg : RingNF.Config；r : Simp.Result。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cleanup routine, which simplifies normalized expressions to a more human-frien
dly format.
This is the `algebra_nf` cleanup routine with a little extra work to turn scalar
 multiplication
into `(MV)Polynomial.C`
-/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    let r ← cleanupSMul cfg r
    let thms : SimpTheorems ← polynomialPostExt.getTheorems
    let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    pure <| ←
      r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Normalize a polynomial expression into standard form. Used by `polynomial_nf`. -/
/-
**Mathlib.Tactic.Polynomial.evalExprPoly** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.Polynomial`。
形式化陈述：evalExprPoly (e : Expr) : AtomM Simp.Result
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normalize a polynomial expression into standard form. Used by `polynomial_nf`.
-/
def evalExprPoly (e : Expr) : AtomM Simp.Result := do
  let ⟨_, α, e⟩ ← inferTypeQ e
  let mut R : Expr := default
  try R ← inferBase α
  catch _ => throwError "not a polynomial"
  let r₁ ← Polynomial.preprocess e
  let r₂ ← Algebra.preprocess r₁.expr
  let ⟨_, R'⟩ ← getLevelQ' R
  let r₃ ← evalExpr R' r₂.expr
  (← r₁.mkEqTrans r₂).mkEqTrans r₃

@[tactic_alt polynomial]
elab (name := polynomialNF) "polynomial_nf" tk:"!"? loc:(location)? : tactic => withMainContext do
  let mut cfg := {}
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) (evalExprPoly) (cleanup cfg)
  transformAtLocation (m ·) "polynomial_nf" loc cfg.ifUnchanged false

@[tactic_alt polynomial]
macro "polynomial_nf!" loc:(location)? : tactic =>
  `(tactic| polynomial_nf ! $(loc)?)

end Mathlib.Tactic.Polynomial

open Polynomial

end

