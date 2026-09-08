/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Derivatives of polynomials

In this file we prove that derivatives of polynomials in the analysis sense agree with their
derivatives in the algebraic sense.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## TODO

* Add results about multivariable polynomials.
* Generalize some (most?) results to an algebra over the base field.

## Keywords

derivative, polynomial
-/

public section


universe u

open scoped Polynomial

open ContinuousLinearMap (smulRight)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

namespace Polynomial

/-! ### Derivative of a polynomial -/


variable {R : Type*} [CommSemiring R] [Algebra R 𝕜]
variable (p : 𝕜[X]) (q : R[X])

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
/-
**Polynomial.hasStrictDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (p : Polynomial 𝕜) (x : 
𝕜),   HasStrictDerivAt (fun x => Polynomial.eval x p) (Polynomial.eval x (Polyno
mial.derivative p)) x
参数：p : Polynomial 𝕜；x : 𝕜；fun x => Polynomial.eval x p；Polynomial.eval x (Polyno
mial.derivative p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.derivative_add`：derivative_add {f g : R[X]} : derivative (f +
 g) = derivative f + derivative g
· 使用定理 `HasStrictDerivAt.add`：HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x
) (hg : HasStrictDerivAt g g' x) : HasStrictDerivAt (f + g) (f' + g') x
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `Polynomial.derivative_monomial`：derivative_monomial (a : R) (n : Nat) : 
derivative (monomial n a) = monomial (n - 1) (a * n)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `HasStrictDerivAt.const_mul`：HasStrictDerivAt.const_mul (c : 𝔸) (hd : Has
StrictDerivAt d d' x) : HasStrictDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasStrictDerivAt_pow`：hasStrictDerivAt_pow (n : Nat) (x : 𝕜) : HasStrict
DerivAt (fun x : 𝕜 => x ^ n) (n * x ^ (n - 1)) x

--- 原说明 ---
The derivative (in the analysis sense) of a polynomial `p` is given by `p.deriva
tive`.
-/
protected theorem hasStrictDerivAt (x : 𝕜) :
    HasStrictDerivAt (fun x => p.eval x) (p.derivative.eval x) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using! hp.add hq
  | monomial n a => simpa [mul_assoc, derivative_monomial]
                      using! (hasStrictDerivAt_pow n x).const_mul a
/-
**Polynomial.hasStrictDerivAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {R : Type u_1} [inst_1 :
 CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Polynomial R) (x : 𝕜),   HasStric
tDerivAt (fun x => (Polynomial.aeval x) q) ((Polynomial.aeval x) (Polynomial.der
ivative q)) x
参数：q : Polynomial R；x : 𝕜；fun x => (Polynomial.aeval x) q；(Polynomial.aeval x) (
Polynomial.derivative q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `Polynomial.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] (p : Polynomial 𝕜) (x : 𝕜),   HasStrictDerivAt (fun x => Polynomial.eval 
x p) (Polynomial.…
-/
protected theorem hasStrictDerivAt_aeval (x : 𝕜) :
    HasStrictDerivAt (fun x => aeval x q) (aeval x (derivative q)) x := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).hasStrictDerivAt x

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
/-
**Polynomial.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (p : Polynomial 𝕜) (x : 
𝕜),   HasDerivAt (fun x => Polynomial.eval x p) (Polynomial.eval x (Polynomial.d
erivative p)) x
参数：p : Polynomial 𝕜；x : 𝕜；fun x => Polynomial.eval x p；Polynomial.eval x (Polyno
mial.derivative p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Polynomial.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] (p : Polynomial 𝕜) (x : 𝕜),   HasStrictDerivAt (fun x => Polynomial.eval 
x p) (Polynomial.…

--- 原说明 ---
The derivative (in the analysis sense) of a polynomial `p` is given by `p.deriva
tive`.
-/
protected theorem hasDerivAt (x : 𝕜) : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
  (p.hasStrictDerivAt x).hasDerivAt
/-
**Polynomial.hasDerivAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {R : Type u_1} [inst_1 :
 CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Polynomial R) (x : 𝕜),   HasDeriv
At (fun x => (Polynomial.aeval x) q) ((Polynomial.aeval x) (Polynomial.derivativ
e q)) x
参数：q : Polynomial R；x : 𝕜；fun x => (Polynomial.aeval x) q；(Polynomial.aeval x) (
Polynomial.derivative q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Polynomial.hasStrictDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNo
rmedField 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (
q : Polynomial R) (x : …
-/
protected theorem hasDerivAt_aeval (x : 𝕜) :
    HasDerivAt (fun x => aeval x q) (aeval x (derivative q)) x :=
  (q.hasStrictDerivAt_aeval x).hasDerivAt
/-
**Polynomial.hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (p : Polynomial 𝕜) (x : 
𝕜) (s : Set 𝕜),   HasDerivWithinAt (fun x => Polynomial.eval x p) (Polynomial.ev
al x (Polynomial.derivative p)) s x
参数：p : Polynomial 𝕜；x : 𝕜；s : Set 𝕜；fun x => Polynomial.eval x p；Polynomial.eval
 x (Polynomial.derivative p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Polynomial.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 (p : Polynomial 𝕜) (x : 𝕜),   HasDerivAt (fun x => Polynomial.eval x p) (Polyno
mial.eval x…
-/
protected theorem hasDerivWithinAt (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => p.eval x) (p.derivative.eval x) s x :=
  (p.hasDerivAt x).hasDerivWithinAt
/-
**Polynomial.hasDerivWithinAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {R : Type u_1} [inst_1 :
 CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Polynomial R) (x : 𝕜) (s : Set 𝕜)
,   HasDerivWithinAt (fun x => (Polynomial.aeval x) q) ((Polynomial.aeval x) (Po
lynomial.derivative q)) s x
参数：q : Polynomial R；x : 𝕜；s : Set 𝕜；fun x => (Polynomial.aeval x) q；(Polynomial.
aeval x) (Polynomial.derivative q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Polynomial.hasDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Po
lynomial R) (x : …
-/
protected theorem hasDerivWithinAt_aeval (x : 𝕜) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => aeval x q) (aeval x (derivative q)) s x :=
  (q.hasDerivAt_aeval x).hasDerivWithinAt
/-
**Polynomial.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} (p : Polynomial 
𝕜),   DifferentiableAt 𝕜 (fun x => Polynomial.eval x p) x
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Polynomial.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 (p : Polynomial 𝕜) (x : 𝕜),   HasDerivAt (fun x => Polynomial.eval x p) (Polyno
mial.eval x…
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 (fun x => p.eval x) x :=
  (p.hasDerivAt x).differentiableAt
/-
**Polynomial.differentiableAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {R : Type u_1} [
inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R), Differenti
ableAt 𝕜 (fun x => (Polynomial.aeval x) q) x
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Polynomial.hasDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Po
lynomial R) (x : …
-/
protected theorem differentiableAt_aeval : DifferentiableAt 𝕜 (fun x => aeval x q) x :=
  (q.hasDerivAt_aeval x).differentiableAt
/-
**Polynomial.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} (p :
 Polynomial 𝕜),   DifferentiableWithinAt 𝕜 (fun x => Polynomial.eval x p) s x
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Polynomial.differentiableAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {x : 𝕜} (p : Polynomial 𝕜),   DifferentiableAt 𝕜 (fun x => Polynomial.eva
l x p) x
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 (fun x => p.eval x) s x :=
  p.differentiableAt.differentiableWithinAt
/-
**Polynomial.differentiableWithinAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} {R :
 Type u_1} [inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R)
, DifferentiableWithinAt 𝕜 (fun x => (Polynomial.aeval x) q) s x
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Polynomial.differentiableAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNo
rmedField 𝕜] {x : 𝕜} {R : Type u_1} [inst_1 : CommSemiring R]   [inst_2 : Algebr
a R 𝕜] (q : Polynomial …
-/
protected theorem differentiableWithinAt_aeval :
    DifferentiableWithinAt 𝕜 (fun x => aeval x q) s x :=
  q.differentiableAt_aeval.differentiableWithinAt

@[fun_prop]
/-
**Polynomial.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (p : Polynomial 𝕜), Diff
erentiable 𝕜 fun x => Polynomial.eval x p
参数：p : Polynomial 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.differentiableAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {x : 𝕜} (p : Polynomial 𝕜),   DifferentiableAt 𝕜 (fun x => Polynomial.eva
l x p) x
-/
protected theorem differentiable : Differentiable 𝕜 fun x => p.eval x := fun _ => p.differentiableAt
/-
**Polynomial.differentiable_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {R : Type u_1} [inst_1 :
 CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Polynomial R), Differentiable 𝕜 f
un x => (Polynomial.aeval x) q
参数：q : Polynomial R；Polynomial.aeval x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.differentiableAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNo
rmedField 𝕜] {x : 𝕜} {R : Type u_1} [inst_1 : CommSemiring R]   [inst_2 : Algebr
a R 𝕜] (q : Polynomial …
-/
protected theorem differentiable_aeval : Differentiable 𝕜 fun x : 𝕜 => aeval x q := fun _ =>
  q.differentiableAt_aeval
/-
**Polynomial.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {s : Set 𝕜} (p : Polynom
ial 𝕜),   DifferentiableOn 𝕜 (fun x => Polynomial.eval x p) s
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Polynomial.differentiable`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFiel
d 𝕜] (p : Polynomial 𝕜), Differentiable 𝕜 fun x => Polynomial.eval x p
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 (fun x => p.eval x) s :=
  p.differentiable.differentiableOn
/-
**Polynomial.differentiableOn_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {s : Set 𝕜} {R : Type u_
1} [inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R), Differ
entiableOn 𝕜 (fun x => (Polynomial.aeval x) q) s
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Polynomial.differentiable_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNorm
edField 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q 
: Polynomial R), Diff…
-/
protected theorem differentiableOn_aeval : DifferentiableOn 𝕜 (fun x => aeval x q) s :=
  q.differentiable_aeval.differentiableOn

@[simp]
/-
**Polynomial.deriv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} (p : Polynomial 
𝕜),   deriv (fun x => Polynomial.eval x p) x = Polynomial.eval x (Polynomial.der
ivative p)
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p；Polynomial.derivative p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Polynomial.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 (p : Polynomial 𝕜) (x : 𝕜),   HasDerivAt (fun x => Polynomial.eval x p) (Polyno
mial.eval x…
-/
protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x :=
  (p.hasDerivAt x).deriv

@[simp]
/-
**Polynomial.deriv_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {R : Type u_1} [
inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R),   deriv (f
un x => (Polynomial.aeval x) q) x = (Polynomial.aeval x) (Polynomial.derivative 
q)
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q；Polynomial.aeval x；Polynomia
l.derivative q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Polynomial.hasDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Po
lynomial R) (x : …
-/
protected theorem deriv_aeval : deriv (fun x => aeval x q) x = aeval x (derivative q) :=
  (q.hasDerivAt_aeval x).deriv
/-
**Polynomial.derivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} (p :
 Polynomial 𝕜),   UniqueDiffWithinAt 𝕜 s x →     derivWithin (fun x => Polynomia
l.eval x p) s x = Polynomial.eval x (Polynomial.derivative p)
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p；Polynomial.derivative p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.derivWithin`：DifferentiableAt.derivWithin (h : Differen
tiableAt 𝕜 f x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = deriv f x
· 使用定理 `Polynomial.differentiableAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {x : 𝕜} (p : Polynomial 𝕜),   DifferentiableAt 𝕜 (fun x => Polynomial.eva
l x p) x
· 使用定理 `Polynomial.deriv`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x :
 𝕜} (p : Polynomial 𝕜),   deriv (fun x => Polynomial.eval x p) x = Polynomial.ev
al x (…
-/
protected theorem derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => p.eval x) s x = p.derivative.eval x := by
  rw [DifferentiableAt.derivWithin p.differentiableAt hxs]
  exact p.deriv
/-
**Polynomial.derivWithin_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} {R :
 Type u_1} [inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R)
,   UniqueDiffWithinAt 𝕜 s x →     derivWithin (fun x => (Polynomial.aeval x) q)
 s x = (Polynomial.aeval x) (Polynomial.derivative q)
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q；Polynomial.aeval x；Polynomia
l.derivative q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `Polynomial.derivWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {x : 𝕜} {s : Set 𝕜} (p : Polynomial 𝕜),   UniqueDiffWithinAt 𝕜 s x →     deriv
Within (fun …
-/
protected theorem derivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => aeval x q) s x = aeval x (derivative q) := by
  simpa only [aeval_def, eval₂_eq_eval_map, derivative_map] using
    (q.map (algebraMap R 𝕜)).derivWithin hxs
/-
**Polynomial.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] (p : Polynomial 𝕜) (x : 
𝕜),   HasFDerivAt (fun x => Polynomial.eval x p)     (ContinuousLinearMap.smulRi
ght 1 (Polynomial.eval x (Polynomial.derivative p))) x
参数：p : Polynomial 𝕜；x : 𝕜；fun x => Polynomial.eval x p；ContinuousLinearMap.smulR
ight 1 (Polynomial.eval x (Polynomial.derivative p))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 (p : Polynomial 𝕜) (x : 𝕜),   HasDerivAt (fun x => Polynomial.eval x p) (Polyno
mial.eval x…
-/
protected theorem hasFDerivAt (x : 𝕜) :
    HasFDerivAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
  p.hasDerivAt x
/-
**Polynomial.hasFDerivAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {R : Type u_1} [inst_1 :
 CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Polynomial R) (x : 𝕜),   HasFDeri
vAt (fun x => (Polynomial.aeval x) q)     (ContinuousLinearMap.smulRight 1 ((Pol
ynomial.aeval x) (Polynomial.derivative q))) x
参数：q : Polynomial R；x : 𝕜；fun x => (Polynomial.aeval x) q；ContinuousLinearMap.sm
ulRight 1 ((Polynomial.aeval x) (Polynomial.derivative q))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.hasDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : Po
lynomial R) (x : …
-/
protected theorem hasFDerivAt_aeval (x : 𝕜) :
    HasFDerivAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q))) x :=
  q.hasDerivAt_aeval x
/-
**Polynomial.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {s : Set 𝕜} (p : Polynom
ial 𝕜) (x : 𝕜),   HasFDerivWithinAt (fun x => Polynomial.eval x p)     (Continuo
usLinearMap.smulRight 1 (Polynomial.eval x (Polynomial.derivative p))) s x
参数：p : Polynomial 𝕜；x : 𝕜；fun x => Polynomial.eval x p；ContinuousLinearMap.smulR
ight 1 (Polynomial.eval x (Polynomial.derivative p))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Polynomial.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] (p : Polynomial 𝕜) (x : 𝕜),   HasFDerivAt (fun x => Polynomial.eval x p)     (
ContinuousLi…
-/
protected theorem hasFDerivWithinAt (x : 𝕜) :
    HasFDerivWithinAt (fun x => p.eval x) (smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
  (p.hasFDerivAt x).hasFDerivWithinAt
/-
**Polynomial.hasFDerivWithinAt_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {s : Set 𝕜} {R : Type u_
1} [inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R) (x : 𝕜)
,   HasFDerivWithinAt (fun x => (Polynomial.aeval x) q)     (ContinuousLinearMap
.smulRight 1 ((Polynomial.aeval x) (Polynomial.derivative q))) s x
参数：q : Polynomial R；x : 𝕜；fun x => (Polynomial.aeval x) q；ContinuousLinearMap.sm
ulRight 1 ((Polynomial.aeval x) (Polynomial.derivative q))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Polynomial.hasFDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNormedF
ield 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : P
olynomial R) (x : …
-/
protected theorem hasFDerivWithinAt_aeval (x : 𝕜) :
    HasFDerivWithinAt (fun x => aeval x q) (smulRight (1 : 𝕜 →L[𝕜] 𝕜)
      (aeval x (derivative q))) s x :=
  (q.hasFDerivAt_aeval x).hasFDerivWithinAt

@[simp]
/-
**Polynomial.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} (p : Polynomial 
𝕜),   fderiv 𝕜 (fun x => Polynomial.eval x p) x =     ContinuousLinearMap.smulRi
ght 1 (Polynomial.eval x (Polynomial.derivative p))
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p；Polynomial.eval x (Polynomial.d
erivative p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Polynomial.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] (p : Polynomial 𝕜) (x : 𝕜),   HasFDerivAt (fun x => Polynomial.eval x p)     (
ContinuousLi…
-/
protected theorem fderiv :
    fderiv 𝕜 (fun x => p.eval x) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivAt x).fderiv

@[simp]
/-
**Polynomial.fderiv_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {R : Type u_1} [
inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R),   fderiv 𝕜
 (fun x => (Polynomial.aeval x) q) x =     ContinuousLinearMap.smulRight 1 ((Pol
ynomial.aeval x) (Polynomial.derivative q))
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q；(Polynomial.aeval x) (Polyno
mial.derivative q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Polynomial.hasFDerivAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyNormedF
ield 𝕜] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebra R 𝕜]   (q : P
olynomial R) (x : …
-/
protected theorem fderiv_aeval :
    fderiv 𝕜 (fun x => aeval x q) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivAt_aeval x).fderiv
/-
**Polynomial.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} (p :
 Polynomial 𝕜),   UniqueDiffWithinAt 𝕜 s x →     fderivWithin 𝕜 (fun x => Polyno
mial.eval x p) s x =       ContinuousLinearMap.smulRight 1 (Polynomial.eval x (P
olynomial.derivative p))
参数：p : Polynomial 𝕜；fun x => Polynomial.eval x p；Polynomial.eval x (Polynomial.d
erivative p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Polynomial.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedF
ield 𝕜] {s : Set 𝕜} (p : Polynomial 𝕜) (x : 𝕜),   HasFDerivWithinAt (fun x => Po
lynomial.eval x p)…
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => p.eval x) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
  (p.hasFDerivWithinAt x).fderivWithin hxs
/-
**Polynomial.fderivWithin_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜} {R :
 Type u_1} [inst_1 : CommSemiring R]   [inst_2 : Algebra R 𝕜] (q : Polynomial R)
,   UniqueDiffWithinAt 𝕜 s x →     fderivWithin 𝕜 (fun x => (Polynomial.aeval x)
 q) s x =       ContinuousLinearMap.smulRight 1 ((Polynomial.aeval x) (Polynomia
l.derivative q))
参数：q : Polynomial R；fun x => (Polynomial.aeval x) q；(Polynomial.aeval x) (Polyno
mial.derivative q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Polynomial.hasFDerivWithinAt_aeval`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {s : Set 𝕜} {R : Type u_1} [inst_1 : CommSemiring R]   [inst_2 : A
lgebra R 𝕜] (q : Polynom…
-/
protected theorem fderivWithin_aeval (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => aeval x q) s x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (aeval x (derivative q)) :=
  (q.hasFDerivWithinAt_aeval x).fderivWithin hxs

end Polynomial

