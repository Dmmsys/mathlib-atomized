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

variable [NormedRing B] [NormedAlgebra 𝕜 B] [Algebra A B] {f : E → B}

/-
**AnalyticWithinAt.aeval_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticWithinAt.aeval_polynomial (hf : AnalyticWithinAt 𝕜 f s z) (p : A[X
]) : AnalyticWithinAt 𝕜 (fun x => aeval (f x) p) s z
参数：hf : AnalyticWithinAt 𝕜 f s z；p : A[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `analyticWithinAt_const`：analyticWithinAt_const {v : F} {s : Set E} {x : 
E} : AnalyticWithinAt 𝕜 (fun _ => v) s x
· 使用定理 `Polynomial.aeval_add`：aeval_add : aeval x (p + q) = aeval x p + aeval x 
q
· 使用定理 `AnalyticWithinAt.add`：AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s 
x) (hg : AnalyticWithinAt 𝕜 g s x) : AnalyticWithinAt 𝕜 (f + g) s x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AnalyticWithinAt.mul`：AnalyticWithinAt.mul {f g : E -> A} {s : Set E} {z
 : E} (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) : Analytic
WithinAt 𝕜…
-/
theorem AnalyticWithinAt.aeval_polynomial (hf : AnalyticWithinAt 𝕜 f s z) (p : A[X]) :
    AnalyticWithinAt 𝕜 (fun x ↦ aeval (f x) p) s z := by
  refine p.induction_on (fun k ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_
  · simp_rw [aeval_C]; apply analyticWithinAt_const
  · simp_rw [aeval_add]; exact hp.add hq
  · convert! hp.mul hf
    simp_rw [pow_succ, aeval_mul, ← mul_assoc, aeval_X]
/-
**AnalyticAt.aeval_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.aeval_polynomial (hf : AnalyticAt 𝕜 f z) (p : A[X]) : AnalyticA
t 𝕜 (fun x => aeval (f x) p) z
参数：hf : AnalyticAt 𝕜 f z；p : A[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `analyticWithinAt_univ`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 …
· 使用定理 `AnalyticWithinAt.aeval_polynomial`：AnalyticWithinAt.aeval_polynomial (hf
 : AnalyticWithinAt 𝕜 f s z) (p : A[X]) : AnalyticWithinAt 𝕜 (fun x => aeval (f 
x) p) s z
-/
theorem AnalyticAt.aeval_polynomial (hf : AnalyticAt 𝕜 f z) (p : A[X]) :
    AnalyticAt 𝕜 (fun x ↦ aeval (f x) p) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.aeval_polynomial p
/-
**AnalyticOnNhd.aeval_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.aeval_polynomial (hf : AnalyticOnNhd 𝕜 f s) (p : A[X]) : Ana
lyticOnNhd 𝕜 (fun x => aeval (f x) p) s
参数：hf : AnalyticOnNhd 𝕜 f s；p : A[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.aeval_polynomial`：AnalyticAt.aeval_polynomial (hf : AnalyticA
t 𝕜 f z) (p : A[X]) : AnalyticAt 𝕜 (fun x => aeval (f x) p) z
-/
theorem AnalyticOnNhd.aeval_polynomial (hf : AnalyticOnNhd 𝕜 f s) (p : A[X]) :
    AnalyticOnNhd 𝕜 (fun x ↦ aeval (f x) p) s := fun x hx ↦ (hf x hx).aeval_polynomial p
/-
**AnalyticOn.aeval_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.aeval_polynomial (hf : AnalyticOn 𝕜 f s) (p : A[X]) : AnalyticO
n 𝕜 (fun x => aeval (f x) p) s
参数：hf : AnalyticOn 𝕜 f s；p : A[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticWithinAt.aeval_polynomial`：AnalyticWithinAt.aeval_polynomial (hf
 : AnalyticWithinAt 𝕜 f s z) (p : A[X]) : AnalyticWithinAt 𝕜 (fun x => aeval (f 
x) p) s z
-/
theorem AnalyticOn.aeval_polynomial (hf : AnalyticOn 𝕜 f s) (p : A[X]) :
    AnalyticOn 𝕜 (fun x ↦ aeval (f x) p) s := fun x hx ↦ (hf x hx).aeval_polynomial p
/-
**AnalyticOnNhd.eval_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (
p : A[X]) : AnalyticOnNhd 𝕜 (eval · p) Set.univ
参数：p : A[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.aeval_polynomial`：AnalyticOnNhd.aeval_polynomial (hf : Ana
lyticOnNhd 𝕜 f s) (p : A[X]) : AnalyticOnNhd 𝕜 (fun x => aeval (f x) p) s
· 使用定理 `analyticOnNhd_id`：analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E => x) s
-/
theorem AnalyticOnNhd.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) :
    AnalyticOnNhd 𝕜 (eval · p) Set.univ := analyticOnNhd_id.aeval_polynomial p
/-
**AnalyticOn.eval_polynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p :
 A[X]) : AnalyticOn 𝕜 (eval · p) Set.univ
参数：p : A[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOn.aeval_polynomial`：AnalyticOn.aeval_polynomial (hf : AnalyticO
n 𝕜 f s) (p : A[X]) : AnalyticOn 𝕜 (fun x => aeval (f x) p) s
· 使用定理 `analyticOn_id`：analyticOn_id : AnalyticOn 𝕜 (fun x : E => x) s
-/
theorem AnalyticOn.eval_polynomial {A} [NormedCommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) :
    AnalyticOn 𝕜 (eval · p) Set.univ := analyticOn_id.aeval_polynomial p

end Polynomial

section MvPolynomial
open MvPolynomial

variable [NormedCommRing B] [NormedAlgebra 𝕜 B] [Algebra A B] {σ : Type*} {f : E → σ → B}

/-
**AnalyticAt.aeval_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.aeval_mvPolynomial (hf : forall i, AnalyticAt 𝕜 (f · i) z) (p :
 MvPolynomial σ A) : AnalyticAt 𝕜 (fun x => aeval (f x) p) z
参数：hf : forall i, AnalyticAt 𝕜 (f · i) z；p : MvPolynomial σ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.aeval_C`：aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ 
r
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用引理 `AnalyticAt.mul`：AnalyticAt.mul {f g : E -> A} {z : E} (hf : AnalyticAt 𝕜
 f z) (hg : AnalyticAt 𝕜 g z) : AnalyticAt 𝕜 (f * g) z
-/
theorem AnalyticAt.aeval_mvPolynomial (hf : ∀ i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A) :
    AnalyticAt 𝕜 (fun x ↦ aeval (f x) p) z := by
  apply p.induction_on (fun k ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_ -- `refine` doesn't work
  · simp_rw [aeval_C]; apply analyticAt_const
  · simp_rw [map_add]; exact hp.add hq
  · simp_rw [map_mul, aeval_X]; exact hp.mul (hf i)
/-
**AnalyticOnNhd.aeval_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.aeval_mvPolynomial (hf : forall i, AnalyticOnNhd 𝕜 (f · i) s
) (p : MvPolynomial σ A) : AnalyticOnNhd 𝕜 (fun x => aeval (f x) p) s
参数：hf : forall i, AnalyticOnNhd 𝕜 (f · i) s；p : MvPolynomial σ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.aeval_mvPolynomial`：AnalyticAt.aeval_mvPolynomial (hf : foral
l i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A) : AnalyticAt 𝕜 (fun x => aev
al (f x) p) z
-/
theorem AnalyticOnNhd.aeval_mvPolynomial
    (hf : ∀ i, AnalyticOnNhd 𝕜 (f · i) s) (p : MvPolynomial σ A) :
    AnalyticOnNhd 𝕜 (fun x ↦ aeval (f x) p) s := fun x hx ↦ .aeval_mvPolynomial (hf · x hx) p
/-
**AnalyticOnNhd.eval_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eval_continuousLinearMap (f : E ->L[𝕜] σ -> B) (p : MvPolyno
mial σ B) : AnalyticOnNhd 𝕜 (fun x => eval (f x) p) Set.univ
参数：f : E ->L[𝕜] σ -> B；p : MvPolynomial σ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.aeval_mvPolynomial`：AnalyticAt.aeval_mvPolynomial (hf : foral
l i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A) : AnalyticAt 𝕜 (fun x => aev
al (f x) p) z
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
theorem AnalyticOnNhd.eval_continuousLinearMap (f : E →L[𝕜] σ → B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f x) p) Set.univ :=
  fun x _ ↦ .aeval_mvPolynomial (fun i ↦ ((ContinuousLinearMap.proj i).comp f).analyticAt x) p
/-
**AnalyticOnNhd.eval_continuousLinearMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eval_continuousLinearMap' (f : σ -> E ->L[𝕜] B) (p : MvPolyn
omial σ B) : AnalyticOnNhd 𝕜 (fun x => eval (f · x) p) Set.univ
参数：f : σ -> E ->L[𝕜] B；p : MvPolynomial σ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticAt.aeval_mvPolynomial`：AnalyticAt.aeval_mvPolynomial (hf : foral
l i, AnalyticAt 𝕜 (f · i) z) (p : MvPolynomial σ A) : AnalyticAt 𝕜 (fun x => aev
al (f x) p) z
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
theorem AnalyticOnNhd.eval_continuousLinearMap' (f : σ → E →L[𝕜] B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f · x) p) Set.univ :=
  fun x _ ↦ .aeval_mvPolynomial (fun i ↦ (f i).analyticAt x) p

variable [CompleteSpace 𝕜] [T2Space E] [FiniteDimensional 𝕜 E]
/-
**AnalyticOnNhd.eval_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eval_linearMap (f : E ->ₗ[𝕜] σ -> B) (p : MvPolynomial σ B) 
: AnalyticOnNhd 𝕜 (fun x => eval (f x) p) Set.univ
参数：f : E ->ₗ[𝕜] σ -> B；p : MvPolynomial σ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eval_continuousLinearMap`：AnalyticOnNhd.eval_continuousLin
earMap (f : E ->L[𝕜] σ -> B) (p : MvPolynomial σ B) : AnalyticOnNhd 𝕜 (fun x => 
eval (f x) p) Set.univ
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
-/
theorem AnalyticOnNhd.eval_linearMap (f : E →ₗ[𝕜] σ → B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f x) p) Set.univ :=
  AnalyticOnNhd.eval_continuousLinearMap { f with cont := f.continuous_of_finiteDimensional } p
/-
**AnalyticOnNhd.eval_linearMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eval_linearMap' (f : σ -> E ->ₗ[𝕜] B) (p : MvPolynomial σ B)
 : AnalyticOnNhd 𝕜 (fun x => eval (f · x) p) Set.univ
参数：f : σ -> E ->ₗ[𝕜] B；p : MvPolynomial σ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eval_linearMap`：AnalyticOnNhd.eval_linearMap (f : E ->ₗ[𝕜]
 σ -> B) (p : MvPolynomial σ B) : AnalyticOnNhd 𝕜 (fun x => eval (f x) p) Set.un
iv
-/
theorem AnalyticOnNhd.eval_linearMap' (f : σ → E →ₗ[𝕜] B) (p : MvPolynomial σ B) :
    AnalyticOnNhd 𝕜 (fun x ↦ eval (f · x) p) Set.univ := AnalyticOnNhd.eval_linearMap (.pi f) p
/-
**AnalyticOnNhd.eval_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eval_mvPolynomial [Fintype σ] (p : MvPolynomial σ 𝕜) : Analy
ticOnNhd 𝕜 (eval · p) Set.univ
参数：p : MvPolynomial σ 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eval_linearMap`：AnalyticOnNhd.eval_linearMap (f : E ->ₗ[𝕜]
 σ -> B) (p : MvPolynomial σ B) : AnalyticOnNhd 𝕜 (fun x => eval (f x) p) Set.un
iv
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem AnalyticOnNhd.eval_mvPolynomial [Fintype σ] (p : MvPolynomial σ 𝕜) :
    AnalyticOnNhd 𝕜 (eval · p) Set.univ :=
  AnalyticOnNhd.eval_linearMap (.id (R := 𝕜) (M := σ → 𝕜)) p

end MvPolynomial

