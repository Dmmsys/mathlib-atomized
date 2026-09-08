/-
Copyright (c) 2025 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Higher smoothness of polynomials

We prove that polynomials are `C^∞`.
-/

public section

namespace Polynomial

/-- Polynomials are smooth -/
/-
**Polynomial.contDiff_aeval** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：contDiff_aeval {R 𝕜 : Type*} [CommSemiring R] [NontriviallyNormedField 𝕜] 
[Algebra R 𝕜] (f : Polynomial R) (n : WithTop Nat∞) : ContDiff 𝕜 n (fun x : 𝕜 =>
 f.aeval x)
参数：f : Polynomial R；n : WithTop Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `ContDiff.pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : T
ype uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {n : WithTo
p …
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)

--- 原说明 ---
Polynomials are smooth
-/
lemma contDiff_aeval {R 𝕜 : Type*} [CommSemiring R] [NontriviallyNormedField 𝕜] [Algebra R 𝕜]
    (f : Polynomial R) (n : WithTop ℕ∞) : ContDiff 𝕜 n (fun x : 𝕜 ↦ f.aeval x) := by
  induction f using Polynomial.induction_on' with
  | add f g fc gc => simpa using fc.add gc
  | monomial n a => simpa using contDiff_const.mul (contDiff_id.pow _)

end Polynomial

