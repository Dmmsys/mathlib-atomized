/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-! # Continuous functional calculus and projections

This file collects some results related to projections, idempotents,
and the continuous functional calculus. -/

public section

section Field
variable (R : Type*) {A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]

/-
**isIdempotentElem_iff_quasispectrum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIdempotentElem_iff_quasispectrum_subset [NonUnitalRing A] [StarRing A] [
Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [NonUnitalContinuousFunc
tionalCalculus R A p] (a : A) (ha : p a) : IsIdempotentElem a ↔ quasispectrum R 
a subseteq {0, 1}
参数：a : A；ha : p a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsIdempotentElem.quasispectrum_subset`：IsIdempotentElem.quasispectrum_su
bset (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A] [IsScalarT
ower 𝕜 A A] [SMulCommClass …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_id'`：cfcₙ_id' : cfcₙ (fun x : R => x) a = a
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
-/
theorem isIdempotentElem_iff_quasispectrum_subset [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [NonUnitalContinuousFunctionalCalculus R A p]
    (a : A) (ha : p a) : IsIdempotentElem a ↔ quasispectrum R a ⊆ {0, 1} := by
  refine ⟨IsIdempotentElem.quasispectrum_subset R, fun h ↦ ?_⟩
  rw [IsIdempotentElem, ← cfcₙ_id' R a, ← cfcₙ_mul _ _]
  exact cfcₙ_congr fun x hx ↦ by grind
/-
**isIdempotentElem_iff_spectrum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIdempotentElem_iff_spectrum_subset [Ring A] [StarRing A] [Algebra R A] [
NonUnitalContinuousFunctionalCalculus R A p] (a : A) (ha : p a) : IsIdempotentEl
em a ↔ spectrum R a subseteq {0, 1}
参数：a : A；ha : p a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem isIdempotentElem_iff_spectrum_subset [Ring A] [StarRing A] [Algebra R A]
    [NonUnitalContinuousFunctionalCalculus R A p] (a : A) (ha : p a) :
    IsIdempotentElem a ↔ spectrum R a ⊆ {0, 1} := by
  grind [quasispectrum_eq_spectrum_union_zero, isIdempotentElem_iff_quasispectrum_subset R]

end Field

/-
**isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star {A : Typ
e*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module Real A] [IsScala
rTower Real A A] [SMulCommClass Real A A] [NonUnitalContinuousFunctionalCalculus
 Real A IsSelfAdjoint] {x : A} : IsIdempotentElem (star x * x) ↔ IsIdempotentEle
m (x * star x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `isIdempotentElem_iff_quasispectrum_subset`：isIdempotentElem_iff_quasispe
ctrum_subset [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [
SMulCommClass R A A] [NonUnital…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `quasispectrum.mul_comm`：quasispectrum.mul_comm {R A : Type*} [CommRing R
] [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a 
b : A) : qua…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star {A : Type*}
    [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {x : A} : IsIdempotentElem (star x * x) ↔ IsIdempotentElem (x * star x) := by
  simp [isIdempotentElem_iff_quasispectrum_subset ℝ, quasispectrum.mul_comm]
