/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # The positive (and negative) parts of a selfadjoint element in a C⋆-algebra

This file defines the positive and negative parts of a selfadjoint element in a C⋆-algebra via
the continuous functional calculus and develops the basic API, including the uniqueness of the
positive and negative parts.
-/

public section

open scoped NNReal

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

namespace CStarAlgebra

/-
**CStarAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PosPart A where
  posPart := cfcₙ (·⁺ : ℝ → ℝ)
/-
**CStarAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NegPart A where
  negPart := cfcₙ (·⁻ : ℝ → ℝ)

end CStarAlgebra

namespace CFC

/-
**CFC.posPart_def** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : ℝ → ℝ) a := rfl
/-
**CFC.negPart_def** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : ℝ → ℝ) a := rfl

@[simp]
/-
**CFC.posPart_zero** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_zero : (0 : A)⁺ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcₙ_apply_zero`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : 
CommSemiring R] [inst_1 : Nontrivial R] [inst_2 : StarRing R]   [inst_3 : Metric
Space…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma posPart_zero : (0 : A)⁺ = 0 := by simp [posPart_def]

@[simp]
/-
**CFC.negPart_zero** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_zero : (0 : A)⁻ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcₙ_apply_zero`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : 
CommSemiring R] [inst_1 : Nontrivial R] [inst_2 : StarRing R]   [inst_3 : Metric
Space…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma negPart_zero : (0 : A)⁻ = 0 := by simp [negPart_def]
/-
**CFC.posPart_eq_zero_of_not_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁺ 
= 0
参数：ha : ¬IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
-/
lemma posPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁺ = 0 :=
  cfcₙ_apply_of_not_predicate a ha
/-
**CFC.negPart_eq_zero_of_not_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁻ 
= 0
参数：ha : ¬IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
-/
lemma negPart_eq_zero_of_not_isSelfAdjoint {a : A} (ha : ¬IsSelfAdjoint a) : a⁻ = 0 :=
  cfcₙ_apply_of_not_predicate a ha

@[simp]
/-
**CFC.posPart_mul_negPart** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `continuous_negPart`：continuous_negPart : Continuous (negPart : α -> α)
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `cfcₙ_zero`：cfcₙ_zero : cfcₙ (0 : R -> R) a = 0
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

@[simp]
/-
**CFC.negPart_mul_posPart** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_negPart`：continuous_negPart : Continuous (negPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用引理 `cfcₙ_zero`：cfcₙ_zero : cfcₙ (0 : R -> R) a = 0
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total 0 x
  · simp [cfcₙ_apply_of_not_predicate a ha]
/-
**CFC.posPart_sub_negPart** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_sub`：cfcₙ_sub : cfcₙ (fun x => f x - g x) a = cfcₙ f a - cfcₙ g a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `continuous_negPart`：continuous_negPart : Continuous (negPart : α -> α)
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `posPart_sub_negPart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGr
oup α] [AddLeftMono α] (a : α), a⁺ - a⁻ = a
-/
lemma posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : a⁺ - a⁻ = a := by
  rw [posPart_def, negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id ℝ a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

section Unique

variable [T2Space A]

@[simp]
/-
**CFC.posPart_neg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_neg (a : A) : (-a)⁺ = a⁻
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_comp_neg`：cfcₙ_comp_neg (hf : ContinuousOn f ((-·) '' (σₙ R a))
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
-/
lemma posPart_neg (a : A) : (-a)⁺ = a⁻ := by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h ↦ ha (by simpa using h.neg)
    rw [posPart_def, negPart_def, cfcₙ_apply_of_not_predicate a ha,
      cfcₙ_apply_of_not_predicate _ ha']

@[simp]
/-
**CFC.negPart_neg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_neg (a : A) : (-a)⁻ = a⁺
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `CFC.posPart_neg`：posPart_neg (a : A) : (-a)⁺ = a⁻
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma negPart_neg (a : A) : (-a)⁻ = a⁺ := by
  rw [← eq_comm, ← sub_eq_zero, ← posPart_neg, neg_neg, sub_self]

section SMul

variable [StarModule ℝ A]

@[simp]
/-
**CFC.posPart_smul** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_smul {r : Real>=0} {a : A} : (r • a)⁺ = r • a⁺
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_comp_smul`：cfcₙ_comp_smul {S : Type*} [SMulZeroClass S R] [Continuo
usConstSMul S R] [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R
 -> …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfcₙ_smul`：cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMu
l S R] [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (…
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `CFC.posPart_zero`：posPart_zero : (0 : A)⁺ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `IsSelfAdjoint.smul_iff`：smul_iff [Monoid R] [StarMul R] [Star A] [MulAct
ion R A] [StarModule R A] {r : R} (hr : IsSelfAdjoint r) (hu : IsUnit r) {x : A}
 : IsSelfAdj…
（共 36 条，此处仅展示前 30 条）
-/
lemma posPart_smul {r : ℝ≥0} {a : A} : (r • a)⁺ = r • a⁺ := by
  by_cases ha : IsSelfAdjoint a
  · simp only [CFC.posPart_def, NNReal.smul_def]
    rw [← cfcₙ_comp_smul .., ← cfcₙ_smul ..]
    refine cfcₙ_congr fun x hx ↦ ?_
    simp [_root_.posPart_def, mul_max_of_nonneg]
  · obtain (rfl | hr) := eq_or_ne r 0
    · simp
    · have := (not_iff_not.mpr <| (IsSelfAdjoint.all r).smul_iff hr.isUnit (x := a)) |>.mpr ha
      simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate a ha,
        cfcₙ_apply_of_not_predicate _ this]

@[simp]
/-
**CFC.negPart_smul** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_smul {r : Real>=0} {a : A} : (r • a)⁻ = r • a⁻
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `CFC.posPart_neg`：posPart_neg (a : A) : (-a)⁺ = a⁻
· 使用引理 `CFC.posPart_smul`：posPart_smul {r : Real>=0} {a : A} : (r • a)⁺ = r • a⁺
-/
lemma negPart_smul {r : ℝ≥0} {a : A} : (r • a)⁻ = r • a⁻ := by
  simpa using posPart_smul (r := r) (a := -a)
/-
**CFC.posPart_smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_smul_of_nonneg {r : Real} (hr : 0 <= r) {a : A} : (r • a)⁺ = r • a
⁺
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.posPart_smul`：posPart_smul {r : Real>=0} {a : A} : (r • a)⁺ = r • a⁺
-/
lemma posPart_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) {a : A} : (r • a)⁺ = r • a⁺ :=
  posPart_smul (r := ⟨r, hr⟩)
/-
**CFC.posPart_smul_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_smul_of_nonpos {r : Real} (hr : r <= 0) {a : A} : (r • a)⁺ = -r • 
a⁻
参数：hr : r <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `CFC.posPart_smul_of_nonneg`：posPart_smul_of_nonneg {r : Real} (hr : 0 <=
 r) {a : A} : (r • a)⁺ = r • a⁺
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `CFC.posPart_neg`：posPart_neg (a : A) : (-a)⁺ = a⁻
-/
lemma posPart_smul_of_nonpos {r : ℝ} (hr : r ≤ 0) {a : A} : (r • a)⁺ = -r • a⁻ := by
  nth_rw 1 [← neg_neg r]
  rw [neg_smul, ← smul_neg, posPart_smul_of_nonneg (neg_nonneg.mpr hr), posPart_neg]
/-
**CFC.negPart_smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_smul_of_nonneg {r : Real} (hr : 0 <= r) {a : A} : (r • a)⁻ = r • a
⁻
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `CFC.negPart_neg`：negPart_neg (a : A) : (-a)⁻ = a⁺
· 使用引理 `CFC.posPart_smul_of_nonpos`：posPart_smul_of_nonpos {r : Real} (hr : r <=
 0) {a : A} : (r • a)⁺ = -r • a⁻
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma negPart_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) {a : A} : (r • a)⁻ = r • a⁻ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonpos (by simpa), neg_neg]
/-
**CFC.negPart_smul_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_smul_of_nonpos {r : Real} (hr : r <= 0) {a : A} : (r • a)⁻ = -r • 
a⁺
参数：hr : r <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `CFC.negPart_neg`：negPart_neg (a : A) : (-a)⁻ = a⁺
· 使用引理 `CFC.posPart_smul_of_nonneg`：posPart_smul_of_nonneg {r : Real} (hr : 0 <=
 r) {a : A} : (r • a)⁺ = r • a⁺
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma negPart_smul_of_nonpos {r : ℝ} (hr : r ≤ 0) {a : A} : (r • a)⁻ = -r • a⁺ := by
  conv_lhs => rw [← neg_neg r, neg_smul, negPart_neg, posPart_smul_of_nonneg (by simpa)]

end SMul

end Unique

variable [PartialOrder A] [StarOrderedRing A]

@[aesop norm apply (rule_sets := [CStarAlgebra])]
/-
**CFC.posPart_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_nonneg (a : A) : 0 <= a⁺
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_nonneg`：cfcₙ_nonneg {f : R -> R} {a : A} (h : forall x in σₙ R a, 0
 <= f x) : 0 <= cfcₙ f a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `posPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁺
-/
lemma posPart_nonneg (a : A) :
    0 ≤ a⁺ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

@[aesop norm apply (rule_sets := [CStarAlgebra])]
/-
**CFC.negPart_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_nonneg (a : A) : 0 <= a⁻
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_nonneg`：cfcₙ_nonneg {f : R -> R} {a : A} (h : forall x in σₙ R a, 0
 <= f x) : 0 <= cfcₙ f a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `negPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁻
-/
lemma negPart_nonneg (a : A) :
    0 ≤ a⁻ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)
/-
**CFC.** 是 Mathlib 中的一个实例，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SelfAdjointDecompose A where
  exists_nonneg_sub_nonneg {a} ha := ⟨a⁺, a⁻, by cfc_tac, by cfc_tac, (posPart_sub_negPart a).symm⟩
/-
**CFC.posPart_eq_of_eq_sub_negPart** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_eq_of_eq_sub_negPart {a b : A} (hab : a = b - a⁻) (hb : 0 <= b
参数：hab : a = b - a⁻。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `LE.le.isSelfAdjoint`：∀ {R : Type u_1} [inst : NonUnitalSemiring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   {x : R}, 0 ≤ x 
→ IsSelfA…
· 使用引理 `CFC.negPart_nonneg`：negPart_nonneg (a : A) : 0 <= a⁻
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
-/
lemma posPart_eq_of_eq_sub_negPart {a b : A} (hab : a = b - a⁻) (hb : 0 ≤ b := by cfc_tac) :
    a⁺ = b := by
  have ha := hab.symm ▸ hb.isSelfAdjoint.sub (negPart_nonneg a).isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hab
  simpa using hab
/-
**CFC.negPart_eq_of_eq_PosPart_sub** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_eq_of_eq_PosPart_sub {a c : A} (hac : a = a⁺ - c) (hc : 0 <= c
参数：hac : a = a⁺ - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `LE.le.isSelfAdjoint`：∀ {R : Type u_1} [inst : NonUnitalSemiring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   {x : R}, 0 ≤ x 
→ IsSelfA…
· 使用引理 `CFC.posPart_nonneg`：posPart_nonneg (a : A) : 0 <= a⁺
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
-/
lemma negPart_eq_of_eq_PosPart_sub {a c : A} (hac : a = a⁺ - c) (hc : 0 ≤ c := by cfc_tac) :
    a⁻ = c := by
  have ha := hac.symm ▸ (posPart_nonneg a).isSelfAdjoint.sub hc.isSelfAdjoint
  nth_rw 1 [← posPart_sub_negPart a] at hac
  simpa using hac
/-
**CFC.le_posPart** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：le_posPart {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用引理 `CFC.negPart_nonneg`：negPart_nonneg (a : A) : 0 <= a⁻
-/
lemma le_posPart {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : a ≤ a⁺ := by
  simpa [posPart_sub_negPart a] using sub_le_self a⁺ (negPart_nonneg a)
/-
**CFC.neg_negPart_le** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：neg_negPart_le {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用引理 `CFC.posPart_nonneg`：posPart_nonneg (a : A) : 0 <= a⁺
-/
lemma neg_negPart_le {a : A} (ha : IsSelfAdjoint a := by cfc_tac) : -a⁻ ≤ a := by
  simpa only [posPart_sub_negPart a, ← sub_eq_add_neg]
    using le_add_of_nonneg_left (a := -a⁻) (posPart_nonneg a)

variable [NonnegSpectrumClass ℝ A]
/-
**CFC.posPart_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_eq_self (a : A) : a⁺ = a ↔ 0 <= a
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.posPart_nonneg`：posPart_nonneg (a : A) : 0 <= a⁺
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`：∀ {𝕜 : Type u_3} {A 
: Type u_4} {inst : CommSemiring 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NonUnita
lRing A}   {inst_3 : PartialOrder A} {in…
-/
lemma posPart_eq_self (a : A) : a⁺ = a ↔ 0 ≤ a := by
  refine ⟨fun ha ↦ ha ▸ posPart_nonneg a, fun ha ↦ ?_⟩
  conv_rhs => rw [← cfcₙ_id ℝ a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx ↦ ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx
/-
**CFC.negPart_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.posPart_eq_self`：posPart_eq_self (a : A) : a⁺ = a ↔ 0 <= a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma negPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁻ = 0 ↔ 0 ≤ a := by
  rw [← posPart_eq_self, eq_comm (b := a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp
/-
**CFC.negPart_eq_neg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_eq_neg (a : A) : a⁻ = -a ↔ a <= 0
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用引理 `CFC.negPart_nonneg`：negPart_nonneg (a : A) : 0 <= a⁻
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用引理 `cfcₙ_neg`：cfcₙ_neg : cfcₙ (fun x => -(f x)) a = -(cfcₙ f a)
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`：∀ {𝕜 : Type u_3} {A 
: Type u_4} {inst : CommSemiring 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NonUnita
lRing A}   {inst_3 : PartialOrder A} {in…
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr`：quasispectrum_eq_spectrum_inr
 (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTo
wer R A A] [SMulCommClass R A A…
· 使用定理 `Unitization.inr_neg`：inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Uni
tization R A) = -m
· 使用定理 `spectrum.neg_eq`：neg_eq (a : A) : -σ a = σ (-a)
· 使用定理 `Set.mem_neg`：∀ {α : Type u_2} [inst : Neg α] {s : Set α} {a : α}, a ∈ -s
 ↔ -a ∈ s
-/
lemma negPart_eq_neg (a : A) : a⁻ = -a ↔ a ≤ 0 := by
  rw [← neg_inj, neg_neg, eq_comm]
  refine ⟨fun ha ↦ by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha ↦ ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def, ← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id ℝ a]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Unitization.quasispectrum_eq_spectrum_inr ℝ, ← neg_neg x, ← Set.mem_neg,
    spectrum.neg_eq, ← Unitization.inr_neg, ← Unitization.quasispectrum_eq_spectrum_inr ℝ] at hx
  rw [← neg_eq_iff_eq_neg, eq_comm]
  simpa using quasispectrum_nonneg_of_nonneg _ ha _ hx
/-
**CFC.posPart_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.negPart_eq_neg`：negPart_eq_neg (a : A) : a⁻ = -a ↔ a <= 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma posPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁺ = 0 ↔ a ≤ 0 := by
  rw [← negPart_eq_neg, eq_comm (b := -a)]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

local notation "σₙ" => quasispectrum

open ContinuousMapZero

variable [IsSemitopologicalRing A] [T2Space A]

set_option backward.isDefEq.respectTransparency false in
open NonUnitalContinuousFunctionalCalculus in
/-- The positive and negative parts of a selfadjoint element `a` are unique. That is, if
`a = b - c` is the difference of nonnegative elements whose product is zero, then these are
precisely `a⁺` and `a⁻`. -/
/-
**CFC.posPart_negPart_unique** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_negPart_unique {a b c : A} (habc : a = b - c) (hbc : b * c = 0) (h
b : 0 <= b
参数：habc : a = b - c；hbc : b * c = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用引理 `CFC.negPart_eq_of_eq_PosPart_sub`：negPart_eq_of_eq_PosPart_sub {a c : A}
 (hac : a = a⁺ - c) (hc : 0 <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用引理 `NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum`：NonUnital
ContinuousFunctionalCalculus.isCompact_quasispectrum (a : A) : IsCompact (σₙ R a
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `quasispectrum.zero_mem`：quasispectrum.zero_mem [Nontrivial R] (a : A) : 
0 in quasispectrum R a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero`：ContinuousMapZe
ro.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalSemi
ring A] [Star A] [TopologicalSpace A] [Separa…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用引理 `ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero`：ContinuousMapZe
ro.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalSemi
ring A] [Star A] [TopologicalSpace A] [Separa…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
The positive and negative parts of a selfadjoint element `a` are unique. That is
, if
`a = b - c` is the difference of nonnegative elements whose product is zero, the
n these are
precisely `a⁺` and `a⁻`.
-/
lemma posPart_negPart_unique {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
    (hb : 0 ≤ b := by cfc_tac) (hc : 0 ≤ c := by cfc_tac) :
    a⁺ = b ∧ a⁻ = c := by
  /- The key idea is to show that `cfcₙ f a = cfcₙ f b + cfcₙ f (-c)` for all real-valued `f`
  continuous on the union of the spectra of `a`, `b`, and `-c`. Then apply this to `f = (·⁺)`.
  The equality holds because both sides constitute star homomorphisms which agree on `f = id` since
  `a = b - c`. -/
  /- `a`, `b`, `-c` are selfadjoint. -/
  have hb' : IsSelfAdjoint b := .of_nonneg hb
  have hc' : IsSelfAdjoint (-c) := .neg <| .of_nonneg hc
  have ha : IsSelfAdjoint a := habc ▸ hb'.sub <| .of_nonneg hc
  /- It suffices to show `b = a⁺` since `a⁺ - a⁻ = a = b - c` -/
  rw [and_iff_left_of_imp ?of_b_eq]
  case of_b_eq =>
    rintro rfl
    exact negPart_eq_of_eq_PosPart_sub habc hc
  /- `s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)` is compact and each of these sets are subsets of `s`.
  Moreover, `0 ∈ s`. -/
  let s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)
  have hs : CompactSpace s := by
    refine isCompact_iff_compactSpace.mp <| (IsCompact.union ?_ ?_).union ?_
    all_goals exact isCompact_quasispectrum _
  obtain ⟨has, hbs, hcs⟩ : σₙ ℝ a ⊆ s ∧ σₙ ℝ b ⊆ s ∧ σₙ ℝ (-c) ⊆ s := by grind
  have : Fact (0 ∈ s) := ⟨by aesop⟩
  /- The continuous functional calculi for functions `f g : C(s, ℝ)₀` applied to `b` and `(-c)`
  are orthogonal (i.e., the product is always zero). -/
  have mul₁ (f g : C(s, ℝ)₀) :
      (cfcₙHomSuperset hb' hbs f) * (cfcₙHomSuperset hc' hcs g) = 0 := by
    refine f.nonUnitalStarAlgHom_apply_mul_eq_zero _ _ ?id ?star_id
      (cfcₙHomSuperset_continuous hb' hbs)
    case' star_id => rw [star_trivial]
    all_goals
      refine g.mul_nonUnitalStarAlgHom_apply_eq_zero _ _ ?_ ?_
        (cfcₙHomSuperset_continuous hc' hcs)
      all_goals simp only [star_trivial, cfcₙHomSuperset_id hb' hbs,
        cfcₙHomSuperset_id hc' hcs, mul_neg, hbc, neg_zero]
  have mul₂ (f g : C(s, ℝ)₀) : (cfcₙHomSuperset hc' hcs f) * (cfcₙHomSuperset hb' hbs g) = 0 := by
    simpa only [star_mul, star_zero, ← map_star, star_trivial] using congr(star $(mul₁ g f))
  /- `fun f ↦ cfcₙ f b + cfcₙ f (-c)` defines a star homomorphism `ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` which
  agrees with the star homomorphism `cfcₙ · a : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` since
  `cfcₙ id a = a = b - c = cfcₙ id b + cfcₙ id (-c)`. -/
  let ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A :=
    { (cfcₙHomSuperset hb' hbs : C(s, ℝ)₀ →ₗ[ℝ] A) + (cfcₙHomSuperset hc' hcs : C(s, ℝ)₀ →ₗ[ℝ] A)
        with
      toFun := cfcₙHomSuperset hb' hbs + cfcₙHomSuperset hc' hcs
      map_zero' := by simp [-cfcₙHomSuperset_apply]
      map_mul' := fun f g ↦ by
        simp only [Pi.add_apply, map_mul, mul_add, add_mul, mul₂, add_zero, mul₁,
          zero_add]
      map_star' := fun f ↦ by simp [← map_star] }
  have key : (cfcₙHomSuperset ha has) = ψ :=
    have : ContinuousMapZero.UniqueHom ℝ A := inferInstance
    ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id s
    (cfcₙHomSuperset ha has) ψ (cfcₙHomSuperset_continuous ha has)
    ((cfcₙHomSuperset_continuous hb' hbs).add (cfcₙHomSuperset_continuous hc' hcs))
    (by simpa [ψ, -cfcₙHomSuperset_apply, cfcₙHomSuperset_id, sub_eq_add_neg] using habc)
  /- Applying the equality of star homomorphisms to the function `(·⁺ : ℝ → ℝ)` we find that
  `b = cfcₙ id b + cfcₙ 0 (-c) = cfcₙ (·⁺) b - cfcₙ (·⁺) (-c) = cfcₙ (·⁺) a = a⁺`, where the
  second equality follows because these functions are equal on the spectra of `b` and `-c`,
  respectively, since `0 ≤ b` and `-c ≤ 0`. -/
  let f : C(s, ℝ)₀ := ⟨⟨(·⁺), by fun_prop⟩, by simp; norm_cast⟩
  replace key := congr($key f)
  simp only [cfcₙHomSuperset_apply, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk, ψ,
    Pi.add_apply, cfcₙHom_eq_cfcₙ_extend (·⁺)] at key
  symm
  calc
    b = cfcₙ (id : ℝ → ℝ) b + cfcₙ (0 : ℝ → ℝ) (-c) := by simp [cfcₙ_id ℝ b]
    _ = _ := by
      congr! 1
      all_goals
        refine cfcₙ_congr fun x hx ↦ Eq.symm ?_
        lift x to σₙ ℝ _ using hx
        simp only [Subtype.val_injective.extend_apply, comp_apply, coe_mk,
          ContinuousMap.coe_mk, Subtype.map_coe, id_eq, _root_.posPart_eq_self, f, Pi.zero_apply,
          posPart_eq_zero]
      · exact quasispectrum_nonneg_of_nonneg b hb x.val x.property
      · obtain ⟨x, hx⟩ := x
        simp only [← neg_nonneg]
        rw [Unitization.quasispectrum_eq_spectrum_inr ℝ (-c), Unitization.inr_neg,
          ← spectrum.neg_eq, Set.mem_neg, ← Unitization.quasispectrum_eq_spectrum_inr ℝ c]
          at hx
        exact quasispectrum_nonneg_of_nonneg c hc _ hx
    _ = _ := key.symm
    _ = a⁺ := by
      refine cfcₙ_congr fun x hx ↦ ?_
      lift x to σₙ ℝ a using hx
      simp [f]

end CFC

end NonUnital

section Unital

namespace CFC

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [TopologicalSpace A]
variable [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [T2Space A]

@[simp]
/-
**CFC.posPart_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_one : (1 : A)⁺ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `cfc_apply_one`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Co
mmSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopol
ogi…
· 使用定理 `posPart_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegM
onoid α] {a : α}, 0 ≤ a → a⁺ = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma posPart_one : (1 : A)⁺ = 1 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
/-
**CFC.negPart_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_one : (1 : A)⁻ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_negPart`：continuous_negPart : Continuous (negPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `cfc_apply_one`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Co
mmSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopol
ogi…
· 使用定理 `negPart_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], 0 ≤ a → a⁻ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma negPart_one : (1 : A)⁻ = 0 := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
/-
**CFC.posPart_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_algebraMap (r : Real) : (algebraMap Real A r)⁺ = algebraMap Real A
 r⁺
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
-/
lemma posPart_algebraMap (r : ℝ) : (algebraMap ℝ A r)⁺ = algebraMap ℝ A r⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  simp

@[simp]
/-
**CFC.negPart_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：negPart_algebraMap (r : Real) : (algebraMap Real A r)⁻ = algebraMap Real A
 r⁻
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.negPart_def`：negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : Real -> Real) a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_negPart`：continuous_negPart : Continuous (negPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `negPart_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGrou
p α] {a : α} [AddLeftMono α], a ≤ 0 → a⁻ = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
-/
lemma negPart_algebraMap (r : ℝ) : (algebraMap ℝ A r)⁻ = algebraMap ℝ A r⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc]
  simp

open NNReal in
@[simp]
/-
**CFC.posPart_algebraMap_nnreal** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_algebraMap_nnreal (r : Real>=0) : (algebraMap Real>=0 A r)⁺ = alge
braMap Real>=0 A r
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_def`：posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : Real -> Real) a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `posPart_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMonoid
 α], 0⁺ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
· 使用定理 `posPart_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegM
onoid α] {a : α}, 0 ≤ a → a⁺ = a
-/
lemma posPart_algebraMap_nnreal (r : ℝ≥0) : (algebraMap ℝ≥0 A r)⁺ = algebraMap ℝ≥0 A r := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc, IsScalarTower.algebraMap_apply ℝ≥0 ℝ A]
  simp

open NNReal in
@[simp]
/-
**CFC.posPart_natCast** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：posPart_natCast (n : Nat) : (n : A)⁺ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `CFC.posPart_algebraMap_nnreal`：posPart_algebraMap_nnreal (r : Real>=0) :
 (algebraMap Real>=0 A r)⁺ = algebraMap Real>=0 A r
-/
lemma posPart_natCast (n : ℕ) : (n : A)⁺ = n := by
  rw [← map_natCast (algebraMap ℝ≥0 A), posPart_algebraMap_nnreal]

end CFC

end Unital

section SpanNonneg

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
variable [StarRing A] [TopologicalSpace A] [StarModule ℂ A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

open Submodule Complex
open scoped ComplexStarModule

/-
**CStarAlgebra.linear_combination_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.linear_combination_nonneg (x : A) : ((ℜ x : A)⁺ - (ℜ x : A)⁻)
 + (I • (ℑ x : A)⁺ - I • (ℑ x : A)⁻) = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
-/
lemma CStarAlgebra.linear_combination_nonneg (x : A) :
    ((ℜ x : A)⁺ - (ℜ x : A)⁻) + (I • (ℑ x : A)⁺ - I • (ℑ x : A)⁻) = x := by
  rw [CFC.posPart_sub_negPart _ (ℜ x).2, ← smul_sub, CFC.posPart_sub_negPart _ (ℑ x).2,
    realPart_add_I_smul_imaginaryPart x]

variable [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-algebra is spanned by its nonnegative elements. -/
/-
**CStarAlgebra.span_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.span_nonneg : Submodule.span Complex {a : A | 0 <= a} = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CStarAlgebra.linear_combination_nonneg`：CStarAlgebra.linear_combination_
nonneg (x : A) : ((ℜ x : A)⁺ - (ℜ x : A)⁻) + (I • (ℑ x : A)⁺ - I • (ℑ x : A)⁻) =
 x
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `CFC.posPart_nonneg`：posPart_nonneg (a : A) : 0 <= a⁺
· 使用引理 `CFC.negPart_nonneg`：negPart_nonneg (a : A) : 0 <= a⁻
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p

--- 原说明 ---
A C⋆-algebra is spanned by its nonnegative elements.
-/
lemma CStarAlgebra.span_nonneg : Submodule.span ℂ {a : A | 0 ≤ a} = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [← CStarAlgebra.linear_combination_nonneg x]
  apply_rules [sub_mem, Submodule.smul_mem, add_mem]
  all_goals
    refine subset_span ?_
    first | apply CFC.negPart_nonneg | apply CFC.posPart_nonneg

end SpanNonneg

