/-
Copyright (c) 2026 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Conjugating by the square root of a positive element in a C⋆-algebra

This file defines `conjSqrt c a` as `sqrt c * a * sqrt c`, and develops API for this operation.

## Main declarations

* `conjSqrt c`: the map `fun a => sqrt c * a * sqrt c`, bundled as a continuous linear map,
-/

namespace CFC

open Ring

public section ConjSqrt

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [SeparatelyContinuousMul A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugation by the square root of an element, i.e. `sqrt c * a * sqrt c`. -/
@[expose]
/-
**CFC.conjSqrt** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
形式化陈述：conjSqrt (c : A) : A ->L[Real] A where toLinearMap
参数：c : A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ

--- 原说明 ---
Conjugation by the square root of an element, i.e. `sqrt c * a * sqrt c`.
-/
noncomputable def conjSqrt (c : A) : A →L[ℝ] A where
  toLinearMap := .mulLeftRight ℝ (sqrt c, sqrt c)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CFC.toLinearMap_conjSqrt** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : Ring A] [inst_2 : StarR
ing A] [inst_3 : TopologicalSpace A]   [inst_4 : StarOrderedRing A] [inst_5 : Al
gebra ℝ A] [inst_6 : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]   [inst_7 :
 NonnegSpectrumClass ℝ A] [inst_8 : SeparatelyContinuousMul A] (c : A),   ↑(CFC.
conjSqrt c) = LinearMap.mulLeftRight ℝ (CFC.sqrt c, CFC.sqrt c)
参数：c : A；CFC.conjSqrt c；CFC.sqrt c, CFC.sqrt c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
@[simp] lemma toLinearMap_conjSqrt (c : A) :
    (conjSqrt c).toLinearMap = .mulLeftRight ℝ (sqrt c, sqrt c) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CFC.conjSqrt_apply** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a * sqrt c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a * sqrt c := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CFC.conjSqrt_of_not_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 <= c) : conjSqrt c a = 0
参数：hc : ¬0 <= c。
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CFC.sqrt_of_not_nonneg`：sqrt_of_not_nonneg {a : A} (ha : ¬0 <= a) : sqrt
 a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 ≤ c) : conjSqrt c a = 0 := by
  simp [conjSqrt_apply, sqrt_of_not_nonneg hc]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CFC.conjSqrt_monotone** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_monotone {c : A} : Monotone (conjSqrt c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsSelfAdjoint.conjugate_le_conjugate`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R] 
  {a b : R}, a ≤ b → ∀ {c …
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.conjSqrt_of_not_nonneg`：conjSqrt_of_not_nonneg {c a : A} (hc : ¬0 <=
 c) : conjSqrt c a = 0
-/
lemma conjSqrt_monotone {c : A} : Monotone (conjSqrt c) := by
  intro a b hab
  by_cases hc : 0 ≤ c
  · exact IsSelfAdjoint.conjugate_le_conjugate hab (by cfc_tac)
  · simp [conjSqrt_of_not_nonneg hc]

set_option backward.isDefEq.respectTransparency.types false in
@[gcongr]
/-
**CFC.conjSqrt_le_conjSqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_le_conjSqrt {c a b : A} (h : a <= b) : conjSqrt c a <= conjSqrt c
 b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.conjSqrt_monotone`：conjSqrt_monotone {c : A} : Monotone (conjSqrt c)
-/
lemma conjSqrt_le_conjSqrt {c a b : A} (h : a ≤ b) : conjSqrt c a ≤ conjSqrt c b :=
  conjSqrt_monotone h

variable [IsSemitopologicalRing A] [T2Space A]

set_option linter.overlappingInstances false

@[grind =]
/-
**CFC.isStrictlyPositive_conjSqrt_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：isStrictlyPositive_conjSqrt_iff (c a : A) (hc : IsStrictlyPositive c
参数：c a : A。
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
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.conjSqrt_apply`：conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a
 * sqrt c
-/
lemma isStrictlyPositive_conjSqrt_iff (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    IsStrictlyPositive (conjSqrt c a) ↔ IsStrictlyPositive a := by
  have hc' : IsSelfAdjoint (sqrt c) := by cfc_tac
  rw [conjSqrt_apply]
  by_cases ha : IsSelfAdjoint a <;> grind

set_option backward.isDefEq.respectTransparency.types false in
@[grind _=_]
/-
**CFC.ringInverse_conjSqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c
参数：c a : A。
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
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    (conjSqrt c a)⁻¹ʳ = conjSqrt c⁻¹ʳ a⁻¹ʳ := by
  by_cases ha : IsUnit a
  · grind [conjSqrt_apply]
  · have : ¬IsUnit (conjSqrt c a) := by grind [conjSqrt_apply, IsUnit.mul_left_iff]
    simp [inverse_non_unit a ha, inverse_non_unit _ this]

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/-
**CFC.conjSqrt_ringInverse_conjSqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c
参数：c a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma conjSqrt_ringInverse_conjSqrt (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ (conjSqrt c a) = a := by
  grind [IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ (sqrt c) 1, Ring.inverse_mul_cancel,
         conjSqrt_apply] =>
    have : sqrt c⁻¹ʳ * sqrt c = 1
    have : Commute (sqrt c) (sqrt c⁻¹ʳ)
    finish

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/-
**CFC.conjSqrt_conjSqrt_ringInverse** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_conjSqrt_ringInverse (c a : A) (hc : IsStrictlyPositive c
参数：c a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma conjSqrt_conjSqrt_ringInverse (c a : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c (conjSqrt c⁻¹ʳ a) = a := by
  grind [conjSqrt_ringInverse_conjSqrt _ _ hc.ringInverse]

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/-
**CFC.conjSqrt_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_one (c : A) (hc : 0 <= c
参数：c : A。
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
· 使用引理 `CFC.conjSqrt_apply`：conjSqrt_apply {c a : A} : conjSqrt c a = sqrt c * a
 * sqrt c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
-/
lemma conjSqrt_one (c : A) (hc : 0 ≤ c := by cfc_tac) : conjSqrt c 1 = c := by
  rw [conjSqrt_apply, mul_one, sqrt_mul_sqrt_self _]

set_option backward.isDefEq.respectTransparency.types false in
@[grind =]
/-
**CFC.conjSqrt_ringInverse_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：conjSqrt_ringInverse_self (c : A) (hc : IsStrictlyPositive c
参数：c : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma conjSqrt_ringInverse_self (c : A) (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ c = 1 := by
  grind [conjSqrt_one c]

end ConjSqrt

end CFC

