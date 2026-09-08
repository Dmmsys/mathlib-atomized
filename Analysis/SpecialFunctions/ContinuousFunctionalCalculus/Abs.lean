/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric


/-!
# Absolute value defined via the continuous functional calculus

This file defines the absolute value via the non-unital continuous functional calculus
and provides basic API.

## Main declarations

+ `CFC.abs`: The absolute value as `abs a := CFC.sqrt (star a * a)`.

-/

@[expose] public section

variable {𝕜 A : Type*}

open scoped NNReal
open CFC

namespace CFC

section NonUnital

section Real

variable [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

/-- The absolute value defined via the non-unital continuous functional calculus. -/
/-
**CFC.abs** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
形式化陈述：abs (a : A)
参数：a : A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ

--- 原说明 ---
The absolute value defined via the non-unital continuous functional calculus.
-/
noncomputable def abs (a : A) := sqrt (star a * a)

@[simp, grind =]
/-
**CFC.abs_neg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_neg (a : A) : abs (-a) = abs a
参数：a : A。
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
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_neg (a : A) : abs (-a) = abs a := by
  simp [abs]

@[simp, grind ←]
/-
**CFC.abs_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_nonneg (a : A) : 0 <= abs a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
-/
lemma abs_nonneg (a : A) : 0 ≤ abs a := sqrt_nonneg _
/-
**CFC.abs_star** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_star (a : A) (ha : IsStarNormal a
参数：a : A。
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
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `star_comm_self'`：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal 
x] : star x * x = x * star x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_star (a : A) (ha : IsStarNormal a := by cfc_tac) : abs (star a) = abs a := by
  simp [abs, star_comm_self']

@[simp, grind =]
/-
**CFC.abs_zero** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_zero : abs (0 : A) = 0
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
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `CFC.sqrt_zero`：sqrt_zero : sqrt (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_zero : abs (0 : A) = 0 := by
  simp [abs]

variable [IsTopologicalRing A] [T2Space A]
/-
**CFC.abs_mul_abs** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_mul_abs (a : A) : abs a * abs a = star a * a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
-/
lemma abs_mul_abs (a : A) : abs a * abs a = star a * a :=
  sqrt_mul_sqrt_self _ <| star_mul_self_nonneg _

/- The hypotheses could be weakened to `Commute (star a * a) b`, but
in that case one should simply use `Commute.cfcₙ_nnreal` directly.

The point of this theorem is to have simpler hypotheses. -/
/-
**CFC._root_.Commute.cfcAbs_left** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hypotheses could be weakened to `Commute (star a * a) b`, but
in that case one should simply use `Commute.cfcₙ_nnreal` directly.

The point of this theorem is to have simpler hypotheses.
-/
lemma _root_.Commute.cfcAbs_left {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute (abs a) b :=
  .cfcₙ_nnreal (by simp_all [h₂.star_left]) _

/- The hypotheses could be weakened to `Commute (star a * a) b`, but
in that case one should simply use `Commute.cfcₙ_nnreal` directly.

The point of this theorem is to have simpler hypotheses. -/
/-
**CFC._root_.Commute.cfcAbs_right** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hypotheses could be weakened to `Commute (star a * a) b`, but
in that case one should simply use `Commute.cfcₙ_nnreal` directly.

The point of this theorem is to have simpler hypotheses.
-/
lemma _root_.Commute.cfcAbs_right {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute b (abs a) :=
  h₁.cfcAbs_left h₂ |>.symm

/- The hypotheses could be weakened to `Commute (star a * a) (star b * b)`, but
in that case one should simply use `Commute.cfcₙ_nnreal` (twice) directly.

The point of this theorem is to have simpler hypotheses. -/
/-
**CFC._root_.Commute.cfcAbs_cfcAbs** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hypotheses could be weakened to `Commute (star a * a) (star b * b)`, but
in that case one should simply use `Commute.cfcₙ_nnreal` (twice) directly.

The point of this theorem is to have simpler hypotheses.
-/
lemma _root_.Commute.cfcAbs_cfcAbs {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute (abs a) (abs b) :=
  Commute.cfcₙ_nnreal (by simp_all [h₂.star_left]) _ |>.symm.cfcₙ_nnreal _ |>.symm

/-- Normal elements commute with their absolute value. -/
/-
**CFC.commute_abs_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：commute_abs_self (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Commute.cfcAbs_left`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 :
 StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_
4 : SMulC…
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x

--- 原说明 ---
Normal elements commute with their absolute value.
-/
lemma commute_abs_self (a : A) (ha : IsStarNormal a := by cfc_tac) :
    Commute (abs a) a :=
  .cfcAbs_left (.refl a) ha.star_comm_self.symm
/-
**CFC._root_.Commute.cfcAbs_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Commute.cfcAbs_mul_eq {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    abs (a * b) = abs a * abs b := by
  have hab := h₁.cfcAbs_cfcAbs h₂
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _)
    (hab.mul_nonneg (abs_nonneg a) (abs_nonneg b)), hab.eq, hab.mul_mul_mul_comm,
    abs_mul_abs, abs_mul_abs, star_mul, h₂.star_left.symm.mul_mul_mul_comm, h₁.eq]
/-
**CFC.abs_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_mul_self (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.cfcAbs_mul_eq`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1
 : StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [ins
t_4 : SMulC…
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
· 使用引理 `CFC.abs_mul_abs`：abs_mul_abs (a : A) : abs a * abs a = star a * a
-/
lemma abs_mul_self (a : A) (ha : IsStarNormal a := by cfc_tac) :
    abs (a * a) = star a * a := by
  rw [Commute.cfcAbs_mul_eq (.refl a) ha.star_comm_self.symm, abs_mul_abs]
/-
**CFC.abs_nnrpow_two** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_nnrpow_two (a : A) : abs a ^ (2 : Real>=0) = star a * a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.nnrpow_two`：nnrpow_two (a : A) (ha : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CFC.abs_mul_abs`：abs_mul_abs (a : A) : abs a * abs a = star a * a
-/
lemma abs_nnrpow_two (a : A) : abs a ^ (2 : ℝ≥0) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_abs
/-
**CFC.abs_nnrpow_two_mul** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_nnrpow_two_mul (a : A) (x : Real>=0) : abs a ^ (2 * x) = (star a * a) 
^ x
参数：a : A；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.nnrpow_nnrpow`：nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y =
 a ^ (x * y)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `CFC.abs_nnrpow_two`：abs_nnrpow_two (a : A) : abs a ^ (2 : Real>=0) = sta
r a * a
-/
lemma abs_nnrpow_two_mul (a : A) (x : ℝ≥0) :
    abs a ^ (2 * x) = (star a * a) ^ x := by rw [← nnrpow_nnrpow, abs_nnrpow_two]
/-
**CFC.abs_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_nnrpow (a : A) (x : Real>=0) : abs a ^ x = (star a * a) ^ (x / 2)
参数：a : A；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_left_comm`：mul_div_left_comm : a * (b / c) = b * (a / c)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_nnrpow (a : A) (x : ℝ≥0) :
    abs a ^ x = (star a * a) ^ (x / 2) := by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

@[grind =]
/-
**CFC.abs_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_of_nonneg (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.eq_1`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRi
ng A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4 : SMu
lC…
· 使用引理 `LE.le.star_eq`：LE.le.star_eq {x : R} (hx : 0 <= x) : star x = x
· 使用引理 `CFC.sqrt_mul_self`：sqrt_mul_self (a : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
lemma abs_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]
/-
**CFC.abs_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_of_nonpos (a : A) (ha : a <= 0
参数：a : A。
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
· 使用引理 `CFC.abs_neg`：abs_neg (a : A) : abs (-a) = abs a
· 使用引理 `CFC.abs_of_nonneg`：abs_of_nonneg (a : A) (ha : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma abs_of_nonpos (a : A) (ha : a ≤ 0 := by cfc_tac) : abs a = -a := by
  simpa using abs_of_nonneg (-a)
/-
**CFC.abs_eq_cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abs_eq_cfcₙ_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfcₙ (‖·‖) a := by
  conv_lhs =>
    rw [abs, ha.star_eq, sqrt_eq_real_sqrt .., ← cfcₙ_id' ℝ a, ← cfcₙ_mul .., ← cfcₙ_comp' ..]
  simp [← sq, Real.sqrt_sq_eq_abs]
/-
**CFC.posPart_add_negPart** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRing A] [inst_2 : 
TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4 : SMulCommClass ℝ A A
] [inst_5 : IsScalarTower ℝ A A]   [inst_6 : NonUnitalContinuousFunctionalCalcul
us ℝ A IsSelfAdjoint] [inst_7 : PartialOrder A]   [inst_8 : StarOrderedRing A] [
inst_9 : NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A] (a : A),   a
utoParam (IsSelfAdjoint a) CFC.posPart_add_negPart._auto_1 → a⁺ + a⁻ = CFC.abs a
参数：a : A；IsSelfAdjoint a。
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
· 使用引理 `cfcₙ_add`：cfcₙ_add : cfcₙ (fun x => f x + g x) a = cfcₙ f a + cfcₙ g a
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
· 使用引理 `CFC.abs_eq_cfcₙ_norm`：abs_eq_cfcₙ_norm (a : A) (ha : IsSelfAdjoint a
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `posPart_add_negPart`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGr
oup α] [AddLeftMono α] [AddRightMono α] (a : α), a⁺ + a⁻ = |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
protected lemma posPart_add_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁺ + a⁻ = abs a := by
  rw [CFC.posPart_def, CFC.negPart_def, ← cfcₙ_add .., abs_eq_cfcₙ_norm a ha]
  exact cfcₙ_congr fun x hx ↦ posPart_add_negPart x
/-
**CFC.abs_sub_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_sub_self (a : A) (ha : IsSelfAdjoint a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CFC.posPart_add_negPart`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst
_1 : StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [i
nst_4 : SMulC…
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
-/
lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a - a = 2 • a⁻ := by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) - $(CFC.posPart_sub_negPart a)).symm
/-
**CFC.abs_add_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_add_self (a : A) (ha : IsSelfAdjoint a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `add_add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + c + (b - c) = a + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CFC.posPart_add_negPart`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst
_1 : StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [i
nst_4 : SMulC…
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
-/
lemma abs_add_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a + a = 2 • a⁺ := by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) + $(CFC.posPart_sub_negPart a)).symm

@[simp, grind =]
/-
**CFC.cfcAbs_cfcAbs** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：cfcAbs_cfcAbs (a : A) : abs (abs a) = abs a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.abs_of_nonneg`：abs_of_nonneg (a : A) (ha : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma cfcAbs_cfcAbs (a : A) : abs (abs a) = abs a := abs_of_nonneg ..

variable [StarModule ℝ A]

@[simp, grind =]
/-
**CFC.abs_smul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_smul_nonneg {R : Type*} [Semiring R] [SMulWithZero R Real>=0] [SMul R 
A] [IsScalarTower R Real>=0 A] (r : R) (a : A) : abs (r • a) = r • abs a
参数：r : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.eq_1`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRi
ng A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4 : SMu
lC…
· 使用引理 `CFC.sqrt_eq_iff`：sqrt_eq_iff (a b : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用定理 `instStarModuleNNRealOfReal`：∀ {E : Type u_1} [inst : AddCommMonoid E] [i
nst_1 : Star E] [inst_2 : _root_.Module ℝ E] [StarModule ℝ E],   StarModule NNRe
al E
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用引理 `CFC.abs_nonneg`：abs_nonneg (a : A) : 0 <= abs a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `CFC.abs_mul_abs`：abs_mul_abs (a : A) : abs a * abs a = star a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `instTrivialStarNNReal`：TrivialStar NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CFC.abs.congr_simp`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : 
StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4
 : SMulC…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
（共 31 条，此处仅展示前 30 条）
-/
lemma abs_smul_nonneg {R : Type*} [Semiring R] [SMulWithZero R ℝ≥0] [SMul R A]
    [IsScalarTower R ℝ≥0 A] (r : R) (a : A) :
    abs (r • a) = r • abs a := by
  suffices ∀ r : ℝ≥0, abs (r • a) = r • abs a by simpa using this (r • 1)
  intro r
  rw [abs, sqrt_eq_iff _ _ (star_mul_self_nonneg _) (smul_nonneg (by positivity) (abs_nonneg _))]
  simp [mul_smul_comm, smul_mul_assoc, abs_mul_abs]

end Real

section RCLike

variable {p : A → Prop} [RCLike 𝕜]
  [NonUnitalRing A] [TopologicalSpace A] [Module 𝕜 A]
  [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]

open ComplexOrder

/-
**CFC._root_.cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.cfcₙ_norm_sq_nonneg (f : 𝕜 → 𝕜) (a : A) : 0 ≤ cfcₙ (fun z ↦ star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ ↦ star_mul_self_nonneg _
/-
**CFC._root_.cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.cfcₙ_norm_nonneg (f : 𝕜 → 𝕜) (a : A) : 0 ≤ cfcₙ (‖f ·‖ : 𝕜 → 𝕜) a :=
  cfcₙ_nonneg fun _ _ ↦ by simp

variable [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [StarModule 𝕜 A] [StarModule ℝ A] [IsScalarTower ℝ 𝕜 A] in
@[simp]
/-
**CFC.abs_smul** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_smul (r : 𝕜) (a : A) : abs (r • a) = ‖r‖ • abs a
参数：r : 𝕜；a : A。
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
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `RCLike.real_smul_eq_coe_smul`：real_smul_eq_coe_smul [AddCommGroup E] [Mo
dule K E] [Module Real E] [IsScalarTower Real K E] (r : Real) (x : E) : r • x = 
(r : K) • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.conj_mul`：conj_mul (z : K) : conj z * z = ‖z‖ ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `CFC.abs.congr_simp`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : 
StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4
 : SMulC…
· 使用引理 `CFC.abs_smul_nonneg`：abs_smul_nonneg {R : Type*} [Semiring R] [SMulWithZ
ero R Real>=0] [SMul R A] [IsScalarTower R Real>=0 A] (r : R) (a : A) : abs (r •
 a) = r •…
-/
lemma abs_smul (r : 𝕜) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  trans abs (‖r‖ • a)
  · simp only [abs, mul_smul_comm, smul_mul_assoc, star_smul, ← smul_assoc,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [-algebraMap_smul, ← smul_mul_assoc, ← mul_comm (starRingEnd _ _), RCLike.conj_mul, sq]
  · lift ‖r‖ to ℝ≥0 using norm_nonneg _ with r
    simp [← NNReal.smul_def]

variable (𝕜) in
/-
**CFC.abs_eq_cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abs_eq_cfcₙ_coe_norm (a : A) (ha : p a := by cfc_tac) :
    abs a = cfcₙ (fun z : 𝕜 ↦ (‖z‖ : 𝕜)) a := by
  rw [abs, sqrt_eq_iff _ _ (hb := cfcₙ_norm_nonneg _ _), ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id' 𝕜 a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [RCLike.conj_mul, sq]
/-
**CFC._root_.cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.cfcₙ_comp_norm (f : 𝕜 → 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) := by
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [cfcₙ_comp' f (‖·‖) a, ← abs_eq_cfcₙ_coe_norm _ a]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0,
      cfcₙ_apply_of_not_map_zero _ (fun h ↦ (hf0 <| by simpa using h).elim)]
/-
**CFC.quasispectrum_abs** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：quasispectrum_abs (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.abs_eq_cfcₙ_coe_norm`：abs_eq_cfcₙ_coe_norm (a : A) (ha : p a
· 使用引理 `cfcₙ_map_quasispectrum`：cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' 
σₙ R a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasispectrum_abs (a : A) (ha : p a := by cfc_tac) :
    quasispectrum 𝕜 (abs a) = (fun z ↦ (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a ha, cfcₙ_map_quasispectrum ..]

end RCLike

end NonUnital

section Unital

section Real

variable [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [T2Space A]

/-
**CFC.abs_eq_cfc_norm** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_eq_cfc_norm (a : A) (ha : IsSelfAdjoint a
参数：a : A。
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
· 使用引理 `CFC.abs_eq_cfcₙ_norm`：abs_eq_cfcₙ_norm (a : A) (ha : IsSelfAdjoint a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_eq_cfc_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfc (‖·‖) a := by
  rw [abs_eq_cfcₙ_norm _, cfcₙ_eq_cfc]
/-
**CFC.abs_coe_unitary** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：abs_coe_unitary (U : unitary A) : abs (U : A) = 1
参数：U : unitary A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用引理 `CFC.sqrt_one`：sqrt_one : sqrt (1 : A) = 1
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_coe_unitary (U : unitary A) : abs (U : A) = 1 := by simp [abs]
/-
**CFC.abs_of_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarRing A] [inst_2 : Topologic
alSpace A] [inst_3 : Algebra ℝ A]   [inst_4 : ContinuousFunctionalCalculus ℝ A I
sSelfAdjoint] [inst_5 : PartialOrder A] [inst_6 : StarOrderedRing A]   [inst_7 :
 NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A] {U : A}, U ∈ unitary
 A → CFC.abs U = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `CFC.abs_coe_unitary`：abs_coe_unitary (U : unitary A) : abs (U : A) = 1
-/
@[simp] theorem abs_of_mem_unitary {U : A} (hU : U ∈ unitary A) : abs U = 1 :=
  abs_coe_unitary ⟨U, hU⟩
/-
**CFC.abs_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_one : abs (1 : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs_of_mem_unitary`：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarR
ing A] [inst_2 : TopologicalSpace A] [inst_3 : Algebra ℝ A]   [inst_4 : Continuo
usFunctional…
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_one : abs (1 : A) = 1 := by simp

variable [StarModule ℝ A]

@[simp]
/-
**CFC.abs_algebraMap_nnreal** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_algebraMap_nnreal (x : Real>=0) : abs (algebraMap Real>=0 A x) = algeb
raMap Real>=0 A x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.congr_simp`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : 
StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4
 : SMulC…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `CFC.abs_smul_nonneg`：abs_smul_nonneg {R : Type*} [Semiring R] [SMulWithZ
ero R Real>=0] [SMul R A] [IsScalarTower R Real>=0 A] (r : R) (a : A) : abs (r •
 a) = r •…
· 使用定理 `CFC.abs_of_mem_unitary`：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarR
ing A] [inst_2 : TopologicalSpace A] [inst_3 : Algebra ℝ A]   [inst_4 : Continuo
usFunctional…
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]
/-
**CFC.abs_natCast** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_natCast (n : Nat) : abs (n : A) = n
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.congr_simp`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : 
StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4
 : SMulC…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `CFC.abs_algebraMap_nnreal`：abs_algebraMap_nnreal (x : Real>=0) : abs (al
gebraMap Real>=0 A x) = algebraMap Real>=0 A x
-/
lemma abs_natCast (n : ℕ) : abs (n : A) = n := by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_nnreal (n : ℝ≥0)

@[simp]
/-
**CFC.abs_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_ofNat (n : Nat) [n.AtLeastTwo] : abs (ofNat(n) : A) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.abs_natCast`：abs_natCast (n : Nat) : abs (n : A) = n
-/
lemma abs_ofNat (n : ℕ) [n.AtLeastTwo] : abs (ofNat(n) : A) = ofNat(n) := by
  simpa using! abs_natCast n

@[simp]
/-
**CFC.abs_intCast** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_intCast (n : Int) : abs (n : A) = |n|
参数：n : Int。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.congr_simp`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : 
StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4
 : SMulC…
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `CFC.abs_natCast`：abs_natCast (n : Nat) : abs (n : A) = n
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用引理 `CFC.abs_neg`：abs_neg (a : A) : abs (-a) = abs a
-/
lemma abs_intCast (n : ℤ) : abs (n : A) = |n| := by
  cases n with
  | ofNat _ => simp
  | negSucc n =>
    rw [Int.cast_negSucc, abs_neg, abs_natCast, ← Int.cast_natCast]
    congr

end Real

section RCLike

variable {p : A → Prop} [RCLike 𝕜]
  [Ring A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [Algebra ℝ A] [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [StarModule 𝕜 A] [StarModule ℝ A] [IsScalarTower ℝ 𝕜 A] in
@[simp]
/-
**CFC.abs_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_algebraMap (c : 𝕜) : abs (algebraMap 𝕜 A c) = algebraMap Real A ‖c‖
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.congr_simp`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : 
StarRing A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4
 : SMulC…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `CFC.abs_smul`：abs_smul (r : 𝕜) (a : A) : abs (r • a) = ‖r‖ • abs a
· 使用定理 `CFC.abs_of_mem_unitary`：∀ {A : Type u_2} [inst : Ring A] [inst_1 : StarR
ing A] [inst_2 : TopologicalSpace A] [inst_3 : Algebra ℝ A]   [inst_4 : Continuo
usFunctional…
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_algebraMap (c : 𝕜) : abs (algebraMap 𝕜 A c) = algebraMap ℝ A ‖c‖ := by
  simp [Algebra.algebraMap_eq_smul_one]
/-
**CFC._root_.cfc_comp_norm** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.cfc_comp_norm (f : 𝕜 → 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : 𝕜)) '' spectrum 𝕜 a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a, cfcₙ_eq_cfc, ← cfc_comp' ..]
/-
**CFC.abs_sq** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_sq (a : A) : (abs a) ^ 2 = star a * a
参数：a : A。
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
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `CFC.abs_mul_abs`：abs_mul_abs (a : A) : abs a * abs a = star a * a
-/
lemma abs_sq (a : A) : (abs a) ^ 2 = star a * a := by
  rw [sq, abs_mul_abs]
/-
**CFC.spectrum_abs** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：spectrum_abs (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.abs_eq_cfcₙ_coe_norm`：abs_eq_cfcₙ_coe_norm (a : A) (ha : p a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
-/
lemma spectrum_abs (a : A) (ha : p a := by cfc_tac) :
    spectrum 𝕜 (abs a) = (fun z ↦ (‖z‖ : 𝕜)) '' spectrum 𝕜 a := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a, cfcₙ_eq_cfc, cfc_map_spectrum ..]

end RCLike

end Unital

section Isometric

variable [NonUnitalNormedRing A] [StarRing A] [ContinuousStar A]
  [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] [CompleteSpace A]

/-
**CFC.continuous_abs** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：∀ {A : Type u_2} [inst : NonUnitalNormedRing A] [inst_1 : StarRing A] [Con
tinuousStar A] [inst_3 : NormedSpace ℝ A]   [inst_4 : SMulCommClass ℝ A A] [inst
_5 : IsScalarTower ℝ A A]   [inst_6 : NonUnitalIsometricContinuousFunctionalCalc
ulus ℝ A IsSelfAdjoint] [inst_7 : PartialOrder A]   [inst_8 : StarOrderedRing A]
 [inst_9 : NonnegSpectrumClass ℝ A] [CompleteSpace A], Continuous CFC.abs
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用引理 `CFC.continuousOn_sqrt`：continuousOn_sqrt : ContinuousOn sqrt {a : A | 0 
<= a}
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.star`：Continuous.star (hf : Continuous f) : Continuous fun x 
=> star (f x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
protected lemma continuous_abs : Continuous (CFC.abs : A → A) :=
  continuousOn_sqrt.comp_continuous (by fun_prop) (by cfc_tac)

end Isometric

section CStar

/- This section requires `A` to be a `CStarRing` -/

variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
  [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

open CFC

@[simp, grind =]
/-
**CFC.abs_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.abs.eq_1`：∀ {A : Type u_2} [inst : NonUnitalRing A] [inst_1 : StarRi
ng A] [inst_2 : TopologicalSpace A]   [inst_3 : _root_.Module ℝ A] [inst_4 : SMu
lC…
· 使用引理 `CFC.sqrt_eq_zero_iff`：sqrt_eq_zero_iff (a : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CStarRing.star_mul_self_eq_zero_iff`：star_mul_self_eq_zero_iff (x : E) :
 x⋆ * x = 0 ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [CFC.abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[simp, grind =]
/-
**CFC.norm_abs** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：norm_abs {a : A} : ‖abs a‖ = ‖a‖
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
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用引理 `LE.le.star_eq`：LE.le.star_eq {x : R} (hx : 0 <= x) : star x = x
· 使用引理 `CFC.abs_nonneg`：abs_nonneg (a : A) : 0 <= abs a
· 使用引理 `CFC.abs_mul_abs`：abs_mul_abs (a : A) : abs a * abs a = star a * a
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, ← CStarRing.norm_star_mul_self,
    (abs_nonneg _).star_eq, CFC.abs_mul_abs, CStarRing.norm_star_mul_self]

end CStar

end CFC

