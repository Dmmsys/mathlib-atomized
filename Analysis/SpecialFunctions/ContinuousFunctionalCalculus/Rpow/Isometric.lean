/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Properties of `rpow` and `sqrt` over an algebra with an isometric CFC

This file collects results about `CFC.rpow`, `CFC.nnrpow` and `CFC.sqrt` that use facts that
rely on an isometric continuous functional calculus.

## Main theorems

* Various versions of `‖a ^ r‖ = ‖a‖ ^ r` and `‖CFC.sqrt a‖ = sqrt ‖a‖`.

## Tags

continuous functional calculus, rpow, sqrt
-/

public section

open scoped NNReal

namespace CFC

section nonunital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-
**CFC.nnnorm_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnnorm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha : 0 <= a
参数：a : A；hr : 0 < r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `MonotoneOn.nnnorm_cfcₙ`：MonotoneOn.nnnorm_cfcₙ (f : Real>=0 -> Real>=0) 
(a : A) (hf : MonotoneOn f (σₙ Real>=0 a)) (hf₂ : ContinuousOn f (σₙ Real>=0 a)
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用引理 `NNReal.monotone_nnrpow_const`：monotone_nnrpow_const (y : Real>=0) : Mono
tone (nnrpow · y)
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma nnnorm_nnrpow (a : A) {r : ℝ≥0} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ (r : ℝ) :=
  NNReal.monotone_nnrpow_const r |>.monotoneOn _ |>.nnnorm_cfcₙ _ _
/-
**CFC.norm_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：norm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha : 0 <= a
参数：a : A；hr : 0 < r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.nnnorm_nnrpow`：nnnorm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha 
: 0 <= a
-/
lemma norm_nnrpow (a : A) {r : ℝ≥0} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ (r : ℝ) :=
  congr(NNReal.toReal $(nnnorm_nnrpow a hr ha))
/-
**CFC.nnnorm_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnnorm_sqrt (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用定理 `NNReal.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 :
 Real))
· 使用引理 `CFC.nnnorm_nnrpow`：nnnorm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha 
: 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
-/
lemma nnnorm_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : ‖sqrt a‖₊ = NNReal.sqrt ‖a‖₊ := by
  rw [sqrt_eq_nnrpow, NNReal.sqrt_eq_rpow]
  exact nnnorm_nnrpow a (by simp) ha
/-
**CFC.norm_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：norm_sqrt (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用引理 `CFC.nnnorm_sqrt`：nnnorm_sqrt (a : A) (ha : 0 <= a
-/
lemma norm_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : ‖sqrt a‖ = √‖a‖ := by
  simpa using congr(NNReal.toReal $(nnnorm_sqrt a ha))

variable [ContinuousStar A] [CompleteSpace A]
/-
**CFC.continuousOn_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：continuousOn_sqrt : ContinuousOn sqrt {a : A | 0 <= a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet`：ContinuousOn.cfcₙ_nnreal_of_mem
_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0} (f : Real>=0 -
> Real>=0) {a : X -> A} {t : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `NNReal.continuous_sqrt`：continuous_sqrt : Continuous sqrt
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma continuousOn_sqrt : ContinuousOn sqrt {a : A | 0 ≤ a} :=
  continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem
/-
**CFC.continuousOn_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：continuousOn_nnrpow (r : Real>=0) : ContinuousOn (· ^ r) {a : A | 0 <= a}
参数：r : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CFC.nnrpow_zero`：nnrpow_zero {a : A} : a ^ (0 : Real>=0) = 0
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet`：ContinuousOn.cfcₙ_nnreal_of_mem
_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0} (f : Real>=0 -
> Real>=0) {a : X -> A} {t : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
lemma continuousOn_nnrpow (r : ℝ≥0) : ContinuousOn (· ^ r) {a : A | 0 ≤ a} := by
  obtain (rfl | hr) := eq_zero_or_pos r
  · simpa using continuousOn_const
  · exact continuousOn_id.cfcₙ_nnreal_of_mem_nhdsSet _ Filter.univ_mem

end nonunital

section unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-
**CFC.nnnorm_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnnorm_rpow (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= a
参数：a : A；hr : 0 < r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.nnrpow_eq_rpow`：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : 
a ^ x = a ^ (x : Real)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用引理 `CFC.nnnorm_nnrpow`：nnnorm_nnrpow (a : A) {r : Real>=0} (hr : 0 < r) (ha 
: 0 <= a
-/
lemma nnnorm_rpow (a : A) {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖₊ = ‖a‖₊ ^ r := by
  lift r to ℝ≥0 using hr.le
  rw [← nnrpow_eq_rpow, ← nnnorm_nnrpow a]
  all_goals simpa
/-
**CFC.norm_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：norm_rpow (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= a
参数：a : A；hr : 0 < r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.nnnorm_rpow`：nnnorm_rpow (a : A) {r : Real} (hr : 0 < r) (ha : 0 <= 
a
-/
lemma norm_rpow (a : A) {r : ℝ} (hr : 0 < r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a ^ r‖ = ‖a‖ ^ r :=
  congr(NNReal.toReal $(nnnorm_rpow a hr ha))
/-
**CFC.continuousOn_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：continuousOn_rpow [ContinuousStar A] [CompleteSpace A] (r : Real) : Contin
uousOn (· ^ r) {a : A | IsStrictlyPositive a}
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`：ContinuousOn.cfc_nnreal_of_mem_n
hdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0} (f : Real>=0 -> 
Real>=0) {a : X -> A} {t : S…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhdsSet_iUnion`：nhdsSet_iUnion {ι : Sort*} (s : ι -> Set X) : 𝓝ˢ (⋃ i, s
 i) = ⨆ i, 𝓝ˢ (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma continuousOn_rpow [ContinuousStar A] [CompleteSpace A] (r : ℝ) :
    ContinuousOn (· ^ r) {a : A | IsStrictlyPositive a} := by
  refine continuousOn_id.cfc_nnreal_of_mem_nhdsSet _ (s := {0}ᶜ) ?_
  simp_rw [nhdsSet_iUnion, Filter.mem_iSup, isOpen_compl_singleton.mem_nhdsSet]
  exact fun a ha ↦ by simpa using spectrum.zero_notMem _ ha.isUnit

end unital

section cstar

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-
**CFC.norm_star_mul_mul_self_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：norm_star_mul_mul_self_of_nonneg {a : A} (b : A) (ha : 0 <= a
参数：b : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用引理 `LE.le.star_eq`：LE.le.star_eq {x : R} (hx : 0 <= x) : star x = x
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma norm_star_mul_mul_self_of_nonneg {a : A} (b : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖star b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_mul, (CFC.sqrt_nonneg a).star_eq,
    ← mul_assoc _ (CFC.sqrt a), mul_assoc _ _ (CFC.sqrt a), CFC.sqrt_mul_sqrt_self a]
/-
**CFC.IsSelfAdjoint.norm_mul_mul_self_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `CFC.I
sSelfAdjoint`。
形式化陈述：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : NonUnitalNormedRing A] 
[inst_2 : StarRing A] [CStarRing A]   [inst_4 : NormedSpace ℝ A] [inst_5 : SMulC
ommClass ℝ A A] [inst_6 : IsScalarTower ℝ A A] [inst_7 : StarOrderedRing A]   [i
nst_8 : NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [inst_9 : Nonne
gSpectrumClass ℝ A] {a : A} (b : A),   autoParam (IsSelfAdjoint b) CFC.IsSelfAdj
oint.norm_mul_mul_self_of_nonneg._auto_1 →     autoParam (0 ≤ a) CFC.IsSelfAdjoi
nt.norm_mul_mul_self_of_nonneg._auto_3 → ‖b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2
参数：b : A；IsSelfAdjoint b；0 ≤ a。
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
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用引理 `CFC.norm_star_mul_mul_self_of_nonneg`：norm_star_mul_mul_self_of_nonneg {
a : A} (b : A) (ha : 0 <= a
-/
lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg {a : A} (b : A)
    (hb : IsSelfAdjoint b := by cfc_tac) (ha : 0 ≤ a := by cfc_tac) :
    ‖b * a * b‖ = ‖CFC.sqrt a * b‖ ^ 2 := by
  simpa [hb.star_eq] using norm_star_mul_mul_self_of_nonneg b ha
/-
**CFC.norm_mul_mul_star_self_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：norm_mul_mul_star_self_of_nonneg {a : A} (b : A) (ha : 0 <= a
参数：b : A。
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
· 使用引理 `LE.le.star_eq`：LE.le.star_eq {x : R} (hx : 0 <= x) : star x = x
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用引理 `CFC.norm_star_mul_mul_self_of_nonneg`：norm_star_mul_mul_self_of_nonneg {
a : A} (b : A) (ha : 0 <= a
-/
lemma norm_mul_mul_star_self_of_nonneg {a : A} (b : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖b * a * star b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  conv_rhs => rw [← (CFC.sqrt_nonneg a).star_eq, ← star_star b, ← star_mul, norm_star,
    ← norm_star_mul_mul_self_of_nonneg _ ha, star_star]
/-
**CFC.IsSelfAdjoint.norm_mul_mul_self_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `CFC.
IsSelfAdjoint`。
形式化陈述：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : NonUnitalNormedRing A] 
[inst_2 : StarRing A] [CStarRing A]   [inst_4 : NormedSpace ℝ A] [inst_5 : SMulC
ommClass ℝ A A] [inst_6 : IsScalarTower ℝ A A] [inst_7 : StarOrderedRing A]   [i
nst_8 : NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [inst_9 : Nonne
gSpectrumClass ℝ A] {a : A} (b : A),   autoParam (IsSelfAdjoint b) CFC.IsSelfAdj
oint.norm_mul_mul_self_of_nonneg'._auto_1 →     autoParam (0 ≤ a) CFC.IsSelfAdjo
int.norm_mul_mul_self_of_nonneg'._auto_3 → ‖b * a * b‖ = ‖b * CFC.sqrt a‖ ^ 2
参数：b : A；IsSelfAdjoint b；0 ≤ a。
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
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用引理 `CFC.norm_mul_mul_star_self_of_nonneg`：norm_mul_mul_star_self_of_nonneg {
a : A} (b : A) (ha : 0 <= a
-/
lemma IsSelfAdjoint.norm_mul_mul_self_of_nonneg' {a : A} (b : A)
    (hb : IsSelfAdjoint b := by cfc_tac) (ha : 0 ≤ a := by cfc_tac) :
    ‖b * a * b‖ = ‖b * CFC.sqrt a‖ ^ 2 := by
  simpa [hb.star_eq] using norm_mul_mul_star_self_of_nonneg b ha

end cstar

end CFC

