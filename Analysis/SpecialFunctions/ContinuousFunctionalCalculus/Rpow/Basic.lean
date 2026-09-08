/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Order.Star.Prod
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc. The
square root is also defined via the non-unital CFC.

## Main declarations

+ `CFC.nnrpow`: the `ℝ≥0` power function based on the non-unital CFC, i.e. `cfcₙ NNReal.rpow`
  composed with `(↑) : ℝ≥0 → ℝ`.
+ `CFC.sqrt`: the square root function based on the non-unital CFC, i.e. `cfcₙ NNReal.sqrt`
+ `CFC.rpow`: the real power function based on the unital CFC, i.e. `cfc NNReal.rpow`

## Implementation notes

We define two separate versions `CFC.nnrpow` and `CFC.rpow` due to what happens at 0. Since
`NNReal.rpow 0 0 = 1`, this means that this function does not map zero to zero when the exponent
is zero, and hence `CFC.nnrpow a 0 = 0` whereas `CFC.rpow a 0 = 1`. Note that the non-unital version
only makes sense for nonnegative exponents, and hence we define it such that the exponent is in
`ℝ≥0`.

## Notation

+ We define a `Pow A ℝ` instance for `CFC.rpow`, i.e `a ^ y` with `A` an operator and `y : ℝ` works
  as expected. Likewise, we define a `Pow A ℝ≥0` instance for `CFC.nnrpow`. Note that these are
  low-priority instances, in order to avoid overriding instances such as `Pow ℝ ℝ`,
  `Pow (A × B) ℝ` or `Pow (∀ i, A i) ℝ`.

## TODO

+ Relate these to the log and exp functions
+ Lemmas about how these functions interact with commuting `a` and `b`.
+ Prove the order properties (operator monotonicity and concavity/convexity)
-/

@[expose] public section

open scoped NNReal

namespace NNReal

/-- Taking a nonnegative power of a nonnegative number. This is defined as a standalone definition
in order to speed up automation such as `cfc_cont_tac`. -/
/-
**NNReal.nnrpow** 是 Mathlib 中的一个缩写定义，位于命名空间 `NNReal`。
形式化陈述：nnrpow (a : Real>=0) (b : Real>=0) : Real>=0
参数：a : Real>=0；b : Real>=0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking a nonnegative power of a nonnegative number. This is defined as a standal
one definition
in order to speed up automation such as `cfc_cont_tac`.
-/
noncomputable abbrev nnrpow (a : ℝ≥0) (b : ℝ≥0) : ℝ≥0 := a ^ (b : ℝ)
/-
**NNReal.nnrpow_def** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a b : NNReal), a.nnrpow b = a ^ ↑b
参数：a b : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnrpow_def (a b : ℝ≥0) : nnrpow a b = a ^ (b : ℝ) := rfl

@[fun_prop]
/-
**NNReal.continuous_nnrpow_const** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：continuous_nnrpow_const (y : Real>=0) : Continuous (nnrpow · y)
参数：y : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.continuous_rpow_const`：continuous_rpow_const {y : Real} (h : 0 <=
 y) : Continuous fun x : Real>=0 => x ^ y
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
-/
lemma continuous_nnrpow_const (y : ℝ≥0) : Continuous (nnrpow · y) :=
  continuous_rpow_const zero_le_coe

/- This is a "redeclaration" of the attribute to speed up the proofs in this file. -/
attribute [fun_prop] continuousOn_rpow_const

/-
**NNReal.monotone_nnrpow_const** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：monotone_nnrpow_const (y : Real>=0) : Monotone (nnrpow · y)
参数：y : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.monotone_rpow_of_nonneg`：monotone_rpow_of_nonneg {z : Real} (h : 
0 <= z) : Monotone fun x : Real>=0 => x ^ z
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)

--- 原说明 ---
This is a "redeclaration" of the attribute to speed up the proofs in this file.
-/
lemma monotone_nnrpow_const (y : ℝ≥0) : Monotone (nnrpow · y) :=
  monotone_rpow_of_nonneg zero_le_coe

end NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]


/- ## `nnrpow` -/

/-- Real powers of operators, based on the non-unital continuous functional calculus. -/
/-
**CFC.nnrpow** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
形式化陈述：nnrpow (a : A) (y : Real>=0) : A
参数：a : A；y : Real>=0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal

--- 原说明 ---
Real powers of operators, based on the non-unital continuous functional calculus
.
-/
noncomputable def nnrpow (a : A) (y : ℝ≥0) : A := cfcₙ (NNReal.nnrpow · y) a

/-- Enable `a ^ y` notation for `CFC.nnrpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available. -/
/-
**CFC.** 是 Mathlib 中的一个实例，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enable `a ^ y` notation for `CFC.nnrpow`. This is a low-priority instance to mak
e sure it does
not take priority over other instances when they are available.
-/
noncomputable instance (priority := 100) : Pow A ℝ≥0 where
  pow a y := nnrpow a y

@[simp]
/-
**CFC.nnrpow_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_eq_pow {a : A} {y : Real>=0} : nnrpow a y = a ^ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma nnrpow_eq_pow {a : A} {y : ℝ≥0} : nnrpow a y = a ^ y := rfl

@[simp]
/-
**CFC.nnrpow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_nonneg {a : A} {x : Real>=0} : 0 <= a ^ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_predicate`：cfcₙ_predicate (f : R -> R) (a : A) : p (cfcₙ f a)
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
-/
lemma nnrpow_nonneg {a : A} {x : ℝ≥0} : 0 ≤ a ^ x := cfcₙ_predicate _ a

grind_pattern nnrpow_nonneg => NonnegSpectrumClass ℝ A, a ^ x
/-
**CFC.nnrpow_def** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_def {a : A} {y : Real>=0} : a ^ y = cfcₙ (NNReal.nnrpow · y) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma nnrpow_def {a : A} {y : ℝ≥0} : a ^ y = cfcₙ (NNReal.nnrpow · y) a := rfl
/-
**CFC.nnrpow_eq_cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnrpow_eq_cfcₙ_real [T2Space A] [IsSemitopologicalRing A] (a : A)
    (y : ℝ≥0) (ha : 0 ≤ a := by cfc_tac) : a ^ y = cfcₙ (fun x : ℝ => x ^ (y : ℝ)) a := by
  rw [nnrpow_def, cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr ?_
  intro x hx
  have : 0 ≤ x := by grind
  simp [this]
/-
**CFC.nnrpow_add** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_add {a : A} {x y : Real>=0} (hx : 0 < x) (hy : 0 < y) : a ^ (x + y)
 = a ^ x * a ^ y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_add'`：rpow_add' (h : y + z != 0) (x : Real>=0) : x ^ (y + z)
 = x ^ y * x ^ z
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma nnrpow_add {a : A} {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
  exact mod_cast z.rpow_add' <| ne_of_gt (add_pos hx hy)

@[simp]
/-
**CFC.nnrpow_zero** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_zero {a : A} : a ^ (0 : Real>=0) = 0
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
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `cfcₙ.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p
 : p = p_1) [inst : CommSemiring R] [inst_1 : Nontrivial R]   [inst_2 : StarRing
 R] […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用引理 `cfcₙ_apply_of_not_map_zero`：cfcₙ_apply_of_not_map_zero {f : R -> R} (a :
 A) (hf : ¬ f 0 = 0) : cfcₙ f a = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnrpow_zero {a : A} : a ^ (0 : ℝ≥0) = 0 := by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]
/-
**CFC.nnrpow_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_one (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcₙ.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p
 : p = p_1) [inst : CommSemiring R] [inst_1 : Nontrivial R]   [inst_2 : StarRing
 R] […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
-/
lemma nnrpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ≥0) = a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : ℝ≥0 → ℝ≥0) a = a
  rw [cfcₙ_id ℝ≥0 a]
/-
**CFC.nnrpow_one_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_one_eqOn : (Set.Ici (0 : A)).EqOn (fun a : A => a ^ (1 : Real>=0)) 
id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.nnrpow_one`：nnrpow_one (a : A) (ha : 0 <= a
-/
lemma nnrpow_one_eqOn : (Set.Ici (0 : A)).EqOn (fun a : A => a ^ (1 : ℝ≥0)) id :=
  fun _ ha => CFC.nnrpow_one _ ha
/-
**CFC.nnrpow_two** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_two (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcₙ.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p
 : p = p_1) [inst : CommSemiring R] [inst_1 : Nontrivial R]   [inst_2 : StarRing
 R] […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `NNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0) (n : Nat) [n.AtLeastTwo] : x
 ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n : Nat)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
-/
lemma nnrpow_two (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (2 : ℝ≥0) = a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : ℝ≥0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a, cfcₙ_id ℝ≥0 a]
/-
**CFC.nnrpow_three** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_three (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfcₙ.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p
 : p = p_1) [inst : CommSemiring R] [inst_1 : Nontrivial R]   [inst_2 : StarRing
 R] […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `NNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0) (n : Nat) [n.AtLeastTwo] : x
 ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n : Nat)
· 使用引理 `pow_three`：pow_three (a : M) : a ^ 3 = a * (a * a)
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
-/
lemma nnrpow_three (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (3 : ℝ≥0) = a * a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : ℝ≥0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a, cfcₙ_mul id _ a, ← mul_assoc, cfcₙ_id ℝ≥0 a]

@[simp]
/-
**CFC.zero_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：zero_nnrpow {x : Real>=0} : (0 : A) ^ x = 0
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
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_nnrpow {x : ℝ≥0} : (0 : A) ^ x = 0 := by simp [nnrpow_def]

section Unique

variable [IsSemitopologicalRing A] [T2Space A]

@[simp]
/-
**CFC.nnrpow_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y = a ^ (x * y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CFC.nnrpow_zero`：nnrpow_zero {a : A} : a ^ (0 : Real>=0) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.zero_nnrpow`：zero_nnrpow {x : Real>=0} : (0 : A) ^ x = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `cfcₙ_comp`：cfcₙ_comp (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' σ
ₙ R a)
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 38 条，此处仅展示前 30 条）
-/
lemma nnrpow_nnrpow {a : A} {x y : ℝ≥0} : (a ^ x) ^ y = a ^ (x * y) := by
  by_cases ha : 0 ≤ a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply_of_not_predicate a ha]
/-
**CFC.nnrpow_nnrpow_inv** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_nnrpow_inv (a : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a
参数：a : A；hx : x != 0。
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
· 使用引理 `CFC.nnrpow_nnrpow`：nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y =
 a ^ (x * y)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用引理 `CFC.nnrpow_one`：nnrpow_one (a : A) (ha : 0 <= a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnrpow_nnrpow_inv (a : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    (a ^ x) ^ x⁻¹ = a := by
  simp [mul_inv_cancel₀ hx, nnrpow_one _ ha]
/-
**CFC.nnrpow_inv_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_inv_nnrpow (a : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a
参数：a : A；hx : x != 0。
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
· 使用引理 `CFC.nnrpow_nnrpow`：nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y =
 a ^ (x * y)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `CFC.nnrpow_one`：nnrpow_one (a : A) (ha : 0 <= a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnrpow_inv_nnrpow (a : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    (a ^ x⁻¹) ^ x = a := by
  simp [inv_mul_cancel₀ hx, nnrpow_one _ ha]
/-
**CFC.nnrpow_inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_inv_eq (a b : A) {x : Real>=0} (hx : x != 0) (ha : 0 <= a
参数：a b : A；hx : x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.nnrpow_inv_nnrpow`：nnrpow_inv_nnrpow (a : A) {x : Real>=0} (hx : x !
= 0) (ha : 0 <= a
· 使用引理 `CFC.nnrpow_nnrpow_inv`：nnrpow_nnrpow_inv (a : A) {x : Real>=0} (hx : x !
= 0) (ha : 0 <= a
-/
lemma nnrpow_inv_eq (a b : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac)
    (hb : 0 ≤ b := by cfc_tac) : a ^ x⁻¹ = b ↔ b ^ x = a :=
  ⟨fun h ↦ nnrpow_inv_nnrpow a hx ▸ congr($(h) ^ x).symm,
    fun h ↦ nnrpow_nnrpow_inv b hx ▸ congr($(h) ^ x⁻¹).symm⟩

section prod

variable {B : Type*} [PartialOrder B] [NonUnitalRing B] [TopologicalSpace B] [StarRing B]
  [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]
  [NonUnitalContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint]
  [IsSemitopologicalRing B] [T2Space B]
  [NonnegSpectrumClass ℝ B] [NonnegSpectrumClass ℝ (A × B)]
  [StarOrderedRing B]

/- Note that there is higher-priority instance of `Pow (A × B) ℝ≥0` coming from the `Pow` instance
for products, hence the direct use of `nnrpow` here. -/
/-
**CFC.nnrpow_map_prod** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_map_prod {a : A} {b : B} {x : Real>=0} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `cfcₙ_map_prod`：cfcₙ_map_prod (f : R -> R) (a : A) (b : B) (hf : Continuo
usOn f (quasispectrum R a union quasispectrum R b)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `NNReal.continuous_nnrpow_const`：continuous_nnrpow_const (y : Real>=0) : 
Continuous (nnrpow · y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.le_def`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE 
β] {x y : α × β}, x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2

--- 原说明 ---
Note that there is higher-priority instance of `Pow (A × B) ℝ≥0` coming from the
 `Pow` instance
for products, hence the direct use of `nnrpow` here.
-/
lemma nnrpow_map_prod {a : A} {b : B} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    nnrpow (a, b) x = (a ^ x, b ^ x) := by
  simp only [nnrpow_def]
  unfold nnrpow
  refine cfcₙ_map_prod (S := ℝ) _ a b (by fun_prop) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha, hb]
/-
**CFC.nnrpow_eq_nnrpow_prod** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_eq_nnrpow_prod {a : A} {b : B} {x : Real>=0} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.nnrpow_map_prod`：nnrpow_map_prod {a : A} {b : B} {x : Real>=0} (ha :
 0 <= a
-/
lemma nnrpow_eq_nnrpow_prod {a : A} {b : B} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    nnrpow (a, b) x = (a, b) ^ x := nnrpow_map_prod

end prod

section pi

variable {ι : Type*} {C : ι → Type*} [∀ i, PartialOrder (C i)] [∀ i, NonUnitalRing (C i)]
  [∀ i, TopologicalSpace (C i)] [∀ i, StarRing (C i)]
  [∀ i, StarOrderedRing (C i)] [StarOrderedRing (∀ i, C i)]
  [∀ i, Module ℝ (C i)] [∀ i, SMulCommClass ℝ (C i) (C i)] [∀ i, IsScalarTower ℝ (C i) (C i)]
  [∀ i, NonUnitalContinuousFunctionalCalculus ℝ (C i) IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (∀ i, C i) IsSelfAdjoint]
  [∀ i, IsSemitopologicalRing (C i)] [∀ i, T2Space (C i)]
  [NonnegSpectrumClass ℝ (∀ i, C i)] [∀ i, NonnegSpectrumClass ℝ (C i)]

/- Note that there is higher-priority instance of `Pow (∀ i, C i) ℝ≥0` coming from the `Pow`
/-
**CFC.for** 是 Mathlib 中的一个实例，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance for pi types, hence the direct use of `nnrpow` here. -/
/-
**CFC.nnrpow_map_pi** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_map_pi {c : forall i, C i} {x : Real>=0} (hc : forall i, 0 <= c i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `cfcₙ_map_pi`：cfcₙ_map_pi (f : R -> R) (a : forall i, A i) (hf : Continuo
usOn f (⋃ i, quasispectrum R (a i))
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
Note that there is higher-priority instance of `Pow (∀ i, C i) ℝ≥0` coming from 
the `Pow`
instance for pi types, hence the direct use of `nnrpow` here.
-/
lemma nnrpow_map_pi {c : ∀ i, C i} {x : ℝ≥0} (hc : ∀ i, 0 ≤ c i := by cfc_tac) :
    nnrpow c x = fun i => (c i) ^ x := by
  simp only [nnrpow_def]
  unfold nnrpow
  exact cfcₙ_map_pi (S := ℝ) _ c
/-
**CFC.nnrpow_eq_nnrpow_pi** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_eq_nnrpow_pi {c : forall i, C i} {x : Real>=0} (hc : forall i, 0 <=
 c i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.nnrpow_map_pi`：nnrpow_map_pi {c : forall i, C i} {x : Real>=0} (hc :
 forall i, 0 <= c i
-/
lemma nnrpow_eq_nnrpow_pi {c : ∀ i, C i} {x : ℝ≥0} (hc : ∀ i, 0 ≤ c i := by cfc_tac) :
    nnrpow c x = c ^ x := nnrpow_map_pi

end pi

end Unique

/- ## `sqrt` -/

section sqrt

/-- Square roots of operators, based on the non-unital continuous functional calculus. -/
/-
**CFC.sqrt** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
形式化陈述：sqrt (a : A) : A
参数：a : A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal

--- 原说明 ---
Square roots of operators, based on the non-unital continuous functional calculu
s.
-/
noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

@[simp]
/-
**CFC.sqrt_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_nonneg (a : A) : 0 <= sqrt a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_predicate`：cfcₙ_predicate (f : R -> R) (a : A) : p (cfcₙ f a)
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
-/
lemma sqrt_nonneg (a : A) : 0 ≤ sqrt a := cfcₙ_predicate _ a

grind_pattern sqrt_nonneg => NonnegSpectrumClass ℝ A, sqrt a
/-
**CFC.sqrt_eq_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>=0)
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
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 :
 Real))
-/
lemma sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : ℝ≥0) := by
  simp only [sqrt]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _
/-
**CFC.sqrt_of_not_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_of_not_nonneg {a : A} (ha : ¬0 <= a) : sqrt a = 0
参数：ha : ¬0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
-/
lemma sqrt_of_not_nonneg {a : A} (ha : ¬0 ≤ a) : sqrt a = 0 :=
  cfcₙ_apply_of_not_predicate a ha

@[simp]
/-
**CFC.sqrt_zero** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_zero : sqrt (0 : A) = 0
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
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

variable [IsSemitopologicalRing A] [T2Space A]

@[simp]
/-
**CFC.nnrpow_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_sqrt {a : A} {x : Real>=0} : (sqrt a) ^ x = a ^ (x / 2)
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
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用引理 `CFC.nnrpow_nnrpow`：nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y =
 a ^ (x * y)
· 使用定理 `one_div_mul_eq_div`：one_div_mul_eq_div : 1 / a * b = b / a
-/
lemma nnrpow_sqrt {a : A} {x : ℝ≥0} : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_nnrpow, nnrpow_nnrpow, one_div_mul_eq_div 2 x]
/-
**CFC.nnrpow_sqrt_two** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_sqrt_two (a : A) (ha : 0 <= a
参数：a : A。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CFC.nnrpow_sqrt`：nnrpow_sqrt {a : A} {x : Real>=0} : (sqrt a) ^ x = a ^ 
(x / 2)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `CFC.nnrpow_one`：nnrpow_one (a : A) (ha : 0 <= a
-/
lemma nnrpow_sqrt_two (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ (2 : ℝ≥0) = a := by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one a]
/-
**CFC.sqrt_mul_sqrt_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
参数：a : A。
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
· 使用引理 `CFC.nnrpow_two`：nnrpow_two (a : A) (ha : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CFC.nnrpow_sqrt_two`：nnrpow_sqrt_two (a : A) (ha : 0 <= a
-/
lemma sqrt_mul_sqrt_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
  rw [← nnrpow_two _, nnrpow_sqrt_two _]

@[simp]
/-
**CFC.sqrt_nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_nnrpow {a : A} {x : Real>=0} : sqrt (a ^ x) = a ^ (x / 2)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `CFC.nnrpow_nnrpow`：nnrpow_nnrpow {a : A} {x y : Real>=0} : (a ^ x) ^ y =
 a ^ (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sqrt_nnrpow {a : A} {x : ℝ≥0} : sqrt (a ^ x) = a ^ (x / 2) := by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]
/-
**CFC.sqrt_nnrpow_two** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_nnrpow_two (a : A) (ha : 0 <= a
参数：a : A。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CFC.sqrt_nnrpow`：sqrt_nnrpow {a : A} {x : Real>=0} : sqrt (a ^ x) = a ^ 
(x / 2)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `CFC.nnrpow_one`：nnrpow_one (a : A) (ha : 0 <= a
-/
lemma sqrt_nnrpow_two (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ (2 : ℝ≥0)) = a := by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one _]
/-
**CFC.sqrt_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_mul_self (a : A) (ha : 0 <= a
参数：a : A。
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
· 使用引理 `CFC.nnrpow_two`：nnrpow_two (a : A) (ha : 0 <= a
· 使用引理 `CFC.sqrt_nnrpow_two`：sqrt_nnrpow_two (a : A) (ha : 0 <= a
-/
lemma sqrt_mul_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a * a) = a := by
  rw [← nnrpow_two _, sqrt_nnrpow_two _]
/-
**CFC.mul_self_eq** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：mul_self_eq {a b : A} (h : sqrt a = b) (ha : 0 <= a
参数：h : sqrt a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
-/
lemma mul_self_eq {a b : A} (h : sqrt a = b) (ha : 0 ≤ a := by cfc_tac) :
    b * b = a :=
  h ▸ sqrt_mul_sqrt_self _ ha
/-
**CFC.sqrt_unique** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_unique {a b : A} (h : b * b = a) (hb : 0 <= b
参数：h : b * b = a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.sqrt_mul_self`：sqrt_mul_self (a : A) (ha : 0 <= a
-/
lemma sqrt_unique {a b : A} (h : b * b = a) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b :=
  h ▸ sqrt_mul_self b
/-
**CFC.sqrt_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_iff (a b : A) (ha : 0 <= a
参数：a b : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.mul_self_eq`：mul_self_eq {a b : A} (h : sqrt a = b) (ha : 0 <= a
· 使用引理 `CFC.sqrt_unique`：sqrt_unique {a b : A} (h : b * b = a) (hb : 0 <= b
-/
lemma sqrt_eq_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b ↔ b * b = a :=
  ⟨(mul_self_eq ·), (sqrt_unique ·)⟩
/-
**CFC.sqrt_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_zero_iff (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_iff`：sqrt_eq_iff (a b : A) (ha : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sqrt_eq_zero_iff (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a = 0 ↔ a = 0 := by
  rw [sqrt_eq_iff a _, mul_zero, eq_comm]
/-
**CFC.mul_self_eq_mul_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：mul_self_eq_mul_self_iff (a b : A) (ha : 0 <= a
参数：a b : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.sqrt_unique`：sqrt_unique {a b : A} (h : b * b = a) (hb : 0 <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.sqrt_mul_self`：sqrt_mul_self (a : A) (ha : 0 <= a
-/
lemma mul_self_eq_mul_self_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    a * a = b * b ↔ a = b :=
  ⟨fun h => sqrt_mul_self a ▸ sqrt_unique h.symm, fun h => h ▸ rfl⟩

/-- Note that the hypothesis `0 ≤ a` is necessary because the continuous functional calculi over
`ℝ≥0` (for the left-hand side) and `ℝ` (for the right-hand side) use different predicates (i.e.,
`(0 ≤ ·)` versus `IsSelfAdjoint`). Consequently, if `a` is selfadjoint but not nonnegative, then
the left-hand side is zero, but the right-hand side is (provably equal to) `CFC.sqrt a⁺`. -/
/-
**CFC.sqrt_eq_real_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_real_sqrt (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`：∀ {𝕜 : Type u_3} {A 
: Type u_4} {inst : CommSemiring 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NonUnita
lRing A}   {inst_3 : PartialOrder A} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.sqrt_eq_iff`：sqrt_eq_iff (a b : A) (ha : 0 <= a
· 使用引理 `cfcₙ_nonneg`：cfcₙ_nonneg {f : R -> R} {a : A} (h : forall x in σₙ R a, 0
 <= f x) : 0 <= cfcₙ f a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用引理 `cfcₙ_id'`：cfcₙ_id' : cfcₙ (fun x : R => x) a = a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用定理 `ContinuousOn.sqrt`：ContinuousOn.sqrt (h : ContinuousOn f s) : Continuous
On (fun x => √(f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note that the hypothesis `0 ≤ a` is necessary because the continuous functional 
calculi over
`ℝ≥0` (for the left-hand side) and `ℝ` (for the right-hand side) use different p
redicates (i.e.,
`(0 ≤ ·)` versus `IsSelfAdjoint`). Consequently, if `a` is selfadjoint but not n
onnegative, then
the left-hand side is zero, but the right-hand side is (provably equal to) `CFC.
sqrt a⁺`.
-/
lemma sqrt_eq_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  suffices cfcₙ (fun x : ℝ ↦ √x * √x) a = cfcₙ (fun x : ℝ ↦ x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ ↦ Real.sqrt_nonneg x))] at this
  exact cfcₙ_congr fun x hx ↦ Real.mul_self_sqrt <| quasispectrum_nonneg_of_nonneg a ha x hx

section prod

variable {B : Type*} [PartialOrder B] [NonUnitalRing B] [TopologicalSpace B] [StarRing B]
  [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] [StarOrderedRing B]
  [NonUnitalContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint]
  [IsSemitopologicalRing B] [T2Space B]
  [NonnegSpectrumClass ℝ B] [NonnegSpectrumClass ℝ (A × B)]

/-
**CFC.sqrt_map_prod** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_map_prod {a : A} {b : B} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用引理 `CFC.nnrpow_map_prod`：nnrpow_map_prod {a : A} {b : B} {x : Real>=0} (ha :
 0 <= a
-/
lemma sqrt_map_prod {a : A} {b : B} (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    sqrt (a, b) = (sqrt a, sqrt b) := by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_prod

end prod

section pi

variable {ι : Type*} {C : ι → Type*} [∀ i, PartialOrder (C i)] [∀ i, NonUnitalRing (C i)]
  [∀ i, TopologicalSpace (C i)] [∀ i, StarRing (C i)]
  [∀ i, StarOrderedRing (C i)] [StarOrderedRing (∀ i, C i)]
  [∀ i, Module ℝ (C i)] [∀ i, SMulCommClass ℝ (C i) (C i)] [∀ i, IsScalarTower ℝ (C i) (C i)]
  [∀ i, NonUnitalContinuousFunctionalCalculus ℝ (C i) IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (∀ i, C i) IsSelfAdjoint]
  [∀ i, IsSemitopologicalRing (C i)] [∀ i, T2Space (C i)]
  [NonnegSpectrumClass ℝ (∀ i, C i)] [∀ i, NonnegSpectrumClass ℝ (C i)]

/-
**CFC.sqrt_map_pi** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_map_pi {c : forall i, C i} (hc : forall i, 0 <= c i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CFC.nnrpow_map_pi`：nnrpow_map_pi {c : forall i, C i} {x : Real>=0} (hc :
 forall i, 0 <= c i
-/
lemma sqrt_map_pi {c : ∀ i, C i} (hc : ∀ i, 0 ≤ c i := by cfc_tac) :
    sqrt c = fun i => sqrt (c i) := by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_pi

end pi

/-- For an element `a` in a C⋆-algebra, TFAE:
1. `0 ≤ a`
2. `a = sqrt a * sqrt a`
3. `a = b * b` for some nonnegative `b`
4. `a = b * b` for some self-adjoint `b`
5. `a = star b * b` for some `b`
6. `a = b * star b` for some `b`
7. `a = a⁺`
8. `a` is self-adjoint and `a⁻ = 0`
9. `a` is self-adjoint and has nonnegative spectrum -/
/-
**CFC._root_.CStarAlgebra.nonneg_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an element `a` in a C⋆-algebra, TFAE:
1. `0 ≤ a`
2. `a = sqrt a * sqrt a`
3. `a = b * b` for some nonnegative `b`
4. `a = b * b` for some self-adjoint `b`
5. `a = star b * b` for some `b`
6. `a = b * star b` for some `b`
7. `a = a⁺`
8. `a` is self-adjoint and `a⁻ = 0`
9. `a` is self-adjoint and has nonnegative spectrum
-/
theorem _root_.CStarAlgebra.nonneg_TFAE {a : A} :
    [ 0 ≤ a,
      a = sqrt a * sqrt a,
      ∃ b : A, 0 ≤ b ∧ a = b * b,
      ∃ b : A, IsSelfAdjoint b ∧ a = b * b,
      ∃ b : A, a = star b * b,
      ∃ b : A, a = b * star b,
      a = a⁺,
      IsSelfAdjoint a ∧ a⁻ = 0,
      IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal ].TFAE := by
  tfae_have 1 ↔ 9 := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  tfae_have 1 ↔ 7 := eq_comm.eq ▸ (CFC.posPart_eq_self a).symm
  tfae_have 1 ↔ 8 := ⟨fun h => ⟨h.isSelfAdjoint, negPart_eq_zero_iff a |>.mpr h⟩,
    fun h => negPart_eq_zero_iff a |>.mp h.2⟩
  tfae_have 1 → 2 := fun h => sqrt_mul_sqrt_self a |>.symm
  tfae_have 2 → 3 := fun h => ⟨sqrt a, sqrt_nonneg a, h⟩
  tfae_have 3 → 4 := fun ⟨b, hb⟩ => ⟨b, hb.1.isSelfAdjoint, hb.2⟩
  tfae_have 4 → 5 := fun ⟨b, hb⟩ => ⟨b, hb.1.symm ▸ hb.2⟩
  tfae_have 5 → 6 := fun ⟨b, hb⟩ => ⟨star b, star_star b |>.symm ▸ hb⟩
  tfae_have 6 → 1 := fun ⟨b, hb⟩ => hb ▸ mul_star_self_nonneg _
  tfae_finish
/-
**CFC._root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt** 是 Mathlib 中的一个定理，位于命名空间 
`CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt {a : A} :
    0 ≤ a ↔ a = sqrt a * sqrt a := CStarAlgebra.nonneg_TFAE.out 0 1
/-
**CFC._root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self** 是 Mathlib 中
的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self {a : A} :
    0 ≤ a ↔ ∃ b, 0 ≤ b ∧ a = b * b := CStarAlgebra.nonneg_TFAE.out 0 2
/-
**CFC._root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self** 是 Ma
thlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self {a : A} :
    0 ≤ a ↔ ∃ b, IsSelfAdjoint b ∧ a = b * b := CStarAlgebra.nonneg_TFAE.out 0 3
/-
**CFC._root_.CStarAlgebra.nonneg_iff_eq_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 
`CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.nonneg_iff_eq_star_mul_self {a : A} :
    0 ≤ a ↔ ∃ b, a = star b * b := CStarAlgebra.nonneg_TFAE.out 0 4
/-
**CFC._root_.CStarAlgebra.nonneg_iff_eq_mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 
`CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.nonneg_iff_eq_mul_star_self {a : A} :
    0 ≤ a ↔ ∃ b, a = b * star b := CStarAlgebra.nonneg_TFAE.out 0 5
/-
**CFC._root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ a⁻ = 0 := CStarAlgebra.nonneg_TFAE.out 0 7

end sqrt

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/- ## `rpow` -/

/-- Real powers of operators, based on the unital continuous functional calculus. -/
/-
**CFC.rpow** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
形式化陈述：rpow (a : A) (y : Real) : A
参数：a : A；y : Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal

--- 原说明 ---
Real powers of operators, based on the unital continuous functional calculus.
-/
noncomputable def rpow (a : A) (y : ℝ) : A := cfc (fun x : ℝ≥0 => x ^ y) a

/-- Enable `a ^ y` notation for `CFC.rpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available (such as `Pow ℝ ℝ`). -/
/-
**CFC.** 是 Mathlib 中的一个实例，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enable `a ^ y` notation for `CFC.rpow`. This is a low-priority instance to make 
sure it does
not take priority over other instances when they are available (such as `Pow ℝ ℝ
`).
-/
noncomputable instance (priority := 100) : Pow A ℝ where
  pow a y := rpow a y

@[simp]
/-
**CFC.rpow_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_eq_pow {a : A} {y : Real} : rpow a y = a ^ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma rpow_eq_pow {a : A} {y : ℝ} : rpow a y = a ^ y := rfl

@[simp]
/-
**CFC.rpow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_nonneg {a : A} {y : Real} : 0 <= a ^ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfc_predicate`：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
-/
lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a

grind_pattern rpow_nonneg => NonnegSpectrumClass ℝ A, a ^ y
/-
**CFC.rpow_def** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0 => x ^ y) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma rpow_def {a : A} {y : ℝ} : a ^ y = cfc (fun x : ℝ≥0 => x ^ y) a := rfl
/-
**CFC.rpow_eq_cfc_real** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_eq_cfc_real [IsSemitopologicalRing A] [T2Space A] {a : A} {y : Real} 
(ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
-/
lemma rpow_eq_cfc_real [IsSemitopologicalRing A] [T2Space A] {a : A} {y : ℝ}
    (ha : 0 ≤ a := by cfc_tac) : a ^ y = cfc (fun x : ℝ => x ^ y) a := by
  rw [CFC.rpow_def, cfc_nnreal_eq_real ..]
  refine cfc_congr ?_
  intro x hx
  simp only [NNReal.coe_rpow, Real.coe_toNNReal']
  grind
/-
**CFC.cfc_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：cfc_rpow [IsSemitopologicalRing A] [T2Space A] {a : A} {y : Real} {f : Rea
l -> Real} (hf₁ : forall x in spectrum Real a, 0 < f x) (hf₂ : ContinuousOn f (s
pectrum Real a)
参数：hf₁ : forall x in spectrum Real a, 0 < f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.rpow_const`：ContinuousOn.rpow_const (hf : ContinuousOn f s)
 (h : forall x in s, f x != 0 ∨ 0 <= p) : ContinuousOn (fun x => f x ^ p) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_eq_cfc_real`：rpow_eq_cfc_real [IsSemitopologicalRing A] [T2Spac
e A] {a : A} {y : Real} (ha : 0 <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_comp`：cfc_comp (g f : R -> R) (a : A) (ha : p a
-/
lemma cfc_rpow [IsSemitopologicalRing A] [T2Space A] {a : A} {y : ℝ} {f : ℝ → ℝ}
    (hf₁ : ∀ x ∈ spectrum ℝ a, 0 < f x) (hf₂ : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) : cfc f a ^ y = cfc (fun r => f r ^ y) a := by
  have hg : ContinuousOn (fun r => r ^ y) (f '' spectrum ℝ a) :=
    ContinuousOn.rpow_const (f := id) (by fun_prop) (by grind)
  rw [CFC.rpow_eq_cfc_real (by grind [cfc_nonneg]), ← cfc_comp _ _ a ha]
  rfl
/-
**CFC.rpow_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_one (a : A) (ha : 0 <= a
参数：a : A。
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) = a := by
  simp only [rpow_def, NNReal.rpow_one, cfc_id' ℝ≥0 a]

@[simp]
/-
**CFC.one_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：one_rpow {x : Real} : (1 : A) ^ x = (1 : A)
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `cfc_apply_one`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Co
mmSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopol
ogi…
· 使用定理 `NNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0) ^ x = 1
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_rpow {x : ℝ} : (1 : A) ^ x = (1 : A) := by simp [rpow_def]
/-
**CFC.rpow_zero** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_zero (a : A) (ha : 0 <= a
参数：a : A。
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用引理 `cfc_const_one`：cfc_const_one : cfc (fun _ : R => 1) a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_zero (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (0 : ℝ) = 1 := by
  simp [rpow_def, cfc_const_one ℝ≥0 a]
/-
**CFC.rpow_zero_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_zero_eqOn : (Set.Ici (0 : A)).EqOn (fun a => a ^ (0 : Real)) (fun _ =
> 1)
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `CFC.rpow_zero`：rpow_zero (a : A) (ha : 0 <= a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_zero_eqOn : (Set.Ici (0 : A)).EqOn (fun a => a ^ (0 : ℝ)) (fun _ => 1) := by
  intro a ha
  simp [rpow_zero a ha]
/-
**CFC.zero_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：zero_rpow {x : Real} (hx : x != 0) : rpow (0 : A) x = 0
参数：hx : x != 0。
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `cfc_apply_zero`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : C
ommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopo
logi…
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
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
lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by simp [rpow, NNReal.zero_rpow hx]
/-
**CFC.rpow_natCast** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_natCast (a : A) (n : Nat) (ha : 0 <= a
参数：a : A；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_natCast (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) : a ^ (n : ℝ) = a ^ n := by
  rw [← cfc_pow_id (R := ℝ≥0) a n, rpow_def]
  congr
  simp

@[simp]
/-
**CFC.rpow_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_algebraMap {x : Real>=0} {y : Real} : (algebraMap Real>=0 A x) ^ y = 
algebraMap Real>=0 A (x ^ y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
-/
lemma rpow_algebraMap {x : ℝ≥0} {y : ℝ} :
    (algebraMap ℝ≥0 A x) ^ y = algebraMap ℝ≥0 A (x ^ y) := by
  rw [rpow_def, cfc_algebraMap ..]
/-
**CFC.rpow_add** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_add {a : A} {x y : Real} (ha : IsUnit a) : a ^ (x + y) = a ^ x * a ^ 
y
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_mul`：cfc_mul (f g : R -> R) (a : A) (hf : ContinuousOn f (spectrum R
 a)
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `NNReal.rpow_add`：rpow_add {x : Real>=0} (hx : x != 0) (y z : Real) : x ^
 (y + z) = x ^ y * x ^ z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_add {a : A} {x y : ℝ} (ha : IsUnit a) :
    a ^ (x + y) = a ^ x * a ^ y := by
  have ha' : 0 ∉ spectrum ℝ≥0 a := spectrum.zero_notMem _ ha
  simp only [rpow_def]
  rw [← cfc_mul _ _ a]
  refine cfc_congr ?_
  intro z hz
  have : z ≠ 0 := by aesop
  simp [NNReal.rpow_add this _ _]
/-
**CFC.rpow_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (x y : Real) (hx :
 x != 0) (ha : IsStrictlyPositive a
参数：a : A；x y : Real；hx : x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_comp`：cfc_comp (g f : R -> R) (a : A) (ha : p a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_rpow [IsSemitopologicalRing A] [T2Space A]
    (a : A) (x y : ℝ) (hx : x ≠ 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    (a ^ x) ^ y = a ^ (x * y) := by
  have ha₁' : 0 ∉ spectrum ℝ≥0 a := spectrum.zero_notMem _ ha.isUnit
  simp only [rpow_def]
  rw [← cfc_comp _ _ a ha.nonneg]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]
/-
**CFC.rpow_rpow_inv** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_rpow_inv [IsSemitopologicalRing A] [T2Space A] (a : A) (x : Real) (hx
 : x != 0) (ha : IsStrictlyPositive a
参数：a : A；x : Real；hx : x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_rpow`：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (
x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用引理 `CFC.rpow_one`：rpow_one (a : A) (ha : 0 <= a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
-/
lemma rpow_rpow_inv [IsSemitopologicalRing A] [T2Space A]
    (a : A) (x : ℝ) (hx : x ≠ 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    (a ^ x) ^ x⁻¹ = a := by
  rw [rpow_rpow a x x⁻¹ hx, mul_inv_cancel₀ hx, rpow_one a ha.nonneg]
/-
**CFC.rpow_inv_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_inv_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (x : Real) (hx
 : x != 0) (ha : IsStrictlyPositive a
参数：a : A；x : Real；hx : x != 0。
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
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `CFC.rpow_rpow_inv`：rpow_rpow_inv [IsSemitopologicalRing A] [T2Space A] (
a : A) (x : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma rpow_inv_rpow [IsSemitopologicalRing A] [T2Space A]
    (a : A) (x : ℝ) (hx : x ≠ 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    (a ^ x⁻¹) ^ x = a := by
  simpa using rpow_rpow_inv a x⁻¹ (inv_ne_zero hx)
/-
**CFC.rpow_rpow_of_exponent_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_rpow_of_exponent_nonneg [IsSemitopologicalRing A] [T2Space A] (a : A)
 (x y : Real) (hx : 0 <= x) (hy : 0 <= y) (ha : 0 <= a
参数：a : A；x y : Real；hx : 0 <= x；hy : 0 <= y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_comp`：cfc_comp (g f : R -> R) (a : A) (ha : p a
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
-/
lemma rpow_rpow_of_exponent_nonneg [IsSemitopologicalRing A] [T2Space A] (a : A) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a := by cfc_tac) : (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]
/-
**CFC.rpow_mul_rpow_neg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_mul_rpow_neg {a : A} (x : Real) (ha : IsStrictlyPositive a
参数：x : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.rpow_add`：rpow_add {a : A} {x y : Real} (ha : IsUnit a) : a ^ (x + y
) = a ^ x * a ^ y
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用引理 `CFC.rpow_zero`：rpow_zero (a : A) (ha : 0 <= a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
-/
lemma rpow_mul_rpow_neg {a : A} (x : ℝ) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ x * a ^ (-x) = 1 := by
  rw [← rpow_add ha.isUnit, add_neg_cancel, rpow_zero a]
/-
**CFC.rpow_neg_mul_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_neg_mul_rpow {a : A} (x : Real) (ha : IsStrictlyPositive a
参数：x : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.rpow_add`：rpow_add {a : A} {x y : Real} (ha : IsUnit a) : a ^ (x + y
) = a ^ x * a ^ y
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `CFC.rpow_zero`：rpow_zero (a : A) (ha : 0 <= a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
-/
lemma rpow_neg_mul_rpow {a : A} (x : ℝ) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ (-x) * a ^ x = 1 := by
  rw [← rpow_add ha.isUnit, neg_add_cancel, rpow_zero a]
/-
**CFC.rpow_neg_one_eq_inv** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) <= a
参数：a : Aˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_eq_of_mul_eq_one_left`：∀ {α : Type u} [inst : Monoid α] {u : α
ˣ} {a : α}, a * ↑u = 1 → ↑u⁻¹ = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_one`：rpow_one (a : A) (ha : 0 <= a
· 使用引理 `CFC.rpow_neg_mul_rpow`：rpow_neg_mul_rpow {a : A} (x : Real) (ha : IsStri
ctlyPositive a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.isStrictlyPositive_iff`：∀ {A : Type u_1} [inst : LE A] [inst_1 : M
onoid A] [inst_2 : Zero A] {a : Aˣ}, IsStrictlyPositive ↑a ↔ 0 ≤ ↑a
-/
lemma rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) ≤ a := by cfc_tac) :
    a ^ (-1 : ℝ) = (↑a⁻¹ : A) := by
  refine a.inv_eq_of_mul_eq_one_left ?_ |>.symm
  simpa [rpow_one (a : A)] using rpow_neg_mul_rpow 1 (a.isStrictlyPositive_iff.mpr ha)
/-
**CFC.rpow_neg_one_eq_cfc_inv** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_neg_one_eq_cfc_inv {A : Type*} [PartialOrder A] [NormedRing A] [StarR
ing A] [StarOrderedRing A] [NormedAlgebra Real A] [NonnegSpectrumClass Real A] [
ContinuousFunctionalCalculus Real A IsSelfAdjoint] (a : A) : a ^ (-1 : Real) = c
fc (·⁻¹ : Real>=0 -> Real>=0) a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.rpow_neg_one`：rpow_neg_one (x : Real>=0) : x ^ (-1 : Real) = x⁻¹
-/
lemma rpow_neg_one_eq_cfc_inv {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A]
    [StarOrderedRing A] [NormedAlgebra ℝ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] (a : A) :
    a ^ (-1 : ℝ) = cfc (·⁻¹ : ℝ≥0 → ℝ≥0) a :=
  cfc_congr fun x _ ↦ NNReal.rpow_neg_one x
/-
**CFC.inverse_eq_rpow_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：inverse_eq_rpow_neg_one {a : A} (ha : IsStrictlyPositive a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `invOf_units`：invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u 
: α) = ↑u⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CFC.rpow_neg_one_eq_inv`：rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) <= a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inverse_eq_rpow_neg_one {a : A} (ha : IsStrictlyPositive a := by cfc_tac) :
    Ring.inverse a = a ^ (-1 : ℝ) := by
  obtain ⟨ax, hax⟩ := ha.isUnit
  simp only [← hax, Ring.inverse_invertible, invOf_units, CFC.rpow_neg_one_eq_inv ax]
/-
**CFC.rpow_neg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_neg [IsSemitopologicalRing A] [T2Space A] (a : Aˣ) (x : Real) (ha' : 
(0 : A) <= a
参数：a : Aˣ；x : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_eq_zero`：inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_inv_id`：cfc_inv_id (a : Aˣ) (ha : p a
· 使用定理 `NNReal.instContinuousInv₀`：ContinuousInv₀ NNReal
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用引理 `Units.continuousOn_inv₀_spectrum`：Units.continuousOn_inv₀_spectrum (a : 
Aˣ) : ContinuousOn (· ⁻¹) (spectrum R (a : A))
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `NNReal.rpow_neg`：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻
¹
· 使用定理 `NNReal.inv_rpow`：inv_rpow (x : Real>=0) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_neg [IsSemitopologicalRing A] [T2Space A] (a : Aˣ) (x : ℝ)
    (ha' : (0 : A) ≤ a := by cfc_tac) : (a : A) ^ (-x) = (↑a⁻¹ : A) ^ x := by
  suffices h₁ : ContinuousOn (fun z ↦ z ^ x) (Inv.inv '' (spectrum ℝ≥0 (a : A))) by
    rw [← cfc_inv_id (R := ℝ≥0) a, rpow_def, rpow_def,
        ← cfc_comp' (fun z => z ^ x) (Inv.inv : ℝ≥0 → ℝ≥0) (a : A) h₁]
    refine cfc_congr fun _ _ => ?_
    simp [NNReal.rpow_neg, NNReal.inv_rpow]
  refine NNReal.continuousOn_rpow_const (.inl ?_)
  rintro ⟨z, hz, hz'⟩
  exact spectrum.zero_notMem ℝ≥0 a.isUnit <| inv_eq_zero.mp hz' ▸ hz
/-
**CFC.rpow_intCast** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_intCast (a : Aˣ) (n : Int) (ha : (0 : A) <= a
参数：a : Aˣ；n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_zpow`：cfc_zpow (a : Aˣ) (n : Int) (ha : p a
· 使用定理 `NNReal.instContinuousInv₀`：ContinuousInv₀ NNReal
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NNReal.rpow_intCast`：rpow_intCast (x : Real>=0) (n : Int) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_intCast (a : Aˣ) (n : ℤ) (ha : (0 : A) ≤ a := by cfc_tac) :
    (a : A) ^ (n : ℝ) = (↑(a ^ n) : A) := by
  rw [← cfc_zpow (R := ℝ≥0) a n, rpow_def]
  refine cfc_congr fun _ _ => ?_
  simp

/-- `a ^ x` bundled as an element of `Aˣ` for `a : Aˣ`. -/
@[simps]
/-
**CFC._root_.Units.cfcRpow** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a ^ x` bundled as an element of `Aˣ` for `a : Aˣ`.
-/
noncomputable def _root_.Units.cfcRpow (a : Aˣ) (x : ℝ) (ha : (0 : A) ≤ a := by cfc_tac) : Aˣ :=
  ⟨(a : A) ^ x, (a : A) ^ (-x), rpow_mul_rpow_neg x, rpow_neg_mul_rpow x⟩

@[aesop safe apply, grind ←]
/-
**CFC._root_.IsUnit.cfcRpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsUnit.cfcRpow {a : A} (ha : IsUnit a) (x : ℝ) (ha_nonneg : 0 ≤ a := by cfc_tac) :
    IsUnit (a ^ x) :=
  ha.unit.cfcRpow x |>.isUnit
/-
**CFC.spectrum_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：spectrum_rpow (a : A) (x : Real) (h : ContinuousOn (· ^ x) (spectrum Real>
=0 a)
参数：a : A；x : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
-/
lemma spectrum_rpow (a : A) (x : ℝ)
    (h : ContinuousOn (· ^ x) (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) :
    spectrum ℝ≥0 (a ^ x) = (· ^ x) '' spectrum ℝ≥0 a :=
  cfc_map_spectrum (· ^ x : ℝ≥0 → ℝ≥0) a ha h

@[grind =]
/-
**CFC.isUnit_rpow_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：isUnit_rpow_iff (a : A) (y : Real) (hy : y != 0) (ha : 0 <= a
参数：a : A；y : Real；hy : y != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `spectrum.isUnit_of_zero_notMem`：∀ (R : Type u) {A : Type v} [inst : Comm
Semiring R] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   0 ∉ spectrum R a
 → IsUnit a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用引理 `isUnit_cfc_iff`：isUnit_cfc_iff (f : R -> R) (a : A) (hf : ContinuousOn f
 (spectrum R a)
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
· 使用定理 `IsUnit.cfcRpow`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : Ring 
A] [inst_2 : StarRing A] [inst_3 : TopologicalSpace A]   [inst_4 : StarOrderedRi
ng A…
-/
lemma isUnit_rpow_iff (a : A) (y : ℝ) (hy : y ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    IsUnit (a ^ y) ↔ IsUnit a := by
  nontriviality A
  refine ⟨fun h => ?_, fun h => h.cfcRpow y ha⟩
  rw [rpow_def] at h
  by_cases hf : ContinuousOn (fun x : ℝ≥0 => x ^ y) (spectrum ℝ≥0 a)
  · rw [isUnit_cfc_iff _ a hf] at h
    refine spectrum.isUnit_of_zero_notMem ℝ≥0 ?_
    intro h0
    specialize h 0 h0
    simp only [ne_eq, NNReal.rpow_eq_zero_iff, true_and, Decidable.not_not] at h
    exact hy h
  · rw [cfc_apply_of_not_continuousOn a hf] at h
    exact False.elim <| not_isUnit_zero h

section prod

variable [IsSemitopologicalRing A] [T2Space A]
variable {B : Type*} [PartialOrder B] [Ring B] [StarRing B] [TopologicalSpace B]
  [StarOrderedRing B]
  [Algebra ℝ B] [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [ContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint]
  [IsSemitopologicalRing B] [T2Space B] [StarOrderedRing (A × B)]
  [NonnegSpectrumClass ℝ B] [NonnegSpectrumClass ℝ (A × B)]

set_option backward.isDefEq.respectTransparency false in
/- Note that there is higher-priority instance of `Pow (A × B) ℝ` coming from the `Pow` instance for
products, hence the direct use of `rpow` here. -/
/-
**CFC.rpow_map_prod** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_map_prod {a : A} {b : B} {x : Real} (ha : IsUnit a) (hb : IsUnit b) (
ha' : 0 <= a
参数：ha : IsUnit a；hb : IsUnit b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用引理 `cfc_map_prod`：cfc_map_prod (f : R -> R) (a : A) (b : B) (hf : Continuous
On f (spectrum R a union spectrum R b)
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Prod.le_def`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE 
β] {x y : α × β}, x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2

--- 原说明 ---
Note that there is higher-priority instance of `Pow (A × B) ℝ` coming from the `
Pow` instance for
products, hence the direct use of `rpow` here.
-/
lemma rpow_map_prod {a : A} {b : B} {x : ℝ} (ha : IsUnit a) (hb : IsUnit b)
    (ha' : 0 ≤ a := by cfc_tac) (hb' : 0 ≤ b := by cfc_tac) :
    rpow (a, b) x = (a ^ x, b ^ x) := by
  have ha'' : 0 ∉ spectrum ℝ≥0 a := spectrum.zero_notMem _ ha
  have hb'' : 0 ∉ spectrum ℝ≥0 b := spectrum.zero_notMem _ hb
  simp only [rpow_def]
  unfold rpow
  refine cfc_map_prod (R := ℝ≥0) (S := ℝ) _ a b (by cfc_cont_tac) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha', hb']
/-
**CFC.rpow_eq_rpow_prod** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_eq_rpow_prod {a : A} {b : B} {x : Real} (ha : IsUnit a) (hb : IsUnit 
b) (ha' : 0 <= a
参数：ha : IsUnit a；hb : IsUnit b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.rpow_map_prod`：rpow_map_prod {a : A} {b : B} {x : Real} (ha : IsUnit
 a) (hb : IsUnit b) (ha' : 0 <= a
-/
lemma rpow_eq_rpow_prod {a : A} {b : B} {x : ℝ} (ha : IsUnit a) (hb : IsUnit b)
    (ha' : 0 ≤ a := by cfc_tac) (hb' : 0 ≤ b := by cfc_tac) :
    rpow (a, b) x = (a, b) ^ x := rpow_map_prod ha hb

end prod

section pi

variable [IsSemitopologicalRing A] [T2Space A]
variable {ι : Type*} {C : ι → Type*} [∀ i, PartialOrder (C i)] [∀ i, Ring (C i)]
  [∀ i, StarRing (C i)] [∀ i, TopologicalSpace (C i)] [∀ i, StarOrderedRing (C i)]
  [StarOrderedRing (∀ i, C i)]
  [∀ i, Algebra ℝ (C i)] [∀ i, ContinuousFunctionalCalculus ℝ (C i) IsSelfAdjoint]
  [ContinuousFunctionalCalculus ℝ (∀ i, C i) IsSelfAdjoint]
  [∀ i, IsSemitopologicalRing (C i)] [∀ i, T2Space (C i)]
  [NonnegSpectrumClass ℝ (∀ i, C i)] [∀ i, NonnegSpectrumClass ℝ (C i)]

set_option backward.isDefEq.respectTransparency false in
/- Note that there is a higher-priority instance of `Pow (∀ i, B i) ℝ` coming from the `Pow`
/-
**CFC.for** 是 Mathlib 中的一个实例，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance for pi types, hence the direct use of `rpow` here. -/
/-
**CFC.rpow_map_pi** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_map_pi {c : forall i, C i} {x : Real} (hc : forall i, IsUnit (c i)) (
hc' : forall i, 0 <= c i
参数：hc : forall i, IsUnit (c i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用引理 `cfc_map_pi`：cfc_map_pi (f : R -> R) (a : forall i, A i) (hf : Continuous
On f (⋃ i, spectrum R (a i))
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NNReal.continuousOn_rpow_const`：continuousOn_rpow_const {r : Real} {s : 
Set Real>=0} (h : 0 ∉ s ∨ 0 <= r) : ContinuousOn (fun z : Real>=0 => z ^ r) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
Note that there is a higher-priority instance of `Pow (∀ i, B i) ℝ` coming from 
the `Pow`
instance for pi types, hence the direct use of `rpow` here.
-/
lemma rpow_map_pi {c : ∀ i, C i} {x : ℝ} (hc : ∀ i, IsUnit (c i))
    (hc' : ∀ i, 0 ≤ c i := by cfc_tac) :
    rpow c x = fun i => (c i) ^ x := by
  have hc'' : ∀ i, 0 ∉ spectrum ℝ≥0 (c i) := fun i => spectrum.zero_notMem _ (hc i)
  simp only [rpow_def]
  unfold rpow
  exact cfc_map_pi (S := ℝ) _ c
/-
**CFC.rpow_eq_rpow_pi** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_eq_rpow_pi {c : forall i, C i} {x : Real} (hc : forall i, IsUnit (c i
)) (hc' : forall i, 0 <= c i
参数：hc : forall i, IsUnit (c i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.rpow_map_pi`：rpow_map_pi {c : forall i, C i} {x : Real} (hc : forall
 i, IsUnit (c i)) (hc' : forall i, 0 <= c i
-/
lemma rpow_eq_rpow_pi {c : ∀ i, C i} {x : ℝ} (hc : ∀ i, IsUnit (c i))
    (hc' : ∀ i, 0 ≤ c i := by cfc_tac) :
    rpow c x = c ^ x := rpow_map_pi hc

end pi

section unital_vs_nonunital

open Ring
variable [IsSemitopologicalRing A] [T2Space A]

-- provides instance `ContinuousFunctionalCalculus.compactSpace_spectrum`
open scoped ContinuousFunctionalCalculus

/-
**CFC.nnrpow_eq_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : a ^ x = a ^ (x : Real)
参数：hx : 0 < x。
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
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.nnrpow_def`：nnrpow_def {a : A} {y : Real>=0} : a ^ y = cfcₙ (NNReal.
nnrpow · y) a
· 使用引理 `CFC.rpow_def`：rpow_def {a : A} {y : Real} : a ^ y = cfc (fun x : Real>=0
 => x ^ y) a
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma nnrpow_eq_rpow {a : A} {x : ℝ≥0} (hx : 0 < x) : a ^ x = a ^ (x : ℝ) := by
  rw [nnrpow_def (A := A), rpow_def, cfcₙ_eq_cfc]
/-
**CFC.sqrt_eq_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.nnrpow_eq_rpow`：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : 
a ^ x = a ^ (x : Real)
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
· 使用引理 `CFC.sqrt_eq_nnrpow`：sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : Real>
=0)
-/
lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ) := by
  have : a ^ (1 / 2 : ℝ) = a ^ ((1 / 2 : ℝ≥0) : ℝ) := rfl
  rw [this, ← nnrpow_eq_rpow (by simp), sqrt_eq_nnrpow a]
/-
**CFC.sqrt_eq_cfc** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `cfcₙ_eq_cfc`：cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [Continuou
sMapZero.UniqueHom R A] {f : R -> R} {a : A} (hf : ContinuousOn f (σₙ R a)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `NNReal.continuous_sqrt`：continuous_sqrt : Continuous sqrt
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a := by
  unfold sqrt
  rw [cfcₙ_eq_cfc]
/-
**CFC.sqrt_sq** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_sq (a : A) (ha : 0 <= a
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
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `CFC.sqrt_mul_self`：sqrt_mul_self (a : A) (ha : 0 <= a
-/
lemma sqrt_sq (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ 2) = a := by
  rw [pow_two, sqrt_mul_self (A := A) a]
/-
**CFC.sq_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sq_sqrt (a : A) (ha : 0 <= a
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
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
-/
lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
  rw [pow_two, sqrt_mul_sqrt_self (A := A) a]
/-
**CFC.sq_eq_sq_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sq_eq_sq_iff (a b : A) (ha : 0 <= a
参数：a b : A。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CFC.mul_self_eq_mul_self_iff`：mul_self_eq_mul_self_iff (a b : A) (ha : 0
 <= a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sq_eq_sq_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    a ^ 2 = b ^ 2 ↔ a = b := by
  simp_rw [sq, mul_self_eq_mul_self_iff a b]

@[simp]
/-
**CFC.sqrt_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_algebraMap {r : Real>=0} : sqrt (algebraMap Real>=0 A r) = algebraMap
 Real>=0 A (NNReal.sqrt r)
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_cfc`：sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
-/
lemma sqrt_algebraMap {r : ℝ≥0} : sqrt (algebraMap ℝ≥0 A r) = algebraMap ℝ≥0 A (NNReal.sqrt r) := by
  rw [sqrt_eq_cfc, cfc_algebraMap]

@[simp]
/-
**CFC.sqrt_one** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_one : sqrt (1 : A) = 1
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
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用引理 `CFC.sqrt_eq_cfc`：sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a
· 使用定理 `cfc_apply_one`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Co
mmSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopol
ogi…
· 使用定理 `NNReal.sqrt_one`：NNReal.sqrt 1 = 1
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sqrt_one : sqrt (1 : A) = 1 := by simp [sqrt_eq_cfc]
/-
**CFC.sqrt_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_one_iff (a : A) (ha : 0 <= a
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
· 使用引理 `CFC.sqrt_eq_iff`：sqrt_eq_iff (a b : A) (ha : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sqrt_eq_one_iff (a : A) (ha : 0 ≤ a := by cfc_tac) :
    sqrt a = 1 ↔ a = 1 := by
  rw [sqrt_eq_iff a _, mul_one, eq_comm]
/-
**CFC.sqrt_eq_one_iff'** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_eq_one_iff' [Nontrivial A] (a : A) : sqrt a = 1 ↔ a = 1
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CFC.sqrt_eq_one_iff`：sqrt_eq_one_iff (a : A) (ha : 0 <= a
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `cfcₙ_def`：∀ {R : Type u_3} {A : Type u_4} {p : A → Prop} [inst : CommSem
iring R] [inst_1 : Nontrivial R] [inst_2 : StarRing R]   [inst_3 : MetricSpace…
· 使用定理 `CFC.sqrt.eq_1`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : NonUni
talRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 : _root
_.M…
· 使用引理 `CFC.sqrt_one`：sqrt_one : sqrt (1 : A) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma sqrt_eq_one_iff' [Nontrivial A] (a : A) :
    sqrt a = 1 ↔ a = 1 := by
  refine ⟨fun h ↦ sqrt_eq_one_iff a ?_ |>.mp h, fun h ↦ by subst h; exact sqrt_one⟩
  rw [sqrt, cfcₙ] at h
  cfc_tac

-- TODO: relate to a strict positivity condition
/-
**CFC.sqrt_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_rpow {a : A} {x : Real} (h : IsUnit a) (hx : x != 0) : sqrt (a ^ x) =
 a ^ (x / 2)
参数：h : IsUnit a；hx : x != 0。
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_rpow`：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `CFC.rpow_rpow`：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (
x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用引理 `cfc_apply_of_not_predicate`：cfc_apply_of_not_predicate {f : R -> R} (a :
 A) (ha : ¬ p a) : cfc f a = 0
· 使用引理 `CFC.sqrt_eq_cfc`：sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a
· 使用定理 `cfc_apply_zero`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : C
ommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopo
logi…
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma sqrt_rpow {a : A} {x : ℝ} (h : IsUnit a)
    (hx : x ≠ 0) : sqrt (a ^ x) = a ^ (x / 2) := by
  by_cases hnonneg : 0 ≤ a
  case pos =>
    have : IsStrictlyPositive a := by grind
    simp [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow _ _ _ hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

-- TODO: relate to a strict positivity condition
/-
**CFC.rpow_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_sqrt (a : A) (x : Real) (h : IsUnit a) (ha : 0 <= a
参数：a : A；x : Real；h : IsUnit a。
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_rpow`：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `CFC.rpow_rpow`：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (
x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
-/
lemma rpow_sqrt (a : A) (x : ℝ) (h : IsUnit a)
    (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ x = a ^ (x / 2) := by
  have : IsStrictlyPositive a := by grind
  rw [sqrt_eq_rpow, div_eq_mul_inv, one_mul,
      rpow_rpow _ _ _ (by simp), inv_mul_eq_div]
/-
**CFC.sqrt_rpow_nnreal** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_rpow_nnreal {a : A} {x : Real>=0} : sqrt (a ^ (x : Real)) = a ^ (x / 
2 : Real)
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用引理 `CFC.rpow_zero`：rpow_zero (a : A) (ha : 0 <= a
· 使用引理 `CFC.sqrt_one`：sqrt_one : sqrt (1 : A) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.nnrpow_eq_rpow`：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : 
a ^ x = a ^ (x : Real)
（共 40 条，此处仅展示前 30 条）
-/
lemma sqrt_rpow_nnreal {a : A} {x : ℝ≥0} : sqrt (a ^ (x : ℝ)) = a ^ (x / 2 : ℝ) := by
  by_cases htriv : 0 ≤ a
  case neg => simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a htriv]
  case pos =>
    cases eq_zero_or_pos x with
    | inl hx => simp [hx, rpow_zero _ htriv]
    | inr h₁ =>
      have h₂ : (x : ℝ) / 2 = NNReal.toReal (x / 2) := by simp
      have h₃ : 0 < x / 2 := by positivity
      rw [← nnrpow_eq_rpow h₁, h₂, ← nnrpow_eq_rpow h₃, sqrt_nnrpow (A := A)]
/-
**CFC.rpow_sqrt_nnreal** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：rpow_sqrt_nnreal {a : A} {x : Real>=0} (ha : 0 <= a
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_zero`：rpow_zero (a : A) (ha : 0 <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
· 使用引理 `CFC.sqrt_eq_rpow`：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
· 使用引理 `CFC.rpow_rpow_of_exponent_nonneg`：rpow_rpow_of_exponent_nonneg [IsSemito
pologicalRing A] [T2Space A] (a : A) (x y : Real) (hx : 0 <= x) (hy : 0 <= y) (h
a : 0 <= a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_div_mul_eq_div`：one_div_mul_eq_div : 1 / a * b = b / a
-/
lemma rpow_sqrt_nnreal {a : A} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ (x : ℝ) = a ^ (x / 2 : ℝ) := by
  by_cases hx : x = 0
  case pos =>
    have ha' : 0 ≤ sqrt a := sqrt_nonneg _
    simp [hx, rpow_zero _ ha', rpow_zero _ ha]
  case neg =>
    have h₁ : 0 ≤ (x : ℝ) := NNReal.zero_le_coe
    rw [sqrt_eq_rpow, rpow_rpow_of_exponent_nonneg _ _ _ (by simp) h₁, one_div_mul_eq_div]

@[grind =]
/-
**CFC.isUnit_nnrpow_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：isUnit_nnrpow_iff (a : A) (y : Real>=0) (hy : y != 0) (ha : 0 <= a
参数：a : A；y : Real>=0；hy : y != 0。
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
· 使用引理 `CFC.nnrpow_eq_rpow`：nnrpow_eq_rpow {a : A} {x : Real>=0} (hx : 0 < x) : 
a ^ x = a ^ (x : Real)
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `CFC.isUnit_rpow_iff`：isUnit_rpow_iff (a : A) (y : Real) (hy : y != 0) (h
a : 0 <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma isUnit_nnrpow_iff (a : A) (y : ℝ≥0) (hy : y ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    IsUnit (a ^ y) ↔ IsUnit a := by
  rw [nnrpow_eq_rpow (pos_of_ne_zero hy)]
  refine isUnit_rpow_iff a y ?_ ha
  exact_mod_cast hy

@[aesop safe apply]
/-
**CFC._root_.IsUnit.cfcNNRpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsUnit.cfcNNRpow (a : A) (y : ℝ≥0) (ha_unit : IsUnit a) (hy : y ≠ 0)
    (ha : 0 ≤ a := by cfc_tac) : IsUnit (a ^ y) :=
  (isUnit_nnrpow_iff a y hy ha).mpr ha_unit
/-
**CFC.isUnit_sqrt_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：isUnit_sqrt_iff (a : A) (ha : 0 <= a
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_rpow`：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
· 使用引理 `CFC.isUnit_rpow_iff`：isUnit_rpow_iff (a : A) (y : Real) (hy : y != 0) (h
a : 0 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma isUnit_sqrt_iff (a : A) (ha : 0 ≤ a := by cfc_tac) : IsUnit (sqrt a) ↔ IsUnit a := by
  rw [sqrt_eq_rpow]
  exact isUnit_rpow_iff a _ (by simp) ha

@[grind =]
/-
**CFC.isUnit_sqrt_iff_isStrictlyPositive** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：isUnit_sqrt_iff_isStrictlyPositive {a : A} : IsUnit (sqrt a) ↔ IsStrictlyP
ositive a
该定理/引理刻画了左右两侧的等价关系。
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
· 使用引理 `IsStrictlyPositive.iff_of_unital`：iff_of_unital [LE A] [Monoid A] [Zero 
A] {a : A} : IsStrictlyPositive a ↔ 0 <= a ∧ IsUnit a
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用引理 `CFC.sqrt_of_not_nonneg`：sqrt_of_not_nonneg {a : A} (ha : ¬0 <= a) : sqrt
 a = 0
· 使用引理 `CFC.isUnit_sqrt_iff`：isUnit_sqrt_iff (a : A) (ha : 0 <= a
-/
lemma isUnit_sqrt_iff_isStrictlyPositive {a : A} : IsUnit (sqrt a) ↔ IsStrictlyPositive a := by
  refine ⟨fun h => ?_, by grind [isUnit_sqrt_iff]⟩
  rw [IsStrictlyPositive.iff_of_unital]
  have ha : 0 ≤ a := by
    nontriviality
    by_contra H
    rw [CFC.sqrt_of_not_nonneg H] at h
    exact not_isUnit_zero h
  refine ⟨ha, ?_⟩
  rwa [isUnit_sqrt_iff _ ha] at h

@[aesop safe apply]
/-
**CFC._root_.IsStrictlyPositive.isUnit_cfcSqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsStrictlyPositive.isUnit_cfcSqrt (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsUnit (sqrt a) := by grind

@[aesop safe apply]
/-
**CFC._root_.IsStrictlyPositive.nnrpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsStrictlyPositive.nnrpow (a : A) (y : ℝ≥0) (hy : y ≠ 0)
    (ha : IsStrictlyPositive a := by cfc_tac) : IsStrictlyPositive (a ^ y) := by grind

@[aesop safe apply]
/-
**CFC._root_.IsStrictlyPositive.sqrt** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsStrictlyPositive.sqrt (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsStrictlyPositive (sqrt a) := by grind

omit [T2Space A] [IsSemitopologicalRing A] in
@[aesop safe apply]
/-
**CFC._root_.IsStrictlyPositive.rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsStrictlyPositive.rpow (a : A) (y : ℝ) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsStrictlyPositive (a ^ y) := by grind
/-
**CFC.inverse_rpow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：inverse_rpow (a : A) (x : Real) (hx : x != 0) (ha : IsStrictlyPositive a
参数：a : A；x : Real；hx : x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_rpow`：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (
x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.inverse_eq_rpow_neg_one`：inverse_eq_rpow_neg_one {a : A} (ha : IsStr
ictlyPositive a
-/
lemma inverse_rpow (a : A) (x : ℝ) (hx : x ≠ 0) (ha : IsStrictlyPositive a := by cfc_tac) :
    Ring.inverse (a ^ x) = a ^ (-x) := by
  have : a ^ (-x) = (a ^ x) ^ (-1 : ℝ) := by
    rw [rpow_rpow (hx := hx) (ha := by grind)]
    simp
  rw [← inverse_eq_rpow_neg_one (by grind)] at this
  rw [this]

omit [IsSemitopologicalRing A] [T2Space A] in
@[aesop safe apply]
/-
**CFC._root_.IsStrictlyPositive.ringInverse** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsStrictlyPositive.ringInverse {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive a⁻¹ʳ := by
  rw [CFC.inverse_eq_rpow_neg_one]
  cfc_tac

omit [IsSemitopologicalRing A] [T2Space A] in
@[grind =]
/-
**CFC._root_.isStrictlyPositive_ringInverse_iff** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isStrictlyPositive_ringInverse_iff {a : A} :
    IsStrictlyPositive a⁻¹ʳ ↔ IsStrictlyPositive a := by
  nontriviality A
  refine ⟨fun h => ?_, IsStrictlyPositive.ringInverse⟩
  have ha : IsUnit a := by
    by_contra H
    rw [Ring.inverse_non_unit _ H, IsStrictlyPositive.iff_of_unital] at h
    exact not_isUnit_zero h.2
  rw [← Ring.inverse_inverse ha]
  exact h.ringInverse

omit [IsSemitopologicalRing A] [T2Space A] in
open Ring in
@[grind =]
/-
**CFC.ringInverse_nonneg_iff_nonneg_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：ringInverse_nonneg_iff_nonneg_of_isUnit {a : A} (ha : IsUnit a) : 0 <= a⁻¹
ʳ ↔ 0 <= a
参数：ha : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma ringInverse_nonneg_iff_nonneg_of_isUnit {a : A} (ha : IsUnit a) :
    0 ≤ a⁻¹ʳ ↔ 0 ≤ a := by
  grind [isStrictlyPositive_ringInverse_iff]

open Ring in
@[grind _=_]
/-
**CFC.sqrt_ringInverse** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：sqrt_ringInverse {a : A} : sqrt a⁻¹ʳ = (sqrt a)⁻¹ʳ
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.sqrt_eq_rpow`：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
· 使用引理 `CFC.inverse_rpow`：inverse_rpow (a : A) (x : Real) (hx : x != 0) (ha : Is
StrictlyPositive a
· 使用引理 `CFC.inverse_eq_rpow_neg_one`：inverse_eq_rpow_neg_one {a : A} (ha : IsStr
ictlyPositive a
· 使用引理 `CFC.rpow_rpow`：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (
x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用引理 `CFC.isUnit_sqrt_iff_isStrictlyPositive`：isUnit_sqrt_iff_isStrictlyPositi
ve {a : A} : IsUnit (sqrt a) ↔ IsStrictlyPositive a
· 使用引理 `CFC.sqrt_of_not_nonneg`：sqrt_of_not_nonneg {a : A} (ha : ¬0 <= a) : sqrt
 a = 0
· 使用定理 `Ring.inverse_zero`：inverse_zero : (0 : M₀)⁻¹ʳ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CFC.sqrt.congr_simp`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : 
NonUnitalRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 :
 _root_.M…
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用引理 `CFC.sqrt_zero`：sqrt_zero : sqrt (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma sqrt_ringInverse {a : A} : sqrt a⁻¹ʳ = (sqrt a)⁻¹ʳ := by
  by_cases ha : IsStrictlyPositive a
  · rw [sqrt_eq_rpow, sqrt_eq_rpow, inverse_rpow _ _ (by grind),
        inverse_eq_rpow_neg_one, rpow_rpow _ _ _ (by grind)]
    grind only
  · have ha' : ¬IsUnit (sqrt a) := by rwa [CFC.isUnit_sqrt_iff_isStrictlyPositive]
    obtain (H | H) : ¬0 ≤ a ∨ ¬IsUnit a := by grind
    · rw [sqrt_of_not_nonneg H, inverse_zero]
      by_cases hunit : IsUnit a
      · have h₂ : ¬0 ≤ inverse a := by grind [CFC.ringInverse_nonneg_iff_nonneg_of_isUnit]
        rw [sqrt_of_not_nonneg h₂]
      · simp [inverse_non_unit _ hunit]
    · simp [inverse_non_unit _ ha', inverse_non_unit _ H]

/-- For an element `a` in a C⋆-algebra, TFAE:
1. `a` is strictly positive,
2. `sqrt a` is strictly positive and `a = sqrt a * sqrt a`,
3. `sqrt a` is invertible and `a = sqrt a * sqrt a`,
4. `a = b * b` for some strictly positive `b`,
5. `a = b * b` for some self-adjoint and invertible `b`,
6. `a = star b * b` for some invertible `b`,
7. `a = b * star b` for some invertible `b`,
8. `0 ≤ a` and `a` is invertible,
9. `a` is self-adjoint and has positive spectrum. -/
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `CFC
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an element `a` in a C⋆-algebra, TFAE:
1. `a` is strictly positive,
2. `sqrt a` is strictly positive and `a = sqrt a * sqrt a`,
3. `sqrt a` is invertible and `a = sqrt a * sqrt a`,
4. `a = b * b` for some strictly positive `b`,
5. `a = b * b` for some self-adjoint and invertible `b`,
6. `a = star b * b` for some invertible `b`,
7. `a = b * star b` for some invertible `b`,
8. `0 ≤ a` and `a` is invertible,
9. `a` is self-adjoint and has positive spectrum.
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_TFAE {a : A} :
    [IsStrictlyPositive a,
     IsStrictlyPositive (sqrt a) ∧ a = sqrt a * sqrt a,
     IsUnit (sqrt a) ∧ a = sqrt a * sqrt a,
     ∃ b, IsStrictlyPositive b ∧ a = b * b,
     ∃ b, IsUnit b ∧ IsSelfAdjoint b ∧ a = b * b,
     ∃ b, IsUnit b ∧ a = star b * b,
     ∃ b, IsUnit b ∧ a = b * star b,
     0 ≤ a ∧ IsUnit a,
     IsSelfAdjoint a ∧ ∀ x ∈ spectrum ℝ a, 0 < x].TFAE := by
  tfae_have 1 ↔ 8 := IsStrictlyPositive.iff_of_unital
  tfae_have 1 ↔ 9 := ⟨fun h => ⟨h.isSelfAdjoint,
      StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a |>.mp h⟩,
    fun h => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a).mpr h.2⟩
  tfae_have 1 → 2 := fun h => ⟨h.sqrt, sqrt_mul_sqrt_self a |>.symm⟩
  tfae_have 2 → 3 := fun h => ⟨h.1.isUnit, h.2⟩
  tfae_have 3 → 4 := fun h => ⟨sqrt a, h.1.isStrictlyPositive (sqrt_nonneg _), h.2⟩
  tfae_have 4 → 5 := fun ⟨b, hb, hab⟩ => ⟨b, hb.isUnit, hb.isSelfAdjoint, hab⟩
  tfae_have 5 → 6 := fun ⟨b, hb, hbsa, hab⟩ => ⟨b, hb, hbsa.symm ▸ hab⟩
  tfae_have 6 → 7 := fun ⟨b, hb, hab⟩ => ⟨star b, hb.star, star_star b |>.symm ▸ hab⟩
  tfae_have 7 → 8 := fun ⟨b, hb, hab⟩ => ⟨hab ▸ mul_star_self_nonneg _, hab ▸ hb.mul hb.star⟩
  tfae_finish
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_
sqrt_mul_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt
    {a : A} : IsStrictlyPositive a ↔ IsStrictlyPositive (sqrt a) ∧ a = sqrt a * sqrt a :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 1
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqr
t** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
    {a : A} : IsStrictlyPositive a ↔ IsUnit (sqrt a) ∧ a = sqrt a * sqrt a :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 2
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_e
q_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_eq_mul_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsStrictlyPositive b ∧ a = b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 3
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint
_and_eq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsUnit b ∧ IsSelfAdjoint b ∧ a = b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 4
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self** 是 Mathlib 中的
一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsUnit b ∧ a = star b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 5
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self** 是 Mathlib 中的
一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsUnit b ∧ a = b * star b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 6
/-
**CFC._root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos*
* 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
    {a : A} : IsStrictlyPositive a ↔ IsSelfAdjoint a ∧ ∀ x ∈ spectrum ℝ a, 0 < x :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 8

end unital_vs_nonunital

end Unital

end CFC

